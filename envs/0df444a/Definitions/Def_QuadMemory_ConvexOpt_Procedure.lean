-- Prove2me | Definitions.Def_QuadMemory_ConvexOpt_Procedure
-- name    : QuadMemory_ConvexOpt_Procedure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:52.26823+00:00
-- url     : https://prove2.me/theorems/1ce0e306-d465-44e1-ac5c-5429d8c5598e
-- title:
--   §3.1, Procedure 1 and Definition 6, pp. 9–11 — the hard functions F_{A,v,p,l}, their subgradient ∂F, the optimization procedure, and success for the procedure
-- statement:
--   This module defines the adaptive hard instance of Blanchard, Zhang and Jaillet.
--
--   1. **Subgradients of $\|Ax\|_\infty$ (p. 9).** $g_A(x)=a_{i_{min}}$ with $i_{min}=\min\{i:|a_i^\top x|=\|Ax\|_\infty\}$, and $\tilde g_A(x)=\epsilon\,g_A(x)$ with $\epsilon=\mathrm{sign}(g_A(x)^\top x)$.
--   2. **Hard functions (p. 9).** For $v_0\in\mathcal D_\delta$ and vectors $v_{p',l'}$ constructed so far, $F_A(x)=\max\{\|Ax\|_\infty-\eta,\eta v_0^\top x\}$ and
--   $$F_{A,v,p,l}(x)=\max\Big\{\|Ax\|_\infty-\eta,\ \eta v_0^\top x,\ \eta\Big(\max_{(p',l')\le_{lex}(p,l)}v_{p',l'}^\top x-p'\gamma_1-l'\gamma_2\Big)\Big\},$$
--   with $F_{A,v,1,0}=F_A$. Its subgradient $\partial F_{A,v,p,l}(x)$ is $\tilde g_A(x)$ if $F_{A,v,p,l}(x)=\|Ax\|_\infty-\eta$; otherwise $\eta v_0$ if $F_{A,v,p,l}(x)=\eta v_0^\top x$; otherwise $\eta v_{p',l'}$ for the lexicographically first maximizer $(p',l')$.
--   3. **Procedure 1 (pp. 10–11)**, run with an algorithm $alg$ and parameter $k$. It samples $A\sim\mathcal U(\{\pm1\}^{n\times d})$ and $v_0\sim\mathcal U(\mathcal D_\delta)$, sets $p=1$, $r=l=0$, and at each iteration $t\ge1$ answers the query $x_t$ of $alg$. If $t>d^2$ the construction ends. If $F_A(x_t)>\eta$ (non-informative) it returns $(\|Ax_t\|_\infty-\eta,\tilde g_A(x_t))$. Otherwise: if $r\le k-1$, $F_{A,v,p,l}(x_t)\le-\eta\gamma_1/2$ and $\|P_{\mathrm{Span}(x_{i_{p,r'}},r'\le r)^\perp}(x_t)\|/\|x_t\|\ge\gamma_2/4$, the query is exploratory and $r$ increases. Then, if $F_{A,v,p,l}(x_t)<-\eta(p\gamma_1+l\gamma_2+\gamma_2/2)$: when $r<k$, a new vector $v_{p,l+1}=\varphi_\delta(y)$ is built from a sample $y$ of the slab of the exploratory queries; else, when $p+1\le p_{max}$, period $p$ ends and $v_{p+1,1}=\varphi_\delta(y)$ is built from the slab of $x_t$, with $p\leftarrow p+1$, $l=r=1$; else the construction ends. The response is $(F_{A,v,p,l}(x_t),\partial F_{A,v,p,l}(x_t))$ with the updated vectors. Once the construction is over, the procedure is a first-order oracle of the final function $F_{A,v,P,L}$.
--   4. **Definition 6 (p. 11).** $alg$ is successful for the procedure with probability $q$ and accuracy $\epsilon$ if, with probability at least $q$ over $A$ and the procedure, its final answer $x^\star(alg)$ satisfies
--   $$F_{A,v,P,L}(x^\star(alg))\le\min_{x\in B_d(0,1)}F_{A,v,P,L}(x)+\epsilon .$$
--
--   These objects carry Lemma 7 and Propositions 8–11.
--
--   **Formalization Note.** The procedure is a deterministic state machine (`procStep`, `procRun`) driven by $A$ and a stream $w$ of hint cells: hint $0$ is $v_0$ and hint $c$ is the $c$-th vector constructed. Its law (`procWeight`) is the product of the slab probabilities of the cells, each slab built from the queries recorded at that draw. Constructed vectors are stored as triples $(p,l,v_{p,l})$ in construction order, which is the lexicographic order. The page's misprints are read as follows: line 6's $F_A(x)$ is $F_A(x_t)$, and the subgradient's $\partial F_{A,v,l,p}$ is $\partial F_{A,v,p,l}$. Line 19 resets $l=r=1$, and the exploratory queries of the new period are $\{x_t\}$. When the algorithm stops, the construction ends (no further query is made). $\mathrm{sign}(0)=0$. A hint index beyond $d-1$ gives the junk vector $0$; it is never reached when $1+kp_{max}\le d$, which (3) ensures.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 9 (g_A, g̃_A, F_{A,v}, F_A, F_{A,v,p,l}, ∂F_{A,v,p,l}), p. 10 (Procedure 1), pp. 10–11 (its prose), p. 11 (Definition 6)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game

open scoped RealInnerProductSpace ENNReal

namespace QuadMemory.ConvexOpt

variable {d : ℕ}

/-! ### The hard family `F_{A,v,p,l}` and its subgradient (§3.1, p. 9) -/

/-- `g_A(x) = a_{i_min}` with `i_min = min{i ∈ [n] : |a_iᵀ x| = ‖A x‖_∞}` (p. 9); `0` if `A` has no
rows. -/
noncomputable def gA (A : SignMatrix d) (x : E d) : E d :=
  open Classical in
  if h : (Finset.univ.filter fun i => |⟪rowVec A i, x⟫| = supNormA A x).Nonempty then
    rowVec A ((Finset.univ.filter fun i => |⟪rowVec A i, x⟫| = supNormA A x).min' h)
  else 0

/-- `g̃_A(x) = ε g_A(x)` with `ε = sign(g_A(x)ᵀ x)` (`sign 0 = 0`), a subgradient of
`x ↦ ‖A x‖_∞` (p. 9). -/
noncomputable def gTildeA (A : SignMatrix d) (x : E d) : E d :=
  Real.sign ⟪gA A x, x⟫ • gA A x

/-- `F_A(x) = max{‖A x‖_∞ - η, η v_0ᵀ x}` (p. 9). -/
noncomputable def FA (A : SignMatrix d) (v0 : E d) (x : E d) : ℝ :=
  max (supNormA A x - eta d) (eta d * ⟪v0, x⟫)

/-- A constructed vector `v_{p,l}` is stored as the triple `(p, l, v_{p,l})`; its term in
`F_{A,v,p,l}` is `v_{p,l}ᵀ x - p γ₁ - l γ₂`. -/
noncomputable def vecTerm (u : ℕ × ℕ × E d) (x : E d) : ℝ :=
  ⟪u.2.2, x⟫ - (u.1 : ℝ) * gamma1 d - (u.2.1 : ℝ) * gamma2 d

/-- `F_{A,v,p,l}(x) = max{‖A x‖_∞ - η, η v_0ᵀ x, η max_{(p',l')} (v_{p',l'}ᵀ x - p' γ₁ - l' γ₂)}`,
the maximum running over the vectors `vs` constructed so far (p. 9); with no vector it is
`F_A` (the convention `F_{A,v,1,0} = F_A`). -/
noncomputable def FAv (A : SignMatrix d) (v0 : E d) (vs : List (ℕ × ℕ × E d)) (x : E d) : ℝ :=
  vs.foldl (fun acc u => max acc (eta d * vecTerm u x)) (FA A v0 x)

/-- The first vector of `vs` (in construction order, which is the lexicographic order of the
indices `(p, l)`) maximizing `v_{p,l}ᵀ x - p γ₁ - l γ₂`; ties go to the earlier vector. -/
noncomputable def argmaxVec (vs : List (ℕ × ℕ × E d)) (x : E d) : Option (ℕ × ℕ × E d) :=
  vs.foldl (fun best u =>
    match best with
    | none => some u
    | some b => if vecTerm b x < vecTerm u x then some u else some b) none

/-- The subgradient `∂F_{A,v,p,l}(x)` (p. 9): `g̃_A(x)` if `F_{A,v,p,l}(x) = ‖A x‖_∞ - η`;
otherwise `η v_0` if `F_{A,v,p,l}(x) = η v_0ᵀ x`; otherwise `η v_{p,l}` for the lexicographically
first maximizer `(p,l)` of `v_{p,l}ᵀ x - p γ₁ - l γ₂`. -/
noncomputable def subgradFAv (A : SignMatrix d) (v0 : E d) (vs : List (ℕ × ℕ × E d)) (x : E d) :
    E d :=
  open Classical in
  if FAv A v0 vs x = supNormA A x - eta d then gTildeA A x
  else if FAv A v0 vs x = eta d * ⟪v0, x⟫ then eta d • v0
  else eta d • ((argmaxVec vs x).elim 0 fun u => u.2.2)

/-! ### Procedure 1 (p. 10, prose pp. 10–11) -/

/-- The state of Procedure 1 run with an algorithm of `M` bits, before a query. -/
structure ProcState (d M : ℕ) where
  /-- the memory of the algorithm -/
  mem : State M
  /-- the current period `p` -/
  p : ℕ
  /-- the number `l` of vectors of the current period constructed so far -/
  l : ℕ
  /-- the number `r` of exploratory queries of the current period -/
  r : ℕ
  /-- the exploratory queries `x_{i_{p,1}}, …, x_{i_{p,r}}` of the current period -/
  expl : List (E d)
  /-- the constructed vectors `v_{p',l'}` as triples `(p', l', v_{p',l'})`, in construction
  order -/
  vs : List (ℕ × ℕ × E d)
  /-- the queries defining the slab of each hint sampled after `v_0`, in sampling order -/
  draws : List (List (E d))
  /-- the construction phase is over (lines 4 and 22, or the algorithm stopped) -/
  done : Bool
  /-- the period `p_max` was ended (line 22) -/
  ended : Bool

/-- The initial state (line 2): memory `0^M`, `p = 1`, `r = l = 0`, nothing constructed. -/
def ProcState.init (d M : ℕ) : ProcState d M :=
  ⟨fun _ => false, 1, 0, 0, [], [], [], false, false⟩

/-- The `c`-th hint vector of the stream `w` of cells: `v = φ_δ(y) = b_{w_c}`. Hint `0` is `v_0`.
(Junk `0` for `c ≥ d`, which the procedure never reaches when `1 + k p_max ≤ d`.) -/
def hintVec (D : SphereDisc d) (w : Fin d → D.ι) (c : ℕ) : E d :=
  if h : c < d then D.rep (w ⟨c, h⟩) else 0

/-- One iteration `t ≥ 1` of Procedure 1 with parameter `k` (lines 4–23, and line 25 once the
construction is over): given the state before the query, return the state after it and the
response `(f_t, g_t)` given to the algorithm for its query `x_t`. The hints are read from the
stream `w` of cells. -/
noncomputable def procStep {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d)
    (A : SignMatrix d) (w : Fin d → D.ι) (t : ℕ) (st : ProcState d M) :
    ProcState d M × (ℝ × E d) :=
  open Classical in
  let v0 := hintVec D w 0
  let x := alg.query st.mem
  let g1 := gamma1 d
  let g2 := gamma2 d
  -- the state and response before the memory update
  let core : ProcState d M × (ℝ × E d) :=
    if st.done ∨ d ^ 2 < t then
      -- line 4 / Part 2 (line 25): a first-order oracle of the final function
      ({ st with done := true }, (FAv A v0 st.vs x, subgradFAv A v0 st.vs x))
    else if eta d < FA A v0 x then
      -- lines 6–7: non-informative query
      (st, (supNormA A x - eta d, gTildeA A x))
    else
      -- lines 8–23: informative query
      let F := FAv A v0 st.vs x
      -- lines 9–10: exploratory query
      let isExpl : Prop := st.r + 1 ≤ k ∧ F ≤ -(eta d * g1 / 2) ∧
        g2 / 4 ≤ Metric.infDist x (Submodule.span ℝ {y | y ∈ st.expl} : Set (E d)) / ‖x‖
      let expl1 := if isExpl then st.expl ++ [x] else st.expl
      let r1 := if isExpl then st.r + 1 else st.r
      let thr := -(eta d * ((st.p : ℝ) * g1 + (st.l : ℝ) * g2 + g2 / 2))
      let st1 : ProcState d M :=
        if F < thr ∧ r1 < k then
          -- lines 11–14: new vector `v_{p,l+1}` from the slab of the exploratory queries
          { st with r := r1, expl := expl1, l := st.l + 1,
                    vs := st.vs ++ [(st.p, st.l + 1, hintVec D w (st.draws.length + 1))],
                    draws := st.draws ++ [expl1] }
        else if F < thr ∧ st.p + 1 ≤ pmax d k then
          -- lines 15–19: period `p` ends, `v_{p+1,1}` from the slab of `x_t`
          { st with p := st.p + 1, l := 1, r := 1, expl := [x],
                    vs := st.vs ++ [(st.p + 1, 1, hintVec D w (st.draws.length + 1))],
                    draws := st.draws ++ [[x]] }
        else if F < thr then
          -- lines 20–22: period `p_max` ends; end of the construction
          { st with r := r1, expl := expl1, done := true, ended := true }
        else
          -- case (2a): nothing is constructed
          { st with r := r1, expl := expl1 }
      -- line 23
      (st1, (FAv A v0 st1.vs x, subgradFAv A v0 st1.vs x))
  let mem' := alg.update st.mem x core.2
  ({ core.1 with mem := mem', done := core.1.done || alg.halt mem' }, core.2)

/-- The state of Procedure 1 after `t` iterations. -/
noncomputable def procRun {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d)
    (A : SignMatrix d) (w : Fin d → D.ι) : ℕ → ProcState d M
  | 0 => ProcState.init d M
  | t + 1 => (procStep alg k D A w (t + 1) (procRun alg k D A w t)).1

/-- The query `x_t` of the algorithm at iteration `t ≥ 1` of the procedure. -/
noncomputable def procQuery {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d)
    (A : SignMatrix d) (w : Fin d → D.ι) (t : ℕ) : E d :=
  alg.query (procRun alg k D A w (t - 1)).mem

/-- The response `(f_t, g_t)` of the procedure at iteration `t ≥ 1`. -/
noncomputable def procResp {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d)
    (A : SignMatrix d) (w : Fin d → D.ι) (t : ℕ) : ℝ × E d :=
  (procStep alg k D A w t (procRun alg k D A w (t - 1))).2

/-- The vectors `v` constructed by the procedure (the construction is over after `d²`
iterations). -/
noncomputable def finalVecs {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d)
    (A : SignMatrix d) (w : Fin d → D.ι) : List (ℕ × ℕ × E d) :=
  (procRun alg k D A w (d ^ 2)).vs

/-- `F_{A,v,P,L}`, the function defined by all constructed vectors (`F_{A,v}` when every period
was completed). -/
noncomputable def Ffinal {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d)
    (A : SignMatrix d) (w : Fin d → D.ι) (x : E d) : ℝ :=
  FAv A (hintVec D w 0) (finalVecs alg k D A w) x

/-- `∂F_{A,v,P,L}`. -/
noncomputable def subgradFfinal {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d)
    (A : SignMatrix d) (w : Fin d → D.ι) (x : E d) : E d :=
  subgradFAv A (hintVec D w 0) (finalVecs alg k D A w) x

/-- The procedure ended the period `p_max` (it reached line 22). -/
def EndsLastPeriod {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d) (A : SignMatrix d)
    (w : Fin d → D.ι) : Prop :=
  (procRun alg k D A w (d ^ 2)).ended = true

/-- The queries defining the slab of hint `c`: none for `c = 0` (`v_0 ∼ U(D_δ)`), the recorded
ones for the hints sampled later, none for hints never sampled. -/
noncomputable def drawQuery {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d)
    (A : SignMatrix d) (w : Fin d → D.ι) (c : Fin d) : List (E d) :=
  if (c : ℕ) = 0 then [] else (procRun alg k D A w (d ^ 2)).draws.getD ((c : ℕ) - 1) []

/-- The probability of the hint cells `w` given `A` in Procedure 1: the product over the hints of
the probability that a uniform sample of the hint's slab falls in the cell `w c` (hints never
sampled are dummy uniform samples, which do not change any probability). -/
noncomputable def procWeight {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d)
    (A : SignMatrix d) (w : Fin d → D.ι) : ℝ≥0∞ :=
  ∏ c : Fin d, hintWeight D (fun i => (drawQuery alg k D A w c).get i) (w c)

/-- The probability of an event `S` of the procedure: `A ∼ U({±1}^{n×d})` and the hints follow
`procWeight`. -/
noncomputable def procProb {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d)
    (S : SignMatrix d → (Fin d → D.ι) → Prop) : ℝ≥0∞ :=
  ∑ A : SignMatrix d, ∑ w : Fin d → D.ι,
    open Classical in
    if S A w then (Fintype.card (SignMatrix d) : ℝ≥0∞)⁻¹ * procWeight alg k D A w else 0

/-- The algorithm, run with the responses of the procedure, stops at some iteration `T ≥ 1`
and its final answer `x_T` satisfies `F_{A,v,P,L}(x_T) ≤ min_{B_d(0,1)} F_{A,v,P,L} + ε`. -/
def ProcSucceeds {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d) (ε : ℝ)
    (A : SignMatrix d) (w : Fin d → D.ι) : Prop :=
  ∃ T : ℕ, 1 ≤ T ∧ alg.halt (procRun alg k D A w T).mem = true ∧
    (∀ s : ℕ, 1 ≤ s → s < T → alg.halt (procRun alg k D A w s).mem = false) ∧
    ∀ y ∈ Metric.closedBall (0 : E d) 1,
      Ffinal alg k D A w (procQuery alg k D A w T) ≤ Ffinal alg k D A w y + ε

/-- Definition 6 (p. 11): `alg` is successful for the optimization procedure with probability
`q` and accuracy `ε`. -/
def ProcSuccess {M : ℕ} (alg : MemAlg d M) (k : ℕ) (D : SphereDisc d) (q ε : ℝ) : Prop :=
  ENNReal.ofReal q ≤ procProb alg k D (ProcSucceeds alg k D ε)

end QuadMemory.ConvexOpt


