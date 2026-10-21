-- Prove2me | Definitions.Def_IwataFF_SFM_Phase
-- name    : IwataFF_SFM_Phase
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:28.636021+00:00
-- url     : https://prove2.me/theorems/b75cf630-8c14-4e56-ba85-68218d6fec4a
-- title:
--   The δ-scaling phase: flows, residual graph, $S$, $T$, $W$, active pairs, Push, augmentation, reduction (§3, Figures 1–2, pp. 6–10)
-- statement:
--   Fix a ground set $V$ and a set function $f$. A **state** of the scaling algorithm consists of a family $(L_i, \lambda_i)_{i \in I}$, stored as a list (a new index is appended), a flow $\varphi : V \times V \to \mathbb{R}$, the scaling parameter $\delta$, and a flag saying whether the first phase has begun. The extreme base $y_i$ is the greedy vector of $L_i$, and $x = \sum_{i} \lambda_i y_i$.
--
--   - **Boundary** $\partial\varphi(v) = \sum_{u \in V} \varphi(u, v)$ (3.1) and $z = x - \partial\varphi$.
--   - $S = \{v \in V \mid x(v) \le \partial\varphi(v) - \delta\}$, $T = \{v \in V \mid x(v) \ge \partial\varphi(v) + \delta\}$.
--   - **Residual arcs** $E(\varphi) = \{(u,v) \mid u, v \in V,\ u \ne v,\ \varphi(u,v) \le 0\}$ (3.2), and $W$ = the vertices reachable from $S$ by residual paths (length $0$ allowed).
--   - $(i, v)$ is an **active pair** if $v \in V \setminus W$ is the last vertex in $L_i$ among the vertices $v'$ of $V \setminus W$ with $W \setminus L_i(v') \ne \emptyset$. $Z \neq \emptyset$ means an active pair exists.
--   - **Phase guard**: $S \ne \emptyset$, $T \ne \emptyset$, and ($Z \ne \emptyset$ or $W \cap T \ne \emptyset$). **Phase end**: $S = \emptyset$, or $T = \emptyset$, or ($Z = \emptyset$ and $W \cap T = \emptyset$). The **printed end** is $S = \emptyset$ or $T = \emptyset$ or $Z = \emptyset$.
--   - **Invariants**: $\delta > 0$, $I \ne \emptyset$, every $L_i$ a linear ordering of $V$, $\lambda_i > 0$, $\sum_i \lambda_i = 1$, $\varphi$ skew-symmetric and $-\delta \le \varphi \le \delta$ on $V \times V$.
--   - **Initial state** for an ordering $L$ and $\delta_0$: $I = \{(L, 1)\}$, $\varphi = 0$, $\delta = \delta_0$, not begun.
--   - **Phase start** (allowed before the first phase or at a phase end): $\delta \leftarrow \delta/2$, then each $\varphi(u,v)$ is moved to the nearest value in $[-\delta, \delta]$.
--   - **Push**$(i,u,v)$ (Figure 2; allowed when the guard holds, $W \cap T = \emptyset$, $(i,v)$ is active and $u$ immediately succeeds $v$ in $L_i$): with $e = \mathrm{ec}(y_i, u, v)$ and $a = \min\{\delta, \lambda_i e\}$, set $\varphi(u,v) \mathrel{-}= a$, $\varphi(v,u) \mathrel{+}= a$; if $a < \lambda_i e$, append a new index with $(L_i, \lambda_i - a/e)$ and set $\lambda_i \leftarrow a/e$; in every case interchange $u$ and $v$ in $L_i$.
--   - **Augmentation** (allowed when the guard holds and $W \cap T \ne \emptyset$): pick a repetition-free path $P$ of residual arcs from a vertex of $S$ to a vertex of $T$, add $\delta$ to $\varphi(u,v)$ and subtract $\delta$ from $\varphi(v,u)$ along each arc $(u,v)$ of $P$, then **reduce**: replace the family by a subfamily (orderings kept in order) with new positive coefficients summing to $1$, the same $x$, and affinely independent greedy vectors $y_i$.
--   - A **scaling step** is a phase start, a push, or an augmentation with its reduction. A **phase run** is a phase end, then a phase start, then pushes and augmentations; `augCount` counts the augmentations.
--   - **Fix step** (§4, p. 12): a scaling step in which a new phase may start only before the first phase or when $\delta \ge \kappa/n^3$ ($n = |V|$). **Fix output** $w$: at a phase end with $\delta < \kappa/n^3$, any $w \in V$ with $x(w) < -n^2\delta$.
--
--   **Formalization Note** The phase guard is the one described in the prose of pp. 7 and 10, not the "S ≠ ∅, T ≠ ∅ and Z ≠ ∅" printed in Figure 1, under which no phase starting from $\varphi = 0$ ever augments (see the findings). $y_i$ is not stored: it is always the greedy vector of $L_i$, which by Lemma 2.1 is what Figure 2's update $y_i \leftarrow y_i + \mathrm{ec}(y_i,u,v)(\chi_u - \chi_v)$ produces. Nondeterministic choices (active pair, augmenting path, subfamily) are relations. Fix stops when $\delta < \kappa/n^3$ rather than after the printed $\lceil \log_2(n^3\eta/\kappa) \rceil$ phases.
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, pp. 6–10, (3.1), (3.2), Figure 1 (p. 8), Figure 2 (p. 9); §4, p. 12

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic

namespace IwataFF.SFM

/-! Iwata, Fleischer & Fujishige, arXiv:math/0004089v1, §3, pp. 6–10, Figures 1–2:
the δ-scaling phase, run on a ground set `V : Finset α` and a set function `f`.

A state holds the family `(L_i, λ_i)_{i ∈ I}` as a list indexed by `i = 0, 1, …` (a new index
`k` is appended at the end), the flow `ϕ : α → α → ℝ` (read on `V × V`), the scaling parameter
`δ`, and a flag recording whether the first phase has begun. The extreme base `y_i` is not
stored: it is the base `greedy f L_i` generated by `L_i` (p. 6: "We also maintain linear
orderings `L_i` … and extreme bases `y_i` generated by them"). -/

/-- A state of the scaling algorithm (§3.1–3.2). -/
structure PhaseState (α : Type) where
  /-- the pairs `(L_i, λ_i)` for `i ∈ I` -/
  idx : List (List α × ℝ)
  /-- the flow `ϕ` -/
  phi : α → α → ℝ
  /-- the scaling parameter `δ` -/
  delta : ℝ
  /-- `false` before the first phase starts (before the first halving of `δ`) -/
  begun : Bool

variable {α : Type} [DecidableEq α]

/-- p. 6: `x = ∑_{i ∈ I} λ_i y_i` with `y_i` the extreme base generated by `L_i`. -/
noncomputable def xOf (f : Finset α → ℝ) (st : PhaseState α) : α → ℝ :=
  fun a => (st.idx.map (fun p => p.2 * greedy f p.1 a)).sum

/-- (3.1), p. 6: the boundary `∂ϕ(v) = ∑_{u ∈ V} ϕ(u, v)`. -/
noncomputable def bdry (V : Finset α) (st : PhaseState α) : α → ℝ :=
  fun v => ∑ u ∈ V, st.phi u v

/-- p. 6: `z = x − ∂ϕ`. -/
noncomputable def zOf (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : α → ℝ :=
  fun v => xOf f st v - bdry V st v

/-- p. 7 and Figure 1: `S = {v ∈ V | x(v) ≤ ∂ϕ(v) − δ}`. -/
noncomputable def Sset (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : Finset α :=
  V.filter (fun v => xOf f st v ≤ bdry V st v - st.delta)

/-- p. 7 and Figure 1: `T = {v ∈ V | x(v) ≥ ∂ϕ(v) + δ}`. -/
noncomputable def Tset (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : Finset α :=
  V.filter (fun v => bdry V st v + st.delta ≤ xOf f st v)

/-- (3.2), p. 7: `(u, v)` is an arc of the residual graph `G(ϕ)`:
`u, v ∈ V`, `u ≠ v`, `ϕ(u, v) ≤ 0`. -/
def resArc (V : Finset α) (st : PhaseState α) (u v : α) : Prop :=
  u ∈ V ∧ v ∈ V ∧ u ≠ v ∧ st.phi u v ≤ 0

open Classical in
/-- p. 7: `W`, the set of vertices reachable by directed paths (possibly of length 0) from `S`
in `G(ϕ)`. -/
noncomputable def Wset (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : Finset α :=
  V.filter (fun v => ∃ s ∈ Sset f V st, Relation.ReflTransGen (resArc V st) s v)

/-- p. 7: `(i, v)` is an active pair: `v ∈ V \ W` is the last vertex in `L_i` among the
vertices of `V \ W` that satisfy `W \ L_i(v) ≠ ∅`. (`i` is a position in the index list.) -/
def IsActive (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) (i : ℕ) (v : α) : Prop :=
  ∃ p : List α × ℝ, st.idx[i]? = some p ∧ v ∈ V ∧ v ∉ Wset f V st ∧
    (Wset f V st \ prefixSet p.1 v).Nonempty ∧
    ∀ v' ∈ V, v' ∉ Wset f V st → (Wset f V st \ prefixSet p.1 v').Nonempty →
      p.1.idxOf v' ≤ p.1.idxOf v

/-- p. 7: `Z ≠ ∅`, there is an active pair. -/
def ZNonempty (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : Prop :=
  ∃ i v, IsActive f V st i v

/-- The guard of the body of a δ-scaling phase, as the prose of pp. 7 and 10 describes it:
`S ≠ ∅`, `T ≠ ∅`, and (`Z ≠ ∅` or `W ∩ T ≠ ∅`). (Figure 1 prints "S ≠ ∅, T ≠ ∅ and Z ≠ ∅";
see the Formalization Notes.) -/
def Guard (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : Prop :=
  (Sset f V st).Nonempty ∧ (Tset f V st).Nonempty ∧
    (ZNonempty f V st ∨ (Wset f V st ∩ Tset f V st).Nonempty)

/-- p. 10: the end of a δ-scaling phase: `S = ∅`, or `T = ∅`, or `Z = ∅` with `W ∩ T = ∅`
("In the last case, we have a set of vertices `W` … such that `W ∩ T = ∅`"). This is the
negation of `Guard`. -/
def PhaseEnd (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : Prop :=
  Sset f V st = ∅ ∨ Tset f V st = ∅ ∨
    (¬ ZNonempty f V st ∧ Wset f V st ∩ Tset f V st = ∅)

/-- The end condition printed in Figure 1 and in the first sentence of p. 10:
`S = ∅`, `T = ∅`, or `Z = ∅` (without `W ∩ T = ∅`). Used only by the sharpness probe. -/
def PrintedPhaseEnd (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : Prop :=
  Sset f V st = ∅ ∨ Tset f V st = ∅ ∨ ¬ ZNonempty f V st

/-- The standing invariants of a scaling-phase state (pp. 6–7): `δ > 0`; `I ≠ ∅`; every `L_i`
is a linear ordering of `V`; `λ_i > 0` and `∑ λ_i = 1`; `ϕ` is skew-symmetric and
δ-feasible on `V × V`. -/
def PhaseInv (V : Finset α) (st : PhaseState α) : Prop :=
  0 < st.delta ∧ st.idx ≠ [] ∧ (∀ p ∈ st.idx, IsOrdering V p.1 ∧ 0 < p.2) ∧
    (st.idx.map Prod.snd).sum = 1 ∧
    (∀ u ∈ V, ∀ v ∈ V, st.phi u v + st.phi v u = 0) ∧
    (∀ u ∈ V, ∀ v ∈ V, -st.delta ≤ st.phi u v ∧ st.phi u v ≤ st.delta)

/-- The initial state from which the scaling algorithm is applied to the extreme base
generated by `L`, with `δ = δ₀` and `ϕ = 0` (p. 6; Figure 1's initialization; §4, p. 12). -/
def initPhase (L : List α) (δ₀ : ℝ) : PhaseState α :=
  { idx := [(L, 1)], phi := fun _ _ => 0, delta := δ₀, begun := false }

/-- Figure 1: each `ϕ(u, v)` moved to the nearest value in `[−δ, δ]`. -/
def clip (phi : α → α → ℝ) (d : ℝ) : α → α → ℝ :=
  fun a b => max (-d) (min d (phi a b))

/-- Figure 1, the start of a δ-scaling phase: `δ ← δ/2`, then clip `ϕ`. Allowed before the
first phase and at the end of a phase. -/
def StartStep (f : Finset α → ℝ) (V : Finset α) (st st' : PhaseState α) : Prop :=
  (st.begun = false ∨ PhaseEnd f V st) ∧
    st' = { idx := st.idx, phi := clip st.phi (st.delta / 2), delta := st.delta / 2,
            begun := true }

/-- Figure 2: `ϕ(u, v) ← ϕ(u, v) − α`, `ϕ(v, u) ← ϕ(v, u) + α`. -/
def phiPush (phi : α → α → ℝ) (u v : α) (a : ℝ) : α → α → ℝ :=
  fun p q => if p = u ∧ q = v then phi p q - a else if p = v ∧ q = u then phi p q + a
    else phi p q

/-- Figure 2, `Push(i, u, v)` on the entry `(L, λ) = (L_i, λ_i)` at position `i`:
`α = min{δ, λ_i ec(y_i, u, v)}`; if `α < λ_i ec(y_i, u, v)` a new index `k` (appended at the
end) gets `λ_k = λ_i − α/ec(y_i, u, v)`, `L_k = L_i`, and `λ_i ← α/ec(y_i, u, v)`; in every
case `L_i` is updated by interchanging `u` and `v` (so `y_i`, generated by `L_i`, becomes
`y_i + ec(y_i, u, v)(χ_u − χ_v)` by Lemma 2.1). -/
noncomputable def pushResult (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) (i : ℕ)
    (L : List α) (lam : ℝ) (u v : α) : PhaseState α :=
  let e := ec V f (greedy f L) u v
  let a := min st.delta (lam * e)
  { idx := if a < lam * e then (st.idx.set i (swapAdj L u v, a / e)) ++ [(L, lam - a / e)]
           else st.idx.set i (swapAdj L u v, lam),
    phi := phiPush st.phi u v a,
    delta := st.delta,
    begun := st.begun }

/-- Figure 1: inside a phase, while `W ∩ T = ∅` and `Z ≠ ∅`, pick an active pair `(i, v)`,
let `u` be the vertex succeeding `v` in `L_i`, and apply `Push(i, u, v)`. -/
def PushStep (f : Finset α → ℝ) (V : Finset α) (st st' : PhaseState α) : Prop :=
  st.begun = true ∧ Guard f V st ∧ Wset f V st ∩ Tset f V st = ∅ ∧
    ∃ (i : ℕ) (L : List α) (lam : ℝ) (u v : α), st.idx[i]? = some (L, lam) ∧
      IsActive f V st i v ∧ ImmSucc L u v ∧ st' = pushResult f V st i L lam u v

/-- Figure 1: `P` is a directed path from `S` to `T` in `G(ϕ)` (a δ-augmenting path), given by
its vertex sequence. -/
def IsAugPath (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) (P : List α) : Prop :=
  P.Nodup ∧ (∃ s, P.head? = some s ∧ s ∈ Sset f V st) ∧
    (∃ t, P.getLast? = some t ∧ t ∈ Tset f V st) ∧ P.IsChain (resArc V st)

open Classical in
/-- Figure 1: for every arc `(u, v)` of `P`, `ϕ(u, v) ← ϕ(u, v) + δ`, `ϕ(v, u) ← ϕ(v, u) − δ`. -/
noncomputable def augPhi (phi : α → α → ℝ) (d : ℝ) (P : List α) : α → α → ℝ :=
  fun a b => phi a b + d * ((if (a, b) ∈ P.zip P.tail then 1 else 0) -
    (if (b, a) ∈ P.zip P.tail then 1 else 0))

/-- Figure 1 and pp. 9–10: "Express `x` as `x = ∑_{i ∈ I} λ_i y_i` by possibly smaller affinely
independent subset `I` and positive coefficients `λ_i > 0` for `i ∈ I`": the new family is a
subfamily of the old (orderings kept in order, coefficients new), the coefficients are positive
and sum to 1, `x` is unchanged, and the extreme bases `y_i` are affinely independent. -/
def Reduces (f : Finset α → ℝ) (st st' : PhaseState α) : Prop :=
  st'.phi = st.phi ∧ st'.delta = st.delta ∧ st'.begun = st.begun ∧
    (st'.idx.map Prod.fst).Sublist (st.idx.map Prod.fst) ∧
    (∀ p ∈ st'.idx, 0 < p.2) ∧ (st'.idx.map Prod.snd).sum = 1 ∧
    xOf f st' = xOf f st ∧
    AffineIndependent ℝ (fun j : Fin st'.idx.length => greedy f (st'.idx.get j).1)

/-- Figure 1: if `W ∩ T ≠ ∅`, augment `δ` units of flow along a δ-augmenting path `P`, then
reduce the convex combination (one step). -/
def AugStep (f : Finset α → ℝ) (V : Finset α) (st st' : PhaseState α) : Prop :=
  st.begun = true ∧ Guard f V st ∧ (Wset f V st ∩ Tset f V st).Nonempty ∧
    ∃ P : List α, IsAugPath f V st P ∧
      Reduces f { st with phi := augPhi st.phi st.delta P } st'

/-- One step of the scaling algorithm (Figures 1–2): a phase start, a push, or an augmentation
with its reduction. No stopping rule. -/
def ScStep (f : Finset α → ℝ) (V : Finset α) (st st' : PhaseState α) : Prop :=
  StartStep f V st st' ∨ PushStep f V st st' ∨ AugStep f V st st'

/-- A run of one δ-scaling phase that follows a completed `2δ`-phase: `s 0` is the end of a
phase, `s 1` is obtained by the phase start, and `s 1 → ⋯ → s m` are pushes and
augmentations. -/
def IsPhaseRun (f : Finset α → ℝ) (V : Finset α) (s : ℕ → PhaseState α) (m : ℕ) : Prop :=
  1 ≤ m ∧ (s 0).begun = true ∧ PhaseEnd f V (s 0) ∧ StartStep f V (s 0) (s 1) ∧
    ∀ j, 1 ≤ j → j < m → PushStep f V (s j) (s (j + 1)) ∨ AugStep f V (s j) (s (j + 1))

open Classical in
/-- The number of δ-augmentations among the steps `s j → s (j+1)`, `j < m`. -/
noncomputable def augCount (f : Finset α → ℝ) (V : Finset α) (s : ℕ → PhaseState α) (m : ℕ) :
    ℕ :=
  ((Finset.range m).filter (fun j => AugStep f V (s j) (s (j + 1)))).card

/-- §4, p. 12, the procedure `Fix(f, x, η)` run until `δ < κ/n³` (`n = |V|`): a scaling step
in which a new phase may start only before the first phase or at the end of a phase with
`δ ≥ κ/n³`. -/
def FixInnerStep (f : Finset α → ℝ) (V : Finset α) (κ : ℝ) (st st' : PhaseState α) : Prop :=
  (StartStep f V st st' ∧ (st.begun = false ∨ κ / (V.card : ℝ) ^ 3 ≤ st.delta)) ∨
    PushStep f V st st' ∨ AugStep f V st st'

/-- §4, p. 12: `Fix` stops at the end of a phase with `δ < κ/n³` and may return any `w ∈ V`
with `x(w) < −n²δ`. -/
def FixOutput (f : Finset α → ℝ) (V : Finset α) (κ : ℝ) (st : PhaseState α) (w : α) : Prop :=
  st.begun = true ∧ PhaseEnd f V st ∧ st.delta < κ / (V.card : ℝ) ^ 3 ∧ w ∈ V ∧
    xOf f st w < -((V.card : ℝ) ^ 2) * st.delta

end IwataFF.SFM


