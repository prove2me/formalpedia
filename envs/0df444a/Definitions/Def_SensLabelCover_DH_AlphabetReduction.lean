-- Prove2me | Definitions.Def_SensLabelCover_DH_AlphabetReduction
-- name    : SensLabelCover_DH_AlphabetReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:37:31.499621+00:00
-- url     : https://prove2.me/theorems/9eaaae7c-dc24-4a69-b060-cc24dae9145d
-- title:
--   Codes with relative distance, the alphabet reduction $T_{AR}$ with recovery $R_{AR}$, and $\mathrm{red}_\varepsilon$ with recovery $R_{\varepsilon,I}$
-- statement:
--   A **code** $C:\Sigma\to\hat\Sigma^k$ with block length $k\ge1$ has **minimum relative distance** $1-\delta$ if for all $a\neq b$ the words $C(a),C(b)$ differ in at least $(1-\delta)k$ coordinates; $C_i(b)=C(b)_i$.
--
--   The **alphabet reduction** $T_{AR}$ maps a left-predicate Label Cover instance on $G=(U,V,E)$ with right alphabet $\Sigma_V$ to one on $(U,V\times[k],E\times[k])$ with right alphabet $\hat\Sigma_V$: for every edge $e=(u,v)$ and $i\in[k]$ there is a distinct edge $(e,i)$ from $u$ to $(v,i)$ with projection $C_i\circ f_e$; predicates are unchanged. Its **recovery** $R_{AR,I}$ copies the left labels and, independently for each $v\in V$, samples $\pi(v)$ from
--   $$p_v(b)=\Pr_{e=(u,v)\ \text{uniform at } v}\big[f_e(\pi'(u))=b\big],$$
--   a uniform edge at $v$ counted with multiplicity, using the projections of all left labels, including those failing their predicates. It reads only the left labels and needs every right vertex to have positive degree.
--
--   For $0<\varepsilon<1/16$ and a constant $c_{AR}$, $d_\varepsilon:=2\lfloor c_{AR}/(2\varepsilon)\rfloor$. Given a code $C$ and degree-reduction data (expanders of degree $d$ and incidence orderings) for the alphabet-reduced graph, $\mathrm{red}_\varepsilon(I)$ applies $T_{AR}$ with $C$ and then $T_{DR}$ with these data. Its recovery is $R_{\varepsilon,I}(\pi'')=(R_{AR,I})_\#\,R_{DR}(\pi'')$: first $R_{DR}$, then $R_{AR,I}$.
--
--   These maps reduce the right alphabet and the right degree of a Label Cover family while controlling value and sensitivity.
--
--   **Formalization Note** `IsCode C δ` includes $k\ge1$. `arGraph G k` has right vertices `V × Fin k` and edges `E × Fin k` (0-based). `recoverAR` draws one uniform incident edge per right vertex: a uniform element of `∀ v, {e // right e = v}`. This has the same law as sampling each $\pi(v)$ from $p_v$ independently. `red C dr I` and `redRecover G k hD I` are parametrized by the code and the data `dr : DRData (arGraph G k) d`, which are the same for every instance of a family. They are not tied to the explicit code and expanders of Propositions 5.1 and 4.2. The structural lemma `arGraph_rdeg_pos` (no isolated right vertex survives alphabet reduction) is used to build `redRecover`.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), pp. 25–26 (PDF 28–29) §5.1; p. 28 (PDF 31) §5.2

import Mathlib
import Definitions.Def_SensLabelCover_DH_DegreeReduction

open scoped BigOperators

namespace SensLabelCover.DH

/-! Fleming, Hopkins, Yoshida, *Sensitivity and Locality Lower Bounds via Low-Soundness Label
Cover*, STOC 2027 submission (manuscript sha256 5bfe95ad…), §5 (pp. 25–28, PDF pp. 28–31): codes
with minimum relative distance, the alphabet reduction `T_AR` with its recovery `R_AR`, and the
combined alphabet-then-degree reduction `red_ε` with recovery `R_{ε,I}`.

`red_ε` is parametrized by its code and its degree-reduction data (expanders and incidence
orderings) rather than by the paper's one explicit choice (Propositions 4.2 and 5.1). -/

noncomputable section

variable {U V E SU SV SH : Type}

/-- `C : Σ → Σ̂^k` is a code (block length `k ≥ 1`) with minimum relative distance `1 − δ`
(p. 25): every two distinct symbols have codewords differing in at least `(1 − δ)k`
coordinates. -/
def IsCode [DecidableEq SH] {k : ℕ} (C : SV → Fin k → SH) (δ : ℝ) : Prop :=
  0 < k ∧ ∀ a b : SV, a ≠ b →
    (1 - δ) * (k : ℝ) ≤ ((Finset.univ.filter (fun i => C a i ≠ C b i)).card : ℝ)

/-- The graph of `T_AR(I)` (p. 25): right vertices `V × [k]`, and for every edge `e = (u, v)` and
`i ∈ [k]` a distinct edge `(e, i)` from `u` to `(v, i)`. -/
def arGraph (G : BGraph U V E) (k : ℕ) : BGraph U (V × Fin k) (E × Fin k) where
  left p := G.left p.1
  right p := (G.right p.1, p.2)

/-- `T_AR(I)` (p. 25): predicates unchanged; the edge `(e, i)` carries `C_i ∘ f_e`. -/
def tar {k : ℕ} (C : SV → Fin k → SH) (I : LCInst U E SU SV) : LCInst U (E × Fin k) SU SH where
  P := I.P
  F p a := C (I.F p.1 a) p.2

/-- If `G` has no isolated right vertex, neither does `arGraph G k`. -/
theorem arGraph_rdeg_pos [Fintype E] [DecidableEq V] (G : BGraph U V E) (k : ℕ)
    (hD : ∀ v, 0 < G.rdeg v) : ∀ w : V × Fin k, 0 < (arGraph G k).rdeg w := by
  intro w
  obtain ⟨e, he⟩ := Finset.card_pos.mp (hD w.1)
  refine Finset.card_pos.mpr ⟨(e, w.2), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  simp [arGraph, he]

/-- The recovery `R_AR,I` (p. 26): copy the left labels; for each `v ∈ V` independently pick an
edge `e = (u, v)` uniformly among the edges at `v` (with multiplicity) and set
`π(v) := f_e(π'(u))` — i.e. sample `π(v)` from `p_v(b) = Pr_e[f_e(π'(u)) = b]`, using the
projections of all left labels, including those failing their predicate. It reads only the left
labels of `π'`, so it accepts an assignment with any right side. -/
def recoverAR [Fintype E] [DecidableEq V] [Fintype V] {V' : Type} (G : BGraph U V E)
    (I : LCInst U E SU SV) (hD : ∀ v, 0 < G.rdeg v) (π' : Assignment U V' SU SH) :
    PMF (Assignment U V SU SV) :=
  haveI : ∀ v : V, Nonempty {e : E // G.right e = v} := fun v => by
    obtain ⟨e, he⟩ := Finset.card_pos.mp (hD v)
    exact ⟨⟨e, (Finset.mem_filter.mp he).2⟩⟩
  (PMF.uniformOfFintype (∀ v : V, {e : E // G.right e = v})).map
    (fun s => (π'.1, fun v => I.F (s v).1 (π'.1 (G.left (s v).1))))

/-- The target degree `d_ε := 2⌊c_AR/(2ε)⌋` of `red_ε` (p. 28). -/
def dEps (cAR ε : ℝ) : ℕ := 2 * ⌊cAR / (2 * ε)⌋₊

/-- The graph of `red_ε(I)`: the right-degree reduction (with data `dr`) of the alphabet-reduced
graph. -/
abbrev redGraph [Fintype E] [DecidableEq V] {G : BGraph U V E} {k d : ℕ}
    (dr : DRData (arGraph G k) d) : BGraph U (DRV (arGraph G k)) (DRE (arGraph G k) d) :=
  drGraph dr

/-- `red_ε(I)` (p. 28): alphabet reduction with the code `C`, transporting the left predicates
unchanged, then right-degree reduction with the data `dr` (target degree `d`, expanders and
incidence orderings on the alphabet-reduced graph, the same for every instance of a family). -/
def red [Fintype E] [DecidableEq V] {G : BGraph U V E} {k d : ℕ} (C : SV → Fin k → SH)
    (dr : DRData (arGraph G k) d) (I : LCInst U E SU SV) :
    LCInst U (DRE (arGraph G k) d) SU SH :=
  tdr dr (tar C I)

/-- The recovery `R_{ε,I}` (p. 28): the two recoveries composed in reverse order, first `R_DR`
on the alphabet-reduced graph, then `R_AR,I`. -/
def redRecover [Fintype E] [DecidableEq V] [Fintype V] (G : BGraph U V E) (k : ℕ)
    (hD : ∀ v, 0 < G.rdeg v) (I : LCInst U E SU SV)
    (π'' : Assignment U (DRV (arGraph G k)) SU SH) : PMF (Assignment U V SU SV) :=
  (recoverDR (arGraph G k) (arGraph_rdeg_pos G k hD) π'').bind (recoverAR G I hD)

end

end SensLabelCover.DH


