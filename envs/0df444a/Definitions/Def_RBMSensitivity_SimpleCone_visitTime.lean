-- Prove2me | Definitions.Def_RBMSensitivity_SimpleCone_visitTime
-- name    : RBMSensitivity_SimpleCone_visitTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:26.328114+00:00
-- url     : https://prove2.me/theorems/fee57f53-445a-494b-ac4b-17133abda242
-- title:
--   The face-visiting times $\tau_K^{\alpha,x}(j)$
-- statement:
--   For a path $z$ in $G$ and $K\in(0,\infty]$, set $\tau_K(0):=0$ and, when $\tau_K(j-1)<\infty$,
--   $$\tau_K(j):=\inf\Big\{t>\tau_K(j-1):\bigcup_{s\in[\tau_K(j-1),t]}\mathcal I(z(s))=\mathcal I,\ z(t)\in G_K\Big\}.$$
--   If $\tau_K(j)=\infty$ then $\tau_K(k):=\infty$ for all $k>j$. Applied to the path of $Z^{\alpha,x}$ this gives the paper's $\tau_K^{\alpha,x}(j)$. When $K=\infty$ the subscript is dropped.
--
--   Each interval between consecutive times contains a visit to every face, and each such visit produces a contraction of the derivative process.
--
--   **Formalization Note** Times take values in $[0,\infty]$, so an infimum over the empty set is $\infty$.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §6.1, (6.1), p.22

import Mathlib
import Definitions.Def_RBMSensitivity_SimpleCone_I
import Definitions.Def_RBMSensitivity_SimpleCone_GK
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The times `τ_K(j)` of (6.1), for a fixed path `z`: arXiv:1907.00472v2, §6.1, p.22.

`τ_K(0) := 0` and `τ_K(j)` is the infimum of the `t > τ_K(j-1)` such that
`⋃_{s ∈ [τ_K(j-1), t]} I(z(s)) = I` and `z(t) ∈ G_K`.

**Formalization Note.** Values are in `ℝ≥0∞`, so the infimum of the empty set is `∞`, as on p.4 of
the paper. No time exceeds `∞`, so `τ_K(j) = ∞` forces `τ_K(k) = ∞` for `k > j`, which is the
paper's convention. The case `K = ∞` of the paper is `K = ⊤`. Evaluated at the path
`s ↦ Z^{α,x}(s, ω)`, this is the paper's `τ_K^{α,x}(j)(ω)`. -/
noncomputable def SimpleCone.visitTime {J : ℕ} (C : SimpleCone J) (K : ℝ≥0∞) (z : ℝ≥0 → E J) :
    ℕ → ℝ≥0∞
  | 0 => 0
  | j + 1 =>
    ⨅ (t : ℝ≥0) (_ : SimpleCone.visitTime C K z j < t ∧
        (⋃ s ∈ {s : ℝ≥0 | SimpleCone.visitTime C K z j ≤ s ∧ s ≤ t}, C.I (z s)) = Set.univ ∧
        z t ∈ C.GK K),
      (t : ℝ≥0∞)

end RBMSensitivity


