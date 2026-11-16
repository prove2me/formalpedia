-- Prove2me | Definitions.Def_GeomDRSub_Supplement_Vn
-- name    : GeomDRSub_Supplement_Vn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:49:38.220887+00:00
-- url     : https://prove2.me/theorems/03fe0864-b62a-442f-a5a2-d2f800cf2b51
-- title:
--   $V_n(\zeta)=\min_{\omega\in\Delta_4}\max_{j}\max_{0\le x\le1/2}Q_{j,n,\zeta}(x;\omega)$
-- statement:
--   With the simplex $\Delta_4=\{\omega\in\mathbb R^4_+:\eta+\theta+\lambda+\mu=1\}$,
--   $$V_n(\zeta)=\min_{\omega\in\Delta_4}\ \max_{j\in\{0,1\}}\ \max_{0\le x\le 1/2}Q_{j,n,\zeta}(x;\omega)$$
--   (Eq. (151)).
--
--   **Formalization Note** The maxima and the minimum are the supremum and infimum of images of compact sets under continuous maps, so they are attained. $\Delta_4$ is Mathlib's standard simplex on four coordinates.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 6.2, p.38, Eq. (151)

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_Q0
import Definitions.Def_GeomDRSub_Supplement_Q1

namespace GeomDRSub.Supplement

/-- **`V_n(ζ) = min_{ω∈Δ₄} max_{j∈{0,1}} max_{0≤x≤1/2} Q_{j,n,ζ}(x; ω)`**, Eq. (151). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545,
Section 6.2, p.38, with the simplex `Δ₄ = {ω ∈ ℝ⁴₊ : η + θ + λ + µ = 1}` (p.37).

**Formalization Note.** `Δ₄` is Mathlib's `stdSimplex ℝ (Fin 4)`. The inner maxima are `sSup` of the
image of `[0, 1/2]` and the outer minimum is `sInf` of the image of `Δ₄`; every set involved is
nonempty and bounded (continuous functions on compact sets), so these are the paper's max and min. -/
noncomputable def Vn (n : ℕ) (ζ : ℝ) : ℝ :=
  sInf ((fun w : Fin 4 → ℝ =>
      max (sSup (Q0 n ζ w '' Set.Icc 0 (1 / 2))) (sSup (Q1 n ζ w '' Set.Icc 0 (1 / 2)))) ''
    stdSimplex ℝ (Fin 4))

end GeomDRSub.Supplement


