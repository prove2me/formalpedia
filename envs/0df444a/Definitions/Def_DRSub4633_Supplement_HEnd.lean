-- Prove2me | Definitions.Def_DRSub4633_Supplement_HEnd
-- name    : DRSub4633_Supplement_HEnd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:34:46.384213+00:00
-- url     : https://prove2.me/theorems/ecee7392-acc1-445e-b264-bad16428bb07
-- title:
--   The endpoint gradient bound $H(f)$, Eq. (5)
-- statement:
--   For $f$ on $[0,1]^n$,
--   $$H_i(f)=\max\{|\partial_if(\mathbf 0)|,|\partial_if(\mathbf 1)|\},\qquad H(f)=\Big(\sum_{i=1}^nH_i(f)^2\Big)^{1/2}.$$
--
--   **Formalization Note** The partial derivatives are taken within the cube (`GeomDRSub.pd`), so at the corners $\mathbf 0$ and $\mathbf 1$ they are the continuous extensions of the interior derivatives.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 3.1, Eq. (5), p.8

import Mathlib
import Definitions.Def_GeomDRSub_pd

namespace DRSub4633.Supplement

/-- **The endpoint gradient bound `H(f)`, Eq. (5).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 3.1, Eq. (5), p.8:
"`Hᵢ(f) = max{|∂ᵢf(0)|, |∂ᵢf(1)|}`, `H(f) = (∑ᵢ Hᵢ(f)²)^{1/2}`".

**Formalization Note.** `∂ᵢf` is the within-cube partial derivative `GeomDRSub.pd` (boundary
derivatives as continuous extensions, p.7); `0` and `1` are the all-zero and all-one vectors. -/
noncomputable def HEnd {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  Real.sqrt (∑ i, (max |GeomDRSub.pd f i 0| |GeomDRSub.pd f i (WithLp.toLp 2 (fun _ => 1))|) ^ 2)

end DRSub4633.Supplement


