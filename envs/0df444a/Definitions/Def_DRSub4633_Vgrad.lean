-- Prove2me | Definitions.Def_DRSub4633_Vgrad
-- name    : DRSub4633_Vgrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:05:33.209991+00:00
-- url     : https://prove2.me/theorems/c6f30b8c-0814-407d-8add-9595a08cb51e
-- title:
--   The gradient combination $V(t)$
-- statement:
--   $$V(t)=\sum_{i=1}^m\chi_i\nabla_SF(a(t),P_i^+),$$
--   where $\nabla_S F$ is the small block of the gradient of $F$ on the cube.
--
--   **Formalization Note** The partial derivatives are the within-cube derivatives `GeomDRSub.pd`.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (16), p.11

import Mathlib
import Definitions.Def_DRSub4633_chi
import Definitions.Def_DRSub4633_mLarge
import Definitions.Def_DRSub4633_Pplus
import Definitions.Def_DRSub4633_resid
import Definitions.Def_DRSub4633_mergePt
import Definitions.Def_DRSub4633_aPath
import Definitions.Def_GeomDRSub_pd

namespace DRSub4633

/-- **The gradient combination `V(t)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (16), p.11:
`V(t) = ∑_(i=1)^m χᵢ ∇_S F(a(t), P⁺ᵢ)`.

`Vgrad f x t j` is the coordinate `j ∈ S` of `V(t)`; `∇_S F` is the small block of the gradient of
`F` on the cube (`GeomDRSub.pd`, the within-cube partial derivative).

**Formalization Note.** The value at a large `j` is not used. -/
noncomputable def Vgrad {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (t : ℝ) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (mLarge x),
    chi x i * GeomDRSub.pd (resid f x) j (mergePt x (aPath x t) (Pplus x i))

end DRSub4633


