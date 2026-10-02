-- Prove2me | Definitions.Def_TeschlQM_SelfAdjoint_defectSpace
-- name    : TeschlQM_SelfAdjoint_defectSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:19:28.917683+00:00
-- url     : https://prove2.me/theorems/b3378778-6dd3-4a3f-86e0-f5bc5165dc82
-- title:
--   Defect spaces K± and equality of the defect indices, Eq. (2.101)
-- statement:
--   For a symmetric operator $A$ the **defect spaces** are
--   $$K_\pm = \operatorname{Ran}(A \pm \mathrm{i})^\perp = \operatorname{Ker}(A^* \mp \mathrm{i}),$$
--   and the **defect indices** are $d_\pm(A) = \dim K_\pm$, the Hilbert dimensions (cardinalities of orthonormal bases, possibly infinite). The defect indices are **equal** when $d_+(A) = d_-(A)$.
--
--   **Formalization Note.** $K_\pm$ are defined by the first expression, $\operatorname{Ran}(A \pm \mathrm{i})^\perp$, which does not involve the adjoint. Equality of the Hilbert dimensions is expressed as the existence of a unitary map (a surjective linear isometry, `≃ₗᵢ[ℂ]`) from $K_+$ onto $K_-$; two Hilbert spaces have equal Hilbert dimension exactly when such a map exists, and this is the form used in the book's argument before Theorem 2.26.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 81, Section 2.6, Eq. (2.101)

import Mathlib
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar

namespace TeschlQM.SelfAdjoint

/-- Teschl (2.101), p. 81: the defect space `K₊ = Ran(A + i)^⊥` (`= Ker(A* - i)`). -/
noncomputable def defectPlus {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (rangeAdd A Complex.I)ᗮ

/-- Teschl (2.101), p. 81: the defect space `K₋ = Ran(A - i)^⊥` (`= Ker(A* + i)`). -/
noncomputable def defectMinus {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (rangeAdd A (-Complex.I))ᗮ

/-- Teschl (2.101), p. 81: the defect indices `d±(A) = dim K±` are equal. The dimension is the
Hilbert dimension (cardinality of an orthonormal basis), and two Hilbert spaces have the same
Hilbert dimension exactly when there is a unitary (a surjective linear isometry) between them;
this is the formulation used here. -/
def HasEqualDefectIndices {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Prop :=
  Nonempty (defectPlus A ≃ₗᵢ[ℂ] defectMinus A)

end TeschlQM.SelfAdjoint


