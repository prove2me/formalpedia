-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
-- name    : QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:07:35.428043+00:00
-- url     : https://prove2.me/theorems/4bc9824a-8e5a-4802-b94e-7b560ae52144
-- title:
--   Step Place Transport
-- statement:
--   Definitions and structural lemmas for Step Place Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/StepPlaceTransport.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepTransport
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
namespace GlobalPlace
variable {k K L : Type*} [Field k] [Finite k]
variable [Field K] [Algebra k K] [Field L] [Algebra k L]
noncomputable def comapAlgEquiv (e : K ≃ₐ[k] L)
    (P : GlobalPlace k L) : GlobalPlace k K where
  valuation := P.valuation.comap e.toRingHom
  normalized := by
    intro gamma
    obtain ⟨y, hy⟩ := P.normalized gamma
    refine ⟨e.symm y, ?_⟩
    change P.valuation (e (e.symm y)) = gamma
    rw [e.apply_symm_apply, hy]
end GlobalPlace
namespace F256GarciaStichtenoth
noncomputable def transportedStepAbovePlace (i : ℕ)
    (P : GlobalPlace F256 (Field i))
    (hP : P.order (distinguishedCoordinate i) = -1) :
    GlobalPlace F256 (Field (i + 1)) :=
  GlobalPlace.comapAlgEquiv
    ((stepFieldEquiv (distinguishedPlace i) P
      (distinguishedCoordinate i) (distinguishedCoordinate_order i) hP).restrictScalars F256)
    (stepAbovePlace P (distinguishedCoordinate i) hP)
end F256GarciaStichtenoth
end
end QEC.Coding.AlgebraicGeometry


