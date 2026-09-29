-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/bbf5aba8-0c64-51a0-bcce-8fb0bd92ed1b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RiemannForm"

namespace MonoScalarTensor

theorem isConstScalar_id {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (M : A.Modules) :
    IsConstScalar f (𝟙 M) 1 := by
  intro U s
  simp only [map_one, one_smul, Scheme.Modules.Hom.id_app]
  rfl

end MonoScalarTensor

open MonoScalarTensor in
theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M : A.Modules} (σ : M ⟶ M) (c : k) (h : IsConstScalar f σ c) (K : A.Modules) :
    IsConstScalar f (σ ▷ K) c ∧ IsConstScalar f (K ◁ σ) c := by
  constructor
  · have := AlgebraicGeometry.RiemannForm.isConstScalar_tensorHom k f σ (𝟙 K) c 1 h (isConstScalar_id f K)
    rwa [mul_one, tensorHom_id] at this
  · have := AlgebraicGeometry.RiemannForm.isConstScalar_tensorHom k f (𝟙 K) σ 1 c (isConstScalar_id f K) h
    rwa [one_mul, id_tensorHom] at this

end S_AlgebraicGeometry_RiemannForm_isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2 (solution)
