-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.iso_of_isPullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3c758b1c-0953-578a-bdb0-49a85e330cbb

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem solution
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (v v' : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u v) (h' : PolarisedAbelianScheme.IsPullback φ u v') :
    PolarisedAbelianScheme.Iso v v' := by
  obtain ⟨gA, hg, hmul, hP, ⟨epol⟩⟩ := h
  obtain ⟨gA', hg', hmul', hP', ⟨epol'⟩⟩ := h'

  let e : v.A ≅ v'.A := hg.isoIsPullback _ _ hg'
  have he₁ : e.hom ≫ gA' = gA := hg.isoIsPullback_hom_fst _ _ hg'
  have he₂ : e.hom ≫ v'.f = v.f := hg.isoIsPullback_hom_snd _ _ hg'
  refine ⟨e, he₂, ?_, ?_, ?_⟩
  ·
    intro T t x y
    apply hg'.hom_ext
    · rw [Category.assoc, he₁, hmul t x y, hmul']
      congr 2 <;> exact Subtype.ext (by simp only [Category.assoc, he₁])
    · rw [Category.assoc, he₂, (v.L.mul t x y).2]
      exact ((v'.L.mul t _ _).2).symm
  ·
    intro i
    apply hg'.hom_ext
    · rw [Category.assoc, he₁, hP i, hP' i]
    · rw [Category.assoc, he₂, (v.P i).2, (v'.P i).2]
  ·
    intro s
    refine ⟨⊤, TopologicalSpace.Opens.mem_top s, ?_⟩
    have E : (Scheme.Modules.pullback e.hom).obj v'.pol ≅ v.pol :=
      (Scheme.Modules.pullback e.hom).mapIso epol'.symm ≪≫ (Scheme.Modules.pullbackComp e.hom gA').app u.pol ≪≫
        (Scheme.Modules.pullbackCongr he₁).app u.pol ≪≫ epol
    exact ⟨(Scheme.Modules.pullback (v.f ⁻¹ᵁ ⊤).ι).mapIso E⟩

end S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback (solution)
