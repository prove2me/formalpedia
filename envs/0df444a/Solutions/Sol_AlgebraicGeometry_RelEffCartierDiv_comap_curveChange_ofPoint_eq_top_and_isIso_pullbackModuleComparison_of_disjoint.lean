-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f4ff12cc-6f33-5fbd-ad42-a8995108bfb9

import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint.AlgebraicGeometry"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme.Hom Scheme.Hom.support_ker Spec Scheme Scheme.ker_eq_top_of_isEmpty Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsClosedImmersion IsSeparated Scheme.Hom.comp_apply Scheme.IdealSheafData RelEffCartierDiv graphOver graphOver_fst RelEffCartierDiv.ofPoint RelEffCartierDiv.ofPoint_I RelPicard.curveChange RelEffCartierDiv.supportedIn_iff Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top RelEffCartierDiv.isInvertible_I_of_supportedIn" namespace RelEffCartierDiv p2m_export "AlgebraicGeometry.RelEffCartierDiv" "I ofPoint ofPoint_I SupportedIn supportedIn_iff isInvertible_I_of_supportedIn" end AlgebraicGeometry.RelEffCartierDiv
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.RelEffCartierDiv" in

theorem AlgebraicGeometry.RelEffCartierDiv.coe_support_ofPoint_I
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    ((RelEffCartierDiv.ofPoint f a ha).I.support : Set ↥(pullback f g)) = Set.range (graphOver f a ha) := by
  rw [RelEffCartierDiv.ofPoint_I, Scheme.Hom.support_ker,
    (graphOver f a ha).isClosedEmbedding.isClosed_range.closure_eq]

p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.RelEffCartierDiv" in

theorem AlgebraicGeometry.RelEffCartierDiv.supportedIn_ofPoint_of_range_subset
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) (U : 𝒞.Opens) (haU : Set.range a ⊆ (U : Set 𝒞)) :
    (RelEffCartierDiv.ofPoint f a ha).SupportedIn U := by
  rw [RelEffCartierDiv.supportedIn_iff]
  intro x hx
  have hx' : x ∈ ((RelEffCartierDiv.ofPoint f a ha).I.support : Set ↥(pullback f g)) := hx
  rw [RelEffCartierDiv.coe_support_ofPoint_I] at hx'
  obtain ⟨y, rfl⟩ := hx'
  rw [← Scheme.Hom.comp_apply, graphOver_fst]
  exact haU ⟨y, rfl⟩

theorem solution
    {R : Type u} [CommRing R] {C C'' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (c'' : C'' ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (i'' : C'' ⟶ C) (hi'' : i'' ≫ c = c'') [IsClosedImmersion i'']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : T ⟶ C) (hQ : Q ≫ c = t)
    (hdisj : Disjoint (Set.range Q.base) (Set.range i''.base))

    (V : C.Opens) (hQV : Set.range Q.base ⊆ (V : Set C)) [SmoothOfRelativeDimension 1 (V.ι ≫ c)] :
    (RelEffCartierDiv.ofPoint c Q hQ).I.comap (RelPicard.curveChange i'' hi'' t) = ⊤ ∧
      IsIso ((RelEffCartierDiv.ofPoint c Q hQ).I.pullbackModuleComparison (RelPicard.curveChange i'' hi'' t)) := by
  set f'' := RelPicard.curveChange i'' hi'' t with hf''

  have hfst : f'' ≫ pullback.fst c t = pullback.fst c'' t ≫ i'' := by
    simp only [hf'', RelPicard.curveChange, pullback.map, pullback.lift_fst]

  haveI hempty : IsEmpty ↥(pullback f'' (graphOver c Q hQ)) := by
    refine ⟨fun z => ?_⟩
    have key := congrArg (fun φ => (φ ≫ pullback.fst c t) z)
      (pullback.condition (f := f'') (g := graphOver c Q hQ))
    simp only [Category.assoc, graphOver_fst, hfst, Scheme.Hom.comp_apply] at key
    exact Set.disjoint_left.mp hdisj ⟨_, rfl⟩ ⟨_, key⟩
  have hcomap : (RelEffCartierDiv.ofPoint c Q hQ).I.comap f'' = ⊤ := by
    rw [RelEffCartierDiv.ofPoint_I, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    exact Scheme.ker_eq_top_of_isEmpty _
  refine ⟨hcomap, ?_⟩

  have hI : (RelEffCartierDiv.ofPoint c Q hQ).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn V _
      (RelEffCartierDiv.supportedIn_ofPoint_of_range_subset c Q hQ V hQV)
  have hI' : ((RelEffCartierDiv.ofPoint c Q hQ).I.comap f'').IsInvertible := by
    rw [hcomap]; exact Scheme.IdealSheafData.isInvertible_top
  exact Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f'' hI hI'

end S_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint (solution)
