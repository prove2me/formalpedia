-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2dfe4f35-714d-5aef-bd05-01500af25bb6

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_forall_comap_openCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_smoothOfRelativeDimension_one
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc"

set_option autoImplicit false

universe u

namespace GenCartier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem main
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {K : Type u} [Field K] {gK : Spec (CommRingCat.of K) ⟶ S}
    [IsSeparated (pullback.snd f gK)] [SmoothOfRelativeDimension 1 (pullback.snd f gK)]
    {r : ℕ} (E : RelEffCartierDiv f r gK) :
    E.I.IsInvertible := by

  let e : pullback (pullback.snd f gK) (𝟙 (Spec (CommRingCat.of K))) ⟶ pullback f gK :=
    pullback.fst (pullback.snd f gK) (𝟙 _)

  have sq1 : IsPullback ((E.I.comapIso e).hom ≫ pullback.snd e E.I.subschemeι) (E.I.comap e).subschemeι
      E.I.subschemeι e := by
    refine (IsPullback.of_iso_pullback ⟨?_⟩ (E.I.comapIso e) ?_ ?_).flip
    · simp [pullback.condition]
    · simp
    · simp
  have sq2 : IsPullback e (pullback.snd (pullback.snd f gK) (𝟙 _)) (pullback.snd f gK) (𝟙 _) :=
    IsPullback.of_hasPullback (pullback.snd f gK) (𝟙 _)
  have sq := sq1.paste_vert sq2
  haveI := E.isFinite
  haveI := E.flat
  haveI := E.locallyOfFinitePresentation
  let D' : RelEffCartierDiv (pullback.snd f gK) r (𝟙 (Spec (CommRingCat.of K))) :=
    { I := E.I.comap e
      isFinite := MorphismProperty.of_isPullback sq ‹_›
      flat := MorphismProperty.of_isPullback sq ‹_›
      locallyOfFinitePresentation := MorphismProperty.of_isPullback sq ‹_›
      finrank_eq := fun t => by
        rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq t]
        exact E.finrank_eq _ }
  have hD' : (E.I.comap e).IsInvertible := RelEffCartierDiv.isInvertible_I D'

  refine Scheme.IdealSheafData.IsInvertible.of_forall_comap_openCover (Scheme.coverOfIsIso.{u, u} e) E.I ?_
  intro i
  simp at hD' ⊢
  exact hD'

end GenCartier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {K : Type u} [Field K] {gK : Spec (CommRingCat.of K) ⟶ S}
    [IsSeparated (pullback.snd f gK)] [SmoothOfRelativeDimension 1 (pullback.snd f gK)]
    {r : ℕ} (E : RelEffCartierDiv f r gK) :
    E.I.IsInvertible :=
  GenCartier.main E

end S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_smoothOfRelativeDimension_one (solution)
