-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_section_comp_eq_of_exists_mem_closure_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/284504fc-38d8-5578-a4f2-7721e22e1096

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_extension_of_mem_image_graph
import Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_mem_closure_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (hcl : ∃ z ∈ closure (Set.range x.base), f.base z = IsLocalRing.closedPoint R) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x := by
  classical
  set ιK := Spec.map (CommRingCat.ofHom (algebraMap R K)) with hιK
  set g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) := 𝟙 _ with hg
  set η : ↥(Spec (CommRingCat.of R)) := IsLocalRing.closedPoint R with hη

  have hηs : g.base η = IsLocalRing.closedPoint R := rfl
  have hgen : ∀ y : ↥(Spec (CommRingCat.of R)), y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η :=
    fun y _ hy => hy
  have hirr : ∀ y : ↥(Spec (CommRingCat.of R)), g.base y = IsLocalRing.closedPoint R → η ⤳ y := by
    intro y hy; change y = _ at hy; subst hy; exact specializes_rfl
  obtain ⟨_, hdvr⟩ := AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R g η hηs hgen
  haveI := hdvr

  let φK : pullback g ιK ⟶ pullback f ιK :=
    pullback.lift (pullback.snd g ιK ≫ x) (pullback.snd g ιK) (by rw [Category.assoc, hx])
  have hφK : φK ≫ pullback.snd f ιK = pullback.snd g ιK := pullback.lift_snd _ _ _
  have hφK1 : φK ≫ pullback.fst f ιK = pullback.snd g ιK ≫ x := pullback.lift_fst _ _ _

  let gr : pullback g ιK ⟶ pullback g f :=
    pullback.lift (pullback.fst g ιK) (φK ≫ pullback.fst f ιK)
      (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])

  haveI : IsIso (pullback.snd g f) := by rw [hg]; infer_instance
  obtain ⟨z, hz, hzf⟩ := hcl

  let z' : ↥(pullback g f) := (inv (pullback.snd g f)).base z
  have hz' : (pullback.snd g f).base z' = z := by
    change ((inv (pullback.snd g f)) ≫ pullback.snd g f).base z = z
    rw [IsIso.inv_hom_id]; rfl
  have hgr2 : gr ≫ pullback.snd g f = pullback.snd g ιK ≫ x := by
    simp only [gr, pullback.lift_snd, hφK1]
  haveI : IsIso (pullback.snd g ιK) := by rw [hg]; infer_instance
  have hrange : Set.range (gr ≫ pullback.snd g f).base = Set.range x.base := by
    rw [hgr2, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    have : Set.range (pullback.snd g ιK).base = Set.univ :=
      Set.range_eq_univ.mpr (pullback.snd g ιK).surjective
    rw [this, Set.image_univ]
  have hz'cl : z' ∈ closure (Set.range gr.base) := by

    have hce := (pullback.snd g f).isClosedEmbedding
    have h1 : closure (Set.range x.base) = (pullback.snd g f).base '' closure (Set.range gr.base) := by
      rw [← hrange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hce.closure_image_eq]
    have h2 : z ∈ (pullback.snd g f).base '' closure (Set.range gr.base) := h1 ▸ hz
    obtain ⟨w, hw, hwz⟩ := h2
    have : w = z' := hce.injective (hwz.trans hz'.symm)
    exact this ▸ hw
  haveI : QuasiCompact gr := by
    haveI : QuasiCompact (gr ≫ pullback.snd g f) := by rw [hgr2]; infer_instance
    exact QuasiCompact.of_comp gr (pullback.snd g f)

  have hrg : Set.range gr.imageι.base = closure (Set.range gr.base) := by
    rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
  obtain ⟨γ, hγ⟩ : z' ∈ Set.range gr.imageι.base := hrg ▸ hz'cl
  have hγη : (gr.imageι ≫ pullback.fst g f).base γ = η := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hγ]
    have hc : (pullback.fst g f).base z' = (pullback.snd g f ≫ f).base z' := by
      rw [← pullback.condition]; rfl
    rw [hc, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hz']
    exact hzf

  obtain ⟨V, v, hv, -, hηV, hle, hcompat⟩ :=
    AlgebraicGeometry.Scheme.exists_opens_extension_of_mem_image_graph K g f η hηs hirr φK hφK γ hγη

  have hV : V = ⊤ := (IsLocalRing.closed_point_mem_iff).mp hηV
  haveI : IsIso V.ι := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Opens.opensRange_ι]; exact hV
  refine ⟨inv V.ι ≫ v, ?_, ?_⟩
  · rw [Category.assoc, hv, IsIso.inv_hom_id_assoc, hg]
  ·
    have hlift : IsOpenImmersion.lift V.ι (pullback.fst g ιK) hle = pullback.fst g ιK ≫ inv V.ι := by
      rw [← cancel_mono V.ι, IsOpenImmersion.lift_fac, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hfst : pullback.fst g ιK = pullback.snd g ιK ≫ ιK := by
      have := pullback.condition (f := g) (g := ιK)
      rw [hg, Category.comp_id] at this
      exact this
    have key : pullback.snd g ιK ≫ (ιK ≫ inv V.ι ≫ v) = pullback.snd g ιK ≫ x := by
      rw [← hφK1, ← hcompat, hlift, hfst]
      simp only [Category.assoc]
    exact (cancel_epi (pullback.snd g ιK)).mp key

end S_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_mem_closure_range
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_mem_closure_range (solution)
