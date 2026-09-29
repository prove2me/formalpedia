-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_comap_eq_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f3dc6e9d-62c7-5e5f-837e-112c6097d699

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {𝒳 S : Scheme.{u}} {c : 𝒳 ⟶ S} [IsSeparated c] (U : 𝒳.Opens) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv (U.ι ≫ c) r g) :
    ∃ D' : RelEffCartierDiv c r g, D'.SupportedIn U ∧
      D'.I.comap (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) = D.I ∧
      D'.I = D.I.map (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) := by

  set j := pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp) with hj
  have hrange : Set.range ⇑j = (pullback.fst c g) ⁻¹' (U : Set 𝒳) := by
    rw [hj, Scheme.Pullback.range_map]
    simp [Scheme.Opens.range_ι]
  have hjsnd : j ≫ pullback.snd c g = pullback.snd (U.ι ≫ c) g := by
    rw [hj, pullback.lift_snd, Category.comp_id]
  haveI := D.isFinite; haveI := D.flat; haveI := D.locallyOfFinitePresentation

  set f := D.I.subschemeι ≫ j with hf
  have hfin : IsFinite f := by
    have h2 : IsFinite (f ≫ pullback.snd c g) := by
      rw [hf, Category.assoc, hjsnd]; infer_instance
    exact MorphismProperty.of_postcomp (W := @IsFinite) f (pullback.snd c g) (inferInstance : IsSeparated _) h2
  haveI hci : IsClosedImmersion f := by
    rw [IsClosedImmersion.iff_isFinite_and_mono]
    exact ⟨hfin, by rw [hf]; exact mono_comp _ _⟩

  haveI : IsIso f.toImage := inferInstance
  have hfac : f.imageι ≫ pullback.snd c g = inv f.toImage ≫ (D.I.subschemeι ≫ pullback.snd (U.ι ≫ c) g) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, Scheme.Hom.toImage_imageι, hf, Category.assoc, hjsnd]
  refine ⟨{ I := f.ker
            isFinite := by change IsFinite (f.imageι ≫ _); rw [hfac]; infer_instance
            flat := by change Flat (f.imageι ≫ _); rw [hfac]; infer_instance
            locallyOfFinitePresentation := by
              change LocallyOfFinitePresentation (f.imageι ≫ _); rw [hfac]; infer_instance
            finrank_eq := fun t => by
              change (f.imageι ≫ pullback.snd c g).finrank t = r
              rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso]
              exact D.finrank_eq t }, ?_, ?_, rfl⟩
  ·
    intro x hx
    change x ∈ (f.ker.support : Set ↥(pullback c g)) at hx
    rw [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq] at hx
    obtain ⟨z, rfl⟩ := hx
    show (pullback.fst c g) (f z) ∈ (U : Set 𝒳)
    rw [← Set.mem_preimage, ← hrange, hf]
    exact ⟨D.I.subschemeι z, (Scheme.Hom.comp_apply _ _ z).symm⟩
  ·
    change f.ker.comap j = D.I
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have hsurj : IsIso (pullback.snd j f) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
      ext z
      simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rw [Scheme.Pullback.range_snd, hf]
      exact ⟨D.I.subschemeι z, (Scheme.Hom.comp_apply _ _ z).symm⟩
    have hfst : pullback.fst j f = pullback.snd j f ≫ D.I.subschemeι := by
      rw [← cancel_mono j, Category.assoc, ← hf]
      exact pullback.condition
    rw [hfst, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

end S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated (solution)
