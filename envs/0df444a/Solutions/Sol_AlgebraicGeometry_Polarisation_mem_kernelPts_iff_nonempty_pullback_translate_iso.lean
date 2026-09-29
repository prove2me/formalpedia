-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.mem_kernelPts_iff_nonempty_pullback_translate_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fb122c3f-8d14-5832-b3fc-00f540c3b5fa

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

namespace KerPts

open GoodReductionJacobian AlgebraicGeometry.Polarisation

set_option maxHeartbeats 3200000 in
theorem main
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 : A.Modules) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x ∈ kernelPts f L 𝓛 ↔ Nonempty ((Scheme.Modules.pullback (L.translate x)).obj 𝓛 ≅ 𝓛) := by
  let t := 𝟙 (Spec (CommRingCat.of k))
  let pfst := pullback.fst f t
  let psnd := pullback.snd f t

  have hmr : L.mulRight t x = pfst ≫ L.translate x := by
    have hψ : pfst ≫ f = psnd ≫ t := pullback.condition
    have h := congrArg Subtype.val (L.mul_natural f (psnd ≫ t) pfst hψ RelativeGroupLaw.idPoint
      ⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩)
    have h1 : schemeHomOverComp pfst hψ (RelativeGroupLaw.idPoint (f := f)) = L.fstPoint t :=
      Subtype.ext (Category.comp_id _)
    have h2 : schemeHomOverComp pfst hψ (⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩ : SchemeHomOver f f) =
        L.sndPoint t x := by
      apply Subtype.ext
      change pfst ≫ f ≫ x.1 = psnd ≫ x.1
      rw [← Category.assoc, hψ, Category.assoc, Category.id_comp]
    rw [h1, h2] at h
    exact h.symm
  change L.IsInStabilizer 𝓛 t x ↔ _
  constructor
  · intro h
    obtain ⟨U, hτ, ⟨e⟩⟩ := h default
    let V : (pullback f t).Opens := psnd ⁻¹ᵁ U

    have hV : ∀ p : ↥(pullback f t), p ∈ V := by
      intro p
      change psnd.base p ∈ U
      rw [Subsingleton.elim (psnd.base p) default]; exact hτ
    let s₀ : pullback f t ⟶ (V : Scheme.{0}) :=
      IsOpenImmersion.lift V.ι (𝟙 _) (by
        rintro p ⟨q, rfl⟩
        rw [Scheme.Opens.range_ι]; exact hV _)
    have hs₀ : s₀ ≫ V.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
    let s : A ⟶ (V : Scheme.{0}) := inv pfst ≫ s₀
    have hs1 : s ≫ V.ι ≫ L.mulRight t x = L.translate x := by
      rw [hmr]; change (inv pfst ≫ s₀) ≫ V.ι ≫ pfst ≫ L.translate x = L.translate x
      rw [Category.assoc, ← Category.assoc s₀, hs₀, Category.id_comp, IsIso.inv_hom_id_assoc]
    have hs2 : s ≫ V.ι ≫ pfst = 𝟙 A := by
      change (inv pfst ≫ s₀) ≫ V.ι ≫ pfst = 𝟙 A
      rw [Category.assoc, ← Category.assoc s₀, hs₀, Category.id_comp, IsIso.inv_hom_id]
    have e' := (Scheme.Modules.pullback s).mapIso e
    refine ⟨?_⟩
    refine ((Scheme.Modules.pullbackCongr hs1).app 𝓛).symm ≪≫
      ((Scheme.Modules.pullbackComp s (V.ι ≫ L.mulRight t x)).app 𝓛).symm ≪≫
      (Scheme.Modules.pullback s).mapIso (((Scheme.Modules.pullbackComp V.ι (L.mulRight t x)).app 𝓛).symm) ≪≫
      e' ≪≫
      (Scheme.Modules.pullback s).mapIso ((Scheme.Modules.pullbackComp V.ι pfst).app 𝓛) ≪≫
      (Scheme.Modules.pullbackComp s (V.ι ≫ pfst)).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr hs2).app 𝓛 ≪≫
      (Scheme.Modules.pullbackId A).app 𝓛
  · rintro ⟨e⟩
    apply Scheme.Modules.LocallyIsoOver.of_iso
    exact (Scheme.Modules.pullbackCongr hmr).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp pfst (L.translate x)).app 𝓛).symm ≪≫
      (Scheme.Modules.pullback pfst).mapIso e

end KerPts

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 : A.Modules) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x ∈ kernelPts f L 𝓛 ↔ Nonempty ((Scheme.Modules.pullback (L.translate x)).obj 𝓛 ≅ 𝓛) :=
  KerPts.main k f L 𝓛 x

end S_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso (solution)
