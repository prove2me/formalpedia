-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.kernelPts_finite_of_nonempty_iso_tensor_pullback_negMor_of_kernelPts_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3e59f553-2650-55a5-8913-245ce01e0f2c

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_kernelPts_finite_of_nonempty_iso_tensor_pullback_negMor_of_kernelPts_finite

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace P2mWs3KptsHalf

theorem translate_comp_translate {k : Type} [Field k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    L.translate y ≫ L.translate x = L.translate (L.mul (𝟙 _) y x) := by
  let pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f → SchemeHomOver f f := fun z =>
    ⟨f ≫ z.1, by rw [Category.assoc, z.2, Category.comp_id]⟩
  have hT : ∀ z, L.translate z = (L.mul f RelativeGroupLaw.idPoint (pt z)).1 := fun z => rfl
  have hψ : L.translate y ≫ f = f := L.translate_over y
  have h1 := L.mul_natural f f (L.translate y) hψ RelativeGroupLaw.idPoint (pt x)
  have hid : schemeHomOverComp (L.translate y) hψ RelativeGroupLaw.idPoint =
      L.mul f RelativeGroupLaw.idPoint (pt y) := by
    apply Subtype.ext
    rw [schemeHomOverComp_coe]
    show L.translate y ≫ 𝟙 A = _
    rw [Category.comp_id]; rfl
  have hx : schemeHomOverComp (L.translate y) hψ (pt x) = pt x := by
    apply Subtype.ext
    rw [schemeHomOverComp_coe]
    show L.translate y ≫ (f ≫ x.1) = f ≫ x.1
    rw [← Category.assoc, hψ]
  rw [hid, hx, L.mul_assoc] at h1
  have h2 := L.mul_natural (𝟙 _) f f (Category.comp_id f) y x
  have hy' : schemeHomOverComp f (Category.comp_id f) y = pt y := Subtype.ext rfl
  have hx' : schemeHomOverComp f (Category.comp_id f) x = pt x := Subtype.ext rfl
  rw [hy', hx'] at h2
  have h3 : pt (L.mul (𝟙 _) y x) = L.mul f (pt y) (pt x) := by
    rw [← h2]; exact Subtype.ext rfl
  rw [hT y, hT x, hT (L.mul _ y x), h3, ← h1, schemeHomOverComp_coe]
  rfl

theorem inv_natural {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (G : RelativeGroupLaw R₀ f) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₀)) (t' : T' ⟶ Spec (CommRingCat.of R₀))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) * GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    show G.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x)) (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = G.one t'
    rw [← G.mul_natural t t' ψ hψ, G.inv_mul_cancel, G.one_natural t t' ψ hψ]
  show GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) = (GoodReductionJacobian.schemeHomOverComp ψ hψ x)⁻¹
  exact (inv_eq_of_mul_eq_one_left h).symm

theorem negMor_comp_translate {k : Type} [Field k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    negMor f L ≫ L.translate x = L.translate (L.inv (𝟙 _) x) ≫ negMor f L := by
  let e₁ := (𝟙 (Spec (CommRingCat.of k)))
  let N := negMor f L
  let Tx := L.translate x
  let x' := L.inv e₁ x
  let Tx' := L.translate x'
  have hN : N ≫ f = f := negMor_over f L
  let pt : SchemeHomOver e₁ f → SchemeHomOver f f := fun z => ⟨f ≫ z.1, by rw [Category.assoc, z.2, Category.comp_id]⟩
  have hpt_comp : ∀ z, GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) z = pt z := fun z => Subtype.ext rfl
  letI := L.pointGroup f
  have hL := L.mul_natural f f N hN RelativeGroupLaw.idPoint (pt x)
  have hL1 : GoodReductionJacobian.schemeHomOverComp N hN RelativeGroupLaw.idPoint = L.inv f RelativeGroupLaw.idPoint := by
    apply Subtype.ext; show N ≫ 𝟙 A = N; rw [Category.comp_id]
  have hL2 : GoodReductionJacobian.schemeHomOverComp N hN (pt x) = pt x := by
    apply Subtype.ext; show N ≫ (f ≫ x.1) = f ≫ x.1; rw [← Category.assoc, hN]
  rw [hL1, hL2] at hL
  have hR := inv_natural L f f Tx' (L.translate_over x') RelativeGroupLaw.idPoint
  have hR1 : GoodReductionJacobian.schemeHomOverComp Tx' (L.translate_over x') RelativeGroupLaw.idPoint =
      L.mul f RelativeGroupLaw.idPoint (pt x') := by
    apply Subtype.ext; show Tx' ≫ 𝟙 A = Tx'; rw [Category.comp_id]
  rw [hR1] at hR
  have hx' : pt x' = L.inv f (pt x) := by
    rw [← hpt_comp, ← hpt_comp]
    exact inv_natural L e₁ f f (Category.comp_id f) x
  rw [hx'] at hR
  have hgrp : L.mul f (L.inv f RelativeGroupLaw.idPoint) (pt x) =
      L.inv f (L.mul f RelativeGroupLaw.idPoint (L.inv f (pt x))) := by
    show (RelativeGroupLaw.idPoint)⁻¹ * pt x = (RelativeGroupLaw.idPoint * (pt x)⁻¹)⁻¹
    rw [mul_inv_rev, inv_inv]
    exact hc _ _ _
  have h3 : (GoodReductionJacobian.schemeHomOverComp N hN (L.mul f RelativeGroupLaw.idPoint (pt x))).1 =
      (GoodReductionJacobian.schemeHomOverComp Tx' (L.translate_over x') (L.inv f RelativeGroupLaw.idPoint)).1 := by
    rw [hL, hR, hgrp]
  exact h3

end P2mWs3KptsHalf

open P2mWs3KptsHalf in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓛₁ 𝓝 : A.Modules)
    (e : Nonempty (𝓝 ≅ 𝓛₁ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₁))
    (hfin : (kernelPts f L 𝓝).Finite) :
    (kernelPts f L 𝓛₁).Finite := by
  obtain ⟨e⟩ := e
  refine hfin.subset fun x hx => ?_
  obtain ⟨ex⟩ := (mem_kernelPts_iff_nonempty_pullback_translate_iso k f L 𝓛₁ x).mp hx
  apply (mem_kernelPts_iff_nonempty_pullback_translate_iso k f L 𝓝 x).mpr

  let e₁ := (𝟙 (Spec (CommRingCat.of k)))
  letI := L.pointGroup e₁
  let N := negMor f L
  let x' := L.inv e₁ x
  let Tx := L.translate x
  let Tx' := L.translate x'

  have h1 : Tx' ≫ Tx = 𝟙 A := by
    show L.translate x' ≫ L.translate x = 𝟙 A
    rw [translate_comp_translate, show L.mul e₁ x' x = L.one e₁ from inv_mul_cancel x, L.translate_one]

  have h2 : Tx ≫ N = N ≫ Tx' := by
    have h := negMor_comp_translate L hc x'
    have hxx : L.inv e₁ x' = x := inv_inv x
    rw [hxx] at h
    exact h.symm

  let ex' : (Scheme.Modules.pullback Tx').obj 𝓛₁ ≅ 𝓛₁ :=
    (Scheme.Modules.pullback Tx').mapIso ex.symm ≪≫ (Scheme.Modules.pullbackComp Tx' Tx).app 𝓛₁ ≪≫
      (Scheme.Modules.pullbackCongr h1).app 𝓛₁ ≪≫ (Scheme.Modules.pullbackId A).app 𝓛₁

  let eN : (Scheme.Modules.pullback Tx).obj ((Scheme.Modules.pullback N).obj 𝓛₁) ≅ (Scheme.Modules.pullback N).obj 𝓛₁ :=
    (Scheme.Modules.pullbackComp Tx N).app 𝓛₁ ≪≫ (Scheme.Modules.pullbackCongr h2).app 𝓛₁ ≪≫
      ((Scheme.Modules.pullbackComp N Tx').app 𝓛₁).symm ≪≫ (Scheme.Modules.pullback N).mapIso ex'
  exact ⟨(Scheme.Modules.pullback Tx).mapIso e ≪≫ Scheme.Modules.pullbackTensorObjIso Tx 𝓛₁ _ ≪≫ (ex ⊗ᵢ eN) ≪≫ e.symm⟩

end S_AlgebraicGeometry_Polarisation_kernelPts_finite_of_nonempty_iso_tensor_pullback_negMor_of_kernelPts_finite
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_kernelPts_finite_of_nonempty_iso_tensor_pullback_negMor_of_kernelPts_finite (solution)
