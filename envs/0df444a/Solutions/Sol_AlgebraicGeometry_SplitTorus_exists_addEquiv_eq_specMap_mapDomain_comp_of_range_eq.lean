-- Prove2me | solution 1 for AlgebraicGeometry.SplitTorus.exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/49954744-8b56-5072-82db-10645ea1e3ec

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_SplitTorus_forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed
import Theorems.Thm_AddMonoidAlgebra_exists_addMonoidHom_forall_bialgHom_single_eq_single
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SplitTorus_exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus

namespace Gamma

theorem ker_le_ker_of_range_subset {X X' Z : Scheme.{0}} (f : X ⟶ Z) (g : X' ⟶ Z) [IsClosedImmersion f] [QuasiCompact g]
    [IsReduced X'] (h : Set.range g.base ⊆ Set.range f.base) : f.ker ≤ g.ker := by
  rw [Scheme.IdealSheafData.le_def]
  intro U s hs
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hs ⊢
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen]

  have hempty : ∀ x : X', g.base x ∉ Z.basicOpen s := by
    intro x hx
    obtain ⟨w, hw⟩ := h ⟨x, rfl⟩
    have hw' : w ∈ f ⁻¹ᵁ Z.basicOpen s := by
      change f.base w ∈ Z.basicOpen s
      rw [hw]; exact hx
    rw [Scheme.preimage_basicOpen, hs, Scheme.basicOpen_zero] at hw'
    exact hw'
  ext x
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  exact hempty x

theorem exists_bialgHom_of_forall_conv
    {κ : Type} [Field κ] {G : Type} [AddCommGroup G]
    (ψ : AddMonoidAlgebra κ G →ₐ[κ] AddMonoidAlgebra κ G)
    (h : ∀ (T : Type) [CommRing T] [Algebra κ T] (χ χ' : WithConv (AddMonoidAlgebra κ G →ₐ[κ] T)),
        WithConv.toConv ((χ * χ').ofConv.comp ψ) =
          WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ)) :
    ∃ ψc : AddMonoidAlgebra κ G →ₐc[κ] AddMonoidAlgebra κ G, ∀ x, ψc x = ψ x := by
  classical

  have hmul : ∀ (T : Type) [CommRing T] [Algebra κ T] (c c' : WithConv (AddMonoidAlgebra κ G →ₐ[κ] T)) (x : AddMonoidAlgebra κ G),
      (c * c') x = Algebra.TensorProduct.lift c.ofConv c'.ofConv (fun _ _ => .all _ _) (Coalgebra.comul x) :=
    fun T _ _ c c' x => AlgHom.convMul_apply c c' x

  have hcomul : (Algebra.TensorProduct.map ψ ψ).comp (Bialgebra.comulAlgHom κ (AddMonoidAlgebra κ G)) =
      (Bialgebra.comulAlgHom κ (AddMonoidAlgebra κ G)).comp ψ := by
    let T := TensorProduct κ (AddMonoidAlgebra κ G) (AddMonoidAlgebra κ G)
    let χ : WithConv (AddMonoidAlgebra κ G →ₐ[κ] T) := WithConv.toConv Algebra.TensorProduct.includeLeft
    let χ' : WithConv (AddMonoidAlgebra κ G →ₐ[κ] T) := WithConv.toConv Algebra.TensorProduct.includeRight
    have hh := congrArg WithConv.ofConv (h T χ χ')
    apply AlgHom.ext
    intro x
    have hx := congrArg (fun f : AddMonoidAlgebra κ G →ₐ[κ] T => f x) hh
    simp only at hx
    change (χ * χ') (ψ x) = (WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ)) x at hx
    rw [hmul, hmul, Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply] at hx
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply, hx]

    have hlift : Algebra.TensorProduct.lift ((WithConv.toConv (χ.ofConv.comp ψ)).ofConv)
        ((WithConv.toConv (χ'.ofConv.comp ψ)).ofConv) (fun _ _ => .all _ _) = Algebra.TensorProduct.map ψ ψ := by
      apply Algebra.TensorProduct.ext'
      intro a b
      rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
      change (ψ a ⊗ₜ[κ] (1 : AddMonoidAlgebra κ G)) * ((1 : AddMonoidAlgebra κ G) ⊗ₜ[κ] ψ b) = ψ a ⊗ₜ[κ] ψ b
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hlift]

  have hcounit : (Bialgebra.counitAlgHom κ (AddMonoidAlgebra κ G)).comp ψ = Bialgebra.counitAlgHom κ (AddMonoidAlgebra κ G) := by
    refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
    rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, AddMonoidAlgebra.counit_single,
      CommSemiring.counit_apply]

    have hh := congrArg WithConv.ofConv (h κ 1 1)
    rw [mul_one] at hh
    have hx := congrArg (fun f : AddMonoidAlgebra κ G →ₐ[κ] κ => f (AddMonoidAlgebra.single g 1)) hh
    simp only at hx
    change (1 : WithConv (AddMonoidAlgebra κ G →ₐ[κ] κ)) (ψ (AddMonoidAlgebra.single g 1)) =
      (WithConv.toConv ((1 : WithConv (AddMonoidAlgebra κ G →ₐ[κ] κ)).ofConv.comp ψ) *
        WithConv.toConv ((1 : WithConv (AddMonoidAlgebra κ G →ₐ[κ] κ)).ofConv.comp ψ)) (AddMonoidAlgebra.single g 1) at hx
    rw [hmul, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul] at hx
    simp only [AlgHom.comp_apply, AlgHom.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply] at hx

    set c := Coalgebra.counit (R := κ) (ψ (AddMonoidAlgebra.single g 1)) with hc
    have hunit : IsUnit c := by
      have hu : IsUnit (AddMonoidAlgebra.single g (1 : κ)) :=
        ⟨⟨AddMonoidAlgebra.single g 1, AddMonoidAlgebra.single (-g) 1,
          by rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]; rfl,
          by rw [AddMonoidAlgebra.single_mul_single, neg_add_cancel, mul_one]; rfl⟩, rfl⟩
      exact ((hu.map ψ).map (Bialgebra.counitAlgHom κ (AddMonoidAlgebra κ G)))
    have hc1 : c * c = c * 1 := by rw [mul_one]; exact hx.symm
    exact (hunit.mul_left_cancel hc1)
  exact ⟨BialgHom.ofAlgHom ψ hcounit hcomul, fun x => rfl⟩

theorem exists_addMonoidHom_eq_mapDomain
    {κ : Type} [Field κ] {G : Type} [AddCommGroup G]
    (ψ : AddMonoidAlgebra κ G →ₐ[κ] AddMonoidAlgebra κ G)
    (h : ∀ (T : Type) [CommRing T] [Algebra κ T] (χ χ' : WithConv (AddMonoidAlgebra κ G →ₐ[κ] T)),
        WithConv.toConv ((χ * χ').ofConv.comp ψ) =
          WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ)) :
    ∃ M : G →+ G, ψ = AddMonoidAlgebra.mapDomainAlgHom κ κ M := by
  obtain ⟨ψc, hψc⟩ := exists_bialgHom_of_forall_conv ψ h
  obtain ⟨M, hM⟩ := AddMonoidAlgebra.exists_addMonoidHom_forall_bialgHom_single_eq_single G ψc
  refine ⟨M, AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)⟩
  rw [← hψc, hM, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]

theorem bijective_of_bijective_mapDomain {κ : Type} [Field κ] {G : Type} [AddCommGroup G] (M : G →+ G)
    (h : Function.Bijective (AddMonoidAlgebra.mapDomainAlgHom κ κ M : AddMonoidAlgebra κ G →ₐ[κ] AddMonoidAlgebra κ G)) :
    Function.Bijective M := by
  classical
  constructor
  · intro a b hab
    have h1 := congrArg (AddMonoidAlgebra.mapDomainAlgHom κ κ M) (rfl : AddMonoidAlgebra.single a (1 : κ) = AddMonoidAlgebra.single a 1)
    have ha : AddMonoidAlgebra.mapDomainAlgHom κ κ M (AddMonoidAlgebra.single a (1 : κ)) = AddMonoidAlgebra.single (M a) 1 := by
      rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
    have hb : AddMonoidAlgebra.mapDomainAlgHom κ κ M (AddMonoidAlgebra.single b (1 : κ)) = AddMonoidAlgebra.single (M b) 1 := by
      rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
    have : AddMonoidAlgebra.single a (1 : κ) = AddMonoidAlgebra.single b 1 := h.1 (by rw [ha, hb, hab])
    exact AddMonoidAlgebra.single_left_injective one_ne_zero this
  · intro g
    obtain ⟨x, hx⟩ := h.2 (AddMonoidAlgebra.single g 1)
    rw [AddMonoidAlgebra.mapDomainAlgHom_apply] at hx
    have hg : g ∈ (Finsupp.mapDomain M x.coeff).support := by
      rw [show Finsupp.mapDomain M x.coeff = (AddMonoidAlgebra.mapDomain M x).coeff from rfl, hx,
        AddMonoidAlgebra.coeff_single]
      simp
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
    exact ⟨a, rfl⟩

end Gamma

open Gamma in

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ]
    {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of κ)) [IsSeparated f] (L : RelativeGroupLaw κ f) (t : ℕ)
    (τ τ' : SchemeHomOver (torusStr κ t) f) (hτ : IsClosedImmersion τ.1) (hτ' : IsClosedImmersion τ'.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ =
        L.mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ))
    (hτ'mul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ' =
        L.mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ')
          (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ'))
    (hrange : Set.range τ'.1.base = Set.range τ.1.base) :
    ∃ Mx : (Fin t → ℤ) ≃+ (Fin t → ℤ),
      τ'.1 = Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ (Mx : (Fin t → ℤ) →+ (Fin t → ℤ)))) ≫ τ.1 := by
  classical
  haveI := hτ
  haveI := hτ'

  let φ : torusScheme κ t ⟶ torusScheme κ t :=
    IsClosedImmersion.lift τ.1 τ'.1 (ker_le_ker_of_range_subset τ.1 τ'.1 hrange.le)
  have hφ : φ ≫ τ.1 = τ'.1 := IsClosedImmersion.lift_fac _ _ _

  let ψr := Spec.preimage φ
  have hψr : Spec.map ψr = φ := Spec.map_preimage φ
  have hφover : φ ≫ torusStr κ t = torusStr κ t := by
    have h1 : τ'.1 ≫ f = torusStr κ t := τ'.2
    rw [← hφ, Category.assoc, τ.2] at h1
    exact h1
  have hψalg : CommRingCat.ofHom (algebraMap κ (torusCoord κ t)) ≫ ψr = CommRingCat.ofHom (algebraMap κ (torusCoord κ t)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψr]
    exact hφover
  let ψ : torusCoord κ t →ₐ[κ] torusCoord κ t :=
    { ψr.hom with
      commutes' := fun r => by
        have := congrArg (fun g => (CommRingCat.Hom.hom g) r) hψalg
        simpa using this }
  have hψ : ∀ x, ψ x = ψr.hom x := fun x => rfl

  have key : ∀ (T : Type) [CommRing T] [Algebra κ T] (η : torusCoord κ t →ₐ[κ] T),
      NeronModelInfra.schemeHomOverComp (torusPt κ T t η) τ' =
        NeronModelInfra.schemeHomOverComp (torusPt κ T t (η.comp ψ)) τ := by
    intro T _ _ η
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe]
    change Spec.map (CommRingCat.ofHom η.toRingHom) ≫ τ'.1 = Spec.map (CommRingCat.ofHom (η.comp ψ).toRingHom) ≫ τ.1
    rw [← hφ, ← hψr, ← Category.assoc, ← Spec.map_comp]
    rfl

  have hτT := AlgebraicGeometry.SplitTorus.forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed f L t τ hτmul
  have hτ'T := AlgebraicGeometry.SplitTorus.forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed f L t τ' hτ'mul
  have h : ∀ (T : Type) [CommRing T] [Algebra κ T] (χ χ' : WithConv (torusCoord κ t →ₐ[κ] T)),
      WithConv.toConv ((χ * χ').ofConv.comp ψ) =
        WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ) := by
    intro T _ _ χ χ'
    have e1 := hτ'T T χ χ'
    rw [key, key, key] at e1
    have e2 := hτT T (WithConv.toConv (χ.ofConv.comp ψ)) (WithConv.toConv (χ'.ofConv.comp ψ))
    rw [← e2] at e1

    have e3 := congrArg Subtype.val e1
    rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, cancel_mono] at e3
    change Spec.map (CommRingCat.ofHom ((χ * χ').ofConv.comp ψ).toRingHom) =
      Spec.map (CommRingCat.ofHom (WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ)).ofConv.toRingHom) at e3
    have e4 : ((χ * χ').ofConv.comp ψ).toRingHom =
        (WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ)).ofConv.toRingHom :=
by
      have := congrArg CommRingCat.Hom.hom (Spec.map_injective e3)
      simpa only [CommRingCat.hom_ofHom] using this
    have e5 : ((χ * χ').ofConv.comp ψ) = (WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ)).ofConv :=
      AlgHom.ext fun x => RingHom.congr_fun e4 x
    exact congrArg WithConv.toConv e5
  obtain ⟨M, hM⟩ := exists_addMonoidHom_eq_mapDomain ψ h

  haveI : IsClosedImmersion (φ ≫ τ.1) := by rw [hφ]; exact hτ'
  haveI : IsClosedImmersion φ := IsClosedImmersion.of_comp_isClosedImmersion φ τ.1
  haveI : Surjective φ := ⟨fun x => by
    obtain ⟨y, hy⟩ := hrange.ge ⟨x, rfl⟩
    refine ⟨y, τ.1.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hφ]
    exact hy⟩
  haveI : IsIso φ := isIso_of_isClosedImmersion_of_surjective φ
  haveI : IsIso (Scheme.Spec.map ψr.op) := by
    change IsIso (Spec.map ψr)
    rw [hψr]
    infer_instance
  haveI : IsIso ψr.op := Spec.fullyFaithful.isIso_of_isIso_map ψr.op
  haveI : IsIso ψr := isIso_of_op ψr
  have hbij : Function.Bijective (AddMonoidAlgebra.mapDomainAlgHom κ κ M : torusCoord κ t →ₐ[κ] torusCoord κ t) := by
    rw [← hM]
    change Function.Bijective ψr.hom
    exact ConcreteCategory.bijective_of_isIso ψr
  let Mx : (Fin t → ℤ) ≃+ (Fin t → ℤ) := AddEquiv.ofBijective M (bijective_of_bijective_mapDomain M hbij)
  refine ⟨Mx, ?_⟩
  rw [← hφ, ← hψr]
  congr 2
  apply CommRingCat.hom_ext
  change ψ.toRingHom = AddMonoidAlgebra.mapDomainRingHom κ (Mx : (Fin t → ℤ) →+ (Fin t → ℤ))
  rw [hM]
  rfl

end S_AlgebraicGeometry_SplitTorus_exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SplitTorus_exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq (solution)
