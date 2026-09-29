-- Prove2me | solution 1 for AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/1eb4e0c6-e80d-55fe-88db-766ab33a5d19

import Mathlib
import Theorems.Thm_ValuationSubring_le_trdeg_residueField_comap_of_le_trdeg_residueField
import Theorems.Thm_ValuationSubring_exists_algebraicIndependent_residue_of_le_trdeg
import Theorems.Thm_ValuationSubring_eq_zero_of_valuation_eval2_lt_one
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure
import Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral
import Theorems.Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace VRwork

variable {k : Type u} [Field k]

noncomputable def stalkValuationSubring (V : Scheme.{u}) [IsIntegral V] (z : V) [ValuationRing (V.presheaf.stalk z)] :
    ValuationSubring V.functionField where
  toSubring := (algebraMap (V.presheaf.stalk z) V.functionField).range
  mem_or_inv_mem' x := by
    rcases ValuationRing.isInteger_or_isInteger (V.presheaf.stalk z) x with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem mem_stalkValuationSubring_iff (V : Scheme.{u}) [IsIntegral V] (z : V) [ValuationRing (V.presheaf.stalk z)]
    (x : V.functionField) :
    x ∈ stalkValuationSubring V z ↔ ∃ r : V.presheaf.stalk z, algebraMap _ V.functionField r = x := Iff.rfl

theorem valuationRing_of_ringKrullDim_eq_one {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] (h1 : ringKrullDim R = 1) (hn : IsIntegrallyClosed R) : ValuationRing R := by
  have hnf : ¬ IsField R := by
    intro hF
    have := ringKrullDim_eq_zero_of_isField hF
    rw [h1] at this; exact one_ne_zero this
  haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by rw [h1]; exact le_rfl)
  have hm : IsLocalRing.maximalIdeal R ≠ ⊥ := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf
  have h4 : IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime :=
    ⟨hn, IsLocalRing.maximalIdeal R, ⟨hm, inferInstance⟩,
      fun P hP => IsLocalRing.eq_maximalIdeal (hP.2.isMaximal_of_ne_bot hP.1)⟩
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 3 1).mp h4

end VRwork

namespace VRwork

theorem specializes_genericPoint_of_denseRange {V Y : Scheme.{u}} [IsIntegral V] [IsIntegral Y] (α : V ⟶ Y)
    (hdom : DenseRange α.base) : α.base (genericPoint V) ⤳ genericPoint Y := by
  have h := (genericPoint_spec V).image α.continuous
  have hcl : closure (α.base '' (Set.univ : Set V)) = (⊤ : Set Y) := by
    rw [Set.image_univ, hdom.closure_range, Set.top_eq_univ]
  rw [hcl] at h
  have : α.base (genericPoint V) = genericPoint Y := h.eq (genericPoint_spec Y)
  rw [this]

noncomputable def ffHom {V Y : Scheme.{u}} [IsIntegral V] [IsIntegral Y] (α : V ⟶ Y) (hdom : DenseRange α.base) :
    Y.functionField ⟶ V.functionField :=
  Y.presheaf.stalkSpecializes (specializes_genericPoint_of_denseRange α hdom) ≫ α.stalkMap (genericPoint V)

theorem ffHom_comp_algebraMap {V Y : Scheme.{u}} [IsIntegral V] [IsIntegral Y] (α : V ⟶ Y)
    (hdom : DenseRange α.base) (z : V) (s : Y.presheaf.stalk (α.base z)) :
    (ffHom α hdom).hom (algebraMap (Y.presheaf.stalk (α.base z)) Y.functionField s) =
      algebraMap (V.presheaf.stalk z) V.functionField ((α.stalkMap z).hom s) := by
  simp only [ffHom, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, RingHom.comp_apply]
  have hz : genericPoint V ⤳ z := genericPoint_specializes z
  have h1 : Y.presheaf.stalkSpecializes (genericPoint_specializes (α.base z)) ≫
      Y.presheaf.stalkSpecializes (specializes_genericPoint_of_denseRange α hdom) =
      Y.presheaf.stalkSpecializes (hz.map α.continuous) :=
    TopCat.Presheaf.stalkSpecializes_comp _ _ _
  have h2 := Scheme.Hom.stalkSpecializes_stalkMap α (genericPoint V) z hz

  have := congrArg (fun φ => φ.hom s) (show
    Y.presheaf.stalkSpecializes (genericPoint_specializes (α.base z)) ≫
      Y.presheaf.stalkSpecializes (specializes_genericPoint_of_denseRange α hdom) ≫ α.stalkMap (genericPoint V) =
      α.stalkMap z ≫ V.presheaf.stalkSpecializes hz from by rw [← Category.assoc, h1, h2])
  simpa using this

end VRwork

namespace VRglue

variable {k : Type u} [Field k]

noncomputable def c {Y : Scheme.{u}} [IsIntegral Y] (fY : Y ⟶ Spec (.of k)) : k →+* Y.functionField :=
  (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom.comp
    (fY.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)

theorem c_eq_algebraMap_germ {Y : Scheme.{u}} [IsIntegral Y] (fY : Y ⟶ Spec (.of k)) (y : Y) (x : k) :
    c fY x = algebraMap (Y.presheaf.stalk y) Y.functionField
      ((Y.presheaf.germ ⊤ y trivial).hom (fY.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom x))) := by
  change (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom _ =
    (Y.presheaf.stalkSpecializes (genericPoint_specializes y)).hom ((Y.presheaf.germ ⊤ y trivial).hom _)
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  rfl

theorem germ_genericPoint_eq_algebraMap_germ {Y : Scheme.{u}} [IsIntegral Y] (fY : Y ⟶ Spec (.of k))
    (y : Y) (x : k) :
    (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom (fY.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom x)) =
      algebraMap (Y.presheaf.stalk y) Y.functionField
        ((Y.presheaf.germ ⊤ y trivial).hom (fY.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom x))) :=
  c_eq_algebraMap_germ fY y x

theorem ffHom_c {V Y : Scheme.{u}} [IsIntegral V] [IsIntegral Y] (fV : V ⟶ Spec (.of k))
    (fY : Y ⟶ Spec (.of k)) (α : V ⟶ Y) (hα : α ≫ fY = fV) (hdom : DenseRange α.base) (x : k) :
    (VRwork.ffHom α hdom).hom (c fY x) = c fV x := by
  change (Y.presheaf.stalkSpecializes (VRwork.specializes_genericPoint_of_denseRange α hdom) ≫
      α.stalkMap (genericPoint V)).hom
      ((Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom (fY.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom x))) =
    (V.presheaf.germ ⊤ (genericPoint V) trivial).hom (fV.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom x))
  rw [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply, ← hα, Scheme.Hom.comp_appTop]
  rfl

theorem ffHom_comp_c {V Y : Scheme.{u}} [IsIntegral V] [IsIntegral Y] (fV : V ⟶ Spec (.of k))
    (fY : Y ⟶ Spec (.of k)) (α : V ⟶ Y) (hα : α ≫ fY = fV) (hdom : DenseRange α.base) :
    (VRwork.ffHom α hdom).hom.comp (c fY) = c fV :=
  RingHom.ext (ffHom_c fV fY α hα hdom)

end VRglue

namespace VRglue

variable {k : Type u} [Field k]

theorem trdeg_eq_of_isFractionRing (k A K : Type u) [Field k] [CommRing A] [IsDomain A] [Field K]
    [Algebra k A] [Algebra A K] [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K] :
    Algebra.trdeg k K = Algebra.trdeg k A := by
  haveI : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  haveI : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).mpr (IsFractionRing.injective A K)
  haveI : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have h := trdeg_add_eq k A (A := K)
  rw [trdeg_eq_zero (R := A) (A := K), add_zero] at h
  exact h.symm

theorem exists_nat_trdeg_functionField {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    letI : Algebra k X.functionField := (c f).toAlgebra
    ∃ n : ℕ, Algebra.trdeg k X.functionField = n ∧ topologicalKrullDim X = (n : WithBot ℕ∞) := by
  letI algK : Algebra k X.functionField := (c f).toAlgebra
  show ∃ n : ℕ, Algebra.trdeg k X.functionField = n ∧ topologicalKrullDim X = (n : WithBot ℕ∞)

  obtain ⟨_, ⟨U, hU, rfl⟩, hζU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  haveI : Nonempty U := ⟨⟨_, hζU⟩⟩
  have hle : U ≤ f ⁻¹ᵁ ⊤ := le_top
  let ι0 := (Scheme.ΓSpecIso (.of k)).inv
  letI algA : Algebra k Γ(X, U) := (ι0 ≫ f.appLE ⊤ U hle).hom.toAlgebra
  haveI : Algebra.FiniteType k Γ(X, U) := by
    have hft : RingHom.FiniteType (f.appLE ⊤ U hle).hom :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (f := f)
        (inferInstance : LocallyOfFiniteType f) ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ hle
    have hft0 : RingHom.FiniteType ι0.hom :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso ι0).2
    exact hft.comp hft0
  haveI : IsScalarTower k Γ(X, U) X.functionField := IsScalarTower.of_algebraMap_eq (fun x => by
    change (X.presheaf.germ ⊤ (genericPoint X) trivial).hom (f.appTop.hom (ι0.hom x)) =
      X.presheaf.germ U (genericPoint X) _ ((f.app ⊤ ≫ X.presheaf.map (homOfLE hle).op) (ι0 x))
    rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
    rfl)
  haveI : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  have htr : Algebra.trdeg k X.functionField = Algebra.trdeg k Γ(X, U) :=
    trdeg_eq_of_isFractionRing k Γ(X, U) X.functionField
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := k) (S := Γ(X, U)))
  refine ⟨n, htr.trans hn, ?_⟩
  rw [AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral f hU ⟨_, hζU⟩,
    Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k Γ(X, U), hn, Cardinal.toENat_nat]
  rfl

theorem trdeg_residueField_stalk_eq {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (z : X) (hz : ringKrullDim (X.presheaf.stalk z) = 1)
    (n : ℕ) (hX : topologicalKrullDim X = (n : WithBot ℕ∞)) :
    letI : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk z)) :=
      ((IsLocalRing.residue _).comp ((X.presheaf.germ ⊤ z trivial).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom))).toAlgebra
    Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z)) = (n - 1 : ℕ) := by
  letI alg : Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk z)) :=
    ((IsLocalRing.residue _).comp ((X.presheaf.germ ⊤ z trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom))).toAlgebra
  show Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z)) = (n - 1 : ℕ)
  have hL1 : (Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z))) : WithBot ℕ∞) =
      topologicalKrullDim ↥(closure ({z} : Set X)) :=
    AlgebraicGeometry.toENat_trdeg_residueField_eq_topologicalKrullDim_closure f z
  have hcd := AlgebraicGeometry.ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral f z
  rw [hz, hX, ← hL1] at hcd

  have h1 : (1 : WithBot ℕ∞) + Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z))) =
      ((n : ℕ∞) : WithBot ℕ∞) := hcd
  have h2 : (1 : ℕ∞) + Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z))) = n := by
    exact_mod_cast h1
  have h3 : Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z))) = (n - 1 : ℕ) := by
    have hfin : Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk z))) ≠ ⊤ := by
      intro ht; rw [ht] at h2; exact (ENat.coe_ne_top n) (by simpa using h2.symm)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hm] at h2 ⊢
    have : 1 + m = n := by exact_mod_cast h2
    congr 1
    omega
  exact Cardinal.toENat_eq_natCast.mp h3

end VRglue

namespace VRwork

theorem core {V Y : Scheme.{u}} (k : Type u) [Field k] (fV : V ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsIntegral V] [IsIntegral Y] (α : V ⟶ Y) (hdom : DenseRange α.base)
    (z : V) [ValuationRing (V.presheaf.stalk z)]
    (hnd : ringKrullDim (Y.presheaf.stalk (α.base z)) ≠ 0) :
    ∃ (O : ValuationSubring Y.functionField) (_ : O ≠ ⊤) (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y)
      (_ : Spec.map (CommRingCat.ofHom (algebraMap O Y.functionField)) ≫ ℓ₀ = Y.fromSpecStalk (genericPoint Y))
      (φ : CommRingCat.of O ⟶ V.presheaf.stalk z),
      IsLocalHom φ.hom ∧ Spec.map φ ≫ ℓ₀ = V.fromSpecStalk z ≫ α ∧

      O = (stalkValuationSubring V z).comap (ffHom α hdom).hom := by
  classical
  set y := α.base z with hy
  let K := Y.functionField
  let L := V.functionField
  let R := V.presheaf.stalk z
  let S := Y.presheaf.stalk y
  let ψ : K →+* L := (ffHom α hdom).hom
  let A : ValuationSubring L := stalkValuationSubring V z
  let O : ValuationSubring K := A.comap ψ

  have hSO : ∀ s : S, algebraMap S K s ∈ O := fun s => by
    rw [ValuationSubring.mem_comap]
    show ψ (algebraMap S K s) ∈ A
    rw [show ψ (algebraMap S K s) = algebraMap R L ((α.stalkMap z).hom s) from ffHom_comp_algebraMap α hdom z s]
    exact ⟨_, rfl⟩
  let σ : S →+* O := (algebraMap S K).codRestrict O.toSubring hSO

  have hinjRL : Function.Injective (algebraMap R L) := IsFractionRing.injective R L
  let eA : R ≃+* A := RingEquiv.ofBijective (algebraMap R L).rangeRestrict
    ⟨fun a b h => hinjRL (congrArg Subtype.val h), (algebraMap R L).rangeRestrict_surjective⟩

  let ρ : O →+* A := ψ.restrict O.toSubring A.toSubring (fun a ha => ValuationSubring.mem_comap.mp ha)
  let φ : O →+* R := eA.symm.toRingHom.comp ρ
  have hφval : ∀ a : O, algebraMap R L (φ a) = ψ (a : K) := fun a => by
    show ((eA (eA.symm (ρ a))) : L) = ψ a
    rw [RingEquiv.apply_symm_apply]; rfl
  have hφσ : ∀ s : S, φ (σ s) = (α.stalkMap z).hom s := fun s =>
    hinjRL (by rw [hφval]; exact ffHom_comp_algebraMap α hdom z s)

  have hφloc : IsLocalHom φ := by
    constructor
    intro a ha

    have hAunit : IsUnit (ρ a) := by
      have := ha.map eA.toRingHom
      simpa [φ] using this
    have ha0 : (a : K) ≠ 0 := by
      rintro h0
      apply hAunit.ne_zero
      ext; show ψ a = 0; rw [h0, map_zero]
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hAunit
    have hbv : (b : L) = (ψ a)⁻¹ := by
      have : ψ a * (b : L) = 1 := by simpa [ρ] using congrArg Subtype.val hb
      exact (eq_inv_of_mul_eq_one_right this)
    have hinvA : (ψ a)⁻¹ ∈ A := hbv ▸ b.2
    have hinvO : (a : K)⁻¹ ∈ O := by
      rw [ValuationSubring.mem_comap, map_inv₀]; exact hinvA
    exact isUnit_iff_exists_inv.mpr ⟨⟨(a : K)⁻¹, hinvO⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

  have hO : O ≠ ⊤ := by

    have hSnf : ¬ IsField S := fun hF => hnd (ringKrullDim_eq_zero_of_isField hF)
    have hmS : IsLocalRing.maximalIdeal S ≠ ⊥ := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hSnf
    obtain ⟨s, hsm, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmS
    have hsu : ¬ IsUnit (σ s) := by
      intro hu
      have h1 : IsUnit (φ (σ s)) := hu.map φ
      rw [hφσ] at h1
      have h2 : IsUnit s := (isUnit_map_iff (α.stalkMap z).hom s).mp h1
      exact hsm (by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h2) |> fun h => h
    have hs0' : ((σ s : O) : K) ≠ 0 := by
      show algebraMap S K s ≠ 0
      exact fun h => hs0 (IsFractionRing.injective S K (by rw [h, map_zero]))
    intro htop
    apply hsu
    have hinv : ((σ s : O) : K)⁻¹ ∈ O := by
      have : ∀ x : K, x ∈ O := fun x => by rw [htop]; trivial
      exact this _
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hs0')⟩

  let ℓ₀ : Spec (CommRingCat.of O) ⟶ Y := Spec.map (CommRingCat.ofHom σ) ≫ Y.fromSpecStalk y
  have hℓ₀ : Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ ℓ₀ = Y.fromSpecStalk (genericPoint Y) := by
    simp only [ℓ₀, ← Spec.map_comp_assoc]
    have : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (algebraMap O K) =
        Y.presheaf.stalkSpecializes (genericPoint_specializes y) := by
      ext s; rfl
    rw [this, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫ ℓ₀ = V.fromSpecStalk z ≫ α := by
    simp only [ℓ₀, ← Spec.map_comp_assoc]
    have : CommRingCat.ofHom σ ≫ CommRingCat.ofHom φ = α.stalkMap z := by
      ext s; exact hφσ s
    rw [this, Scheme.SpecMap_stalkMap_fromSpecStalk]
  exact ⟨O, hO, ℓ₀, hℓ₀, CommRingCat.ofHom φ, hφloc, hφ, rfl⟩

end VRwork

open VRglue in
open VRwork in
theorem solution
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType fX] [QuasiCompact fX] [IsIntegral Y] [IsProper fY]
    (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (hα : α ≫ fY = U.ι ≫ fX) (hdom : DenseRange α.base)
    (z : X) (hzU : z ∈ U) (hz₁ : ringKrullDim (X.presheaf.stalk z) = 1)
    (hzn : IsIntegrallyClosed (X.presheaf.stalk z))
    (hnd : ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩)) ≠ 0) :
    ∃ (O : ValuationSubring Y.functionField) (_ : O ≠ ⊤) (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y)
      (_ : Spec.map (CommRingCat.ofHom (algebraMap O Y.functionField)) ≫ ℓ₀ = Y.fromSpecStalk (genericPoint Y))
      (d : ℕ) (_ : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Y)
      (g : Fin d → Y.functionField) (_ : ∀ i, g i ∈ O)
      (_ : ∀ Q : MvPolynomial (Fin d) k,
        O.valuation (Q.eval₂ ((Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom.comp
          (fY.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) g) < 1 → Q = 0)
      (φ : CommRingCat.of O ⟶ X.presheaf.stalk z),
      IsLocalHom φ.hom ∧ Spec.map φ ≫ ℓ₀ = U.fromSpecStalkOfMem z hzU ≫ α := by
  classical
  haveI : Nonempty ↥(U : Scheme.{u}) := ⟨⟨z, hzU⟩⟩
  haveI : IsIntegral (U : Scheme.{u}) := inferInstance

  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian fX
  haveI hiso : IsIso (U.ι.stalkMap (⟨z, hzU⟩ : ↥(U : Scheme.{u}))) := inferInstance
  let e : X.presheaf.stalk z ≅ (U : Scheme.{u}).presheaf.stalk (⟨z, hzU⟩ : ↥(U : Scheme.{u})) := @asIso _ _ _ _ (U.ι.stalkMap (⟨z, hzU⟩ : ↥(U : Scheme.{u}))) hiso
  haveI : IsLocallyNoetherian (U : Scheme.{u}) := inferInstance
  haveI : IsNoetherianRing ((U : Scheme.{u}).presheaf.stalk (⟨z, hzU⟩ : ↥(U : Scheme.{u}))) := inferInstance
  haveI : ValuationRing ((U : Scheme.{u}).presheaf.stalk (⟨z, hzU⟩ : ↥(U : Scheme.{u}))) := by
    apply valuationRing_of_ringKrullDim_eq_one
    · rw [← hz₁]; exact (ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv).symm
    · haveI := hzn; exact IsIntegrallyClosed.of_equiv e.commRingCatIsoToRingEquiv
  have hnd' : ringKrullDim (Y.presheaf.stalk (α.base (⟨z, hzU⟩ : ↥(U : Scheme.{u})))) ≠ 0 := hnd
  obtain ⟨O, hO, ℓ₀, hℓ₀, φ, hφloc, hφ, hOeq⟩ := core k (U.ι ≫ fX) fY α hdom (⟨z, hzU⟩ : ↥(U : Scheme.{u})) hnd'

  obtain ⟨d, hd, g, hg, hind⟩ : ∃ (d : ℕ) (_ : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Y)
      (g : Fin d → Y.functionField) (_ : ∀ i, g i ∈ O),
      ∀ Q : MvPolynomial (Fin d) k,
        O.valuation (Q.eval₂ ((Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom.comp
          (fY.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) g) < 1 → Q = 0 := by

    let cK : k →+* Y.functionField := VRglue.c fY
    let cL : k →+* (U : Scheme.{u}).functionField := VRglue.c (U.ι ≫ fX)
    letI algK : Algebra k Y.functionField := cK.toAlgebra
    letI algL : Algebra k (U : Scheme.{u}).functionField := cL.toAlgebra
    letI algKL : Algebra Y.functionField (U : Scheme.{u}).functionField := (ffHom α hdom).hom.toAlgebra
    haveI : IsScalarTower k Y.functionField (U : Scheme.{u}).functionField :=
      IsScalarTower.of_algebraMap_eq (fun x => (VRglue.ffHom_c (U.ι ≫ fX) fY α hα hdom x).symm)
    obtain ⟨nY, hnY, hdimY⟩ := VRglue.exists_nat_trdeg_functionField (k := k) fY
    obtain ⟨nV, hnV, hdimV⟩ := VRglue.exists_nat_trdeg_functionField (k := k) (U.ι ≫ fX)

    let A : ValuationSubring (U : Scheme.{u}).functionField := stalkValuationSubring (U : Scheme.{u}) (⟨z, hzU⟩ : ↥(U : Scheme.{u}))
    have hkA : ∀ x : k, algebraMap k (U : Scheme.{u}).functionField x ∈ A := fun x => by
      show cL x ∈ A
      rw [show cL x = _ from VRglue.c_eq_algebraMap_germ (U.ι ≫ fX) (⟨z, hzU⟩ : ↥(U : Scheme.{u})) x]
      exact ⟨_, rfl⟩

    have hz1' : ringKrullDim ((U : Scheme.{u}).presheaf.stalk (⟨z, hzU⟩ : ↥(U : Scheme.{u}))) = 1 := by
      rw [← hz₁]; exact (ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv).symm
    have hA : letI : Algebra k (IsLocalRing.ResidueField A) :=
        ((IsLocalRing.residue A).comp ((algebraMap k (U : Scheme.{u}).functionField).codRestrict A.toSubring hkA)).toAlgebra
        ((nV - 1 : ℕ) : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField A) := by

      let R := (U : Scheme.{u}).presheaf.stalk (⟨z, hzU⟩ : ↥(U : Scheme.{u}))
      have hinjRL : Function.Injective (algebraMap R (U : Scheme.{u}).functionField) := IsFractionRing.injective R _
      let eA : R ≃+* A := RingEquiv.ofBijective (algebraMap R (U : Scheme.{u}).functionField).rangeRestrict
        ⟨fun a b h => hinjRL (congrArg Subtype.val h), (algebraMap R (U : Scheme.{u}).functionField).rangeRestrict_surjective⟩
      let gR : k →+* R := (((U : Scheme.{u}).presheaf.germ ⊤ (⟨z, hzU⟩ : ↥(U : Scheme.{u})) trivial).hom.comp
        ((U.ι ≫ fX).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom))
      letI algR : Algebra k (IsLocalRing.ResidueField R) := ((IsLocalRing.residue R).comp gR).toAlgebra
      letI algA' : Algebra k (IsLocalRing.ResidueField A) :=
        ((IsLocalRing.residue A).comp ((algebraMap k (U : Scheme.{u}).functionField).codRestrict A.toSubring hkA)).toAlgebra
      have hA2 : Algebra.trdeg k (IsLocalRing.ResidueField R) = (nV - 1 : ℕ) :=
        VRglue.trdeg_residueField_stalk_eq (k := k) (U.ι ≫ fX) (⟨z, hzU⟩ : ↥(U : Scheme.{u})) hz1' nV hdimV
      let eκ : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField A := IsLocalRing.ResidueField.mapEquiv eA
      have hcomm : ∀ x : k, eκ (algebraMap k (IsLocalRing.ResidueField R) x) = algebraMap k (IsLocalRing.ResidueField A) x := by
        intro x
        show IsLocalRing.ResidueField.mapEquiv eA (IsLocalRing.residue R (gR x)) =
          IsLocalRing.residue A ((algebraMap k (U : Scheme.{u}).functionField).codRestrict A.toSubring hkA x)
        have h1 : IsLocalRing.ResidueField.mapEquiv eA (IsLocalRing.residue R (gR x)) = IsLocalRing.residue A (eA (gR x)) := rfl
        rw [h1]
        congr 1
        apply Subtype.ext
        show algebraMap R (U : Scheme.{u}).functionField (gR x) = cL x
        exact (VRglue.c_eq_algebraMap_germ (U.ι ≫ fX) (⟨z, hzU⟩ : ↥(U : Scheme.{u})) x).symm
      let eκa : IsLocalRing.ResidueField R ≃ₐ[k] IsLocalRing.ResidueField A := AlgEquiv.ofRingEquiv (f := eκ) hcomm
      show ((nV - 1 : ℕ) : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField A)
      rw [← eκa.trdeg_eq, hA2]

    have hTR := ValuationSubring.le_trdeg_residueField_comap_of_le_trdeg_residueField A hkA nY nV hnY hnV hA

    have hnY1 : 1 ≤ nY := by
      by_contra hlt
      have h0 : nY = 0 := by omega
      have hcd := AlgebraicGeometry.ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral fY
        (α.base (⟨z, hzU⟩ : ↥(U : Scheme.{u})))
      rw [hdimY, h0] at hcd
      have ha : (0 : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk (α.base (⟨z, hzU⟩ : ↥(U : Scheme.{u})))) :=
        ringKrullDim_nonneg_of_nontrivial
      have hb : (0 : WithBot ℕ∞) ≤ topologicalKrullDim ↥(closure ({α.base (⟨z, hzU⟩ : ↥(U : Scheme.{u}))} : Set Y)) := by
        haveI : Nonempty (TopologicalSpace.IrreducibleCloseds ↥(closure ({α.base (⟨z, hzU⟩ : ↥(U : Scheme.{u}))} : Set Y))) :=
          ⟨⟨closure {⟨_, subset_closure rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
        exact Order.krullDim_nonneg
      apply hnd
      apply le_antisymm _ ha
      calc ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩))
          ≤ ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩)) +
              topologicalKrullDim ↥(closure ({α.base (⟨z, hzU⟩ : ↥(U : Scheme.{u}))} : Set Y)) :=
            le_add_of_nonneg_right hb
        _ = ((0 : ℕ) : WithBot ℕ∞) := hcd
        _ = 0 := by simp

    subst hOeq
    have hc : ∀ x : k, cK x ∈ A.comap (ffHom α hdom).hom := fun x => by
      rw [ValuationSubring.mem_comap]
      show (ffHom α hdom).hom (cK x) ∈ A
      rw [VRglue.ffHom_c (U.ι ≫ fX) fY α hα hdom x]
      exact hkA x
    obtain ⟨g, hg, hgi⟩ := ValuationSubring.exists_algebraicIndependent_residue_of_le_trdeg cK
      (A.comap (ffHom α hdom).hom) hc (d := nY - 1) (by exact hTR)
    refine ⟨nY - 1, ?_, g, hg, fun Q hQ => ValuationSubring.eq_zero_of_valuation_eval2_lt_one cK _ hc g hg hgi Q hQ⟩
    rw [hdimY]; congr 1; exact_mod_cast Nat.sub_add_cancel hnY1
  refine ⟨O, hO, ℓ₀, hℓ₀, d, hd, g, hg, hind, φ ≫ e.inv, ?_, ?_⟩
  ·
    haveI := hφloc
    show IsLocalHom (e.inv.hom.comp φ.hom)
    exact RingHom.isLocalHom_comp _ _
  · rw [Spec.map_comp, Category.assoc, hφ]
    simp only [e, asIso_inv, Scheme.Opens.fromSpecStalkOfMem, Category.assoc]

end S_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one (solution)
