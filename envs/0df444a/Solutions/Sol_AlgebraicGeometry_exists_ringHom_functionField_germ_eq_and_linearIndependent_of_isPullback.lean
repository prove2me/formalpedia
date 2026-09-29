-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringHom_functionField_germ_eq_and_linearIndependent_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/aab90e9f-1312-5e9c-b8fc-c2315b3a50d5

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_and_linearIndependent_of_isPullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_and_linearIndependent_of_isPullback.AlgebraicGeometry AlgebraicCurve"
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.germToFunctionField isPushout_appTop_of_isPullback Scheme.Hom Scheme.Hom.germ_stalkMap_apply isPullback_morphismRestrict IsAffineOpen.isoSpec_hom Spec IsIntegral Scheme.Opens.toScheme Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Opens.toSpecΓ_naturality Scheme.toSpecΓ_appTop functionField_isFractionRing_of_isAffineOpen Scheme.Hom.comp_appTop Flat IsAffineOpen Scheme.Opens Scheme.ΓSpecIso_naturality IsAffineHom toSpecΓ Scheme.ΓSpecIso"
namespace FunctionFieldGroundFieldBaseChange
p2m_open "AlgebraicGeometry"

section Pull

variable {X Y : Scheme.{u}}

def pull [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y) : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint X)

theorem pull_germ [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    pull f h (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (h.mem_open U.isOpen hU) (f.app U s) := by
  simp only [pull, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

end Pull

section Core

variable {κ k A B KX KY : Type*} [Field κ] [Field k] [CommRing A] [CommRing B] [Field KX] [Field KY]
  [Algebra κ k] [Algebra κ A] [Algebra A KX] [IsFractionRing A KX] [Algebra B KY] [IsFractionRing B KY]
  [Algebra κ KX] [Algebra k KY]

theorem linearIndependent_of_tensor
    (hKX : ∀ x, algebraMap κ KX x = algebraMap A KX (algebraMap κ A x))
    (β : k →+* B) (hKY : ∀ t, algebraMap k KY t = algebraMap B KY (β t))
    (α : A →+* B) (Λ : k ⊗[κ] A →+* B) (hΛ : ∀ t a, Λ (t ⊗ₜ a) = β t * α a)
    (hΛi : Function.Injective Λ)
    (φ : KX →+* KY) (hφ : ∀ a, φ (algebraMap A KX a) = algebraMap B KY (α a))
    {ιx : Type*} (b : ιx → KX) (hb : LinearIndependent κ b) :
    LinearIndependent k (fun i => φ (b i)) := by
  classical
  haveI : IsScalarTower κ A KX := IsScalarTower.of_algebraMap_eq hKX
  haveI : Nontrivial A := (algebraMap A KX).domain_nontrivial
  rw [linearIndependent_iff']
  intro s g hg

  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) s b
  have hint' : ∀ i ∈ s, ∃ y : A, algebraMap A KX y = algebraMap A KX d * b i := by
    intro i hi
    obtain ⟨y, hy⟩ := hint i hi
    exact ⟨y, by rw [hy]; simp [Algebra.smul_def]⟩
  choose! a ha using hint'
  have hd0 : algebraMap A KX d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd

  have hbs : LinearIndependent κ (fun i : s => a i) := by
    have h1 : LinearIndependent κ (fun i : s => b i) := hb.comp _ Subtype.val_injective
    have h2 : LinearIndependent κ (fun i : s => algebraMap A KX d * b i) := by
      have := h1.map' (LinearMap.mulLeft κ (algebraMap A KX d))
        (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hd0))
      exact this
    have h3 : (fun i : s => algebraMap A KX d * b i) =
        (IsScalarTower.toAlgHom κ A KX).toLinearMap ∘ (fun i : s => a i) := by
      funext i
      simp [ha i i.2]
    rw [h3] at h2
    exact LinearIndependent.of_comp _ h2

  have htens : LinearIndependent k (fun i : s => (1 : k) ⊗ₜ[κ] a i) :=
    Module.Flat.linearIndependent_one_tmul hbs

  have hrel : ∑ i ∈ s, algebraMap B KY (Λ (g i ⊗ₜ a i)) = 0 := by
    have h1 : φ (algebraMap A KX d) * ∑ i ∈ s, g i • φ (b i) = 0 := by rw [hg, mul_zero]
    rw [Finset.mul_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hΛ, map_mul, ← hKY, ← hφ, ha i hi, map_mul, Algebra.smul_def]
    ring
  rw [← map_sum, ← map_sum, map_eq_zero_iff _ (IsFractionRing.injective B KY),
    map_eq_zero_iff _ hΛi] at hrel
  have hrel' : ∑ i : s, g i • ((1 : k) ⊗ₜ[κ] a i) = 0 := by
    rw [Finset.sum_coe_sort s (fun i => g i • ((1 : k) ⊗ₜ[κ] a i)), ← hrel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  intro i hi
  exact (Fintype.linearIndependent_iff.mp htens (fun i : s => g i) hrel') ⟨i, hi⟩

omit [IsFractionRing A KX] [Algebra κ KX] in

theorem exists_div_of_tensor
    (β : k →+* B) (hKY : ∀ t, algebraMap k KY t = algebraMap B KY (β t))
    (α : A →+* B) (Λ : k ⊗[κ] A →+* B) (hΛ : ∀ t a, Λ (t ⊗ₜ a) = β t * α a)
    (hΛs : Function.Surjective Λ)
    (φ : KX →+* KY) (hφ : ∀ a, φ (algebraMap A KX a) = algebraMap B KY (α a)) (z : KY) :
    ∃ u ∈ Algebra.adjoin k (Set.range φ), ∃ v ∈ Algebra.adjoin k (Set.range φ),
      v ≠ 0 ∧ z * v = u := by
  haveI : Nontrivial B := (algebraMap B KY).domain_nontrivial
  have hmem : ∀ p : B, algebraMap B KY p ∈ Algebra.adjoin k (Set.range φ) := by
    intro p
    obtain ⟨x, rfl⟩ := hΛs p
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t a =>
      rw [hΛ, map_mul, ← hKY, ← hφ]
      exact mul_mem (Subalgebra.algebraMap_mem _ t) (Algebra.subset_adjoin ⟨_, rfl⟩)
    | add x y hx hy =>
      rw [map_add, map_add]
      exact add_mem hx hy
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := B) z
  have hq0 : algebraMap B KY q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  exact ⟨_, hmem p, _, hmem q, hq0, div_mul_cancel₀ _ hq0⟩

end Core

section Chart

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

theorem fromSpec_appTop_ΓSpecIso_hom :
    hU.fromSpec.appTop ≫ (Scheme.ΓSpecIso Γ(X, U)).hom = X.presheaf.map (homOfLE le_top).op := by
  have h : (hU.fromSpec ≫ X.toSpecΓ).appTop =
      (Spec.map (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)).appTop := by
    rw [hU.fromSpec_toSpecΓ]
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
  have h2 := Scheme.ΓSpecIso_naturality (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)
  rw [← h, Category.assoc] at h2
  exact (cancel_epi _).mp h2

end Chart

end AlgebraicGeometry.FunctionFieldGroundFieldBaseChange

end

open AlgebraicGeometry.FunctionFieldGroundFieldBaseChange in
theorem solution
    {κ : Type u} [Field κ] {k : Type u} [Field k] (ι : κ →+* k)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (c : X ⟶ Spec (CommRingCat.of κ)) (d : Y ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ X)
    (hP : IsPullback f d c (Spec.map (CommRingCat.ofHom ι))) :
    letI := (baseToFunctionField c).toAlgebra
    letI := (baseToFunctionField d).toAlgebra
    ∃ φ : X.functionField →+* Y.functionField,
      (∀ a : κ, φ (baseToFunctionField c a) = baseToFunctionField d (ι a)) ∧
      (∀ (U : X.Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ U))]
        (s : Γ(X, U)),
        φ (X.germToFunctionField U s) = Y.germToFunctionField (f ⁻¹ᵁ U) ((f.app U).hom s)) ∧
      (∀ {ιx : Type u} (b : ιx → X.functionField),
        LinearIndependent κ b → LinearIndependent k (fun i => φ (b i))) ∧
      (∀ z : Y.functionField, ∃ u ∈ Algebra.adjoin k (Set.range φ), ∃ v ∈ Algebra.adjoin k (Set.range φ),
        v ≠ 0 ∧ z * v = u) := by
  letI := (baseToFunctionField c).toAlgebra
  letI := (baseToFunctionField d).toAlgebra

  have hsurj0 : Surjective (Spec.map (CommRingCat.ofHom ι)) :=
    ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  haveI : Surjective f := MorphismProperty.of_isPullback (P := @Surjective) hP.flip hsurj0
  haveI : IsAffineHom f :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hP.flip inferInstance

  have hgen : f.base (genericPoint Y) ⤳ genericPoint X := by
    obtain ⟨y, hy⟩ := f.surjective (genericPoint X)
    have := (genericPoint_specializes y).map f.base.hom.continuous
    rwa [show f.base.hom y = genericPoint X from hy] at this
  let φ : X.functionField →+* Y.functionField := (pull f hgen).hom
  have hφgerm : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(X, U)),
      φ (X.presheaf.germ U (genericPoint X) hU s) =
        Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) (hgen.mem_open U.isOpen hU) (f.app U s) :=
    fun U hU s => pull_germ f hgen U hU s
  refine ⟨φ, ?_, ?_, ?_⟩
  ·
    intro a
    have e1 : f.appTop (c.appTop ((Scheme.ΓSpecIso (.of κ)).inv a)) =
        d.appTop ((Spec.map (CommRingCat.ofHom ι)).appTop ((Scheme.ΓSpecIso (.of κ)).inv a)) := by
      change (c.appTop ≫ f.appTop) _ = ((Spec.map _).appTop ≫ d.appTop) _
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hP.w]
    have e2 : (Spec.map (CommRingCat.ofHom ι)).appTop ((Scheme.ΓSpecIso (.of κ)).inv a) =
        (Scheme.ΓSpecIso (.of k)).inv (ι a) := by
      have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ι)
      have := congrArg (fun ψ : CommRingCat.of κ ⟶ _ => ψ.hom a) h
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      exact this.symm
    calc φ (baseToFunctionField c a)
        = Y.presheaf.germ ⊤ (genericPoint Y) trivial
            (f.appTop (c.appTop ((Scheme.ΓSpecIso (.of κ)).inv a))) :=
          hφgerm ⊤ trivial _
      _ = baseToFunctionField d (ι a) := by rw [e1, e2]; rfl
  ·
    intro U _ _ s
    exact hφgerm U _ s

  obtain ⟨U, hU, hxU⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
    exact ⟨U, hU, hxU⟩
  have hyV : genericPoint Y ∈ f ⁻¹ᵁ U := hgen.mem_open U.isOpen hxU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨_, hyV⟩⟩
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  haveI := functionField_isFractionRing_of_isAffineOpen Y (f ⁻¹ᵁ U) hV

  have hP1 : IsPullback (f ∣_ U) ((f ⁻¹ᵁ U).ι ≫ d) (U.ι ≫ c) (Spec.map (CommRingCat.ofHom ι)) :=
    (isPullback_morphismRestrict f U).paste_vert hP
  have hP2 : IsPullback (Spec.map (f.app U)) (hV.fromSpec ≫ d) (hU.fromSpec ≫ c)
      (Spec.map (CommRingCat.ofHom ι)) := by
    refine hP1.of_iso hV.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
      exact (Scheme.Opens.toSpecΓ_naturality f U).symm
    · simp [IsAffineOpen.isoSpec_hom]
    · simp [IsAffineOpen.isoSpec_hom]
    · simp
  have hPO := isPushout_appTop_of_isPullback hP2

  let gA : κ →+* Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of κ)).inv ≫ c.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom
  let βB : k →+* Γ(Y, f ⁻¹ᵁ U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ d.appTop ≫ Y.presheaf.map (homOfLE le_top).op).hom
  letI : Algebra κ k := ι.toAlgebra
  letI : Algebra κ Γ(X, U) := gA.toAlgebra
  have hPO' : IsPushout (CommRingCat.ofHom (algebraMap κ k)) (CommRingCat.ofHom (algebraMap κ Γ(X, U)))
      (CommRingCat.ofHom βB) (f.app U) := by
    refine hPO.flip.of_iso (Scheme.ΓSpecIso (.of κ)) (Scheme.ΓSpecIso (.of k))
      (Scheme.ΓSpecIso Γ(X, U)) (Scheme.ΓSpecIso Γ(Y, f ⁻¹ᵁ U)) ?_ ?_ ?_ ?_
    · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ι)
    · rw [Scheme.Hom.comp_appTop, Category.assoc, fromSpec_appTop_ΓSpecIso_hom]
      change _ = (Scheme.ΓSpecIso (.of κ)).hom ≫ (Scheme.ΓSpecIso (.of κ)).inv ≫ c.appTop ≫
        X.presheaf.map (homOfLE le_top).op
      rw [Iso.hom_inv_id_assoc]
    · rw [Scheme.Hom.comp_appTop, Category.assoc, fromSpec_appTop_ΓSpecIso_hom]
      change _ = (Scheme.ΓSpecIso (.of k)).hom ≫ (Scheme.ΓSpecIso (.of k)).inv ≫ d.appTop ≫
        Y.presheaf.map (homOfLE le_top).op
      rw [Iso.hom_inv_id_assoc]
    · exact Scheme.ΓSpecIso_naturality (f.app U)
  let Θ : CommRingCat.of (k ⊗[κ] Γ(X, U)) ≅ Γ(Y, f ⁻¹ᵁ U) :=
    (CommRingCat.isPushout_tensorProduct κ k Γ(X, U)).isoIsPushout _ _ hPO'
  let Λ : k ⊗[κ] Γ(X, U) ≃+* Γ(Y, f ⁻¹ᵁ U) := Θ.commRingCatIsoToRingEquiv
  have hΛl : ∀ t : k, Λ (t ⊗ₜ 1) = βB t := fun t => by
    have := congrArg (fun ψ => ψ.hom t)
      ((CommRingCat.isPushout_tensorProduct κ k Γ(X, U)).inl_isoIsPushout_hom _ _ hPO')
    exact this
  have hΛr : ∀ a : Γ(X, U), Λ (1 ⊗ₜ a) = f.app U a := fun a => by
    have := congrArg (fun ψ => ψ.hom a)
      ((CommRingCat.isPushout_tensorProduct κ k Γ(X, U)).inr_isoIsPushout_hom _ _ hPO')
    exact this
  have hΛ : ∀ (t : k) (a : Γ(X, U)), Λ.toRingHom (t ⊗ₜ a) = βB t * (f.app U).hom a := by
    intro t a
    rw [show t ⊗ₜ[κ] a = (t ⊗ₜ[κ] (1 : Γ(X, U))) * ((1 : k) ⊗ₜ[κ] a) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_mul, hΛl, hΛr]

  have hKX : ∀ x : κ, algebraMap κ X.functionField x =
      algebraMap Γ(X, U) X.functionField (algebraMap κ Γ(X, U) x) := by
    intro x
    change baseToFunctionField c x =
      X.germToFunctionField U ((X.presheaf.map (homOfLE le_top).op) (c.appTop ((Scheme.ΓSpecIso (.of κ)).inv x)))
    dsimp only [baseToFunctionField, Scheme.germToFunctionField, RingHom.coe_comp, Function.comp_apply]
    rw [TopCat.Presheaf.germ_res_apply]
  have hKY : ∀ t : k, algebraMap k Y.functionField t =
      algebraMap Γ(Y, f ⁻¹ᵁ U) Y.functionField (βB t) := by
    intro t
    change baseToFunctionField d t =
      Y.germToFunctionField (f ⁻¹ᵁ U)
        ((Y.presheaf.map (homOfLE le_top).op) (d.appTop ((Scheme.ΓSpecIso (.of k)).inv t)))
    dsimp only [baseToFunctionField, Scheme.germToFunctionField, RingHom.coe_comp, Function.comp_apply]
    rw [TopCat.Presheaf.germ_res_apply]
  have hφA : ∀ a : Γ(X, U), φ (algebraMap Γ(X, U) X.functionField a) =
      algebraMap Γ(Y, f ⁻¹ᵁ U) Y.functionField ((f.app U).hom a) :=
    fun a => hφgerm U _ a
  refine ⟨?_, ?_⟩
  · intro ιx b hb
    exact linearIndependent_of_tensor hKX βB hKY (f.app U).hom Λ.toRingHom hΛ Λ.injective φ hφA b hb
  · intro z
    exact exists_div_of_tensor βB hKY (f.app U).hom Λ.toRingHom hΛ Λ.surjective φ hφA z

end S_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_and_linearIndependent_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_and_linearIndependent_of_isPullback (solution)
