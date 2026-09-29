-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensorProduct_chartAlg_adjoin_coeffMap_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b2a1ecf1-43ca-5087-bbb2-2131b3de1f49

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_IntermediateField_injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensorProduct_chartAlg_adjoin_coeffMap_of_isIntegrallyClosed

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct
open AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type) [CommRing R] [IsDomain R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F₀ : IntermediateField K₀ (LaurentSeries K₀)) [Algebra R ↥F₀] [IsScalarTower R K₀ ↥F₀]
    (x : ↥F₀) [Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ ({x} : Set ↥F₀)) ↥F₀]
    [Module.Flat R ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))]
    (L : Type) [Field L] (i : K₀ →+* L)
    (K' : IntermediateField L (LaurentSeries L))
    (hK' : K' = IntermediateField.adjoin L (⇑(ModularCurve.coeffMap i) '' (F₀ : Set (LaurentSeries K₀))))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra R A] (hRA : ∀ r : R, algebraMap A L (algebraMap R A r) = i (algebraMap R K₀ r))
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (x' : ↥K') (hx' : ((x' : ↥K') : LaurentSeries L) = ModularCurve.coeffMap i ((x : ↥F₀) : LaurentSeries K₀))
    [IsDomain (A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)))]
    [IsIntegrallyClosed (A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)))] :
    ∃ e : A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) ≃ₐ[A] ↥(chartAlg A ↥K' ({x'} : Set ↥K')),
      ∀ b : ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)),
        (((e (1 ⊗ₜ[R] b) : ↥K') : LaurentSeries L)) = ModularCurve.coeffMap i ((b : ↥F₀) : LaurentSeries K₀) := by
  classical

  letI algRL : Algebra R L := ((algebraMap A L).comp (algebraMap R A)).toAlgebra
  haveI stRAL : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI algRK' : Algebra R ↥K' := ((algebraMap A ↥K').comp (algebraMap R A)).toAlgebra
  haveI stRAK' : IsScalarTower R A ↥K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI algK₀L : Algebra K₀ L := i.toAlgebra
  haveI stRK₀L : IsScalarTower R K₀ L := IsScalarTower.of_algebraMap_eq (fun r => by
    show algebraMap A L (algebraMap R A r) = i (algebraMap R K₀ r)
    exact hRA r)

  have hLLS : ∀ l : L, algebraMap L (LaurentSeries L) l = HahnSeries.single 0 l :=
    fun l => ModularCurve.algebraMap_laurentSeries_eq_single L l
  have hLPS : ∀ l : L, algebraMap L (LaurentSeries L) l =
      HahnSeries.ofPowerSeries ℤ L (algebraMap L (PowerSeries L) l) := fun _ => rfl
  have hK₀LS : ∀ k : K₀, algebraMap K₀ (LaurentSeries L) k = HahnSeries.single 0 (i k) := by
    intro k
    have h1 : algebraMap K₀ (LaurentSeries L) k = HahnSeries.ofPowerSeries ℤ L (algebraMap K₀ (PowerSeries L) k) := rfl
    rw [h1, IsScalarTower.algebraMap_apply K₀ L (PowerSeries L), ← hLPS, hLLS]
    rfl
  have hRLS : ∀ r : R, algebraMap R (LaurentSeries L) r = HahnSeries.single 0 (algebraMap A L (algebraMap R A r)) := by
    intro r
    have h1 : algebraMap R (LaurentSeries L) r = HahnSeries.ofPowerSeries ℤ L (algebraMap R (PowerSeries L) r) := rfl
    rw [h1, IsScalarTower.algebraMap_apply R L (PowerSeries L), ← hLPS, hLLS]
    rfl
  haveI stK₀LLS := IsScalarTower.of_algebraMap_eq (R := K₀) (S := L) (A := LaurentSeries L)
    (fun k => by rw [hLLS, hK₀LS]; rfl)
  haveI stRLLS := IsScalarTower.of_algebraMap_eq (R := R) (S := L) (A := LaurentSeries L)
    (fun r => by rw [hLLS, hRLS]; rfl)
  haveI stRK₀LS := IsScalarTower.of_algebraMap_eq (R := R) (S := K₀) (A := LaurentSeries L)
    (fun r => by rw [hK₀LS, hRLS, ← hRA])
  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

  have hcoe_alg : ∀ l : L, ((algebraMap L ↥K' l : ↥K') : LaurentSeries L) = HahnSeries.single 0 l := by
    intro l
    rw [← ModularCurve.algebraMap_laurentSeries_eq_single L l]
    rfl
  have hcoe_algF : ∀ k : K₀, ((algebraMap K₀ ↥F₀ k : ↥F₀) : LaurentSeries K₀) = HahnSeries.single 0 k := by
    intro k
    rw [← ModularCurve.algebraMap_laurentSeries_eq_single K₀ k]
    rfl

  have hmemK' : ∀ f : ↥F₀, ModularCurve.coeffMap i ((f : ↥F₀) : LaurentSeries K₀) ∈ K' := by
    intro f
    rw [hK']
    exact IntermediateField.subset_adjoin L _ ⟨(f : LaurentSeries K₀), f.2, rfl⟩
  let ιF : ↥F₀ →+* ↥K' :=
    { toFun := fun f => ⟨ModularCurve.coeffMap i ((f : ↥F₀) : LaurentSeries K₀), hmemK' f⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hιF : ∀ f : ↥F₀, ((ιF f : ↥K') : LaurentSeries L) = ModularCurve.coeffMap i ((f : ↥F₀) : LaurentSeries K₀) :=
    fun f => rfl
  have hιF_alg : ∀ r : R, ιF (algebraMap R ↥F₀ r) = algebraMap R ↥K' r := by
    intro r
    apply Subtype.ext
    rw [hιF, IsScalarTower.algebraMap_apply R K₀ ↥F₀, hcoe_algF, ModularCurve.coeffMap_single]
    show HahnSeries.single 0 (i (algebraMap R K₀ r)) = ((algebraMap A ↥K' (algebraMap R A r) : ↥K') : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K', hcoe_alg, hRA]
  have hιF_x : ιF x = x' := Subtype.ext (by rw [hιF]; exact hx'.symm)

  let ιB : ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) →ₐ[R] ↥K' :=
    { toRingHom := ιF.comp (chartAlg R ↥F₀ ({x} : Set ↥F₀)).val.toRingHom
      commutes' := fun r => by
        show ιF (((algebraMap R ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) r) : ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))) : ↥F₀) = algebraMap R ↥K' r
        rw [Subalgebra.coe_algebraMap]
        exact hιF_alg r }
  let θ : A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) →ₐ[A] ↥K' :=
    Algebra.TensorProduct.lift (Algebra.ofId A ↥K') ιB (fun _ _ => Commute.all _ _)
  have hθ : ∀ (a : A) (b : ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))), θ (a ⊗ₜ[R] b) = algebraMap A ↥K' a * ιF (b : ↥F₀) := by
    intro a b
    show Algebra.TensorProduct.lift (Algebra.ofId A ↥K') ιB (fun _ _ => Commute.all _ _) (a ⊗ₜ[R] b) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl

  have hadj : ∀ f : ↥F₀, f ∈ Algebra.adjoin R ({x} : Set ↥F₀) → ιF f ∈ Algebra.adjoin A ({x'} : Set ↥K') := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem z hz =>
        rw [Set.mem_singleton_iff] at hz
        subst hz
        rw [hιF_x]
        exact Algebra.subset_adjoin (Set.mem_singleton x')
    | algebraMap r =>
        rw [hιF_alg, IsScalarTower.algebraMap_apply R A ↥K']
        exact Subalgebra.algebraMap_mem _ _
    | add f g _ _ ihf ihg => rw [map_add]; exact Subalgebra.add_mem _ ihf ihg
    | mul f g _ _ ihf ihg => rw [map_mul]; exact Subalgebra.mul_mem _ ihf ihg
  let φadj : ↥(Algebra.adjoin R ({x} : Set ↥F₀)) →+* ↥(Algebra.adjoin A ({x'} : Set ↥K')) :=
    ιF.restrict _ _ (fun f hf => hadj f hf)
  have hθmem : ∀ z : A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)), θ z ∈ chartAlg A ↥K' ({x'} : Set ↥K') := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subalgebra.zero_mem _
    | tmul a b =>
        rw [hθ]
        refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) ?_
        rw [mem_chartAlg_iff]
        have hb : IsIntegral ↥(Algebra.adjoin R ({x} : Set ↥F₀)) (b : ↥F₀) := (mem_chartAlg_iff R ↥F₀).mp b.2
        exact hb.map_of_comp_eq φadj ιF (by ext f; rfl)
    | add z w hz hw => rw [map_add]; exact Subalgebra.add_mem _ hz hw
  let θ' : A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) →ₐ[A] ↥(chartAlg A ↥K' ({x'} : Set ↥K')) := θ.codRestrict (chartAlg A ↥K' ({x'} : Set ↥K')) hθmem
  have hθ' : ∀ z, ((θ' z : ↥(chartAlg A ↥K' ({x'} : Set ↥K'))) : ↥K') = θ z := fun z => rfl

  haveI : Module.Flat R K₀ := IsLocalization.flat K₀ (nonZeroDivisors R)
  haveI : Module.Flat R L := Module.Flat.trans R K₀ L
  let ψ : ↥F₀ →ₐ[K₀] LaurentSeries L :=
    { toRingHom := (ModularCurve.coeffMap i).comp (IntermediateField.val F₀).toRingHom
      commutes' := fun k => by
        rw [hK₀LS]
        show ModularCurve.coeffMap i (((algebraMap K₀ ↥F₀ k) : ↥F₀) : LaurentSeries K₀) = _
        rw [hcoe_algF, ModularCurve.coeffMap_single] }
  have hψ : ∀ f : ↥F₀, ψ f = ModularCurve.coeffMap i ((f : ↥F₀) : LaurentSeries K₀) := fun f => rfl
  let f₄ : L ⊗[K₀] ↥F₀ →ₐ[L] LaurentSeries L :=
    Algebra.TensorProduct.lift (Algebra.ofId L (LaurentSeries L)) ψ (fun _ _ => Commute.all _ _)
  have hf₄ : ∀ (l : L) (f : ↥F₀), f₄ (l ⊗ₜ[K₀] f) = algebraMap L (LaurentSeries L) l * ψ f := by
    intro l f
    show Algebra.TensorProduct.lift (Algebra.ofId L (LaurentSeries L)) ψ (fun _ _ => Commute.all _ _) (l ⊗ₜ[K₀] f) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  have hf₄inj : Function.Injective f₄ :=
    IntermediateField.injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries K₀ L F₀ f₄ (fun f => by
      rw [hf₄, map_one, one_mul, hψ]
      rfl)
  haveI := IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors R) K₀ L ↥F₀
  let f₃ : L ⊗[K₀] ↥F₀ ≃ₗ[K₀] L ⊗[R] ↥F₀ := IsLocalization.moduleTensorEquiv (nonZeroDivisors R) K₀ L ↥F₀
  have hf₃ : ∀ (l : L) (f : ↥F₀), f₃ (l ⊗ₜ[K₀] f) = l ⊗ₜ[R] f := fun l f =>
    TensorProduct.mapOfCompatibleSMul_tmul ..
  let ψR : ↥F₀ →ₐ[R] LaurentSeries L := ψ.restrictScalars R
  let f₄' : L ⊗[R] ↥F₀ →ₐ[L] LaurentSeries L :=
    Algebra.TensorProduct.lift (Algebra.ofId L (LaurentSeries L)) ψR (fun _ _ => Commute.all _ _)
  have hf₄' : ∀ (l : L) (f : ↥F₀), f₄' (l ⊗ₜ[R] f) = algebraMap L (LaurentSeries L) l * ψ f := by
    intro l f
    show Algebra.TensorProduct.lift (Algebra.ofId L (LaurentSeries L)) ψR (fun _ _ => Commute.all _ _) (l ⊗ₜ[R] f) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  have hcomp : ∀ z : L ⊗[K₀] ↥F₀, f₄' (f₃ z) = f₄ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul l f => rw [hf₃, hf₄', hf₄]
    | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]
  have hf₄'inj : Function.Injective f₄' := by
    intro z w hzw
    have hz := hcomp (f₃.symm z)
    have hw := hcomp (f₃.symm w)
    rw [LinearEquiv.apply_symm_apply] at hz hw
    have : f₄ (f₃.symm z) = f₄ (f₃.symm w) := by rw [← hz, ← hw, hzw]
    exact f₃.symm.injective (hf₄inj this)
  let aAL : A →ₗ[R] L := (IsScalarTower.toAlgHom R A L).toLinearMap
  have haAL : ∀ a : A, aAL a = algebraMap A L a := fun a => rfl
  let f₁ : A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) →ₗ[R] L ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) := LinearMap.rTensor ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) aAL
  have hf₁inj : Function.Injective f₁ :=
    Module.Flat.rTensor_preserves_injective_linearMap aAL hinjAL
  let vB : ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) →ₗ[R] ↥F₀ := (chartAlg R ↥F₀ ({x} : Set ↥F₀)).val.toLinearMap
  let f₂ : L ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) →ₗ[R] L ⊗[R] ↥F₀ := LinearMap.lTensor L vB
  have hf₂inj : Function.Injective f₂ :=
    Module.Flat.lTensor_preserves_injective_linearMap vB (fun a b h => Subtype.ext h)
  have hchain : ∀ z : A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)), f₄' (f₂ (f₁ z)) = ((θ z : ↥K') : LaurentSeries L) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | tmul a b =>
        have h1 : f₁ (a ⊗ₜ[R] b) = algebraMap A L a ⊗ₜ[R] b := by
          show LinearMap.rTensor _ aAL (a ⊗ₜ[R] b) = _
          rw [LinearMap.rTensor_tmul]
          rfl
        have h2 : f₂ (algebraMap A L a ⊗ₜ[R] b) = algebraMap A L a ⊗ₜ[R] ((b : ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))) : ↥F₀) := by
          show LinearMap.lTensor L vB _ = _
          rw [LinearMap.lTensor_tmul]
          rfl
        rw [h1, h2, hf₄', hψ, hθ]
        show _ = ((algebraMap A ↥K' a : ↥K') : LaurentSeries L) * ((ιF (b : ↥F₀) : ↥K') : LaurentSeries L)
        rw [hιF, IsScalarTower.algebraMap_apply A L ↥K', hcoe_alg, hLLS]
    | add z w hz hw =>
        rw [map_add, map_add, map_add, hz, hw, map_add]
        rfl
  have hθinj : Function.Injective θ := by
    intro z w hzw
    apply hf₁inj
    apply hf₂inj
    apply hf₄'inj
    rw [hchain, hchain, hzw]

  haveI : IsFractionRing ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) ↥F₀ :=
    AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg R K₀ ↥F₀ ({x} : Set ↥F₀)
  let θL : A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) →+* LaurentSeries L := (IntermediateField.val K').toRingHom.comp θ.toRingHom
  have hθL : ∀ z, θL z = ((θ z : ↥K') : LaurentSeries L) := fun z => rfl
  have hLmem : ∀ l : L, algebraMap L (LaurentSeries L) l ∈ Subfield.closure (Set.range θL) := by
    intro l
    obtain ⟨a, a', -, hl⟩ := IsFractionRing.div_surjective (A := A) l
    rw [← hl, map_div₀]
    have hmem : ∀ a : A, algebraMap L (LaurentSeries L) (algebraMap A L a) ∈ Subfield.closure (Set.range θL) := by
      intro a
      refine Subfield.subset_closure ⟨a ⊗ₜ[R] 1, ?_⟩
      rw [hθL, hθ, OneMemClass.coe_one, map_one, mul_one, IsScalarTower.algebraMap_apply A L ↥K', hcoe_alg, hLLS]
    exact div_mem (hmem a) (hmem a')
  let E : IntermediateField L (LaurentSeries L) := (Subfield.closure (Set.range θL)).toIntermediateField hLmem
  have hadjE : IntermediateField.adjoin L (⇑(ModularCurve.coeffMap i) '' (F₀ : Set (LaurentSeries K₀))) ≤ E := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨f, hf, rfl⟩
    show ModularCurve.coeffMap i f ∈ Subfield.closure (Set.range θL)
    obtain ⟨b, c, -, hbc⟩ := IsFractionRing.div_surjective (A := ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))) (⟨f, hf⟩ : ↥F₀)
    have hf' : f = ((b : ↥F₀) : LaurentSeries K₀) / ((c : ↥F₀) : LaurentSeries K₀) := by
      have h := congrArg (fun w : ↥F₀ => (w : LaurentSeries K₀)) hbc
      exact h.symm
    rw [hf', map_div₀]
    refine div_mem (Subfield.subset_closure ⟨1 ⊗ₜ[R] b, ?_⟩) (Subfield.subset_closure ⟨1 ⊗ₜ[R] c, ?_⟩)
    · rw [hθL, hθ, map_one, one_mul, hιF]
    · rw [hθL, hθ, map_one, one_mul, hιF]
  have hK'E : K' ≤ E := hK'.trans_le hadjE
  have hcl : Subring.closure (Set.range θL) = θL.range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  have hfracK' : ∀ z : ↥K', ∃ u v : A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)), z = θ u / θ v := by
    intro z
    have hz : (z : LaurentSeries L) ∈ Subfield.closure (Set.range θL) := hK'E z.2
    obtain ⟨y, hy, w, hw, hyw⟩ := Subfield.mem_closure_iff.mp hz
    rw [hcl] at hy hw
    obtain ⟨u, rfl⟩ := RingHom.mem_range.mp hy
    obtain ⟨v, rfl⟩ := RingHom.mem_range.mp hw
    refine ⟨u, v, Subtype.ext ?_⟩
    rw [← hyw, hθL, hθL]
    rfl
  letI algDK' : Algebra (A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))) ↥K' := θ.toRingHom.toAlgebra
  haveI : FaithfulSMul (A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))) ↥K' := (faithfulSMul_iff_algebraMap_injective _ _).mpr hθinj
  haveI : IsFractionRing (A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))) ↥K' :=
    IsFractionRing.of_field (surj := fun z => hfracK' z)
  have hxB : (x : ↥F₀) ∈ chartAlg R ↥F₀ ({x} : Set ↥F₀) := subset_chartAlg R ↥F₀ _ (Set.mem_singleton x)
  have hrange : Algebra.adjoin A ({x'} : Set ↥K') ≤ θ.range := by
    refine Algebra.adjoin_le ?_
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    refine ⟨1 ⊗ₜ[R] ⟨x, hxB⟩, ?_⟩
    show θ (1 ⊗ₜ[R] ⟨x, hxB⟩) = _
    rw [hθ, map_one, one_mul]
    exact hιF_x
  have hθsurj : ∀ c : ↥(chartAlg A ↥K' ({x'} : Set ↥K')), ∃ y, θ y = (c : ↥K') := by
    intro c
    have hc : IsIntegral ↥(Algebra.adjoin A ({x'} : Set ↥K')) (c : ↥K') := (mem_chartAlg_iff A ↥K').mp c.2
    have hc2 : IsIntegral ↥θ.range (c : ↥K') :=
      hc.map_of_comp_eq (Subalgebra.inclusion hrange).toRingHom (RingHom.id ↥K') (by ext; rfl)
    let eθ := AlgEquiv.ofInjective θ hθinj
    have hc3 : IsIntegral (A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))) (c : ↥K') := by
      refine hc2.map_of_comp_eq (eθ.symm : ↥θ.range →ₐ[A] A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))).toRingHom (RingHom.id ↥K') ?_
      refine RingHom.ext (fun w => ?_)
      show θ (eθ.symm w) = (w : ↥K')
      have h := congrArg (fun t : ↥θ.range => (t : ↥K')) (AlgEquiv.apply_symm_apply eθ w)
      exact h
    exact (IsIntegrallyClosed.isIntegral_iff (R := A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))) (K := ↥K')).mp hc3

  have hbij : Function.Bijective θ' := by
    refine ⟨fun z w h => hθinj ?_, fun c => ?_⟩
    · rw [← hθ', ← hθ', h]
    · obtain ⟨y, hy⟩ := hθsurj c
      exact ⟨y, Subtype.ext hy⟩
  refine ⟨AlgEquiv.ofBijective θ' hbij, fun b => ?_⟩
  show ((θ (1 ⊗ₜ[R] b) : ↥K') : LaurentSeries L) = _
  rw [hθ, map_one, one_mul, hιF]

end S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensorProduct_chartAlg_adjoin_coeffMap_of_isIntegrallyClosed
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensorProduct_chartAlg_adjoin_coeffMap_of_isIntegrallyClosed (solution)
