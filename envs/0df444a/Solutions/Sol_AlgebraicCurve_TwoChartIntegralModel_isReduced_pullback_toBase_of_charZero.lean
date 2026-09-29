-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/84e73b16-0a69-53d4-8b76-56ec64a8ea71

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_charZero

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped TensorProduct

noncomputable section

namespace GenRed8d5d971b

theorem isReduced_tensorProduct_of_isSeparable (K Ω L : Type*) [Field K] [Field Ω] [Field L]
    [Algebra K Ω] [Algebra K L] [Algebra.IsSeparable K L] : _root_.IsReduced (Ω ⊗[K] L) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB => ?_
  obtain ⟨s, hs⟩ := hB
  let M : IntermediateField K L := IntermediateField.adjoin K (s : Set L)
  have hBM : ∀ x : L, x ∈ B → x ∈ M := by
    intro x hx
    have hle : B ≤ M.toSubalgebra := by
      rw [← hs, Algebra.adjoin_le_iff]
      exact IntermediateField.subset_adjoin K _
    exact hle hx
  haveI : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : Algebra.IsSeparable K M := Algebra.isSeparable_tower_bot_of_isSeparable K M L
  haveI : Algebra.FormallyUnramified K M := Algebra.FormallyUnramified.of_isSeparable K M
  haveI : Algebra.FormallyUnramified Ω (Ω ⊗[K] M) := Algebra.FormallyUnramified.base_change Ω
  haveI : Module.Finite Ω (Ω ⊗[K] M) := inferInstance
  haveI : Algebra.FiniteType Ω (Ω ⊗[K] M) := inferInstance
  haveI : Algebra.EssFiniteType Ω (Ω ⊗[K] M) := inferInstance
  haveI : _root_.IsReduced (Ω ⊗[K] M) :=
    Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[K] M)
  let f : B →ₐ[K] M :=
    { toFun := fun b => ⟨b.1, hBM b.1 b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id K Ω) f)
    (Module.Flat.lTensor_preserves_injective_linearMap (M := Ω) f.toLinearMap hf)

theorem isDomain_tensorProduct_of_algEquiv_mvPolynomial (K E P : Type*) [Field K] [Field E]
    [Algebra K E] [CommRing P] [Algebra K P] {ι : Type*} (e : P ≃ₐ[K] MvPolynomial ι K) :
    IsDomain (P ⊗[K] E) := by
  let e₁ : P ⊗[K] E ≃+* MvPolynomial ι E :=
    ((Algebra.TensorProduct.comm K P E).trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[K] E) e)).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv K E).toRingEquiv
  exact Function.Injective.isDomain e₁ e₁.injective

theorem isDomain_tensorProduct_of_isFractionRing (K E P K₁ : Type*) [Field K] [Field E]
    [Algebra K E] [CommRing P] [IsDomain P] [Algebra K P] [Field K₁] [Algebra K K₁] [Algebra P K₁]
    [IsScalarTower K P K₁] [IsFractionRing P K₁] [IsDomain (P ⊗[K] E)] :
    IsDomain (K₁ ⊗[K] E) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (P ⊗[K] E) (nonZeroDivisors P))
      ((P ⊗[K] E) ⊗[P] K₁) := IsLocalization.tensor K₁ (nonZeroDivisors P)
  have hinj : Function.Injective (algebraMap P (P ⊗[K] E)) := by
    have h := Algebra.TensorProduct.includeLeft_injective (R := K) (S := K) (A := P) (B := E)
      (algebraMap K E).injective
    intro x y hxy
    exact h hxy
  have hle : Algebra.algebraMapSubmonoid (P ⊗[K] E) (nonZeroDivisors P) ≤
      nonZeroDivisors (P ⊗[K] E) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    have hx0 : (x : P) ≠ 0 := nonZeroDivisors.ne_zero hx
    exact hx0 (hinj (h0.trans (map_zero _).symm))
  haveI : IsDomain ((P ⊗[K] E) ⊗[P] K₁) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors ((P ⊗[K] E) ⊗[P] K₁) hle
  let e₂ : K₁ ⊗[K] E ≃+* (P ⊗[K] E) ⊗[P] K₁ :=
    (Algebra.TensorProduct.cancelBaseChange K P K₁ K₁ E).symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm P K₁ (P ⊗[K] E)).toRingEquiv
  exact Function.Injective.isDomain e₂ e₂.injective

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem isDomain_adjoin_tensorProduct (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E]
    [Algebra K L] {ι : Type*} {v : ι → L} (hv : AlgebraicIndependent K v) :
    IsDomain ((IntermediateField.adjoin K (Set.range v)) ⊗[K] E) := by
  haveI : IsDomain ((Algebra.adjoin K (Set.range v)) ⊗[K] E) :=
    isDomain_tensorProduct_of_algEquiv_mvPolynomial K E _ hv.aevalEquiv.symm
  exact isDomain_tensorProduct_of_isFractionRing K E (Algebra.adjoin K (Set.range v)) _

theorem isReduced_tensorProduct_of_tower (K K₁ E L Ω : Type*) [Field K] [Field K₁] [Field E]
    [Field L] [Field Ω] [Algebra K K₁] [Algebra K E] [Algebra K L] [Algebra K₁ L]
    [IsScalarTower K K₁ L] [Algebra.IsSeparable K₁ L] [Algebra K₁ Ω]
    (φ : (K₁ ⊗[K] E) →ₐ[K₁] Ω) (hφ : Function.Injective φ) : _root_.IsReduced (E ⊗[K] L) := by
  haveI : _root_.IsReduced (Ω ⊗[K₁] L) := isReduced_tensorProduct_of_isSeparable K₁ Ω L
  haveI : _root_.IsReduced ((K₁ ⊗[K] E) ⊗[K₁] L) :=
    isReduced_of_injective (Algebra.TensorProduct.map φ (AlgHom.id K₁ L))
      (Module.Flat.rTensor_preserves_injective_linearMap (M := L) φ.toLinearMap hφ)
  let e : E ⊗[K] L ≃+* (K₁ ⊗[K] E) ⊗[K₁] L :=
    (Algebra.TensorProduct.comm K E L).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange K K₁ K₁ L E).symm.toRingEquiv.trans
        (Algebra.TensorProduct.comm K₁ L (K₁ ⊗[K] E)).toRingEquiv)
  exact isReduced_of_injective e e.injective

theorem isReduced_tensorProduct_of_charZero (K E L : Type*) [Field K] [CharZero K] [Field E]
    [Field L] [Algebra K E] [Algebra K L] : _root_.IsReduced (E ⊗[K] L) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  let K₁ : IntermediateField K L := IntermediateField.adjoin K (Set.range ((↑) : s → L))
  haveI : Algebra.IsAlgebraic K₁ L := hs.isAlgebraic_field
  haveI : Algebra.IsSeparable K₁ L := inferInstance
  haveI : IsDomain (K₁ ⊗[K] E) := isDomain_adjoin_tensorProduct K E L hs.1
  exact isReduced_tensorProduct_of_tower K K₁ E L (FractionRing (K₁ ⊗[K] E))
    (IsScalarTower.toAlgHom K₁ (K₁ ⊗[K] E) (FractionRing (K₁ ⊗[K] E)))
    (fun a b h => IsFractionRing.injective (K₁ ⊗[K] E) (FractionRing (K₁ ⊗[K] E)) h)

theorem isReduced_subalgebra_tensorProduct (R : Type*) [CommRing R] [IsDomain R] (K₀ : Type*)
    [Field K₀] [Algebra R K₀] [IsFractionRing R K₀] [CharZero K₀]
    (F : Type*) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (k : Type*) [Field k] [Algebra R k] [Algebra K₀ k] [IsScalarTower R K₀ k]
    (A : Subalgebra R F) : _root_.IsReduced (A ⊗[R] k) := by
  haveI : Module.Flat R K₀ := IsLocalization.flat K₀ (nonZeroDivisors R)
  haveI : Module.Flat R k := Module.Flat.trans R K₀ k
  haveI : _root_.IsReduced (F ⊗[K₀] k) := isReduced_tensorProduct_of_charZero K₀ F k
  haveI : TensorProduct.CompatibleSMul R K₀ F k :=
    IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors R) K₀ F k
  let e : F ⊗[K₀] k ≃ₐ[R] F ⊗[R] k := Algebra.TensorProduct.equivOfCompatibleSMul R K₀ R F k
  haveI : _root_.IsReduced (F ⊗[R] k) := isReduced_of_injective e.symm e.symm.injective
  exact isReduced_of_injective (Algebra.TensorProduct.map A.val (AlgHom.id R k))
    (Module.Flat.rTensor_preserves_injective_linearMap (M := k) A.val.toLinearMap
      Subtype.val_injective)

end GenRed8d5d971b

end

open scoped TensorProduct in
open AlgebraicCurve.TwoChartIntegralModel in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀] [CharZero K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] (j : F) [Fact (j ≠ 0)]
    (k : Type u) [Field k] [Algebra R k] [Algebra K₀ k] [IsScalarTower R K₀ k] :
    AlgebraicGeometry.IsReduced
      (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R k)))) := by

  have haff : ∀ (S : Set F), AlgebraicGeometry.IsReduced
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlg R F S))))
        (Spec.map (CommRingCat.ofHom (algebraMap R k)))) := fun S => by
    haveI : _root_.IsReduced (↥(chartAlg R F S) ⊗[R] k) :=
      GenRed8d5d971b.isReduced_subalgebra_tensorProduct R K₀ F k (chartAlg R F S)
    haveI : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (↥(chartAlg R F S) ⊗[R] k))) :=
      inferInstance
    exact isReduced_of_isOpenImmersion (pullbackSpecIso R ↥(chartAlg R F S) k).hom

  let 𝒰 := Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰 (toBase R F j)
    (Spec.map (CommRingCat.ofHom (algebraMap R k)))
  haveI : ∀ i, AlgebraicGeometry.IsReduced (𝒱.X i) := by
    intro i
    change AlgebraicGeometry.IsReduced
      (pullback (𝒰.f i ≫ toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R k))))
    rcases i with (_ | _ | _)
    · have hw : 𝒰.f none = fFin R F j ≫ ιFin R F j :=
        (colimit.w (span (fFin R F j) (fInf R F j)) WalkingSpan.Hom.fst).symm
      have e : 𝒰.f none ≫ toBase R F j =
          Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgMid R F j))) := by
        rw [hw]
        show (fFin R F j ≫ ιFin R F j) ≫ toBase R F j = _
        calc (fFin R F j ≫ ιFin R F j) ≫ toBase R F j
            = fFin R F j ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j))) := by
              rw [Category.assoc, ιFin_toBase]
          _ = Spec.map (CommRingCat.ofHom
                (((inclFin R F j).toRingHom).comp (algebraMap R ↥(chartAlgFin R F j)))) := by
              rw [CommRingCat.ofHom_comp, Spec.map_comp]
          _ = Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgMid R F j))) := by
              rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
      rw [e]
      exact haff _
    · have e : 𝒰.f (some WalkingPair.left) ≫ toBase R F j =
          Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j))) := ιFin_toBase R F j
      rw [e]
      exact haff _
    · have e : 𝒰.f (some WalkingPair.right) ≫ toBase R F j =
          Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgInf R F j))) := ιInf_toBase R F j
      rw [e]
      exact haff _
  exact AlgebraicGeometry.IsReduced.of_openCover _ 𝒱

end S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_charZero
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_charZero (solution)
