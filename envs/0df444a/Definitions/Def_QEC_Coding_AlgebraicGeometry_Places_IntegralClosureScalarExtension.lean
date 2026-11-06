-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureScalarExtension
-- name    : QEC_Coding_AlgebraicGeometry_Places_IntegralClosureScalarExtension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:46:11.2397+00:00
-- url     : https://prove2.me/theorems/01c11e7e-1c00-4fdb-af72-3388c61c6dfd
-- title:
--   Integral Closure Scalar Extension
-- statement:
--   Definitions and structural lemmas for Integral Closure Scalar Extension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralClosureScalarExtension.lean

import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
set_option autoImplicit false
namespace QEC.Coding.IntegralClosureScalarExtension
open scoped TensorProduct
noncomputable section
variable {k L B : Type*} [Field k] [Field L] [Algebra k L]
  [CommRing B] [Algebra k B] [Algebra.IsAlgebraic k L]
omit [Algebra.IsAlgebraic k L] in
lemma fieldTensorMap_inclusion_comp
    {E F : IntermediateField k L} (h : E ≤ F) (x : E ⊗[k] B) :
    Algebra.TensorProduct.map F.val (AlgHom.id k B)
      (Algebra.TensorProduct.map (IntermediateField.inclusion h) (AlgHom.id k B) x) =
    Algebra.TensorProduct.map E.val (AlgHom.id k B) x := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => rfl
lemma fieldTensorMap_val_injective (E : IntermediateField k L) :
    Function.Injective (Algebra.TensorProduct.map E.val (AlgHom.id k B)) := by
  change Function.Injective
    (TensorProduct.map E.val.toLinearMap (LinearMap.id : B →ₗ[k] B))
  exact TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Function.injective_id
lemma fieldTensor_exists_finite_intermediate (x : L ⊗[k] B) :
    ∃ E : IntermediateField k L, Module.Finite k E ∧
      ∃ y : E ⊗[k] B,
        Algebra.TensorProduct.map E.val (AlgHom.id k B) y = x := by
  classical
  obtain ⟨A, hA, y, hy⟩ := TensorProduct.Algebra.exists_of_fg x
  let : Algebra.IsAlgebraic k A :=
    Algebra.IsAlgebraic.of_injective A.val Subtype.val_injective
  let : Algebra.FiniteType k A := A.fg_iff_finiteType.mp hA
  let : Module.Finite k A := Algebra.IsIntegral.finite
  let E := Algebra.IsAlgebraic.toIntermediateField A
  have hE : Module.Finite k E := inferInstanceAs (Module.Finite k A)
  refine ⟨E, hE, y, ?_⟩
  exact hy
lemma fieldTensor_exists_finite_intermediate_many
    {ι : Type*} [Fintype ι] (f : ι → L ⊗[k] B) :
    ∃ E : IntermediateField k L, Module.Finite k E ∧ ∀ i : ι,
      ∃ y : E ⊗[k] B,
        Algebra.TensorProduct.map E.val (AlgHom.id k B) y = f i := by
  classical
  choose E hE y hy using fun i => fieldTensor_exists_finite_intermediate (f i)
  let : ∀ i, Module.Finite k (E i) := hE
  let F : IntermediateField k L := iSup E
  have hF : Module.Finite k F := inferInstance
  refine ⟨F, hF, fun i => ?_⟩
  let h : E i ≤ F := le_iSup E i
  refine ⟨Algebra.TensorProduct.map (IntermediateField.inclusion h) (AlgHom.id k B) (y i), ?_⟩
  rw [fieldTensorMap_inclusion_comp, hy]
lemma fieldTensor_polynomial_exists_finite_intermediate
    (p : Polynomial (L ⊗[k] B)) :
    ∃ E : IntermediateField k L, Module.Finite k E ∧
      ∃ q : Polynomial (E ⊗[k] B),
        q.map (Algebra.TensorProduct.map E.val (AlgHom.id k B)).toRingHom = p := by
  classical
  obtain ⟨E, hE, h⟩ := fieldTensor_exists_finite_intermediate_many
    (fun i : p.support => p.coeff i.val)
  choose y hy using h
  refine ⟨E, hE, ∑ i : p.support, Polynomial.monomial i.val (y i), ?_⟩
  have hcoeff (i : p.support) :
      (Algebra.TensorProduct.map E.val (AlgHom.id k B)).toRingHom (y i) = p.coeff i.val := hy i
  simp only [Polynomial.map_sum, Polynomial.map_monomial, hcoeff]
  exact (Finset.sum_coe_sort p.support (fun n => Polynomial.monomial n (p.coeff n))).trans
    (Polynomial.sum_monomial_eq p)
lemma fieldTensor_exists_joint_finite_intermediate
    {R : Type*} [CommRing R] [Algebra k R]
    (x : L ⊗[k] B) (p : Polynomial (L ⊗[k] R)) :
    ∃ E : IntermediateField k L, Module.Finite k E ∧
      ∃ y : E ⊗[k] B, ∃ q : Polynomial (E ⊗[k] R),
        Algebra.TensorProduct.map E.val (AlgHom.id k B) y = x ∧
        q.map (Algebra.TensorProduct.map E.val (AlgHom.id k R)).toRingHom = p := by
  classical
  obtain ⟨E₁, h₁, y, hy⟩ := fieldTensor_exists_finite_intermediate x
  obtain ⟨E₂, h₂, q, hq⟩ := fieldTensor_polynomial_exists_finite_intermediate p
  let : Module.Finite k E₁ := h₁
  let : Module.Finite k E₂ := h₂
  let E : IntermediateField k L := E₁ ⊔ E₂
  have hE : Module.Finite k E := inferInstance
  let j₁ : E₁ →ₐ[k] E := IntermediateField.inclusion le_sup_left
  let j₂ : E₂ →ₐ[k] E := IntermediateField.inclusion le_sup_right
  let ψ : E₂ ⊗[k] R →ₐ[k] E ⊗[k] R := Algebra.TensorProduct.map j₂ (AlgHom.id k R)
  let φ : E ⊗[k] R →ₐ[k] L ⊗[k] R := Algebra.TensorProduct.map E.val (AlgHom.id k R)
  refine ⟨E, hE, Algebra.TensorProduct.map j₁ (AlgHom.id k B) y,
    q.map ψ.toRingHom, ?_, ?_⟩
  · exact (fieldTensorMap_inclusion_comp le_sup_left y).trans hy
  · change (q.map ψ.toRingHom).map φ.toRingHom = p
    rw [Polynomial.map_map]
    have hφ : φ.toRingHom.comp ψ.toRingHom =
        (Algebra.TensorProduct.map E₂.val (AlgHom.id k R)).toRingHom := by
      apply RingHom.ext
      intro z
      exact fieldTensorMap_inclusion_comp (le_sup_right : E₂ ≤ E) z
    rw [hφ, hq]
lemma fieldTensor_integral_exists_finite_intermediate
    {R : Type*} [CommRing R] [Algebra k R] (f : R →ₐ[k] B)
    (x : L ⊗[k] B)
    (hx : (Algebra.TensorProduct.map (AlgHom.id k L) f).toRingHom.IsIntegralElem x) :
    ∃ E : IntermediateField k L, Module.Finite k E ∧
      ∃ y : E ⊗[k] B,
        (Algebra.TensorProduct.map (AlgHom.id k E) f).toRingHom.IsIntegralElem y ∧
        Algebra.TensorProduct.map E.val (AlgHom.id k B) y = x := by
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨E, hE, y, q, hy, hq⟩ := fieldTensor_exists_joint_finite_intermediate x p
  let φR : E ⊗[k] R →+* L ⊗[k] R :=
    (Algebra.TensorProduct.map E.val (AlgHom.id k R)).toRingHom
  let φB : E ⊗[k] B →+* L ⊗[k] B :=
    (Algebra.TensorProduct.map E.val (AlgHom.id k B)).toRingHom
  let fE : E ⊗[k] R →+* E ⊗[k] B :=
    (Algebra.TensorProduct.map (AlgHom.id k E) f).toRingHom
  let fL : L ⊗[k] R →+* L ⊗[k] B :=
    (Algebra.TensorProduct.map (AlgHom.id k L) f).toRingHom
  have hqMonic : q.Monic := Polynomial.monic_of_injective
    (fieldTensorMap_val_injective E) (hq.symm ▸ hp)
  have hnat : φB.comp fE = fL.comp φR := by
    apply RingHom.ext
    intro z
    induction z with
    | zero => simp
    | add z w hz hw => simp_all only [RingHom.comp_apply, map_add]
    | tmul a r => rfl
  refine ⟨E, hE, y, ⟨q, hqMonic, ?_⟩, hy⟩
  apply (fieldTensorMap_val_injective (B := B) E)
  change φB (q.eval₂ fE y) = φB 0
  rw [map_zero, Polynomial.hom_eval₂, hnat, ← Polynomial.eval₂_map, hq]
  have hyRing : φB y = x := hy
  change p.eval₂ fL (φB y) = 0
  rw [hyRing]
  exact hpx
omit [Algebra.IsAlgebraic k L] in
lemma finiteIntermediateField_etale (E : IntermediateField k L)
    [Module.Finite k E] [Algebra.IsSeparable k E] : Algebra.Etale k E := by
  let : Algebra.FormallyEtale k E := Algebra.FormallyEtale.of_isSeparable k E
  let : Algebra.FinitePresentation k E :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩
section FiniteRightBaseChange
attribute [local instance] Algebra.TensorProduct.rightAlgebra
omit [Algebra.IsAlgebraic k L] in
def fieldBaseChangeRightAlgEquiv (E : Type*) [CommRing E] [Algebra k E]
    (R : Type*) [CommRing R] [Algebra k R] :
    R ⊗[k] E ≃ₐ[R] E ⊗[k] R where
  toRingEquiv := (Algebra.TensorProduct.comm k R E).toRingEquiv
  commutes' r := by
    change Algebra.TensorProduct.comm k R E (r ⊗ₜ[k] (1 : E)) = (1 : E) ⊗ₜ[k] r
    rfl
omit [Algebra.IsAlgebraic k L] in
lemma finiteFieldRightBaseChange_smooth (E : IntermediateField k L)
    [Module.Finite k E] [Algebra.IsSeparable k E]
    (R : Type*) [CommRing R] [Algebra k R] : Algebra.Smooth R (E ⊗[k] R) := by
  let : Algebra.Etale k E := finiteIntermediateField_etale E
  let : Algebra.Smooth R (R ⊗[k] E) := inferInstance
  exact Algebra.Smooth.of_equiv (R := R) (A := R ⊗[k] E) (B := E ⊗[k] R)
    (fieldBaseChangeRightAlgEquiv E R)
local instance fieldNativeBaseAlgebra (E : IntermediateField k L) : Algebra k E :=
  E.toSubalgebra.algebra
local instance fieldRightBaseModule (E : Type*) [CommRing E] [Algebra k E]
    (R : Type*) [CommRing R] [Algebra k R] : Module R (E ⊗[k] R) :=
  @Algebra.toModule R (E ⊗[k] R) _ _
    (Algebra.TensorProduct.rightAlgebra (R := k) (A := E) (B := R))
omit [Algebra.IsAlgebraic k L] in
def fieldChartTensorCancelEquiv (E : Type*) [CommRing E] [Algebra k E]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B] :
    (E ⊗[k] R) ⊗[R] B ≃ₐ[k] E ⊗[k] B := by
  let e₁ : (E ⊗[k] R) ⊗[R] B ≃ₐ[k] (R ⊗[k] E) ⊗[R] B :=
    (Algebra.TensorProduct.congr (fieldBaseChangeRightAlgEquiv E R).symm
      (AlgEquiv.refl (R := R) (A₁ := B))).restrictScalars k
  let e₂ : (R ⊗[k] E) ⊗[R] B ≃ₐ[k] B ⊗[R] (R ⊗[k] E) :=
    (Algebra.TensorProduct.comm R (R ⊗[k] E) B).restrictScalars k
  let e₃ : B ⊗[R] (R ⊗[k] E) ≃ₐ[k] B ⊗[k] E :=
    (Algebra.TensorProduct.cancelBaseChange k R R B E).restrictScalars k
  let e₄ : B ⊗[k] E ≃ₐ[k] E ⊗[k] B := Algebra.TensorProduct.comm k B E
  exact e₁.trans (e₂.trans (e₃.trans e₄))
omit [Algebra.IsAlgebraic k L] in
lemma fieldChartTensorCancelEquiv_tmul (E : Type*) [CommRing E] [Algebra k E]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B]
    (a : E) (r : R) (b : B) :
    fieldChartTensorCancelEquiv E R ((a ⊗ₜ[k] r) ⊗ₜ[R] b) =
      a ⊗ₜ[k] ((algebraMap R B r) * b) := by
  simp [fieldChartTensorCancelEquiv, fieldBaseChangeRightAlgEquiv, Algebra.smul_def]
omit [Algebra.IsAlgebraic k L] in
def fieldChartTensorCancelBaseAlgEquiv (E : Type*) [CommRing E] [Algebra k E]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B] :
    let : Algebra (E ⊗[k] R) (E ⊗[k] B) :=
      (Algebra.TensorProduct.map (AlgHom.id k E) (IsScalarTower.toAlgHom k R B)).toAlgebra
    (E ⊗[k] R) ⊗[R] B ≃ₐ[E ⊗[k] R] E ⊗[k] B := by
  let : Algebra (E ⊗[k] R) (E ⊗[k] B) :=
    (Algebra.TensorProduct.map (AlgHom.id k E) (IsScalarTower.toAlgHom k R B)).toAlgebra
  refine { toRingEquiv := (fieldChartTensorCancelEquiv E R).toRingEquiv, commutes' := ?_ }
  intro s
  change fieldChartTensorCancelEquiv E R (algebraMap (E ⊗[k] R) ((E ⊗[k] R) ⊗[R] B) s) =
    algebraMap (E ⊗[k] R) (E ⊗[k] B) s
  induction s with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a r =>
    change fieldChartTensorCancelEquiv E R ((a ⊗ₜ[k] r) ⊗ₜ[R] (1 : B)) =
      a ⊗ₜ[k] (algebraMap R B r)
    rw [fieldChartTensorCancelEquiv_tmul, mul_one]
omit [Algebra.IsAlgebraic k L] in
lemma fieldChartTensorCancelIntegralClosure_naturality (E : Type*) [CommRing E] [Algebra k E]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B]
    (z : (E ⊗[k] R) ⊗[R] integralClosure R B) :
    fieldChartTensorCancelEquiv E R
      (Algebra.TensorProduct.map (AlgHom.id R (E ⊗[k] R)) (integralClosure R B).val z) =
    Algebra.TensorProduct.map (AlgHom.id k E)
      ((integralClosure R B).val.restrictScalars k)
      (fieldChartTensorCancelEquiv E R z) := by
  induction z with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul s c =>
    induction s with
    | zero => simp
    | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]
    | tmul a r =>
      simp [fieldChartTensorCancelEquiv_tmul]
omit [Algebra.IsAlgebraic k L] in
lemma finiteFieldTensorIntegralClosure_surjective (E : IntermediateField k L)
    [Module.Finite k E] [Algebra.IsSeparable k E]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B]
    (y : E ⊗[k] B)
    (hy : (Algebra.TensorProduct.map (AlgHom.id k E)
      (IsScalarTower.toAlgHom k R B)).toRingHom.IsIntegralElem y) :
    ∃ z : E ⊗[k] integralClosure R B,
      Algebra.TensorProduct.map (AlgHom.id k E)
        ((integralClosure R B).val.restrictScalars k) z = y := by
  let S := E ⊗[k] R
  let : Algebra S (E ⊗[k] B) :=
    (Algebra.TensorProduct.map (AlgHom.id k E) (IsScalarTower.toAlgHom k R B)).toAlgebra
  let : Algebra.Smooth R S := finiteFieldRightBaseChange_smooth E R
  let e : S ⊗[R] B ≃ₐ[S] E ⊗[k] B := fieldChartTensorCancelBaseAlgEquiv E R
  have hyI : IsIntegral S y := hy
  have hyI' : IsIntegral S (e.symm y) :=
    (isIntegral_algHom_iff (R := S) (A := E ⊗[k] B) (B := S ⊗[R] B)
      e.symm.toAlgHom e.symm.injective).mpr hyI
  let y' : integralClosure S (S ⊗[R] B) := ⟨e.symm y, hyI'⟩
  obtain ⟨z, hz⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := S) (B := B)).2 y'
  have hzEq : Algebra.TensorProduct.map (AlgHom.id R S) (integralClosure R B).val z =
      e.symm y := congrArg Subtype.val hz
  refine ⟨fieldChartTensorCancelEquiv E R z, ?_⟩
  rw [← fieldChartTensorCancelIntegralClosure_naturality, hzEq]
  exact e.apply_symm_apply y
omit [Algebra.IsAlgebraic k L] in
lemma fieldTensorIntegralClosure_inclusion_naturality (E : IntermediateField k L)
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B]
    (z : E ⊗[k] integralClosure R B) :
    Algebra.TensorProduct.map (AlgHom.id k L)
      ((integralClosure R B).val.restrictScalars k)
      (Algebra.TensorProduct.map E.val (AlgHom.id k (integralClosure R B)) z) =
    Algebra.TensorProduct.map E.val (AlgHom.id k B)
      (Algebra.TensorProduct.map (AlgHom.id k E)
        ((integralClosure R B).val.restrictScalars k) z) := by
  induction z with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a c => rfl
omit [Algebra.IsAlgebraic k L] in
lemma separableFieldTensorIntegralClosure_surjective [Algebra.IsSeparable k L]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B]
    (x : L ⊗[k] B)
    (hx : (Algebra.TensorProduct.map (AlgHom.id k L)
      (IsScalarTower.toAlgHom k R B)).toRingHom.IsIntegralElem x) :
    ∃ z : L ⊗[k] integralClosure R B,
      Algebra.TensorProduct.map (AlgHom.id k L)
        ((integralClosure R B).val.restrictScalars k) z = x := by
  obtain ⟨E, hE, y, hy, hxy⟩ := fieldTensor_integral_exists_finite_intermediate
    (IsScalarTower.toAlgHom k R B) x hx
  let : Module.Finite k E := hE
  obtain ⟨z, hz⟩ := finiteFieldTensorIntegralClosure_surjective E R y hy
  refine ⟨Algebra.TensorProduct.map E.val (AlgHom.id k (integralClosure R B)) z, ?_⟩
  rw [fieldTensorIntegralClosure_inclusion_naturality, hz, hxy]
omit [Algebra.IsAlgebraic k L] in
def fieldTensorIntegralClosureHom
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B] :
    let : Algebra (L ⊗[k] R) (L ⊗[k] B) :=
      (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k R B)).toAlgebra
    L ⊗[k] integralClosure R B →+* integralClosure (L ⊗[k] R) (L ⊗[k] B) :=
  let : Algebra (L ⊗[k] R) (L ⊗[k] B) :=
    (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k R B)).toAlgebra
  let e := fieldChartTensorCancelBaseAlgEquiv L R (B := B)
  e.mapIntegralClosure.toRingHom.comp
    ((TensorProduct.toIntegralClosure R (L ⊗[k] R) B).toRingHom.comp
      (fieldChartTensorCancelEquiv L R (B := integralClosure R B)).symm.toRingHom)
omit [Algebra.IsAlgebraic k L] in
lemma fieldTensorIntegralClosureHom_val
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B] :
    let : Algebra (L ⊗[k] R) (L ⊗[k] B) :=
      (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k R B)).toAlgebra
    ∀ z : L ⊗[k] integralClosure R B,
      (fieldTensorIntegralClosureHom (k := k) (L := L) R z).val =
        Algebra.TensorProduct.map (AlgHom.id k L)
          ((integralClosure R B).val.restrictScalars k) z := by
  let : Algebra (L ⊗[k] R) (L ⊗[k] B) :=
    (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k R B)).toAlgebra
  dsimp only
  intro z
  change fieldChartTensorCancelEquiv L R
    (Algebra.TensorProduct.map (AlgHom.id R (L ⊗[k] R)) (integralClosure R B).val
      ((fieldChartTensorCancelEquiv L R (B := integralClosure R B)).symm z)) = _
  rw [fieldChartTensorCancelIntegralClosure_naturality, AlgEquiv.apply_symm_apply]
omit [Algebra.IsAlgebraic k L] in
lemma fieldTensorIntegralClosureHom_bijective [Algebra.IsSeparable k L]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B] :
    Function.Bijective (fieldTensorIntegralClosureHom (k := k) (L := L) (B := B) R) := by
  let : Algebra (L ⊗[k] R) (L ⊗[k] B) :=
    (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k R B)).toAlgebra
  constructor
  · intro z w h
    have hm := congrArg Subtype.val h
    rw [fieldTensorIntegralClosureHom_val, fieldTensorIntegralClosureHom_val] at hm
    have hinj : Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id k L)
          ((integralClosure R B).val.restrictScalars k)) := by
      change Function.Injective
        (TensorProduct.map (LinearMap.id : L →ₗ[k] L)
          ((integralClosure R B).val.restrictScalars k).toLinearMap)
      exact TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id Subtype.val_injective
    exact hinj hm
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz⟩ := separableFieldTensorIntegralClosure_surjective R x hx
    refine ⟨z, Subtype.ext ?_⟩
    exact (fieldTensorIntegralClosureHom_val R z).trans hz
omit [Algebra.IsAlgebraic k L] in
noncomputable def separableFieldTensorIntegralClosureEquiv [Algebra.IsSeparable k L]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B] :
    let : Algebra (L ⊗[k] R) (L ⊗[k] B) :=
      (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k R B)).toAlgebra
    L ⊗[k] integralClosure R B ≃+* integralClosure (L ⊗[k] R) (L ⊗[k] B) :=
  RingEquiv.ofBijective (fieldTensorIntegralClosureHom R)
    (fieldTensorIntegralClosureHom_bijective R)
namespace BaseRing
variable {K F B0 : Type*} [CommRing K] [CommRing F] [Algebra K F]
  [CommRing B0] [Algebra K B0]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
def fieldBaseChangeRightAlgEquiv (E : Type*) [CommRing E] [Algebra K E]
    (R : Type*) [CommRing R] [Algebra K R] :
    R ⊗[K] E ≃ₐ[R] E ⊗[K] R where
  toRingEquiv := (Algebra.TensorProduct.comm K R E).toRingEquiv
  commutes' r := by
    change Algebra.TensorProduct.comm K R E (r ⊗ₜ[K] (1 : E)) = (1 : E) ⊗ₜ[K] r
    rfl
local instance fieldRightBaseModule (E : Type*) [CommRing E] [Algebra K E]
    (R : Type*) [CommRing R] [Algebra K R] : Module R (E ⊗[K] R) :=
  @Algebra.toModule R (E ⊗[K] R) _ _
    (Algebra.TensorProduct.rightAlgebra (R := K) (A := E) (B := R))
def fieldChartTensorCancelEquiv (E : Type*) [CommRing E] [Algebra K E]
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0] :
    (E ⊗[K] R) ⊗[R] B0 ≃ₐ[K] E ⊗[K] B0 := by
  let e₁ : (E ⊗[K] R) ⊗[R] B0 ≃ₐ[K] (R ⊗[K] E) ⊗[R] B0 :=
    (Algebra.TensorProduct.congr (fieldBaseChangeRightAlgEquiv (K := K) E R).symm
      (AlgEquiv.refl (R := R) (A₁ := B0))).restrictScalars K
  let e₂ : (R ⊗[K] E) ⊗[R] B0 ≃ₐ[K] B0 ⊗[R] (R ⊗[K] E) :=
    (Algebra.TensorProduct.comm R (R ⊗[K] E) B0).restrictScalars K
  let e₃ : B0 ⊗[R] (R ⊗[K] E) ≃ₐ[K] B0 ⊗[K] E :=
    (Algebra.TensorProduct.cancelBaseChange K R R B0 E).restrictScalars K
  let e₄ : B0 ⊗[K] E ≃ₐ[K] E ⊗[K] B0 := Algebra.TensorProduct.comm K B0 E
  exact e₁.trans (e₂.trans (e₃.trans e₄))
lemma fieldChartTensorCancelEquiv_tmul (E : Type*) [CommRing E] [Algebra K E]
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0]
    (a : E) (r : R) (b : B0) :
    fieldChartTensorCancelEquiv (K := K) E R ((a ⊗ₜ[K] r) ⊗ₜ[R] b) =
      a ⊗ₜ[K] ((algebraMap R B0 r) * b) := by
  simp [fieldChartTensorCancelEquiv, fieldBaseChangeRightAlgEquiv, Algebra.smul_def]
def fieldChartTensorCancelBaseAlgEquiv (E : Type*) [CommRing E] [Algebra K E]
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0] :
    let : Algebra (E ⊗[K] R) (E ⊗[K] B0) :=
      (Algebra.TensorProduct.map (AlgHom.id K E) (IsScalarTower.toAlgHom K R B0)).toAlgebra
    (E ⊗[K] R) ⊗[R] B0 ≃ₐ[E ⊗[K] R] E ⊗[K] B0 := by
  let : Algebra (E ⊗[K] R) (E ⊗[K] B0) :=
    (Algebra.TensorProduct.map (AlgHom.id K E) (IsScalarTower.toAlgHom K R B0)).toAlgebra
  refine { toRingEquiv := (fieldChartTensorCancelEquiv (K := K) E R).toRingEquiv, commutes' := ?_ }
  intro s
  change fieldChartTensorCancelEquiv (K := K) E R (algebraMap (E ⊗[K] R) ((E ⊗[K] R) ⊗[R] B0) s) =
    algebraMap (E ⊗[K] R) (E ⊗[K] B0) s
  induction s with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a r =>
    change fieldChartTensorCancelEquiv (K := K) E R ((a ⊗ₜ[K] r) ⊗ₜ[R] (1 : B0)) =
      a ⊗ₜ[K] (algebraMap R B0 r)
    rw [fieldChartTensorCancelEquiv_tmul, mul_one]
def fieldTensorIntegralClosureHom
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0] :
    let : Algebra (F ⊗[K] R) (F ⊗[K] B0) :=
      (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K R B0)).toAlgebra
    F ⊗[K] integralClosure R B0 →+* integralClosure (F ⊗[K] R) (F ⊗[K] B0) :=
  let : Algebra (F ⊗[K] R) (F ⊗[K] B0) :=
    (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K R B0)).toAlgebra
  let e := fieldChartTensorCancelBaseAlgEquiv (K := K) F R (B0 := B0)
  e.mapIntegralClosure.toRingHom.comp
    ((TensorProduct.toIntegralClosure R (F ⊗[K] R) B0).toRingHom.comp
      (fieldChartTensorCancelEquiv (K := K) F R (B0 := integralClosure R B0)).symm.toRingHom)
omit [Algebra K F] in
lemma integralElem_transport_iff
    {A C : Type*} [CommRing A] [CommRing C]
    (f : K →+* A) (g : F →+* C) (e : K ≃+* F) (u : A ≃+* C)
    (hcomp : u.toRingHom.comp f = g.comp e.toRingHom) (x : A) :
    f.IsIntegralElem x ↔ g.IsIntegralElem (u x) := by
  have hinv : u.symm.toRingHom.comp g = f.comp e.symm.toRingHom := by
    apply RingHom.ext
    intro t
    have h := congrArg u.symm
      (congrArg (fun v : K →+* C => v (e.symm t)) hcomp)
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply] using h.symm
  constructor
  · intro hx
    have h := hx.map u.toRingHom
    rw [hcomp] at h
    exact h.of_comp
  · intro hx
    have h := hx.map u.symm.toRingHom
    rw [hinv] at h
    have h' : f.IsIntegralElem (u.symm (u x)) := h.of_comp
    simpa only [RingEquiv.symm_apply_apply] using h'
omit [Algebra K F] in
def integralClosureTransportEquiv
    {A C : Type*} [CommRing A] [CommRing C] [Algebra K A] [Algebra F C]
    (e : K ≃+* F) (u : A ≃+* C)
    (hcomp : u.toRingHom.comp (algebraMap K A) = (algebraMap F C).comp e.toRingHom) :
    integralClosure K A ≃+* integralClosure F C where
  toFun x := ⟨u x.val, (integralElem_transport_iff (algebraMap K A) (algebraMap F C)
    e u hcomp x.val).mp x.property⟩
  invFun y := ⟨u.symm y.val, (integralElem_transport_iff (algebraMap K A) (algebraMap F C)
    e u hcomp (u.symm y.val)).mpr (by simpa only [RingEquiv.apply_symm_apply] using (show (algebraMap F C).IsIntegralElem y.val from y.property))⟩
  left_inv x := Subtype.ext (u.symm_apply_apply x.val)
  right_inv y := Subtype.ext (u.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (u.map_mul x.val y.val)
  map_add' x y := Subtype.ext (u.map_add x.val y.val)
lemma toIntegralClosure_bijective_of_baseEquiv
    {T : Type*} [CommRing T] [Algebra K T] (e : F ≃ₐ[K] T)
    (h : Function.Bijective (TensorProduct.toIntegralClosure K F B0)) :
    Function.Bijective (TensorProduct.toIntegralClosure K T B0) := by
  let u : F ⊗[K] B0 ≃ₐ[K] T ⊗[K] B0 :=
    Algebra.TensorProduct.congr e (AlgEquiv.refl (R := K) (A₁ := B0))
  let v : F ⊗[K] integralClosure K B0 ≃ₐ[K] T ⊗[K] integralClosure K B0 :=
    Algebra.TensorProduct.congr e (AlgEquiv.refl (R := K) (A₁ := integralClosure K B0))
  have hcomp : u.toRingHom.comp (algebraMap F (F ⊗[K] B0)) =
      (algebraMap T (T ⊗[K] B0)).comp e.toRingHom := by
    apply RingHom.ext
    intro f
    change u (f ⊗ₜ[K] (1 : B0)) = (e f) ⊗ₜ[K] (1 : B0)
    rfl
  let w : integralClosure F (F ⊗[K] B0) ≃+* integralClosure T (T ⊗[K] B0) :=
    integralClosureTransportEquiv e.toRingEquiv u.toRingEquiv hcomp
  have hsquare : w.toRingHom.comp (TensorProduct.toIntegralClosure K F B0).toRingHom =
      (TensorProduct.toIntegralClosure K T B0).toRingHom.comp v.toRingHom := by
    apply RingHom.ext
    intro z
    apply Subtype.ext
    change u (Algebra.TensorProduct.map (AlgHom.id K F) (integralClosure K B0).val z) =
      Algebra.TensorProduct.map (AlgHom.id K T) (integralClosure K B0).val (v z)
    induction z with
    | zero => simp
    | add z q hz hq => simp only [map_add, hz, hq]
    | tmul f b => rfl
  have hb : Function.Bijective ((TensorProduct.toIntegralClosure K T B0).toRingHom.comp v.toRingHom) := by
    rw [← hsquare]
    exact w.bijective.comp h
  exact (Function.Bijective.of_comp_iff _ v.bijective).mp hb
lemma fieldTensorIntegralClosureHom_bijective_iff
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0] :
    Function.Bijective (fieldTensorIntegralClosureHom (K := K) (F := F) (B0 := B0) R) ↔
      Function.Bijective (TensorProduct.toIntegralClosure R (F ⊗[K] R) B0) := by
  let : Algebra (F ⊗[K] R) (F ⊗[K] B0) :=
    (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K R B0)).toAlgebra
  let e := fieldChartTensorCancelBaseAlgEquiv (K := K) F R (B0 := B0)
  let c := fieldChartTensorCancelEquiv (K := K) F R (B0 := integralClosure R B0)
  change Function.Bijective (e.mapIntegralClosure ∘
    (TensorProduct.toIntegralClosure R (F ⊗[K] R) B0) ∘ c.symm) ↔ _
  exact (Function.Bijective.of_comp_iff' e.mapIntegralClosure.bijective _).trans
    (Function.Bijective.of_comp_iff _ c.symm.bijective)
lemma mvPolynomialBase_toIntegralClosure_bijective {σ : Type*}
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0] :
    Function.Bijective (TensorProduct.toIntegralClosure R ((MvPolynomial σ K) ⊗[K] R) B0) := by
  let e : (MvPolynomial σ K) ⊗[K] R ≃ₐ[R] MvPolynomial σ R :=
    (fieldBaseChangeRightAlgEquiv (K := K) (MvPolynomial σ K) R).symm.trans
      (MvPolynomial.algebraTensorAlgEquiv K R)
  exact toIntegralClosure_bijective_of_baseEquiv e.symm
    (TensorProduct.toIntegralClosure_mvPolynomial_bijective (R := R) (B := B0))
lemma fractionMvPolynomialBase_toIntegralClosure_bijective {σ : Type*}
    (R : Type*) [CommRing R] [Algebra K R] [Algebra R B0] [IsScalarTower K R B0] :
    Function.Bijective (TensorProduct.toIntegralClosure R
      ((FractionRing (MvPolynomial σ K)) ⊗[K] R) B0) := by
  let P := MvPolynomial σ K
  let F' := FractionRing P
  let S₁ := P ⊗[K] R
  let S₂ := F' ⊗[K] R
  let g : S₁ →ₐ[P] S₂ :=
    Algebra.TensorProduct.map (Algebra.ofId P F') (AlgHom.id K R)
  let : Algebra S₁ S₂ := g.toAlgebra
  let : IsScalarTower P S₁ S₂ := .of_algebraMap_eq' g.comp_algebraMap.symm
  let : IsScalarTower R S₁ S₂ := .of_algebraMap_eq fun r => by
    change (1 : F') ⊗ₜ[K] r =
      Algebra.TensorProduct.map (Algebra.ofId P F') (AlgHom.id K R) ((1 : P) ⊗ₜ[K] r)
    simp
  let : IsLocalization (Algebra.algebraMapSubmonoid S₁ (nonZeroDivisors P)) S₂ :=
    IsLocalization.tensorProduct_tensorProduct K R (nonZeroDivisors P) F' (by
      ext r
      change g ((1 : P) ⊗ₜ[K] r) = (1 : F') ⊗ₜ[K] r
      change (Algebra.ofId P F') (1 : P) ⊗ₜ[K] (AlgHom.id K R) r = (1 : F') ⊗ₜ[K] r
      rw [map_one]
      rfl)
  exact TensorProduct.toIntegralClosure_bijective_of_tower
    (R := R) (S := S₁) (T := S₂) (B := B0)
    (mvPolynomialBase_toIntegralClosure_bijective (K := K) (σ := σ) (B0 := B0) R)
    (TensorProduct.toIntegralClosure_bijective_of_isLocalization
      (Algebra.algebraMapSubmonoid S₁ (nonZeroDivisors P)))
def rightTensorBaseCongrAlgEquiv
    {T : Type*} [CommRing T] [Algebra K T] (e : F ≃ₐ[K] T)
    (R : Type*) [CommRing R] [Algebra K R] : F ⊗[K] R ≃ₐ[R] T ⊗[K] R where
  toRingEquiv := (Algebra.TensorProduct.congr e (AlgEquiv.refl (R := K) (A₁ := R))).toRingEquiv
  commutes' r := by
    change (e (1 : F)) ⊗ₜ[K] r = (1 : T) ⊗ₜ[K] r
    rw [map_one]
def towerTensorCancelBaseAlgEquiv
    {T : Type*} [CommRing T] [Algebra K T] [Algebra F T] [IsScalarTower K F T]
    (R : Type*) [CommRing R] [Algebra K R] :
    let : Algebra (F ⊗[K] R) (T ⊗[K] R) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K F T) (AlgHom.id K R)).toAlgebra
    T ⊗[F] (F ⊗[K] R) ≃ₐ[F ⊗[K] R] T ⊗[K] R := by
  let : Algebra (F ⊗[K] R) (T ⊗[K] R) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K F T) (AlgHom.id K R)).toAlgebra
  let c := Algebra.TensorProduct.cancelBaseChange K F T T R
  refine { toRingEquiv := c.toRingEquiv, commutes' := ?_ }
  intro s
  change c ((1 : T) ⊗ₜ[F] s) =
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K F T) (AlgHom.id K R) s
  induction s with
  | zero => simp
  | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]
  | tmul f r =>
    change c ((1 : T) ⊗ₜ[F] (f ⊗ₜ[K] r)) = (algebraMap F T f) ⊗ₜ[K] r
    simp only [c, Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
end BaseRing
omit [Algebra.IsAlgebraic k L] in
lemma separableField_toIntegralClosure_bijective [Algebra.IsSeparable k L]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B] :
    Function.Bijective (TensorProduct.toIntegralClosure R (L ⊗[k] R) B) := by
  apply (BaseRing.fieldTensorIntegralClosureHom_bijective_iff
    (K := k) (F := L) (B0 := B) R).mp
  exact fieldTensorIntegralClosureHom_bijective R
omit [Algebra.IsAlgebraic k L] in
lemma charZeroField_toIntegralClosure_bijective [CharZero k]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B] :
    Function.Bijective (TensorProduct.toIntegralClosure R (L ⊗[k] R) B) := by
  classical
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis k L
  let x : t → L := Subtype.val
  let E := IntermediateField.adjoin k (Set.range x)
  let : Algebra.IsAlgebraic E L := ht.isAlgebraic_field
  let : CharZero E := inferInstance
  let : Algebra.IsSeparable E L := inferInstance
  let S₁ := E ⊗[k] R
  let S₂ := L ⊗[k] R
  let g : S₁ →ₐ[k] S₂ := Algebra.TensorProduct.map E.val (AlgHom.id k R)
  let : Algebra S₁ S₂ := g.toAlgebra
  let : IsScalarTower R S₁ S₂ := .of_algebraMap_eq fun r => by
    change (1 : L) ⊗ₜ[k] r = E.val (1 : E) ⊗ₜ[k] r
    rw [map_one]
  let a : FractionRing (MvPolynomial t k) ≃ₐ[k] E := ht.1.aevalEquivField
  let b : (FractionRing (MvPolynomial t k)) ⊗[k] R ≃ₐ[R] S₁ :=
    BaseRing.rightTensorBaseCongrAlgEquiv a R
  have h₁ : Function.Bijective (TensorProduct.toIntegralClosure R S₁ B) :=
    BaseRing.toIntegralClosure_bijective_of_baseEquiv b
      (BaseRing.fractionMvPolynomialBase_toIntegralClosure_bijective
        (K := k) (σ := t) (B0 := B) R)
  let c : L ⊗[E] S₁ ≃ₐ[S₁] S₂ :=
    BaseRing.towerTensorCancelBaseAlgEquiv (K := k) (F := E) (T := L) R
  have h₂ : Function.Bijective (TensorProduct.toIntegralClosure S₁ S₂ (S₁ ⊗[R] B)) :=
    BaseRing.toIntegralClosure_bijective_of_baseEquiv c
      (separableField_toIntegralClosure_bijective (k := E) (L := L) (B := S₁ ⊗[R] B) S₁)
  exact TensorProduct.toIntegralClosure_bijective_of_tower h₁ h₂
omit [Algebra.IsAlgebraic k L] in
lemma charZeroFieldTensorIntegralClosureHom_bijective [CharZero k]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B] :
    Function.Bijective (fieldTensorIntegralClosureHom (k := k) (L := L) (B := B) R) := by
  exact (BaseRing.fieldTensorIntegralClosureHom_bijective_iff
    (K := k) (F := L) (B0 := B) R).mpr (charZeroField_toIntegralClosure_bijective R)
omit [Algebra.IsAlgebraic k L] in
noncomputable def charZeroFieldTensorIntegralClosureEquiv [CharZero k]
    (R : Type*) [CommRing R] [Algebra k R] [Algebra R B] [IsScalarTower k R B] :
    let : Algebra (L ⊗[k] R) (L ⊗[k] B) :=
      (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k R B)).toAlgebra
    L ⊗[k] integralClosure R B ≃+* integralClosure (L ⊗[k] R) (L ⊗[k] B) :=
  RingEquiv.ofBijective (fieldTensorIntegralClosureHom R)
    (charZeroFieldTensorIntegralClosureHom_bijective R)
end FiniteRightBaseChange
end
end QEC.Coding.IntegralClosureScalarExtension


