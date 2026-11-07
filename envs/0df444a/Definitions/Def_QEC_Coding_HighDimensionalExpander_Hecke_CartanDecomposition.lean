-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
-- name    : QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:40:12.692679+00:00
-- url     : https://prove2.me/theorems/c42fd861-4415-4dc0-b681-414fdd6ee5c2
-- title:
--   Cartan Decomposition
-- statement:
--   Definitions and structural lemmas for Cartan Decomposition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/CartanDecomposition.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
def integralClearingExponent
    {k : Type u} [Field k] (f : LocalFunctionField k) : ℕ :=
  Int.toNat (-f.order)
theorem integralClearingExponent_spec
    {k : Type u} [Field k] (f : LocalFunctionField k) :
    (uniformizerUnit k : LocalFunctionField k) ^ integralClearingExponent f * f ∈
      Valued.integer (LocalFunctionField k) := by
  rw [Valuation.mem_integer_iff]
  apply (LaurentSeries.val_le_one_iff_eq_coe k _).2
  by_cases h : f.order ≤ 0
  · refine ⟨f.powerSeriesPart, ?_⟩
    rw [LaurentSeries.ofPowerSeries_powerSeriesPart]
    simp only [integralClearingExponent, Int.toNat_of_nonneg (neg_nonneg.mpr h),
      coe_uniformizerUnit, HahnSeries.single_pow, one_pow, nsmul_eq_mul,
      mul_one]
  · have hpos : 0 ≤ f.order := le_of_lt (lt_of_not_ge h)
    refine ⟨PowerSeries.X ^ Int.natAbs f.order * f.powerSeriesPart, ?_⟩
    rw [integralClearingExponent,
      Int.toNat_eq_zero.mpr (neg_nonpos.mpr hpos), pow_zero, one_mul]
    exact LaurentSeries.X_order_mul_powerSeriesPart
      (Int.natAbs_of_nonneg hpos)
theorem uniformizer_pow_mem_integer
    {k : Type u} [Field k] (n : ℕ) :
    (uniformizerUnit k : LocalFunctionField k) ^ n ∈
      Valued.integer (LocalFunctionField k) := by
  rw [Valuation.mem_integer_iff]
  apply (LaurentSeries.val_le_one_iff_eq_coe k _).2
  exact ⟨PowerSeries.X ^ n, by simp [coe_uniformizerUnit]⟩
theorem scaled_mem_integer_of_clearingExponent_le
    {k : Type u} [Field k] (f : LocalFunctionField k) {n : ℕ}
    (h : integralClearingExponent f ≤ n) :
    (uniformizerUnit k : LocalFunctionField k) ^ n * f ∈
      Valued.integer (LocalFunctionField k) := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_assoc]
  exact (Valued.integer (LocalFunctionField k)).mul_mem
    (uniformizer_pow_mem_integer (n - integralClearingExponent f))
    (integralClearingExponent_spec f)
def matrixClearingExponent
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) : ℕ :=
  Finset.univ.sup fun i =>
    Finset.univ.sup fun j => integralClearingExponent (A i j)
theorem integralClearingExponent_le_matrixClearingExponent
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) (i j : Fin d) :
    integralClearingExponent (A i j) ≤ matrixClearingExponent A := by
  apply le_trans (Finset.le_sup (f := fun j : Fin d =>
    integralClearingExponent (A i j)) (Finset.mem_univ j))
  exact Finset.le_sup (f := fun i : Fin d => Finset.univ.sup fun j =>
    integralClearingExponent (A i j)) (Finset.mem_univ i)
theorem matrix_scaled_entry_mem_integer
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) (i j : Fin d) :
    (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A * A i j ∈
      Valued.integer (LocalFunctionField k) :=
  scaled_mem_integer_of_clearingExponent_le (A i j)
    (integralClearingExponent_le_matrixClearingExponent A i j)
def clearedMatrix
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) :
    Matrix (Fin d) (Fin d) (Valued.integer (LocalFunctionField k)) :=
  fun i j =>
    ⟨(uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A * A i j,
      matrix_scaled_entry_mem_integer A i j⟩
@[simp]
theorem coe_clearedMatrix_apply
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) (i j : Fin d) :
    ((clearedMatrix A i j : Valued.integer (LocalFunctionField k)) :
      LocalFunctionField k) =
      (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A * A i j :=
  rfl
def clearedPowerSeriesEntry
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) (i j : Fin d) :
    IntegerRing k :=
  (LocalTopology.powerSeriesIntegerEquiv k).symm
    (clearedMatrix (k := k) (d := d) A i j)
theorem coe_clearedPowerSeriesEntry
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) (i j : Fin d) :
    (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A * A i j =
      HahnSeries.ofPowerSeries Int k
        (clearedPowerSeriesEntry (k := k) (d := d) A i j) :=
  (congrArg Subtype.val
    ((LocalTopology.powerSeriesIntegerEquiv k).apply_symm_apply
      (clearedMatrix (k := k) (d := d) A i j))).symm
def clearedPowerSeriesMatrix
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) :
    Matrix (Fin d) (Fin d) (IntegerRing k) :=
  fun i j => clearedPowerSeriesEntry (k := k) (d := d) A i j
theorem map_clearedPowerSeriesMatrix
    {k : Type u} [Field k] {d : ℕ}
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) :
    (HahnSeries.ofPowerSeries Int k).mapMatrix
        (clearedPowerSeriesMatrix (k := k) (d := d) A) =
      (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A • A := by
  apply Matrix.ext
  intro i j
  change HahnSeries.ofPowerSeries Int k
      (clearedPowerSeriesEntry (k := k) (d := d) A i j) =
    (uniformizerUnit k : LocalFunctionField k) ^ matrixClearingExponent A * A i j
  exact (coe_clearedPowerSeriesEntry (k := k) (d := d) A i j).symm
theorem clearedPowerSeriesMatrix_det_ne_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (clearedPowerSeriesMatrix (k := k) (d := d)
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).det ≠ 0 := by
  intro hdet
  have hmap := congrArg (HahnSeries.ofPowerSeries Int k) hdet
  rw [map_zero, RingHom.map_det, map_clearedPowerSeriesMatrix, Matrix.det_smul] at hmap
  have hu : (uniformizerUnit k : LocalFunctionField k) ≠ 0 := Units.ne_zero _
  have hupow :
      ((uniformizerUnit k : LocalFunctionField k) ^
        matrixClearingExponent
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) ^
            Fintype.card (Fin d) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ hu)
  exact (mul_ne_zero hupow A.det_ne_zero) hmap
theorem clearedPowerSeriesMatrix_mulVec_injective
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    ∀ x y : Fin d → IntegerRing k,
      Matrix.mulVec
          (clearedPowerSeriesMatrix (k := k) (d := d)
            (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) x =
        Matrix.mulVec
          (clearedPowerSeriesMatrix (k := k) (d := d)
            (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) y →
      x = y := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero
    (clearedPowerSeriesMatrix_det_ne_zero (k := k) (d := d) A)
  rw [Matrix.mulVec_sub, hxy, sub_self]
theorem clearedPowerSeriesMatrix_range_finrank
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Module.finrank (IntegerRing k)
        (LinearMap.range
          (clearedPowerSeriesMatrix (k := k) (d := d)
            (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin) =
      Module.finrank (IntegerRing k) (Fin d → IntegerRing k) :=
  LinearMap.finrank_range_of_inj
    (clearedPowerSeriesMatrix_mulVec_injective (k := k) (d := d) A)
def clearedImage
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Submodule (IntegerRing k) (Fin d → IntegerRing k) :=
  LinearMap.range
    (clearedPowerSeriesMatrix (k := k) (d := d)
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin
theorem clearedImage_finrank
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Module.finrank (IntegerRing k) (clearedImage (k := k) (d := d) A) =
      Module.finrank (IntegerRing k) (Fin d → IntegerRing k) := by
  exact clearedPowerSeriesMatrix_range_finrank (k := k) (d := d) A
def clearedImageEquiv
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    (Fin d → IntegerRing k) ≃ₗ[IntegerRing k]
      clearedImage (k := k) (d := d) A :=
  LinearEquiv.ofInjective
    (clearedPowerSeriesMatrix (k := k) (d := d)
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin
    (clearedPowerSeriesMatrix_mulVec_injective (k := k) (d := d) A)
def smithAmbientBasis
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Basis (Fin d) (IntegerRing k) (Fin d → IntegerRing k) :=
  (clearedImage (k := k) (d := d) A).smithNormalFormTopBasis
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A)
def smithImageBasis
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Basis (Fin d) (IntegerRing k) (clearedImage (k := k) (d := d) A) :=
  (clearedImage (k := k) (d := d) A).smithNormalFormBotBasis
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A)
def smithDiagonalCoeff
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : Fin d → IntegerRing k :=
  (clearedImage (k := k) (d := d) A).smithNormalFormCoeffs
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A)
theorem smithDiagonalCoeff_ne_zero
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) (i : Fin d) :
    smithDiagonalCoeff (k := k) (d := d) A i ≠ 0 :=
  (clearedImage (k := k) (d := d) A).smithNormalFormCoeffs_ne_zero
    (Pi.basisFun (IntegerRing k) (Fin d))
    (clearedImage_finrank (k := k) (d := d) A) i
def smithDomainBasis
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Basis (Fin d) (IntegerRing k) (Fin d → IntegerRing k) :=
  (smithImageBasis (k := k) (d := d) A).map
    (clearedImageEquiv (k := k) (d := d) A).symm
def basisChangeGeneralLinear
    {R : Type u} [CommRing R] {d : ℕ}
    (b : Basis (Fin d) R (Fin d → R)) : GL (Fin d) R where
  val := (Pi.basisFun R (Fin d)).toMatrix b
  inv := b.toMatrix (Pi.basisFun R (Fin d))
  val_inv := Basis.toMatrix_mul_toMatrix_flip _ _
  inv_val := Basis.toMatrix_mul_toMatrix_flip _ _
def smithAmbientGeneralLinear
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : GL (Fin d) (IntegerRing k) :=
  basisChangeGeneralLinear (smithAmbientBasis (k := k) (d := d) A)
def smithDomainGeneralLinear
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : GL (Fin d) (IntegerRing k) :=
  basisChangeGeneralLinear (smithDomainBasis (k := k) (d := d) A)
def smithExponent
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) (i : Fin d) : ℕ :=
  Classical.choose
    (IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (smithDiagonalCoeff_ne_zero (k := k) (d := d) A i)
      (PowerSeries.X_irreducible (R := k)))
def smithCoeffUnit
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) (i : Fin d) : (IntegerRing k)ˣ :=
  Classical.choose
    (Classical.choose_spec
      (IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (smithDiagonalCoeff_ne_zero (k := k) (d := d) A i)
        (PowerSeries.X_irreducible (R := k))))
def smithUnitGeneralLinear
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : GL (Fin d) (IntegerRing k) :=
  diagonalGeneralLinear (IntegerRing k) d
    (smithCoeffUnit (k := k) (d := d) A)
def smithPowerDiagonal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Matrix (Fin d) (Fin d) (IntegerRing k) :=
  Matrix.diagonal fun i => PowerSeries.X ^ smithExponent (k := k) (d := d) A i
def smithLeftGeneralLinear
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : GL (Fin d) (IntegerRing k) :=
  smithAmbientGeneralLinear (k := k) (d := d) A *
    smithUnitGeneralLinear (k := k) (d := d) A
def smithPowerGeneralLinearLocal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    GL (Fin d) (LocalFunctionField k) :=
  diagonalGeneralLinear (LocalFunctionField k) d fun i =>
    uniformizerUnit k ^ smithExponent (k := k) (d := d) A i
def smithLeftGeneralLinearLocal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    GL (Fin d) (LocalFunctionField k) :=
  powerSeriesGeneralLinearToLocal k d
    (smithLeftGeneralLinear (k := k) (d := d) A)
def smithRightGeneralLinearLocal
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    GL (Fin d) (LocalFunctionField k) :=
  powerSeriesGeneralLinearToLocal k d
    (smithDomainGeneralLinear (k := k) (d := d) A)
def matrixClearingScalarUnit
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    Units (LocalFunctionField k) :=
  uniformizerUnit k ^ matrixClearingExponent
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))
def powerSeriesGeneralLinearToInteger
    (k : Type u) [Field k] (d : ℕ) :
    GL (Fin d) (IntegerRing k) →*
      GL (Fin d) (Valued.integer (LocalFunctionField k)) :=
  Matrix.GeneralLinearGroup.map
    (LocalTopology.powerSeriesIntegerEquiv k).toRingHom
def smithPowerCoweight
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    PGL(Fin d, LocalFunctionField k) :=
  Matrix.ProjGenLinGroup.mk
    (smithPowerGeneralLinearLocal (k := k) (d := d) A)
def diagonalGeneralLinearHom (R : Type u) [CommRing R] (d : ℕ) :
    (Fin d → Units R) →* GL (Fin d) R :=
  (Units.map (Matrix.diagonalRingHom (Fin d) R).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom
@[simp]
theorem diagonalGeneralLinearHom_apply
    (R : Type u) [CommRing R] (d : ℕ) (v : Fin d → Units R) :
    diagonalGeneralLinearHom R d v = diagonalGeneralLinear R d v :=
  rfl
def coordinateUniformizerUnits
    (k : Type u) [Field k] (d : ℕ) (i : Fin d) :
    Fin d → Units (LocalFunctionField k) :=
  fun j => if j = i then uniformizerUnit k else 1
def coordinateUniformizerGeneralLinear
    (k : Type u) [Field k] (d : ℕ) (i : Fin d) :
    GL (Fin d) (LocalFunctionField k) :=
  diagonalGeneralLinear (LocalFunctionField k) d
    (coordinateUniformizerUnits k d i)
def coordinateUniformizerCoweight
    (k : Type u) [Field k] (d : ℕ) (i : Fin d) :
    PGL(Fin d, LocalFunctionField k) :=
  Matrix.ProjGenLinGroup.mk (coordinateUniformizerGeneralLinear k d i)
def permutationGeneralLinear
    (R : Type u) [CommRing R] {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    GL (Fin d) R where
  val := σ.permMatrix R
  inv := σ⁻¹.permMatrix R
  val_inv := by
    rw [← Matrix.permMatrix_mul]
    simp
  inv_val := by
    rw [← Matrix.permMatrix_mul]
    simp
@[simp]
theorem permutationGeneralLinear_apply
    (R : Type u) [CommRing R] {d : ℕ} (σ : Equiv.Perm (Fin d))
    (i j : Fin d) :
    permutationGeneralLinear R σ i j = σ.permMatrix R i j :=
  rfl
def permutationCoweight
    (k : Type u) [Field k] {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    PGL(Fin d, LocalFunctionField k) :=
  Matrix.ProjGenLinGroup.mk
    (permutationGeneralLinear (LocalFunctionField k) σ)
def contragredientGeneralLinearHom
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] :
    GL n R →* GL n R where
  toFun A :=
    { val := Matrix.transpose (((A⁻¹ : GL n R) : Matrix n n R))
      inv := Matrix.transpose ((A : GL n R) : Matrix n n R)
      val_inv := by
        rw [← Matrix.transpose_mul]
        simp
      inv_val := by
        rw [← Matrix.transpose_mul]
        simp }
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun₂ (Matrix.transpose_one (n := n) (α := R)) i j
  map_mul' A B := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change Matrix.transpose
      ((((A * B)⁻¹ : GL n R) : Matrix n n R)) i j = _
    rw [mul_inv_rev]
    exact congrFun₂ (Matrix.transpose_mul
      (((B⁻¹ : GL n R) : Matrix n n R))
      (((A⁻¹ : GL n R) : Matrix n n R))) i j
theorem contragredientGeneralLinear_involutive
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : GL n R) :
    contragredientGeneralLinearHom
        (contragredientGeneralLinearHom A) = A := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change Matrix.transpose (Matrix.transpose ((A : Matrix n n R))) i j = _
  rfl
theorem contragredientGeneralLinear_mem_center
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {A : GL n R} (hA : A ∈ Subgroup.center (GL n R)) :
    contragredientGeneralLinearHom A ∈ Subgroup.center (GL n R) := by
  rw [Subgroup.mem_center_iff] at hA ⊢
  intro B
  have h := congrArg contragredientGeneralLinearHom
    (hA (contragredientGeneralLinearHom B))
  simpa only [map_mul, contragredientGeneralLinear_involutive] using h
def projectiveContragredientHom
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] :
    PGL(n, R) →* PGL(n, R) :=
  Matrix.ProjGenLinGroup.lift
    (Matrix.ProjGenLinGroup.mk.comp
      (contragredientGeneralLinearHom (R := R) (n := n))) (by
      ext u
      apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
      apply contragredientGeneralLinear_mem_center
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩)
theorem projectiveContragredient_involutive
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (g : PGL(n, R)) :
    projectiveContragredientHom (projectiveContragredientHom g) = g := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk A => simp [projectiveContragredientHom,
      contragredientGeneralLinear_involutive]
def projectiveContragredientEquiv
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] :
    PGL(n, R) ≃* PGL(n, R) where
  toFun := projectiveContragredientHom
  invFun := projectiveContragredientHom
  left_inv := projectiveContragredient_involutive
  right_inv := projectiveContragredient_involutive
  map_mul' := map_mul projectiveContragredientHom
theorem continuous_contragredientGeneralLinear
    {k : Type u} [Field k] {d : ℕ} :
    Continuous (contragredientGeneralLinearHom
      (R := LocalFunctionField k) (n := Fin d)) := by
  apply Units.continuous_iff.2
  exact ⟨(Units.continuous_val.comp continuous_inv).matrix_transpose,
    Units.continuous_val.matrix_transpose⟩
theorem continuous_projectiveContragredient
    {k : Type u} [Field k] {d : ℕ} :
    Continuous (projectiveContragredientHom :
      PGL(Fin d, LocalFunctionField k) →
        PGL(Fin d, LocalFunctionField k)) := by
  apply (QuotientGroup.isQuotientMap_mk
    (Subgroup.center (GL (Fin d) (LocalFunctionField k)))).continuous_iff.mpr
  change Continuous (fun A : GL (Fin d) (LocalFunctionField k) ↦
    projectiveContragredientHom (Matrix.ProjGenLinGroup.mk A))
  exact QuotientGroup.continuous_mk.comp
    (continuous_contragredientGeneralLinear (k := k) (d := d))
def projectiveTranspose
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (g : PGL(n, R)) : PGL(n, R) :=
  projectiveContragredientHom g⁻¹
theorem projectiveTranspose_involutive
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (g : PGL(n, R)) : projectiveTranspose (projectiveTranspose g) = g := by
  simp [projectiveTranspose, projectiveContragredient_involutive]
def projectiveTransposeEquiv
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] :
    PGL(n, R) ≃ PGL(n, R) where
  toFun := projectiveTranspose
  invFun := projectiveTranspose
  left_inv := projectiveTranspose_involutive
  right_inv := projectiveTranspose_involutive
theorem continuous_projectiveTranspose
    {k : Type u} [Field k] {d : ℕ} :
    Continuous (projectiveTranspose :
      PGL(Fin d, LocalFunctionField k) →
        PGL(Fin d, LocalFunctionField k)) :=
  continuous_projectiveContragredient.comp continuous_inv
def projectiveTransposeMeasurableEquiv
    {k : Type u} [Field k] {d : ℕ} :
    PGL(Fin d, LocalFunctionField k) ≃ᵐ
      PGL(Fin d, LocalFunctionField k) where
  toEquiv := projectiveTransposeEquiv
  measurable_toFun := continuous_projectiveTranspose.measurable
  measurable_invFun := continuous_projectiveTranspose.measurable
structure DominantCoweight (d : ℕ) where
  exponent : Fin d → ℕ
  antitone_exponent : Antitone exponent
@[ext]
theorem DominantCoweight.ext {d : ℕ} {a b : DominantCoweight d}
    (h : a.exponent = b.exponent) : a = b := by
  cases a
  cases b
  cases h
  rfl
instance (d : ℕ) : Countable (DominantCoweight d) :=
  (show Function.Injective DominantCoweight.exponent from
    fun _ _ h => DominantCoweight.ext h).countable
structure ProjectiveDominantCoweight (n : ℕ) where
  toDominant : DominantCoweight (n + 1)
  last_exponent_eq_zero : toDominant.exponent (Fin.last n) = 0
@[ext]
theorem ProjectiveDominantCoweight.ext {n : ℕ}
    {a b : ProjectiveDominantCoweight n}
    (h : a.toDominant.exponent = b.toDominant.exponent) : a = b := by
  cases a
  cases b
  cases DominantCoweight.ext h
  rfl
instance (n : ℕ) : Countable (ProjectiveDominantCoweight n) :=
  (show Function.Injective
      (fun weight : ProjectiveDominantCoweight n ↦
        weight.toDominant.exponent) from
    fun _ _ h ↦ ProjectiveDominantCoweight.ext h).countable
def normalizeDominantCoweight {n : ℕ}
    (weight : DominantCoweight (n + 1)) : ProjectiveDominantCoweight n where
  toDominant :=
    { exponent := fun i ↦
        weight.exponent i - weight.exponent (Fin.last n)
      antitone_exponent := by
        intro i j hij
        exact Nat.sub_le_sub_right (weight.antitone_exponent hij) _ }
  last_exponent_eq_zero := Nat.sub_self _
@[simp]
theorem normalizeDominantCoweight_exponent {n : ℕ}
    (weight : DominantCoweight (n + 1)) (i : Fin (n + 1)) :
    (normalizeDominantCoweight weight).toDominant.exponent i =
      weight.exponent i - weight.exponent (Fin.last n) :=
  rfl
def MatrixOrderLowerBound {k : Type u} [Field k] {d : ℕ} (m : WithTop ℤ)
    (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) : Prop :=
  ∀ i j, m ≤ (A i j).orderTop
def localUnitOrder {k : Type u} [Field k]
    (c : Units (LocalFunctionField k)) : ℤ :=
  (c : LocalFunctionField k).order
theorem orderTop_coe_localUnit
    {k : Type u} [Field k] (c : Units (LocalFunctionField k)) :
    (c : LocalFunctionField k).orderTop =
      (localUnitOrder c : WithTop ℤ) := by
  exact (HahnSeries.order_eq_orderTop_of_ne_zero c.ne_zero).symm
@[simp]
theorem orderTop_uniformizerUnit_pow
    {k : Type u} [Field k] (m : ℕ) :
    ((uniformizerUnit k ^ m : Units (LocalFunctionField k)) :
      LocalFunctionField k).orderTop = (m : WithTop ℤ) := by
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero (by simp)]
  simp [coe_uniformizerUnit]
@[simp]
theorem localUnitOrder_uniformizerUnit_pow
    {k : Type u} [Field k] (m : ℕ) :
    localUnitOrder (uniformizerUnit k ^ m) = (m : ℤ) := by
  have h := orderTop_uniformizerUnit_pow (k := k) m
  rw [orderTop_coe_localUnit] at h
  exact WithTop.coe_eq_coe.mp h
theorem localUnitOrder_inv
    {k : Type u} [Field k] (c : Units (LocalFunctionField k)) :
    localUnitOrder c⁻¹ = -localUnitOrder c := by
  have hmul := HahnSeries.order_mul c.ne_zero c⁻¹.ne_zero
  have hprod :
      (c : LocalFunctionField k) * (c⁻¹ : Units (LocalFunctionField k)) = 1 := by
    simp
  rw [hprod, HahnSeries.order_one] at hmul
  apply eq_neg_of_add_eq_zero_left
  simpa [localUnitOrder, add_comm] using hmul.symm
theorem orderTop_coe_localUnit_inv
    {k : Type u} [Field k] (c : Units (LocalFunctionField k)) :
    ((c⁻¹ : Units (LocalFunctionField k)) :
      LocalFunctionField k).orderTop =
      ((-localUnitOrder c : ℤ) : WithTop ℤ) := by
  rw [orderTop_coe_localUnit, localUnitOrder_inv]
def dominantSortPermutation {d : ℕ} (n : Fin d → ℕ) :
    Equiv.Perm (Fin d) :=
  Tuple.sort (OrderDual.toDual ∘ n)
def dominantSort {d : ℕ} (n : Fin d → ℕ) : Fin d → ℕ :=
  n ∘ dominantSortPermutation n
theorem dominantSort_antitone {d : ℕ} (n : Fin d → ℕ) :
    Antitone (dominantSort n) := by
  intro i j hij
  exact Tuple.monotone_sort (OrderDual.toDual ∘ n) hij
def smithDominantCoweight
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) : DominantCoweight d where
  exponent := dominantSort (smithExponent (k := k) (d := d) A)
  antitone_exponent := dominantSort_antitone _
def dominantGeneralLinear
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    GL (Fin d) (LocalFunctionField k) :=
  diagonalGeneralLinear (LocalFunctionField k) d fun i =>
    uniformizerUnit k ^ weight.exponent i
def dominantCoweight
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    PGL(Fin d, LocalFunctionField k) :=
  Matrix.ProjGenLinGroup.mk (dominantGeneralLinear k weight)
def dominantDoubleCoset
    (k : Type u) [Field k] {d : ℕ} (weight : DominantCoweight d) :
    Set PGL(Fin d, LocalFunctionField k) :=
  (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) *
    ({dominantCoweight k weight} : Set PGL(Fin d, LocalFunctionField k)) *
    (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k))
def projectiveDominantDoubleCoset
    (k : Type u) [Field k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    Set PGL(Fin (n + 1), LocalFunctionField k) :=
  dominantDoubleCoset k weight.toDominant
@[simp]
theorem orderTop_uniformizerUnit_pow_inv
    {k : Type u} [Field k] (m : ℕ) :
    (((uniformizerUnit k ^ m)⁻¹ : Units (LocalFunctionField k)) :
      LocalFunctionField k).orderTop =
      ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
  rw [orderTop_coe_localUnit_inv]
  have h := orderTop_uniformizerUnit_pow (k := k) m
  rw [orderTop_coe_localUnit] at h
  have hInt : localUnitOrder (uniformizerUnit k ^ m) = (m : ℤ) :=
    WithTop.coe_eq_coe.mp h
  rw [hInt]
def fundamentalDominantCoweight (d r : ℕ) : DominantCoweight d where
  exponent i := if i.val < r then 1 else 0
  antitone_exponent := by
    intro i j hij
    by_cases hj : j.val < r
    · have hi : i.val < r := lt_of_le_of_lt (Fin.mk_le_mk.mp hij) hj
      simp [hi, hj]
    · simp [hj]
def fundamentalProjectiveDominantCoweight
    (n r : ℕ) (hr : r ≤ n) : ProjectiveDominantCoweight n where
  toDominant := fundamentalDominantCoweight (n + 1) r
  last_exponent_eq_zero := by
    simp [fundamentalDominantCoweight, hr]
@[simp]
theorem diagonalGeneralLinear_inv
    (R : Type u) [CommRing R] (d : ℕ) (v : Fin d → Units R) :
    (diagonalGeneralLinear R d v)⁻¹ =
      diagonalGeneralLinear R d (fun i => (v i)⁻¹) := by
  change (diagonalGeneralLinearHom R d v)⁻¹ =
    diagonalGeneralLinearHom R d (fun i => (v i)⁻¹)
  rw [← map_inv]
  rfl
def rankFourWedgeFirst : Fin 6 → Fin 4 :=
  ![0, 0, 0, 1, 1, 2]
def rankFourWedgeSecond : Fin 6 → Fin 4 :=
  ![1, 2, 3, 2, 3, 3]
def rankFourSecondCompound
    {R : Type u} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 6) (Fin 6) R :=
  fun p q ↦
    A (rankFourWedgeFirst p) (rankFourWedgeFirst q) *
        A (rankFourWedgeSecond p) (rankFourWedgeSecond q) -
      A (rankFourWedgeFirst p) (rankFourWedgeSecond q) *
        A (rankFourWedgeSecond p) (rankFourWedgeFirst q)
@[simp]
theorem rankFourSecondCompound_one
    {R : Type u} [CommRing R] :
    rankFourSecondCompound (1 : Matrix (Fin 4) (Fin 4) R) = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [rankFourSecondCompound, rankFourWedgeFirst,
      rankFourWedgeSecond, Matrix.one_apply]
theorem rankFourSecondCompound_mul
    {R : Type u} [CommRing R]
    (A B : Matrix (Fin 4) (Fin 4) R) :
    rankFourSecondCompound (A * B) =
      rankFourSecondCompound A * rankFourSecondCompound B := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [rankFourSecondCompound, rankFourWedgeFirst,
      rankFourWedgeSecond, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring
def rankFourSecondCompoundGeneralLinear
    {R : Type u} [CommRing R] (A : GL (Fin 4) R) : GL (Fin 6) R where
  val := rankFourSecondCompound A
  inv := rankFourSecondCompound
    (((A⁻¹ : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R))
  val_inv := by
    rw [← rankFourSecondCompound_mul]
    simp
  inv_val := by
    rw [← rankFourSecondCompound_mul]
    simp
end QEC.Coding.HighDimensionalExpander.SphericalHecke


