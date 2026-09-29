-- Prove2me | solution 1 for AutomorphicForm.exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/179f9dc5-76ed-5f12-a850-2e34fc7de9e2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
import Theorems.Thm_NumberField_distribHaarChar_idelicNorm_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.preimage_mulLeft_smul ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open scoped TensorProduct
open Polynomial Matrix NumberField

namespace R3M4Torus

section Alg

variable {K : Type*} [Field K] (γ₀ : Matrix (Fin 2) (Fin 2) K)

theorem irreducible_charpoly (h : ∀ a : K, ¬ γ₀.charpoly.IsRoot a) : Irreducible γ₀.charpoly := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ h
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  decide

theorem entry01_ne_zero (h : ∀ a : K, ¬ γ₀.charpoly.IsRoot a) : γ₀ 0 1 ≠ 0 := by
  intro h0
  apply h (γ₀ 0 0)
  rw [Matrix.charpoly_fin_two, Polynomial.IsRoot, Matrix.trace_fin_two, Matrix.det_fin_two, h0]
  simp; ring

variable [Fact (Irreducible γ₀.charpoly)]

abbrev E : Type _ := AdjoinRoot γ₀.charpoly

noncomputable def ι₀ : E γ₀ →ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  Ideal.Quotient.liftₐ (Ideal.span {γ₀.charpoly}) (Polynomial.aeval γ₀) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, Matrix.aeval_self_charpoly, mul_zero])

theorem ι₀_mk (p : K[X]) : ι₀ γ₀ (AdjoinRoot.mk γ₀.charpoly p) = Polynomial.aeval γ₀ p := rfl

theorem ι₀_root : ι₀ γ₀ (AdjoinRoot.root γ₀.charpoly) = γ₀ := by
  rw [AdjoinRoot.root, ι₀_mk, Polynomial.aeval_X]

theorem ι₀_of (a : K) : ι₀ γ₀ (AdjoinRoot.of γ₀.charpoly a) = algebraMap K _ a := by
  rw [← AdjoinRoot.algebraMap_eq, AlgHom.commutes]

variable (A : Type*) [CommRing A] [Algebra K A]

noncomputable def ιA : A ⊗[K] E γ₀ →ₐ[A] Matrix (Fin 2) (Fin 2) A :=
  Algebra.TensorProduct.lift (Algebra.ofId A _)
    ((AlgHom.mapMatrix (Algebra.ofId K A)).comp (ι₀ γ₀))
    (fun a _ => Algebra.commute_algebraMap_left a _)

theorem ιA_tmul (a : A) (e : E γ₀) :
    ιA γ₀ A (a ⊗ₜ[K] e) = a • (ι₀ γ₀ e).map (algebraMap K A) := by
  rw [ιA, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]
  rfl

abbrev γA : Matrix (Fin 2) (Fin 2) A := γ₀.map (algebraMap K A)

theorem ιA_one_tmul_root : ιA γ₀ A (1 ⊗ₜ[K] AdjoinRoot.root γ₀.charpoly) = γA γ₀ A := by
  rw [ιA_tmul, ι₀_root, one_smul]

omit [Fact (Irreducible γ₀.charpoly)] in
theorem natDegree_charpoly : γ₀.charpoly.natDegree = 2 := by
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

noncomputable def bE : Module.Basis (Fin 2) K (E γ₀) :=
  ((AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible γ₀.charpoly))).basis.reindex
      (finCongr (by rw [AdjoinRoot.powerBasis_dim, natDegree_charpoly])))

theorem bE_apply (i : Fin 2) : bE γ₀ i = AdjoinRoot.root γ₀.charpoly ^ (i : ℕ) := by
  rw [bE, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
  simp only [finCongr_symm, finCongr_apply, Fin.val_cast]

theorem bE_zero : bE γ₀ 0 = 1 := by rw [bE_apply]; simp

theorem bE_one : bE γ₀ 1 = AdjoinRoot.root γ₀.charpoly := by rw [bE_apply]; simp

noncomputable def bA : Module.Basis (Fin 2) A (A ⊗[K] E γ₀) :=
  Algebra.TensorProduct.basis A (bE γ₀)

theorem bA_apply (i : Fin 2) : bA γ₀ A i = 1 ⊗ₜ[K] bE γ₀ i :=
  Algebra.TensorProduct.basis_apply (bE γ₀) i

theorem bA_zero : bA γ₀ A 0 = 1 := by
  rw [bA_apply, bE_zero]; rfl

theorem bA_one : bA γ₀ A 1 = 1 ⊗ₜ[K] AdjoinRoot.root γ₀.charpoly := by
  rw [bA_apply, bE_one]

theorem eq_smul_one_add_smul_root (z : A ⊗[K] E γ₀) :
    z = (bA γ₀ A).repr z 0 • (1 : A ⊗[K] E γ₀) +
      (bA γ₀ A).repr z 1 • ((1 : A) ⊗ₜ[K] AdjoinRoot.root γ₀.charpoly) := by
  conv_lhs => rw [← (bA γ₀ A).sum_repr z]
  rw [Fin.sum_univ_two, bA_zero, bA_one]

theorem ιA_smul_one_add_smul_root (c₀ c₁ : A) :
    ιA γ₀ A (c₀ • (1 : A ⊗[K] E γ₀) + c₁ • ((1 : A) ⊗ₜ[K] AdjoinRoot.root γ₀.charpoly)) =
      c₀ • (1 : Matrix (Fin 2) (Fin 2) A) + c₁ • γA γ₀ A := by
  rw [map_add, map_smul, map_smul, map_one, ιA_one_tmul_root]

theorem ιA_eq (z : A ⊗[K] E γ₀) :
    ιA γ₀ A z = (bA γ₀ A).repr z 0 • (1 : Matrix (Fin 2) (Fin 2) A) +
      (bA γ₀ A).repr z 1 • γA γ₀ A := by
  conv_lhs => rw [eq_smul_one_add_smul_root γ₀ A z]
  exact ιA_smul_one_add_smul_root γ₀ A _ _

variable (hq : γ₀ 0 1 ≠ 0)
include hq

theorem ιA_injective : Function.Injective (ιA γ₀ A) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  rw [ιA_eq] at hz
  have h01 := congrFun (congrFun hz 0) 1
  have h00 := congrFun (congrFun hz 0) 0
  simp at h01 h00
  have hqA : IsUnit (algebraMap K A (γ₀ 0 1)) := (hq.isUnit).map _
  have h1 : (bA γ₀ A).repr z 1 = 0 := by
    rw [mul_comm] at h01
    exact hqA.mul_right_eq_zero.mp h01
  rw [h1] at h00
  simp at h00
  rw [eq_smul_one_add_smul_root γ₀ A z, h00, h1, zero_smul, zero_smul, add_zero]

omit [Fact (Irreducible γ₀.charpoly)] in

theorem exists_of_commute (X : Matrix (Fin 2) (Fin 2) A) (hX : Commute X (γA γ₀ A)) :
    ∃ α β : A, X = α • (1 : Matrix (Fin 2) (Fin 2) A) + β • γA γ₀ A := by
  have hqA : IsUnit (algebraMap K A (γ₀ 0 1)) := (hq.isUnit).map _
  obtain ⟨qi, hqi⟩ := hqA.exists_left_inv
  set p := algebraMap K A (γ₀ 0 0)
  set q := algebraMap K A (γ₀ 0 1)
  set r := algebraMap K A (γ₀ 1 0)
  set s := algebraMap K A (γ₀ 1 1)
  have hγ : γA γ₀ A = !![p, q; r, s] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hc := hX.eq
  rw [hγ] at hc
  have hXe : X = !![X 0 0, X 0 1; X 1 0, X 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hXe] at hc
  simp only [Matrix.cons_mul, Matrix.vecMul_cons, Matrix.smul_cons, smul_eq_mul,
    Matrix.smul_empty, Matrix.empty_vecMul, add_zero, Matrix.empty_mul, Matrix.cons_add_cons,
    Matrix.empty_add_empty] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp at e00 e01 e10 e11
  refine ⟨X 0 0 - X 0 1 * qi * p, X 0 1 * qi, ?_⟩
  have h10 : X 1 0 = X 0 1 * qi * r := by
    have : q * X 1 0 = X 0 1 * r := by linear_combination e00.symm
    calc X 1 0 = qi * q * X 1 0 := by rw [hqi, one_mul]
      _ = qi * (X 0 1 * r) := by rw [mul_assoc, this]
      _ = X 0 1 * qi * r := by ring
  have h11 : X 1 1 = (X 0 0 - X 0 1 * qi * p) + X 0 1 * qi * s := by
    have : q * X 1 1 = X 0 0 * q + X 0 1 * s - p * X 0 1 := by linear_combination e01.symm
    calc X 1 1 = qi * q * X 1 1 := by rw [hqi, one_mul]
      _ = qi * (X 0 0 * q + X 0 1 * s - p * X 0 1) := by rw [mul_assoc, this]
      _ = X 0 0 * (qi * q) + X 0 1 * qi * s - X 0 1 * qi * p := by ring
      _ = _ := by rw [hqi]; ring
  have h01 : X 0 1 = X 0 1 * qi * q := by rw [mul_assoc, hqi, mul_one]
  rw [hγ, hXe]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simpa [Matrix.one_apply] using h01
  · simpa [Matrix.one_apply] using h10
  · simpa [Matrix.one_apply] using h11

theorem mem_range_ιA_iff (X : Matrix (Fin 2) (Fin 2) A) :
    X ∈ Set.range (ιA γ₀ A) ↔ Commute X (γA γ₀ A) := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [ιA_eq]
    exact ((Commute.one_left _).smul_left _).add_left ((Commute.refl _).smul_left _)
  · intro hX
    obtain ⟨α, β, rfl⟩ := exists_of_commute γ₀ A hq X hX
    exact ⟨α • 1 + β • (1 ⊗ₜ AdjoinRoot.root γ₀.charpoly), ιA_smul_one_add_smul_root γ₀ A α β⟩

end Alg

end R3M4Torus

namespace R3M4Torus

section UnitsLayer

variable {K : Type*} [Field K] (γ₀ : Matrix (Fin 2) (Fin 2) K) [Fact (Irreducible γ₀.charpoly)]
  (A : Type*) [CommRing A] [Algebra K A]

noncomputable def ΦA : (A ⊗[K] E γ₀)ˣ →* GL (Fin 2) A := Units.map (ιA γ₀ A : A ⊗[K] E γ₀ →* _)

theorem ΦA_val (x : (A ⊗[K] E γ₀)ˣ) : ((ΦA γ₀ A x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
    ιA γ₀ A (x : A ⊗[K] E γ₀) := rfl

variable (hq : γ₀ 0 1 ≠ 0)
include hq

theorem ΦA_injective : Function.Injective (ΦA γ₀ A) := fun _ _ h =>
  Units.ext (ιA_injective γ₀ A hq (congrArg (fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A)) h))

theorem mem_range_ΦA_iff (t : GL (Fin 2) A) :
    t ∈ Set.range (ΦA γ₀ A) ↔ Commute (t : Matrix (Fin 2) (Fin 2) A) (γA γ₀ A) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (mem_range_ιA_iff γ₀ A hq _).1 ⟨_, rfl⟩
  · intro ht
    have ht' : Commute ((t⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) (γA γ₀ A) :=
      ht.units_inv_left
    obtain ⟨a, ha⟩ := (mem_range_ιA_iff γ₀ A hq _).2 ht
    obtain ⟨b, hb⟩ := (mem_range_ιA_iff γ₀ A hq _).2 ht'
    have hab : a * b = 1 := ιA_injective γ₀ A hq (by
      rw [map_mul, ha, hb, map_one]; exact Units.mul_inv t |>.symm ▸ (by simp))
    have hba : b * a = 1 := by rw [mul_comm]; exact hab
    refine ⟨⟨a, b, hab, hba⟩, Units.ext ?_⟩
    rw [ΦA_val]; exact ha

end UnitsLayer

section Rational

variable {K : Type*} [Field K] (γ₀ : Matrix (Fin 2) (Fin 2) K) [Fact (Irreducible γ₀.charpoly)]

theorem ι₀_injective : Function.Injective (ι₀ γ₀) := (ι₀ γ₀).toRingHom.injective

omit [Fact (Irreducible γ₀.charpoly)] in
theorem γA_self : γA γ₀ K = γ₀ := by
  ext i j; simp [γA]

theorem ιA_self_tmul (a : K) (e : E γ₀) : ιA γ₀ K (a ⊗ₜ[K] e) = a • ι₀ γ₀ e := by
  rw [ιA_tmul]; congr 1

variable (hq : γ₀ 0 1 ≠ 0)
include hq

theorem exists_eq_ι₀_of_commute (X : Matrix (Fin 2) (Fin 2) K) (hX : Commute X γ₀) :
    ∃ e : E γ₀, X = ι₀ γ₀ e := by
  have hX' : Commute X (γA γ₀ K) := by rwa [γA_self]
  obtain ⟨α, β, rfl⟩ := exists_of_commute γ₀ K hq X hX'
  refine ⟨algebraMap K _ α + algebraMap K _ β * AdjoinRoot.root γ₀.charpoly, ?_⟩
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, ι₀_root, γA_self,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem exists_units_eq_of_commute (g : GL (Fin 2) K)
    (hg : Commute (g : Matrix (Fin 2) (Fin 2) K) γ₀) :
    ∃ e : (E γ₀)ˣ, Units.map (ι₀ γ₀ : E γ₀ →* Matrix (Fin 2) (Fin 2) K) e = g := by
  obtain ⟨a, ha⟩ := exists_eq_ι₀_of_commute γ₀ hq _ hg
  have hg' : Commute ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) γ₀ := hg.units_inv_left
  obtain ⟨b, hb⟩ := exists_eq_ι₀_of_commute γ₀ hq _ hg'
  have hab : a * b = 1 := ι₀_injective γ₀ (by
    rw [map_mul, ← ha, ← hb, map_one]; simp)
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  exact ⟨⟨a, b, hab, hba⟩, Units.ext ha.symm⟩

end Rational

section Norm

variable {K : Type*} [Field K] (γ₀ : Matrix (Fin 2) (Fin 2) K) [Fact (Irreducible γ₀.charpoly)]
  (A : Type*) [CommRing A] [Algebra K A]

theorem root_sq : AdjoinRoot.root γ₀.charpoly ^ 2 =
    algebraMap K _ γ₀.trace * AdjoinRoot.root γ₀.charpoly - algebraMap K _ γ₀.det := by
  have h := congrArg (Polynomial.aeval (AdjoinRoot.root γ₀.charpoly)) (Matrix.charpoly_fin_two γ₀)
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self] at h
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C] at h
  linear_combination -h

theorem oneTmulRoot_sq : ((1 : A) ⊗ₜ[K] AdjoinRoot.root γ₀.charpoly) ^ 2 =
    algebraMap K A γ₀.trace • ((1 : A) ⊗ₜ[K] AdjoinRoot.root γ₀.charpoly) -
      algebraMap K A γ₀.det • (1 : A ⊗[K] E γ₀) := by
  rw [sq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← sq, root_sq, TensorProduct.tmul_sub,
    algebraMap_smul, algebraMap_smul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  rfl

theorem norm_eq_det (z : A ⊗[K] E γ₀) : Algebra.norm A z = (ιA γ₀ A z).det := by
  classical
  set c₀ := (bA γ₀ A).repr z 0
  set c₁ := (bA γ₀ A).repr z 1
  have hz := eq_smul_one_add_smul_root γ₀ A z
  rw [Algebra.norm_eq_matrix_det (bA γ₀ A) z, Matrix.det_fin_two, ιA_eq, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, bA_zero, bA_one, mul_one]

  have hzr : z * ((1 : A) ⊗ₜ[K] AdjoinRoot.root γ₀.charpoly) =
      (-(c₁ * algebraMap K A γ₀.det)) • (bA γ₀ A 0) +
        (c₀ + c₁ * algebraMap K A γ₀.trace) • (bA γ₀ A 1) := by
    rw [bA_zero, bA_one]
    conv_lhs => rw [hz]
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, ← sq, oneTmulRoot_sq, smul_sub,
      smul_smul, smul_smul, add_smul, neg_smul]
    abel
  have hr0 : (bA γ₀ A).repr (z * ((1 : A) ⊗ₜ[K] AdjoinRoot.root γ₀.charpoly)) 0 =
      -(c₁ * algebraMap K A γ₀.det) := by
    rw [hzr, map_add, map_smul, map_smul, (bA γ₀ A).repr_self, (bA γ₀ A).repr_self]
    simp
  have hr1 : (bA γ₀ A).repr (z * ((1 : A) ⊗ₜ[K] AdjoinRoot.root γ₀.charpoly)) 1 =
      c₀ + c₁ * algebraMap K A γ₀.trace := by
    rw [hzr, map_add, map_smul, map_smul, (bA γ₀ A).repr_self, (bA γ₀ A).repr_self]
    simp
  rw [hr0, hr1, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [γA]
  ring

end Norm

end R3M4Torus

namespace R3M4Torus

section Adelic

open M4aHerbrand M4aHerbrand.Bridge M4aHerbrand.GenuineDescent AutomorphicForm IsDedekindDomain
open Topology

variable (K : Type) [Field K] [NumberField K] (γ₀ : Matrix (Fin 2) (Fin 2) K)
  [Fact (Irreducible γ₀.charpoly)]

omit [NumberField K] in
theorem finrank_E : Module.finrank K (E γ₀) = 2 := by
  rw [(AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible γ₀.charpoly))).finrank,
    AdjoinRoot.powerBasis_dim, natDegree_charpoly]

scoped instance finiteDimensional_E : FiniteDimensional K (E γ₀) :=
  (AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible γ₀.charpoly))).finite

scoped instance isQuadraticExtension_E : Algebra.IsQuadraticExtension K (E γ₀) :=
  ⟨finrank_E K γ₀⟩

scoped instance numberField_E : NumberField (E γ₀) := NumberField.of_module_finite K (E γ₀)

scoped instance isGalois_E : IsGalois K (E γ₀) := inferInstance

local notation "𝔸K" => AdeleRing (𝓞 K) K
local notation "𝔸E" => AdeleRing (𝓞 (E γ₀)) (E γ₀)

@[reducible] noncomputable def instAlgAE :
    Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 (E γ₀)) (E γ₀)) :=
  (genuineβ K (E γ₀)).toAlgebra

attribute [local instance] instAlgAE

noncomputable def te : (𝔸K ⊗[K] E γ₀) ≃ₐ[𝔸K] 𝔸E := genuineTensorEquiv K (E γ₀)

theorem te_one_tmul (e : E γ₀) : te K γ₀ ((1 : 𝔸K) ⊗ₜ[K] e) = algebraMap (E γ₀) (𝔸E) e :=
  genuineTensorEquiv_one_tmul K (E γ₀) e

theorem isModuleTopology_AE : IsModuleTopology (𝔸K) (𝔸E) :=
  isModuleTopology_adeleRing_of_free (𝓞 K) K (𝓞 (E γ₀)) (E γ₀) (continuous_genuineβ K (E γ₀))
    (te K γ₀)

noncomputable def Ψ : (𝔸E) →ₐ[𝔸K] Matrix (Fin 2) (Fin 2) (𝔸K) :=
  (ιA γ₀ (𝔸K)).comp ((te K γ₀).symm : (𝔸E) →ₐ[𝔸K] 𝔸K ⊗[K] E γ₀)

theorem Ψ_apply (y : 𝔸E) : Ψ K γ₀ y = ιA γ₀ (𝔸K) ((te K γ₀).symm y) := rfl

noncomputable def Φ : (𝔸E)ˣ →* GL (Fin 2) (𝔸K) := Units.map (Ψ K γ₀ : (𝔸E) →* _)

theorem Φ_val (x : (𝔸E)ˣ) :
    ((Φ K γ₀ x : GL (Fin 2) (𝔸K)) : Matrix (Fin 2) (Fin 2) (𝔸K)) = Ψ K γ₀ (x : 𝔸E) := rfl

theorem Φ_eq_ΦA (x : (𝔸E)ˣ) :
    Φ K γ₀ x = ΦA γ₀ (𝔸K) (Units.map ((te K γ₀).symm : (𝔸E) →* 𝔸K ⊗[K] E γ₀) x) :=
  Units.ext rfl

variable (hq : γ₀ 0 1 ≠ 0)
include hq in
theorem Φ_injective : Function.Injective (Φ K γ₀) := by
  intro x y h
  rw [Φ_eq_ΦA, Φ_eq_ΦA] at h
  have := ΦA_injective γ₀ (𝔸K) hq h
  have h2 : Function.Injective (Units.map ((te K γ₀).symm : (𝔸E) →* 𝔸K ⊗[K] E γ₀)) := by
    intro a b hab
    exact Units.ext ((te K γ₀).symm.injective (congrArg (fun u : (𝔸K ⊗[K] E γ₀)ˣ => (u : 𝔸K ⊗[K] E γ₀)) hab))
  exact h2 this

include hq in
theorem mem_range_Φ_iff (t : GL (Fin 2) (𝔸K)) :
    t ∈ Set.range (Φ K γ₀) ↔ Commute (t : Matrix (Fin 2) (Fin 2) (𝔸K)) (γA γ₀ (𝔸K)) := by
  rw [← mem_range_ΦA_iff γ₀ (𝔸K) hq t]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨_, (Φ_eq_ΦA K γ₀ x).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨Units.map ((te K γ₀) : (𝔸K ⊗[K] E γ₀) →* 𝔸E) z, ?_⟩
    rw [Φ_eq_ΦA]; congr 1; ext; simp

theorem mem_centralizer_iff (g₀ : GL (Fin 2) K) (u : (𝔸K)ˣ) (t : GL (Fin 2) (𝔸K)) :
    t ∈ Subgroup.centralizer ({globalPoints (𝓞 K) K g₀ * centralScalar (𝓞 K) K u} :
      Set (AdelicGL2 (𝓞 K) K)) ↔
    Commute (t : Matrix (Fin 2) (Fin 2) (𝔸K)) (γA (g₀ : Matrix (Fin 2) (Fin 2) K) (𝔸K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hval : ((globalPoints (𝓞 K) K g₀ * centralScalar (𝓞 K) K u : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (𝔸K)) = (u : 𝔸K) • γA (g₀ : Matrix (Fin 2) (Fin 2) K) (𝔸K) := by
    rw [Units.val_mul]
    change (RingHom.mapMatrix (algebraMap K (𝔸K))) (g₀ : Matrix (Fin 2) (Fin 2) K) *
      Matrix.scalar (Fin 2) (u : 𝔸K) = _
    rw [Matrix.scalar_apply]
    ext i j
    rw [Matrix.mul_diagonal]
    simp [γA, mul_comm]
  constructor
  · intro h
    have h' := congrArg (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (𝔸K))) h
    simp only [Units.val_mul, hval, Matrix.smul_mul, Matrix.mul_smul] at h'
    have := congrArg (fun M => ((u⁻¹ : (𝔸K)ˣ) : 𝔸K) • M) h'
    simp only [smul_smul, Units.inv_mul, one_smul] at this
    exact this
  · intro h
    apply Units.ext
    simp only [Units.val_mul, hval, Matrix.smul_mul, Matrix.mul_smul]
    rw [h.eq]

theorem continuous_Ψ : Continuous (Ψ K γ₀) := by
  haveI := isModuleTopology_AE K γ₀
  exact IsModuleTopology.continuous_of_linearMap (Ψ K γ₀).toLinearMap

noncomputable def θA : 𝔸E := algebraMap (E γ₀) (𝔸E) (AdjoinRoot.root γ₀.charpoly)

theorem te_symm_θA : (te K γ₀).symm (θA K γ₀) = (1 : 𝔸K) ⊗ₜ[K] AdjoinRoot.root γ₀.charpoly := by
  rw [θA, ← te_one_tmul, AlgEquiv.symm_apply_apply]

theorem eq_smul_one_add_smul_θA (y : 𝔸E) :
    y = (bA γ₀ (𝔸K)).repr ((te K γ₀).symm y) 0 • (1 : 𝔸E) +
      (bA γ₀ (𝔸K)).repr ((te K γ₀).symm y) 1 • θA K γ₀ := by
  have h := eq_smul_one_add_smul_root γ₀ (𝔸K) ((te K γ₀).symm y)
  have h2 := congrArg (te K γ₀) h
  rw [AlgEquiv.apply_symm_apply, map_add, map_smul, map_smul, map_one, ← te_symm_θA,
    AlgEquiv.apply_symm_apply] at h2
  exact h2

theorem Ψ_smul_one_add_smul_θA (c₀ c₁ : 𝔸K) :
    Ψ K γ₀ (c₀ • (1 : 𝔸E) + c₁ • θA K γ₀) =
      c₀ • (1 : Matrix (Fin 2) (Fin 2) (𝔸K)) + c₁ • γA γ₀ (𝔸K) := by
  rw [map_add, map_smul, map_smul, map_one, Ψ_apply, te_symm_θA, ιA_one_tmul_root]

noncomputable def ρ : Matrix (Fin 2) (Fin 2) (𝔸K) →ₗ[𝔸K] 𝔸E where
  toFun X := (X 0 0 - X 0 1 * algebraMap K (𝔸K) ((γ₀ 0 1)⁻¹ * γ₀ 0 0)) • (1 : 𝔸E) +
    (X 0 1 * algebraMap K (𝔸K) (γ₀ 0 1)⁻¹) • θA K γ₀
  map_add' X Y := by
    simp only [Matrix.add_apply]
    rw [show (X 0 0 + Y 0 0 - (X 0 1 + Y 0 1) * algebraMap K (𝔸K) ((γ₀ 0 1)⁻¹ * γ₀ 0 0)) =
      (X 0 0 - X 0 1 * algebraMap K (𝔸K) ((γ₀ 0 1)⁻¹ * γ₀ 0 0)) +
        (Y 0 0 - Y 0 1 * algebraMap K (𝔸K) ((γ₀ 0 1)⁻¹ * γ₀ 0 0)) by ring,
      add_mul, add_smul, add_smul]
    abel
  map_smul' a X := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul, mul_sub,
      mul_assoc]

theorem continuous_ρ : Continuous (ρ K γ₀) := by
  haveI := isModuleTopology_AE K γ₀
  haveI : ContinuousSMul (𝔸K) (𝔸E) := IsModuleTopology.toContinuousSMul (𝔸K) (𝔸E)
  have h00 : Continuous fun X : Matrix (Fin 2) (Fin 2) (𝔸K) => X 0 0 :=
    (continuous_apply 0).comp (continuous_apply 0)
  have h01 : Continuous fun X : Matrix (Fin 2) (Fin 2) (𝔸K) => X 0 1 :=
    (continuous_apply 1).comp (continuous_apply 0)
  show Continuous fun X : Matrix (Fin 2) (Fin 2) (𝔸K) =>
    (X 0 0 - X 0 1 * algebraMap K (𝔸K) ((γ₀ 0 1)⁻¹ * γ₀ 0 0)) • (1 : 𝔸E) +
      (X 0 1 * algebraMap K (𝔸K) (γ₀ 0 1)⁻¹) • θA K γ₀
  exact ((h00.sub (h01.mul continuous_const)).smul continuous_const).add
    ((h01.mul continuous_const).smul continuous_const)

include hq in
theorem ρ_Ψ (y : 𝔸E) : ρ K γ₀ (Ψ K γ₀ y) = y := by
  set c₀ := (bA γ₀ (𝔸K)).repr ((te K γ₀).symm y) 0
  set c₁ := (bA γ₀ (𝔸K)).repr ((te K γ₀).symm y) 1
  have hy := eq_smul_one_add_smul_θA K γ₀ y
  rw [hy, Ψ_smul_one_add_smul_θA]
  show (((c₀ • (1 : Matrix (Fin 2) (Fin 2) (𝔸K)) + c₁ • γA γ₀ (𝔸K)) 0 0 -
      (c₀ • (1 : Matrix (Fin 2) (Fin 2) (𝔸K)) + c₁ • γA γ₀ (𝔸K)) 0 1 *
        algebraMap K (𝔸K) ((γ₀ 0 1)⁻¹ * γ₀ 0 0)) • (1 : 𝔸E) +
    ((c₀ • (1 : Matrix (Fin 2) (Fin 2) (𝔸K)) + c₁ • γA γ₀ (𝔸K)) 0 1 *
      algebraMap K (𝔸K) (γ₀ 0 1)⁻¹) • θA K γ₀) = c₀ • (1 : 𝔸E) + c₁ • θA K γ₀
  have hqq : algebraMap K (𝔸K) (γ₀ 0 1) * algebraMap K (𝔸K) (γ₀ 0 1)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq, map_one]
  congr 1
  · congr 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne
      (show (0 : Fin 2) ≠ 1 by decide), γA, Matrix.map_apply, smul_eq_mul, mul_one, mul_zero,
      zero_add, map_mul]
    calc c₀ + c₁ * algebraMap K (𝔸K) (γ₀ 0 0) -
          c₁ * algebraMap K (𝔸K) (γ₀ 0 1) * (algebraMap K (𝔸K) (γ₀ 0 1)⁻¹ * algebraMap K (𝔸K) (γ₀ 0 0))
        = c₀ + c₁ * algebraMap K (𝔸K) (γ₀ 0 0) -
          c₁ * (algebraMap K (𝔸K) (γ₀ 0 1) * algebraMap K (𝔸K) (γ₀ 0 1)⁻¹) * algebraMap K (𝔸K) (γ₀ 0 0) := by ring
      _ = c₀ := by rw [hqq]; ring
  · congr 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne
      (show (0 : Fin 2) ≠ 1 by decide), γA, Matrix.map_apply, smul_eq_mul, mul_zero, zero_add]
    rw [mul_assoc, hqq, mul_one]

include hq in
theorem isInducing_Ψ : IsInducing (Ψ K γ₀) := by
  refine IsInducing.of_comp (continuous_Ψ K γ₀) (continuous_ρ K γ₀) ?_
  have : (ρ K γ₀ : Matrix (Fin 2) (Fin 2) (𝔸K) → 𝔸E) ∘ (Ψ K γ₀) = id := funext (ρ_Ψ K γ₀ hq)
  rw [this]; exact IsInducing.id

include hq in
theorem isInducing_Φ : IsInducing (Φ K γ₀) :=
  (isInducing_Ψ K γ₀ hq).units_map

theorem continuous_Φ : Continuous (Φ K γ₀) :=
  Continuous.units_map _ (continuous_Ψ K γ₀)

section Theta

variable (g₀ : GL (Fin 2) K) [Fact (Irreducible (g₀ : Matrix (Fin 2) (Fin 2) K).charpoly)]

noncomputable abbrev T (u : (AdeleRing (𝓞 K) K)ˣ) : Subgroup (AdelicGL2 (𝓞 K) K) :=
  Subgroup.centralizer ({globalPoints (𝓞 K) K g₀ * centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K))

variable (hq' : (g₀ : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0)
include hq'

theorem range_Φ_eq (u : (AdeleRing (𝓞 K) K)ˣ) :
    (Φ K (g₀ : Matrix (Fin 2) (Fin 2) K)).range = T K g₀ u := by
  ext t
  rw [MonoidHom.mem_range, mem_centralizer_iff, ← mem_range_Φ_iff K _ hq', Set.mem_range]

noncomputable def Θ₀ (u : (AdeleRing (𝓞 K) K)ˣ) :
    (AdeleRing (𝓞 (E (g₀ : Matrix (Fin 2) (Fin 2) K))) (E (g₀ : Matrix (Fin 2) (Fin 2) K)))ˣ ≃*
      T K g₀ u :=
  (MonoidHom.ofInjective (Φ_injective K _ hq')).trans (MulEquiv.subgroupCongr (range_Φ_eq K g₀ hq' u))

theorem Θ₀_val (u : (AdeleRing (𝓞 K) K)ˣ)
    (x : (AdeleRing (𝓞 (E (g₀ : Matrix (Fin 2) (Fin 2) K))) (E (g₀ : Matrix (Fin 2) (Fin 2) K)))ˣ) :
    ((Θ₀ K g₀ hq' u x : T K g₀ u) : AdelicGL2 (𝓞 K) K) = Φ K (g₀ : Matrix (Fin 2) (Fin 2) K) x := rfl

noncomputable def Θ (u : (AdeleRing (𝓞 K) K)ˣ) :
    (AdeleRing (𝓞 (E (g₀ : Matrix (Fin 2) (Fin 2) K))) (E (g₀ : Matrix (Fin 2) (Fin 2) K)))ˣ ≃ₜ*
      T K g₀ u where
  toMulEquiv := Θ₀ K g₀ hq' u
  continuous_toFun := (continuous_Φ K _).subtype_mk _
  continuous_invFun := by
    rw [(isInducing_Φ K (g₀ : Matrix (Fin 2) (Fin 2) K) hq').continuous_iff]
    have : (Φ K (g₀ : Matrix (Fin 2) (Fin 2) K)) ∘ (Θ₀ K g₀ hq' u).invFun =
        fun t : T K g₀ u => (t : AdelicGL2 (𝓞 K) K) := by
      funext t
      show Φ K _ ((Θ₀ K g₀ hq' u).symm t) = _
      rw [← Θ₀_val K g₀ hq' u, MulEquiv.apply_symm_apply]
    rw [this]
    exact continuous_subtype_val

theorem Θ_val (u : (AdeleRing (𝓞 K) K)ˣ)
    (x : (AdeleRing (𝓞 (E (g₀ : Matrix (Fin 2) (Fin 2) K))) (E (g₀ : Matrix (Fin 2) (Fin 2) K)))ˣ) :
    ((Θ K g₀ hq' u x : T K g₀ u) : AdelicGL2 (𝓞 K) K) = Φ K (g₀ : Matrix (Fin 2) (Fin 2) K) x := rfl

end Theta

section RationalPoints

variable (g₀ : GL (Fin 2) K) [Fact (Irreducible (g₀ : Matrix (Fin 2) (Fin 2) K).charpoly)]

local notation "γ₀'" => (g₀ : Matrix (Fin 2) (Fin 2) K)
local notation "E'" => E (g₀ : Matrix (Fin 2) (Fin 2) K)
local notation "𝔸E'" => AdeleRing (𝓞 (E (g₀ : Matrix (Fin 2) (Fin 2) K))) (E (g₀ : Matrix (Fin 2) (Fin 2) K))

theorem Φ_unitsMap_algebraMap (e : (E')ˣ) :
    Φ K γ₀' (Units.map (algebraMap E' 𝔸E' : E' →* 𝔸E') e) =
      globalPoints (𝓞 K) K (Units.map (ι₀ γ₀' : E' →* Matrix (Fin 2) (Fin 2) K) e) := by
  apply Units.ext
  rw [Φ_val, Units.coe_map, MonoidHom.coe_coe, Ψ_apply, ← te_one_tmul, AlgEquiv.symm_apply_apply,
    ιA_tmul, one_smul]
  rfl

omit [NumberField K] in

theorem unitsMap_ι₀_mem_centralizer (e : (E')ˣ) :
    Units.map (ι₀ γ₀' : E' →* Matrix (Fin 2) (Fin 2) K) e ∈
      Subgroup.centralizer ({g₀} : Set (GL (Fin 2) K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  have h := congrArg (ι₀ γ₀') (mul_comm (AdjoinRoot.root _) (e : E'))
  rw [map_mul, map_mul, ι₀_root] at h
  exact h.symm

noncomputable abbrev ΓK (u : (AdeleRing (𝓞 K) K)ˣ) : Subgroup (T K g₀ u) :=
  ((Subgroup.centralizer ({g₀} : Set (GL (Fin 2) K))).map (globalPoints (𝓞 K) K)).subgroupOf (T K g₀ u)

noncomputable abbrev ΓE : Subgroup (𝔸E')ˣ := (Units.map (algebraMap E' 𝔸E' : E' →* 𝔸E')).range

variable (hq' : (g₀ : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0)
include hq'

theorem Θ_mem_ΓK_of_mem_ΓE (u : (AdeleRing (𝓞 K) K)ˣ) {h : (𝔸E')ˣ} (hh : h ∈ ΓE K g₀) :
    Θ K g₀ hq' u h ∈ ΓK K g₀ u := by
  obtain ⟨e, rfl⟩ := hh
  rw [Subgroup.mem_subgroupOf, Θ_val, Φ_unitsMap_algebraMap]
  exact Subgroup.mem_map_of_mem _ (unitsMap_ι₀_mem_centralizer K g₀ e)

theorem Θ_symm_mem_ΓE_of_mem_ΓK (u : (AdeleRing (𝓞 K) K)ˣ) {t : T K g₀ u} (ht : t ∈ ΓK K g₀ u) :
    (Θ K g₀ hq' u).symm t ∈ ΓE K g₀ := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at ht
  obtain ⟨g, hg, hgt⟩ := ht
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hgc : Commute (g : Matrix (Fin 2) (Fin 2) K) γ₀' := by
    have := congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K)) hg
    simp only [Units.val_mul] at this
    unfold Commute SemiconjBy
    exact this
  obtain ⟨e, he⟩ := exists_units_eq_of_commute γ₀' hq' g hgc
  refine ⟨e, ?_⟩
  apply (Θ K g₀ hq' u).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [Θ_val, Φ_unitsMap_algebraMap, he, hgt]

noncomputable def eΓ (u : (AdeleRing (𝓞 K) K)ˣ) : (ΓK K g₀ u).op → ΓE K g₀ := fun g =>
  ⟨(Θ K g₀ hq' u).symm (MulOpposite.unop (g : (T K g₀ u)ᵐᵒᵖ)),
    Θ_symm_mem_ΓE_of_mem_ΓK K g₀ hq' u (Subgroup.mem_op.mp g.2)⟩

theorem eΓ_bijective (u : (AdeleRing (𝓞 K) K)ˣ) : Function.Bijective (eΓ K g₀ hq' u) := by
  constructor
  · intro g₁ g₂ h
    have h' := congrArg (fun x : ΓE K g₀ => (x : (𝔸E')ˣ)) h
    simp only [eΓ] at h'
    exact Subtype.ext (MulOpposite.unop_injective ((Θ K g₀ hq' u).symm.injective h'))
  · intro h
    refine ⟨⟨MulOpposite.op (Θ K g₀ hq' u h), Subgroup.mem_op.mpr ?_⟩, ?_⟩
    · rw [MulOpposite.unop_op]; exact Θ_mem_ΓK_of_mem_ΓE K g₀ hq' u h.2
    · apply Subtype.ext
      simp only [eΓ, MulOpposite.unop_op, ContinuousMulEquiv.symm_apply_apply]

theorem eΓ_semiconj (u : (AdeleRing (𝓞 K) K)ˣ) (g : (ΓK K g₀ u).op) (x : (𝔸E')ˣ) :
    Θ K g₀ hq' u (eΓ K g₀ hq' u g • x) = g • Θ K g₀ hq' u x := by
  rw [Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, MulOpposite.smul_eq_mul_unop]
  show Θ K g₀ hq' u ((Θ K g₀ hq' u).symm (MulOpposite.unop (g : (T K g₀ u)ᵐᵒᵖ)) * x) = _
  rw [mul_comm, map_mul, ContinuousMulEquiv.apply_symm_apply]

end RationalPoints

section DetNorm

theorem det_Φ (x : (𝔸E)ˣ) :
    Matrix.GeneralLinearGroup.det (Φ K γ₀ x) = (genuineBaseChange K (E γ₀)).idelicNorm x := by
  apply Units.ext
  change ((Φ K γ₀ x : GL (Fin 2) (𝔸K)) : Matrix (Fin 2) (Fin 2) (𝔸K)).det =
    Algebra.norm (𝔸K) (x : 𝔸E)
  rw [Φ_val, Ψ_apply, ← norm_eq_det, Algebra.norm_eq_of_algEquiv]

theorem ideleNorm_det_Φ (x : (𝔸E)ˣ) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (Φ K γ₀ x)) =
      NumberField.TateGlobal.ideleNorm (E γ₀) x := by
  unfold NumberField.TateGlobal.ideleNorm
  rw [det_Φ, NumberField.distribHaarChar_idelicNorm_genuineBaseChange K (E γ₀) x]

end DetNorm

section Transport

open MeasureTheory

variable (g₀ : GL (Fin 2) K) [Fact (Irreducible (g₀ : Matrix (Fin 2) (Fin 2) K).charpoly)]
  (hq' : (g₀ : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0)

local notation "E'" => E (g₀ : Matrix (Fin 2) (Fin 2) K)
local notation "𝔸E'" => AdeleRing (𝓞 (E (g₀ : Matrix (Fin 2) (Fin 2) K))) (E (g₀ : Matrix (Fin 2) (Fin 2) K))

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

@[reducible] noncomputable def ideleBorel : MeasurableSpace (𝔸E)ˣ := borel _

attribute [local instance] ideleBorel

include hq' in

theorem main (u : (AdeleRing (𝓞 K) K)ˣ) (τ : Measure (T K g₀ u)) [τ.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ D : Set (T K g₀ u), IsFundamentalDomain (ΓK K g₀ u).op D τ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) := by
  haveI : BorelSpace (T K g₀ u) := ⟨rfl⟩
  haveI : BorelSpace (𝔸E')ˣ := ⟨rfl⟩
  set Θ' := Θ K g₀ hq' u with hΘ'
  let Θm : (𝔸E')ˣ ≃ᵐ T K g₀ u := Θ'.toHomeomorph.toMeasurableEquiv
  have hΘm : (Θm : (𝔸E')ˣ → T K g₀ u) = Θ' := rfl
  have hΘms : (Θm.symm : T K g₀ u → (𝔸E')ˣ) = Θ'.symm := rfl
  let ν : Measure (𝔸E')ˣ := Measure.map Θ'.symm τ
  haveI : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map τ Θ'.symm
  obtain ⟨C, hC0, hCtop, hC⟩ :=
    NumberField.TateGlobal.exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log E' ν
  refine ⟨C, hC0, hCtop, fun D hD a b ha hab => ?_⟩

  have hqmp : Measure.QuasiMeasurePreserving Θ' ν τ := by
    refine ⟨Θ'.continuous.measurable, ?_⟩
    have : Measure.map Θ' ν = τ := by
      show Measure.map Θm (Measure.map Θm.symm τ) = τ
      exact Θm.map_map_symm
    rw [this]
  have hΩ : IsFundamentalDomain (ΓE K g₀) (Θ' ⁻¹' D) ν :=
    hD.preimage_of_equiv hqmp (eΓ_bijective K g₀ hq' u) (fun g x => eΓ_semiconj K g₀ hq' u g x)
  have key := hC (Θ' ⁻¹' D) hΩ a b ha hab

  have hset : D ∩ {t : T K g₀ u | NumberField.TateGlobal.ideleNorm K
      (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b} =
      Θm.symm ⁻¹' (Θ' ⁻¹' D ∩ {x | NumberField.TateGlobal.ideleNorm E' x ∈ Set.Icc a b}) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, hΘms,
      ContinuousMulEquiv.apply_symm_apply]
    rw [← ideleNorm_det_Φ K (g₀ : Matrix (Fin 2) (Fin 2) K) (Θ'.symm t), ← Θ_val K g₀ hq' u,
      ContinuousMulEquiv.apply_symm_apply]
  rw [hset, ← MeasurableEquiv.map_apply, hΘms]
  exact key

end Transport

end Adelic

end R3M4Torus
p2m_reactivate "P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell.R3M4Torus"

open MeasureTheory NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K) (u : (AdeleRing (𝓞 K) K)ˣ)
    (τ : Measure (Subgroup.centralizer
      ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K u} :
        Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    [τ.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ D : Set (Subgroup.centralizer
        ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K u} :
          Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
        IsFundamentalDomain
          (((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map
            (AutomorphicForm.globalPoints (𝓞 K) K)).subgroupOf
            (Subgroup.centralizer {AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
              AutomorphicForm.centralScalar (𝓞 K) K u})).op D τ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) := by
  haveI : Fact (Irreducible (γ₀ : Matrix (Fin 2) (Fin 2) K).charpoly) :=
    ⟨R3M4Torus.irreducible_charpoly _ hγ₀⟩
  exact R3M4Torus.main K γ₀ (R3M4Torus.entry01_ne_zero _ hγ₀) u τ

end S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell
end P2MW
export P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell (solution)
