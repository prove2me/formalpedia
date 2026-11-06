-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
-- name    : OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:37.425144+00:00
-- url     : https://prove2.me/theorems/af135710-5b30-4136-b1fa-07c905c0bb6a
-- title:
--   Eisenstein Ideals
-- statement:
--   Definitions and structural lemmas for Eisenstein Ideals, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
set_option autoImplicit false
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
namespace ActualEisensteinSieve
abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K
instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K
def omega : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger
def lambda : O := omega - 1
def lambdaIdeal : Ideal O := Ideal.span {lambda}
theorem lambda_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'
theorem lambda_maximal : lambdaIdeal.IsMaximal := by
  have hp : lambdaIdeal.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime lambda_prime
  have hne : lambdaIdeal ≠ ⊥ := by
    exact Ideal.span_singleton_eq_bot.not.mpr lambda_prime.ne_zero
  exact hp.isMaximal hne
theorem lambda_card : Nat.card (O ⧸ lambdaIdeal) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [lambdaIdeal, lambda, omega,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
      (by decide)]
  norm_num
example (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
example (P : Ideal O) [P.IsMaximal] : Finite (O ⧸ P) := inferInstance
def localQuadratic (P : Ideal O) [P.IsMaximal] (x : O) : ℤ := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  exact quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x)
theorem localQuadratic_one (P : Ideal O) [P.IsMaximal] :
    localQuadratic P 1 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) 1 = 1
  exact map_one _
theorem localQuadratic_mul (P : Ideal O) [P.IsMaximal] (x y : O) :
    localQuadratic P (x * y) = localQuadratic P x * localQuadratic P y := by
  simp [localQuadratic, map_mul]
theorem localQuadratic_neg_one (P : Ideal O) [P.IsMaximal]
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    localQuadratic P (-1) = ZMod.χ₄ (Nat.card (O ⧸ P)) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) (-1) = ZMod.χ₄ (Nat.card (O ⧸ P))
  simpa only [Nat.card_eq_fintype_card] using quadraticChar_neg_one hodd
theorem localQuadratic_cube_root_one (P : Ideal O) [P.IsMaximal]
    (u : O) (hu : u ^ 3 = 1) : localQuadratic P u = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  let v : O ⧸ P := Ideal.Quotient.mk P u
  have hv3 : v ^ 3 = 1 := by
    simpa [v] using congrArg (Ideal.Quotient.mk P) hu
  have hvne : v ≠ 0 := by
    intro hv0
    simp [hv0] at hv3
  have hv4 : v ^ 4 = v := by
    calc
      v ^ 4 = v ^ 3 * v := by ring
      _ = v := by rw [hv3, one_mul]
  have hsq : quadraticChar (O ⧸ P) (v ^ 4) = 1 := by
    simpa only [← pow_mul] using quadraticChar_sq_one' (F := O ⧸ P)
      (a := v ^ 2) (pow_ne_zero _ hvne)
  change quadraticChar (O ⧸ P) v = 1
  rwa [hv4] at hsq
instance : lambdaIdeal.IsMaximal := lambda_maximal
theorem lambda_residue_odd : ringChar (O ⧸ lambdaIdeal) ≠ 2 := by
  classical
  let : Field (O ⧸ lambdaIdeal) := Ideal.Quotient.field lambdaIdeal
  let : Fintype (O ⧸ lambdaIdeal) := Fintype.ofFinite (O ⧸ lambdaIdeal)
  intro hchar
  have hcard := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, lambda_card] at hcard
  norm_num at hcard
theorem lambdaQuadratic_neg_one : localQuadratic lambdaIdeal (-1) = -1 := by
  rw [localQuadratic_neg_one lambdaIdeal lambda_residue_odd, lambda_card]
  rfl
theorem localQuadratic_congr (P : Ideal O) [P.IsMaximal] (x y : O)
    (h : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y) :
    localQuadratic P x = localQuadratic P y := by
  simp only [localQuadratic, h]
theorem lambdaQuadratic_omega : localQuadratic lambdaIdeal omega = 1 := by
  apply (localQuadratic_congr lambdaIdeal omega 1 ?_).trans
    (localQuadratic_one lambdaIdeal)
  apply Ideal.Quotient.eq.mpr
  exact Ideal.subset_span (by simp [lambda, omega])
def quadraticProduct
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) : ℤ :=
  ∏ i : ι, localQuadratic (P i) x
theorem quadraticProduct_one
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : quadraticProduct P 1 = 1 := by
  simp [quadraticProduct, localQuadratic_one]
theorem quadraticProduct_mul
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x y : O) :
    quadraticProduct P (x * y) = quadraticProduct P x * quadraticProduct P y := by
  simp [quadraticProduct, localQuadratic_mul, Finset.prod_mul_distrib]
theorem quadraticProduct_neg_one_square
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : quadraticProduct P (-1) ^ 2 = 1 := by
  calc
    quadraticProduct P (-1) ^ 2 =
        quadraticProduct P ((-1 : O) * (-1)) := by
          rw [pow_two, quadraticProduct_mul]
    _ = 1 := by simpa using quadraticProduct_one P
def correctedQuadraticProduct
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) : ℤ :=
  if quadraticProduct P (-1) = 1 then quadraticProduct P x
  else quadraticProduct P x * localQuadratic lambdaIdeal x
theorem correctedQuadraticProduct_neg_one
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    correctedQuadraticProduct P (-1) = 1 := by
  classical
  have hsq := quadraticProduct_neg_one_square P
  have hsign : quadraticProduct P (-1) = 1 ∨
      quadraticProduct P (-1) = -1 :=
    sq_eq_one_iff.mp hsq
  rcases hsign with h | h
  · simp [correctedQuadraticProduct, h]
  · simp [correctedQuadraticProduct, h, lambdaQuadratic_neg_one]
theorem correctedQuadraticProduct_omega
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    correctedQuadraticProduct P omega = 1 := by
  have hq : quadraticProduct P omega = 1 := by
    simp [quadraticProduct, localQuadratic_cube_root_one,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_cube_eq_one,
      omega]
  by_cases h : quadraticProduct P (-1) = 1
  · simp [correctedQuadraticProduct, h, hq]
  · simp [correctedQuadraticProduct, h, hq, lambdaQuadratic_omega]
theorem correctedQuadraticProduct_one
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    correctedQuadraticProduct P 1 = 1 := by
  by_cases h : quadraticProduct P (-1) = 1
  · simp [correctedQuadraticProduct, h, quadraticProduct_one]
  · simp [correctedQuadraticProduct, h, quadraticProduct_one,
      localQuadratic_one]
theorem correctedQuadraticProduct_mul
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x y : O) :
    correctedQuadraticProduct P (x * y) =
      correctedQuadraticProduct P x * correctedQuadraticProduct P y := by
  by_cases h : quadraticProduct P (-1) = 1
  · simp [correctedQuadraticProduct, h, quadraticProduct_mul]
  · simp only [correctedQuadraticProduct, h, ite_false,
      quadraticProduct_mul, localQuadratic_mul]
    ring
def correctedQuadraticHom
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : O →* ℤ where
  toFun := correctedQuadraticProduct P
  map_one' := correctedQuadraticProduct_one P
  map_mul' := correctedQuadraticProduct_mul P
theorem correctedQuadraticProduct_units
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (u : Oˣ) :
    correctedQuadraticProduct P (u : O) = 1 := by
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (IsPrimitiveRoot.isUnit hζ.toInteger_isPrimitiveRoot
    (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · subst u
    simpa using correctedQuadraticProduct_one P
  · subst u
    simpa using correctedQuadraticProduct_neg_one P
  · subst u
    change correctedQuadraticProduct P (η : O) = 1
    rw [hη]
    exact correctedQuadraticProduct_omega P
  · subst u
    change correctedQuadraticProduct P (-(η : O)) = 1
    rw [neg_eq_neg_one_mul, correctedQuadraticProduct_mul,
      correctedQuadraticProduct_neg_one, hη,
      correctedQuadraticProduct_omega]
    norm_num
  · subst u
    change correctedQuadraticProduct P ((η : O) ^ 2) = 1
    rw [pow_two, correctedQuadraticProduct_mul, hη,
      correctedQuadraticProduct_omega]
    norm_num
  · subst u
    change correctedQuadraticProduct P (-((η : O) ^ 2)) = 1
    rw [neg_eq_neg_one_mul, correctedQuadraticProduct_mul,
      correctedQuadraticProduct_neg_one]
    have hpow : correctedQuadraticProduct P ((η : O) ^ 2) = 1 := by
      rw [pow_two, correctedQuadraticProduct_mul, hη,
        correctedQuadraticProduct_omega]
      norm_num
    rw [hpow]
    norm_num
noncomputable def correctedAssociatesHom
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : Associates O →* ℤ where
  toFun := Quotient.lift (correctedQuadraticProduct P) (by
    intro a b hab
    obtain ⟨u, hu⟩ := hab
    rw [← hu, correctedQuadraticProduct_mul,
      correctedQuadraticProduct_units, mul_one])
  map_one' := by
    change correctedQuadraticProduct P 1 = 1
    exact correctedQuadraticProduct_one P
  map_mul' := by
    intro x y
    obtain ⟨a, rfl⟩ := Associates.mk_surjective x
    obtain ⟨b, rfl⟩ := Associates.mk_surjective y
    change correctedQuadraticProduct P (a * b) =
      correctedQuadraticProduct P a * correctedQuadraticProduct P b
    exact correctedQuadraticProduct_mul P a b
noncomputable def idealGeneratorClass (I : Ideal O) : Associates O :=
  (Ideal.associatesMulEquivIsPrincipal O).symm
    ⟨I, IsPrincipalIdealRing.principal I⟩
theorem idealGeneratorClass_one : idealGeneratorClass (1 : Ideal O) = 1 := by
  apply (Ideal.associatesMulEquivIsPrincipal O).injective
  simp [idealGeneratorClass]
theorem idealGeneratorClass_mul (I J : Ideal O) :
    idealGeneratorClass (I * J) = idealGeneratorClass I * idealGeneratorClass J := by
  apply (Ideal.associatesMulEquivIsPrincipal O).injective
  simp [idealGeneratorClass]
  apply Subtype.ext
  rfl
noncomputable def correctedIdealHom
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : Ideal O →* ℤ where
  toFun I := correctedAssociatesHom P (idealGeneratorClass I)
  map_one' := by
    rw [idealGeneratorClass_one, map_one]
  map_mul' := by
    intro I J
    rw [idealGeneratorClass_mul, map_mul]
def finiteQuadraticOnQuotient
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (z : O ⧸ Finset.univ.prod P) : ℤ :=
  ∏ j : ι, localQuadratic (P j) (Quotient.out z)
noncomputable def squarefreeCRT
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    (O ⧸ Finset.univ.prod P) ≃+* ((i : ι) → O ⧸ P i) := by
  classical
  have hpairU : ((Finset.univ : Finset ι) : Set ι).Pairwise
      (Function.onFun IsCoprime P) := by
    intro i hi j hj hij
    exact hpair hij
  have hprod : Finset.univ.prod P = ⨅ i, P i := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairU
  exact (Ideal.quotEquivOfEq hprod).trans
    (Ideal.quotientInfRingEquivPiQuotient P hpair)
noncomputable def localResidueChar (P : Ideal O) [P.IsMaximal] :
    MulChar (O ⧸ P) ℤ := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  exact quadraticChar (O ⧸ P)
theorem localResidueChar_zero_iff (P : Ideal O) [P.IsMaximal]
    (z : O ⧸ P) : localResidueChar P z = 0 ↔ z = 0 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) z = 0 ↔ z = 0
  exact quadraticChar_eq_zero_iff
noncomputable def squarefreePiChar
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    MulChar ((i : ι) → O ⧸ P i) ℤ where
  toFun z := ∏ i : ι, localResidueChar (P i) (z i)
  map_one' := by
    classical
    simp
  map_mul' := by
    classical
    intro x y
    simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    classical
    intro z hz
    by_contra hprod
    have hnonzero (i : ι) : localResidueChar (P i) (z i) ≠ 0 := by
      intro hzero
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
    have hunit_i (i : ι) : IsUnit (z i) := by
      let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
      exact isUnit_iff_ne_zero.mpr
        ((localResidueChar_zero_iff (P i) (z i)).not.mp (hnonzero i))
    exact hz (Pi.isUnit_iff.mpr hunit_i)
noncomputable def squarefreeQuotientChar
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    MulChar (O ⧸ Finset.univ.prod P) ℤ where
  toFun z := squarefreePiChar P (squarefreeCRT P hpair z)
  map_one' := by
    simp
  map_mul' := by
    intro x y
    simp
  map_nonunit' := by
    intro z hz
    apply (squarefreePiChar P).map_nonunit
    intro hu
    have hzunit : IsUnit z := by
      simpa using hu.map (squarefreeCRT P hpair).symm.toRingHom
    exact hz hzunit
end ActualEisensteinSieve
end
end OAI


