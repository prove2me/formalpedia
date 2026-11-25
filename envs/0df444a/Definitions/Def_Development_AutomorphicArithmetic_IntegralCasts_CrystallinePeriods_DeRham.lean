-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:36.806999+00:00
-- url     : https://prove2.me/theorems/4558d234-869f-43f7-ae2b-a99dcc029473
-- title:
--   De Rham
-- statement:
--   Definitions and structural lemmas for De Rham, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_Acris_ext_eval
import Theorems.Thm_Reformulated_AutPerF_AinfInv_algebraMap_injective
import Theorems.Thm_Reformulated_AutPerF_AinfInv_eq_zero_of_forall_mem_kerTheta_pow
import Theorems.Thm_Reformulated_AutPerF_AinfInv_kerTheta_eq
import Theorems.Thm_Reformulated_AutPerF_AinfInv_kerTheta_fg
import Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_surjective
import Theorems.Thm_Reformulated_AutPerF_Ainf_eq_zero_of_forall_xi_pow_dvd
import Theorems.Thm_Reformulated_AutPerF_Ainf_ker_theta
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_eq_zero_iff
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_surjective
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_Ainf_xi_ne_zero
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_ext_eval
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_theta_eq_zero_iff
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
import Theorems.Thm_Reformulated_AutPerF_eq_zero_of_forall_pow_dvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Ainf.theta_xi
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


set_option autoImplicit false
noncomputable section
open Ideal
namespace Reformulated.AutPerF
universe u
section Adic
variable {A : Type u} [CommRing A]
theorem evalₐ_eq_zero_iff_dvd_of_eq_span {I : Ideal A} {a : A} (hI : I = span {a}) (n : ℕ)
    (x : AdicCompletion I A) :
    AdicCompletion.evalₐ I n x = 0 ↔ algebraMap A (AdicCompletion I A) a ^ n ∣ x := by
  have hfg : I.FG := hI ▸ Submodule.fg_span_singleton a
  have h1 : AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I A n x = 0 := by
    constructor
    · intro h
      rw [← AdicCompletion.factor_evalₐ_eq_eval I x (by simp), h, map_zero]
    · intro h
      rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), h, map_zero]
  rw [h1, ← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval hfg]
  have h2 : I ^ n = span {a ^ n} := by rw [hI, Ideal.span_singleton_pow]
  rw [h2, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, trivial, by rw [Algebra.smul_def, map_pow]⟩
theorem eq_zero_of_algebraMap_mul_eq_zero [IsDomain A] {I : Ideal A} {a : A} (hI : I = span {a})
    (ha : a ≠ 0) {x : AdicCompletion I A} (h : algebraMap A (AdicCompletion I A) a * x = 0) :
    x = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  have h1 := congrArg (AdicCompletion.evalₐ I (n + 1)) h
  rw [map_mul, AlgHom.commutes, ← hy, map_zero, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : ∀ m, I ^ m = span {a ^ m} := fun m => by rw [hI, Ideal.span_singleton_pow]
  rw [h2, mem_span_singleton, pow_succ', mul_dvd_mul_iff_left ha] at h1
  rw [← factorPow_evalₐ I n.le_succ, ← hy, map_zero]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [h2, mem_span_singleton]
  exact h1
end Adic
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]
omit [Fact ¬IsUnit (p : R)] [CharZero R] [Fact p.Prime] in
theorem exists_dvd_p_pow {x : R} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ (p : R) ^ n := by
  by_contra h
  push Not at h
  exact hx (eq_zero_of_forall_pow_dvd (p : R) fun n =>
    (ValuationRing.dvd_total x _).resolve_left (h n))
instance isFractionRing_away : IsFractionRing R (Localization.Away (p : R)) :=
  IsLocalization.isLocalization_of_is_exists_mul_mem _ (Submonoid.powers (p : R)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
    (fun ⟨x, hx⟩ => by
      obtain ⟨n, c, hc⟩ := exists_dvd_p_pow (p := p) (nonZeroDivisors.ne_zero hx)
      exact ⟨c, n, by simp [hc, mul_comm]⟩)
variable (p R) in
omit [Fact ¬IsUnit (p : R)] in
theorem isField_away : IsField (Localization.Away (p : R)) :=
  (IsFractionRing.toField R (K := Localization.Away (p : R))).toIsField
namespace BdRPlus
omit [IsDomain R] [ValuationRing R] [CharZero R] in

def xi (ϖ : PFlat p R) : BdRPlus p R := algebraMap (Ainf p R) _ (Ainf.xi ϖ)
omit [IsDomain R] [ValuationRing R] [CharZero R] in
@[simp] theorem theta_algebraMap_ainf (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = algebraMap R _ (Ainf.theta p R x) :=
  AinfInv.theta_algebraMap x
theorem eval_eq_zero_iff (ϖ : PFlat p R) (n : ℕ) (x : BdRPlus p R) :
    eval p R n x = 0 ↔ xi ϖ ^ n ∣ x :=
  evalₐ_eq_zero_iff_dvd_of_eq_span (AinfInv.kerTheta_eq ϖ) n x
theorem theta_eq_zero_iff_dvd (ϖ : PFlat p R) (x : BdRPlus p R) :
    theta p R x = 0 ↔ xi ϖ ∣ x := by
  rw [← pow_one (xi ϖ), ← eval_eq_zero_iff, theta_eq_zero_iff]
  refine Iff.trans (Eq.congr_left (AdicCompletion.factorₐ_evalₐ_one _ _).symm)
    (map_eq_zero_iff _ ?_)
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact hy
theorem ker_theta (ϖ : PFlat p R) : RingHom.ker (theta p R) = span {xi ϖ} := by
  ext x
  rw [RingHom.mem_ker, theta_eq_zero_iff_dvd ϖ, mem_span_singleton]
theorem fil_eq_span (ϖ : PFlat p R) (n : ℕ) : fil p R n = span {xi ϖ ^ n} := by
  rw [fil, ker_theta ϖ, Ideal.span_singleton_pow]
theorem eq_zero_of_xi_mul_eq_zero (ϖ : PFlat p R) {x : BdRPlus p R} (h : xi ϖ * x = 0) : x = 0 :=
  eq_zero_of_algebraMap_mul_eq_zero (AinfInv.kerTheta_eq ϖ)
    ((map_ne_zero_iff _ AinfInv.algebraMap_injective).2 (Ainf.xi_ne_zero ϖ)) h
theorem eq_zero_of_forall_xi_pow_dvd (ϖ : PFlat p R) {x : BdRPlus p R}
    (h : ∀ n : ℕ, xi ϖ ^ n ∣ x) : x = 0 :=
  ext_eval fun n => by rw [map_zero, eval_eq_zero_iff ϖ]; exact h n
variable [IsAlgClosed (FractionRing R)]
theorem ker_theta_eq_map : RingHom.ker (theta p R) =
    (AinfInv.kerTheta p R).map (algebraMap (AinfInv p R) (BdRPlus p R)) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have h := congrArg (Ideal.map (algebraMap (AinfInv p R) (BdRPlus p R))) (AinfInv.kerTheta_eq ϖ)
  rw [ker_theta ϖ, h, Ideal.map_span, Set.image_singleton]
  rfl
instance isAdicComplete_ker_theta : IsAdicComplete (RingHom.ker (theta p R)) (BdRPlus p R) := by
  rw [ker_theta_eq_map]
  exact AdicCompletion.isAdicComplete_self _ AinfInv.kerTheta_fg
instance isAdicComplete_fil_one : IsAdicComplete (fil p R 1) (BdRPlus p R) := by
  rw [fil, pow_one]
  infer_instance
omit [CharZero R] in

theorem theta_surjective : Function.Surjective (theta p R) := fun y =>
  let ⟨x, hx⟩ := AinfInv.theta_surjective (p := p) y
  ⟨algebraMap _ _ x, hx⟩
theorem isUnit_iff_theta_ne_zero (x : BdRPlus p R) : IsUnit x ↔ theta p R x ≠ 0 := by
  have := (isField_away p R).nontrivial
  refine ⟨fun h => (h.map _).ne_zero, fun h => ?_⟩
  obtain ⟨z, hz⟩ := (isField_away p R).mul_inv_cancel h
  obtain ⟨y, rfl⟩ := theta_surjective (p := p) z
  have h1 : x * y - 1 ∈ RingHom.ker (theta p R) := by
    rw [RingHom.mem_ker, map_sub, map_mul, hz, map_one, sub_self]
  have h2 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h1) 1
  rw [mul_one, sub_add_cancel] at h2
  exact isUnit_of_mul_isUnit_left h2
theorem exists_associated_xi_pow (ϖ : PFlat p R) {x : BdRPlus p R} (hx : x ≠ 0) :
    ∃ n : ℕ, Associated (xi ϖ ^ n) x := by
  classical
  have h : ∃ n : ℕ, ¬xi ϖ ^ (n + 1) ∣ x := by
    by_contra h
    push Not at h
    exact hx (eq_zero_of_forall_xi_pow_dvd ϖ fun n => (pow_dvd_pow _ n.le_succ).trans (h n))
  obtain ⟨u, hu⟩ : xi ϖ ^ Nat.find h ∣ x := by
    rcases e : Nat.find h with _ | m
    · simp
    · exact not_not.1 (Nat.find_min h (by omega))
  have hu' : IsUnit u := by
    rw [isUnit_iff_theta_ne_zero, Ne, theta_eq_zero_iff_dvd ϖ]
    intro hd
    apply Nat.find_spec h
    obtain ⟨v, rfl⟩ := hd
    exact ⟨v, hu.trans (by ring)⟩
  exact ⟨_, hu'.unit, hu.symm⟩
instance nontrivial : Nontrivial (BdRPlus p R) :=
  have := (isField_away p R).nontrivial
  (theta p R).domain_nontrivial
instance isDomain : IsDomain (BdRPlus p R) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have key : ∀ (n : ℕ) (y : BdRPlus p R), xi ϖ ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro y hy
      exact ih y (eq_zero_of_xi_mul_eq_zero ϖ (by rw [← mul_assoc, ← pow_succ', hy]))
  have : NoZeroDivisors (BdRPlus p R) := ⟨fun {a b} h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    obtain ⟨n, u, rfl⟩ := exists_associated_xi_pow ϖ ha
    exact Or.inr ((Units.mul_right_eq_zero u).1 (key n _ (by rw [← mul_assoc, h])))⟩
  exact NoZeroDivisors.to_isDomain _
theorem xi_ne_zero (ϖ : PFlat p R) : xi ϖ ≠ 0 := fun h =>
  one_ne_zero (eq_zero_of_xi_mul_eq_zero ϖ (x := 1) (by rw [h, zero_mul]))
theorem prime_xi (ϖ : PFlat p R) : Prime (xi ϖ) := by
  have := (isField_away p R).isDomain
  rw [← Ideal.span_singleton_prime (xi_ne_zero ϖ), ← ker_theta]
  exact RingHom.ker_isPrime _
instance isDiscreteValuationRing : IsDiscreteValuationRing (BdRPlus p R) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨xi ϖ, (prime_xi ϖ).irreducible, exists_associated_xi_pow ϖ⟩
theorem maximalIdeal_eq : IsLocalRing.maximalIdeal (BdRPlus p R) = RingHom.ker (theta p R) := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_theta_ne_zero, not_not,
    RingHom.mem_ker]
instance isAdicComplete_maximalIdeal :
    IsAdicComplete (IsLocalRing.maximalIdeal (BdRPlus p R)) (BdRPlus p R) := by
  rw [maximalIdeal_eq]
  infer_instance
theorem irreducible_iff (π : BdRPlus p R) : Irreducible π ↔ RingHom.ker (theta p R) = span {π} := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, maximalIdeal_eq]
variable (p R) in

def residueFieldEquiv : IsLocalRing.ResidueField (BdRPlus p R) ≃+* Localization.Away (p : R) :=
  (Ideal.quotEquivOfEq maximalIdeal_eq).trans (RingHom.quotientKerEquivOfSurjective theta_surjective)
@[simp] theorem residueFieldEquiv_residue (x : BdRPlus p R) :
    residueFieldEquiv p R (IsLocalRing.residue _ x) = theta p R x := rfl
theorem algebraMap_injective : Function.Injective (algebraMap (AinfInv p R) (BdRPlus p R)) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine AinfInv.eq_zero_of_forall_mem_kerTheta_pow ϖ fun n => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← eval_algebraMap, hx, map_zero]
end BdRPlus
namespace BdR
variable [IsAlgClosed (FractionRing R)]
instance field : Field (BdR p R) := IsFractionRing.toField (BdRPlus p R)
theorem algebraMap_injective : Function.Injective (algebraMap (BdRPlus p R) (BdR p R)) :=
  IsFractionRing.injective _ _
section Uniformizer
variable {π : BdRPlus p R} (hπ : RingHom.ker (BdRPlus.theta p R) = span {π})
include hπ
theorem algebraMap_ne_zero : algebraMap (BdRPlus p R) (BdR p R) π ≠ 0 :=
  (map_ne_zero_iff _ algebraMap_injective).2 ((BdRPlus.irreducible_iff π).2 hπ).ne_zero
theorem filNat_eq_span (n : ℕ) :
    filNat p R n = Submodule.span (BdRPlus p R) {algebraMap (BdRPlus p R) (BdR p R) π ^ n} := by
  rw [filNat, BdRPlus.fil, hπ, Ideal.span_singleton_pow, ← Ideal.submodule_span_eq,
    Submodule.map_span, Set.image_singleton, Algebra.linearMap_apply, map_pow]
theorem fil_eq_span (i : ℤ) :
    fil p R i = Submodule.span (BdRPlus p R) {algebraMap (BdRPlus p R) (BdR p R) π ^ i} := by
  have h0 := algebraMap_ne_zero hπ
  set t := algebraMap (BdRPlus p R) (BdR p R) π
  have hi : t ^ i * t ^ (-i).toNat = t ^ i.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0]
    congr 1
    omega
  ext x
  rw [fil, filNat_eq_span hπ, filNat_eq_span hπ, Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h _ (Submodule.mem_span_singleton_self _))
    refine Submodule.mem_span_singleton.2 ⟨c, mul_right_cancel₀ (pow_ne_zero (-i).toNat h0) ?_⟩
    rw [smul_mul_assoc, hi, hc]
  · intro h y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 h
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact Submodule.mem_span_singleton.2 ⟨c * d, by rw [smul_mul_smul_comm, hi]⟩
end Uniformizer
theorem fil_zero : fil p R 0 = 1 := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [fil_eq_span (BdRPlus.ker_theta ϖ), zpow_zero, Submodule.one_eq_span]
theorem mem_fil_zero_iff (x : BdR p R) :
    x ∈ fil p R 0 ↔ ∃ c : BdRPlus p R, algebraMap _ _ c = x := by
  rw [fil_zero, Submodule.mem_one]
theorem fil_mul_fil (i j : ℤ) : fil p R i * fil p R j = fil p R (i + j) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have h := BdRPlus.ker_theta ϖ
  rw [fil_eq_span h, fil_eq_span h, fil_eq_span h, Submodule.span_mul_span,
    Set.singleton_mul_singleton, zpow_add₀ (algebraMap_ne_zero h)]
theorem mul_mem_fil {i j : ℤ} {x y : BdR p R} (hx : x ∈ fil p R i) (hy : y ∈ fil p R j) :
    x * y ∈ fil p R (i + j) := fil_mul_fil (p := p) (R := R) i j ▸ Submodule.mul_mem_mul hx hy
instance gradedMonoid : SetLike.GradedMonoid (fil p R) where
  one_mem := (mem_fil_zero_iff _).2 ⟨1, map_one _⟩
  mul_mem _ _ _ _ := mul_mem_fil
instance charZero : CharZero (BdR p R) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] (BdR p R)).injective
end BdR
end Reformulated.AutPerF


