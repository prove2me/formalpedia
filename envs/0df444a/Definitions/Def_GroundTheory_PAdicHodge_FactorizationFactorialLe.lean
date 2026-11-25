-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
-- name    : GroundTheory_PAdicHodge_FactorizationFactorialLe
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:56:03.129285+00:00
-- url     : https://prove2.me/theorems/9fe15cc5-ae64-4c6f-bc3d-e4557d1c3246
-- title:
--   Factorization Factorial Le
-- statement:
--   Definitions and structural lemmas for Factorization Factorial Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_coeff
import Theorems.Thm_GroundTheory_PAdicHodge_isUnit_of_isUnit_coeff_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open _root_.WittVector
section NatUnits
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
theorem WittVector.isUnit_natCast_of_coprime {m : ℕ} (hm : m.Coprime p) :
    IsUnit (m : WittVector p R) := by
  apply isUnit_of_isUnit_coeff_zero
  have h : (m : WittVector p R).coeff 0 = (m : R) := by
    rw [← WittVector.constantCoeff_apply, map_natCast]
  rw [h]
  have hu : IsUnit (m : ZMod p) := (ZMod.unitOfCoprime m hm).isUnit
  simpa using hu.map (ZMod.castHom (dvd_refl p) R)
theorem WittVector.isUnit_natCast_away {m : ℕ} (hm : m ≠ 0) :
    IsUnit (m : Localization.Away (p : WittVector p R)) := by
  obtain ⟨k, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.out.ne_one
  have h1 : IsUnit (p : Localization.Away (p : WittVector p R)) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : WittVector p R))
      (p : WittVector p R)
  have hc : m'.Coprime p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm')
  have h2 : IsUnit (m' : Localization.Away (p : WittVector p R)) := by
    simpa using (WittVector.isUnit_natCast_of_coprime (R := R) hc).map
      (algebraMap (WittVector p R) (Localization.Away (p : WittVector p R)))
  push_cast
  exact (h1.pow k).mul h2
end NatUnits
section AdicExtend
variable {A B : Type*} [CommRing A] [CommRing B]
theorem AdicCompletion.factorPow_evalₐ (J : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion J A) :
    Ideal.Quotient.factorPow J hle (AdicCompletion.evalₐ J n x) = AdicCompletion.evalₐ J m x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective J A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simp only [Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk J hle c
def AdicCompletion.extendFamily (J : Ideal A) (I : Ideal B) (f : A →+* B) (hf : J ≤ I.comap f)
    (n : ℕ) : AdicCompletion J A →+* B ⧸ I ^ n :=
  (Ideal.quotientMap (I ^ n) f ((Ideal.pow_right_mono hf n).trans
    (Ideal.le_comap_pow f n))).comp (AdicCompletion.evalₐ J n).toRingHom
theorem AdicCompletion.extendFamily_compat (J : Ideal A) (I : Ideal B) (f : A →+* B)
    (hf : J ≤ I.comap f) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp (AdicCompletion.extendFamily J I f hf n) =
      AdicCompletion.extendFamily J I f hf m := by
  ext x
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  simp only [AdicCompletion.extendFamily, RingHom.coe_comp, Function.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← AdicCompletion.factorPow_evalₐ J hle x, ← hy, Ideal.quotientMap_mk]
  simp only [Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]
def AdicCompletion.extendRingHom (J : Ideal A) (I : Ideal B) [IsAdicComplete I B] (f : A →+* B)
    (hf : J ≤ I.comap f) : AdicCompletion J A →+* B :=
  IsAdicComplete.liftRingHom I (AdicCompletion.extendFamily J I f hf)
    (AdicCompletion.extendFamily_compat J I f hf)
end AdicExtend
namespace ACris
section Defs
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
theorem isUnit_natCast {m : ℕ} (hm : m ≠ 0) : IsUnit (m : 𝔸) :=
  WittVector.isUnit_natCast_away hm
def dpow (n : ℕ) (x : AInf K p) : 𝔸 :=
  Ring.inverse (n.factorial : 𝔸) * algebraMap (AInf K p) 𝔸 x ^ n
theorem factorial_mul_dpow (n : ℕ) (x : AInf K p) :
    (n.factorial : 𝔸) * dpow n x = algebraMap (AInf K p) 𝔸 x ^ n := by
  rw [dpow, ← mul_assoc, Ring.mul_inverse_cancel _ (isUnit_natCast (Nat.factorial_ne_zero n)),
    one_mul]
theorem dpow_eq_iff (n : ℕ) (x : AInf K p) (y : 𝔸) :
    dpow n x = y ↔ (n.factorial : 𝔸) * y = algebraMap (AInf K p) 𝔸 x ^ n := by
  constructor
  · rintro rfl; exact factorial_mul_dpow n x
  · intro h
    have hu := isUnit_natCast (K := K) (p := p) (Nat.factorial_ne_zero n)
    rw [← factorial_mul_dpow n x] at h
    exact (hu.mul_left_cancel h).symm
@[simp]
theorem dpow_zero (x : AInf K p) : dpow 0 x = 1 := by
  rw [dpow_eq_iff]; simp
@[simp]
theorem dpow_one (x : AInf K p) : dpow 1 x = algebraMap (AInf K p) 𝔸 x := by
  rw [dpow_eq_iff]; simp
variable (K p) in

def ACrisZero : Subalgebra (AInf K p) 𝔸 :=
  Algebra.adjoin (AInf K p) {y | ∃ n : ℕ, ∃ x ∈ RingHom.ker θ, dpow n x = y}
theorem dpow_mem {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) :
    dpow n x ∈ ACrisZero K p :=
  Algebra.subset_adjoin ⟨n, x, hx, rfl⟩
variable (K p) in

abbrev ACris : Type _ :=
  AdicCompletion (Ideal.span {(p : ACrisZero K p)}) (ACrisZero K p)
end Defs
section Theta
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
variable (K p) in

def thetaAway : 𝔸 →+* K :=
  ((IsPerfectoidField.awayEquiv (K := K) p : Localization.Away (p : 𝒪) ≃ₐ[𝒪] K) :
    Localization.Away (p : 𝒪) →+* K).comp (fontaineThetaInvertP 𝒪 p)
theorem thetaAway_algebraMap (x : AInf K p) :
    thetaAway K p (algebraMap (AInf K p) 𝔸 x) = (θ x : K) := by
  rw [thetaAway, RingHom.comp_apply, fontaineThetaInvertP_algebraMap]
  exact (IsPerfectoidField.awayEquiv (K := K) p).commutes (θ x)
theorem thetaAway_dpow {x : AInf K p} (hx : x ∈ RingHom.ker θ) {n : ℕ} (hn : n ≠ 0) :
    thetaAway K p (dpow n x) = 0 := by
  have h := congrArg (thetaAway K p) (factorial_mul_dpow n x)
  rw [map_mul, map_pow, thetaAway_algebraMap, RingHom.mem_ker.1 hx, map_natCast] at h
  simp only [ZeroMemClass.coe_zero, zero_pow hn, mul_eq_zero, Nat.cast_eq_zero] at h
  exact h.resolve_left (Nat.factorial_ne_zero n)
variable (K p) in

def thetaIntegral : Subalgebra (AInf K p) 𝔸 :=
  { (normInteger K).comap (thetaAway K p) with
    algebraMap_mem' := fun x => by
      show thetaAway K p _ ∈ normInteger K
      rw [thetaAway_algebraMap]
      exact (θ x).2 }
theorem acrisZero_le_thetaIntegral : ACrisZero K p ≤ thetaIntegral K p := by
  apply Algebra.adjoin_le
  rintro _ ⟨n, x, hx, rfl⟩
  show thetaAway K p (dpow n x) ∈ normInteger K
  rcases n with _ | n
  · rw [dpow_zero, map_one]; exact one_mem _
  · rw [thetaAway_dpow hx n.succ_ne_zero]; exact zero_mem _
variable (K p) in

def thetaZero : ACrisZero K p →+* 𝒪 :=
  ((thetaAway K p).comp (ACrisZero K p).val.toRingHom).codRestrict (normInteger K)
    fun y => acrisZero_le_thetaIntegral y.2
theorem span_p_le_comap_thetaZero :
    Ideal.span {(p : ACrisZero K p)} ≤ (Ideal.span {(p : 𝒪)}).comap (thetaZero K p) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _
variable (K p) in

def theta : ACris K p →+* 𝒪 :=
  AdicCompletion.extendRingHom _ _ (thetaZero K p) span_p_le_comap_thetaZero
end Theta
section Frobenius
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
theorem exists_natCast_mul_eq_pow {n k : ℕ} (hn : n ≠ 0) (hk : n.factorization p ≤ k) :
    ∃ w : AInf K p, (n : AInf K p) * w = (p : AInf K p) ^ k := by
  set e := n.factorization p
  set d := ordCompl[p] n
  have hnd : (n : AInf K p) = (p : AInf K p) ^ e * (d : AInf K p) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self n p]
  have hu : IsUnit (d : AInf K p) :=
    WittVector.isUnit_natCast_of_coprime (Nat.coprime_comm.mp (Nat.coprime_ordCompl hp.out hn))
  refine ⟨(p : AInf K p) ^ (k - e) * ↑hu.unit⁻¹, ?_⟩
  rw [hnd]
  calc (p : AInf K p) ^ e * (d : AInf K p) * ((p : AInf K p) ^ (k - e) * ↑hu.unit⁻¹)
      = (p : AInf K p) ^ e * (p : AInf K p) ^ (k - e) * ((d : AInf K p) * ↑hu.unit⁻¹) := by ring
    _ = (p : AInf K p) ^ k := by
        rw [← pow_add, Nat.add_sub_cancel' hk, IsUnit.mul_val_inv, mul_one]
theorem factorization_factorial_le (m : ℕ) : (m.factorial).factorization p ≤ m := by
  rw [Nat.factorization_def _ hp.out]
  have h : (p - 1) * padicValNat p m.factorial = m - (p.digits m).sum :=
    sub_one_mul_padicValNat_factorial m
  have h1 : 1 ≤ p - 1 := Nat.le_sub_of_add_le hp.out.two_le
  calc padicValNat p m.factorial ≤ (p - 1) * padicValNat p m.factorial := Nat.le_mul_of_pos_left _ h1
    _ = m - (p.digits m).sum := h
    _ ≤ m := Nat.sub_le _ _
theorem exists_dpow_p_mul (m : ℕ) (y : AInf K p) :
    ∃ w : AInf K p, dpow m ((p : AInf K p) * y) = algebraMap (AInf K p) 𝔸 w := by
  obtain ⟨c, hc⟩ := exists_natCast_mul_eq_pow (K := K) (p := p) (Nat.factorial_ne_zero m)
    (factorization_factorial_le (p := p) m)
  refine ⟨c * y ^ m, ?_⟩
  rw [dpow_eq_iff, map_mul, map_pow, ← mul_assoc, ← map_natCast (algebraMap (AInf K p) 𝔸),
    ← map_mul, hc, map_mul, map_pow, mul_pow]
theorem dpow_add (n : ℕ) (x y : AInf K p) :
    dpow n (x + y) = ∑ k ∈ Finset.range (n + 1), dpow k x * dpow (n - k) y := by
  rw [dpow_eq_iff, Finset.mul_sum, map_add, add_pow]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [← Nat.choose_mul_factorial_mul_factorial hk']
  calc ((n.choose k * k.factorial * (n - k).factorial : ℕ) : 𝔸) * (dpow k x * dpow (n - k) y)
      = (n.choose k : 𝔸) * ((k.factorial * dpow k x) * ((n - k).factorial * dpow (n - k) y)) := by
        push_cast; ring
    _ = _ := by rw [factorial_mul_dpow, factorial_mul_dpow]; ring
theorem dpow_pow {m : ℕ} (hm : m ≠ 0) (k : ℕ) (x : AInf K p) :
    dpow k (x ^ m) = (((m * k).factorial / k.factorial : ℕ) : 𝔸) * dpow (m * k) x := by
  have hdvd : k.factorial ∣ (m * k).factorial :=
    Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero hm))
  rw [dpow_eq_iff, ← mul_assoc, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd, factorial_mul_dpow,
    map_pow, ← pow_mul]
theorem exists_frobenius_eq (x : AInf K p) : ∃ y : AInf K p, φ x = x ^ p + (p : AInf K p) * y := by
  have h : φ x - x ^ p ∈ Ideal.span {(p : AInf K p)} := by
    rw [mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub, map_pow,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
      WittVector.frobeniusEquiv_coeff, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨y, by rw [mul_comm, hy]; ring⟩
theorem dpow_frobenius_mem {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) :
    dpow n (φ x) ∈ ACrisZero K p := by
  obtain ⟨y, hy⟩ := exists_frobenius_eq x
  rw [hy, dpow_add]
  refine Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ ?_ ?_
  · rw [dpow_pow hp.out.ne_zero]
    exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (dpow_mem hx _)
  · obtain ⟨w, hw⟩ := exists_dpow_p_mul (n - k) y
    rw [hw]
    exact Subalgebra.algebraMap_mem _ w
variable (K p) in

def phiAway : 𝔸 →+* 𝔸 :=
  Localization.awayLift ((algebraMap (AInf K p) 𝔸).comp (φ : AInf K p →+* AInf K p)) (p : AInf K p)
    (by
      rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, map_natCast]
      exact IsLocalization.Away.algebraMap_isUnit (p : AInf K p))
theorem phiAway_algebraMap (x : AInf K p) :
    phiAway K p (algebraMap (AInf K p) 𝔸 x) = algebraMap (AInf K p) 𝔸 (φ x) :=
  IsLocalization.lift_eq _ x
theorem phiAway_dpow (n : ℕ) (x : AInf K p) : phiAway K p (dpow n x) = dpow n (φ x) := by
  symm
  rw [dpow_eq_iff, ← map_natCast (phiAway K p), ← map_mul, factorial_mul_dpow, map_pow,
    phiAway_algebraMap]
theorem phiAway_mem {y : 𝔸} (hy : y ∈ ACrisZero K p) : phiAway K p y ∈ ACrisZero K p := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rw [phiAway_dpow]
    exact dpow_frobenius_mem hx n
  | algebraMap r =>
    rw [phiAway_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
variable (K p) in

def phiZero : ACrisZero K p →+* ACrisZero K p :=
  ((phiAway K p).comp (ACrisZero K p).val.toRingHom).codRestrict (ACrisZero K p)
    fun y => phiAway_mem y.2
variable (K p) in

instance isAdicComplete : IsAdicComplete (Ideal.span {(p : ACris K p)}) (ACris K p) := by
  have h := AdicCompletion.isAdicComplete_self (Ideal.span {(p : ACrisZero K p)})
    (Submodule.fg_span_singleton _)
  have h' : (Ideal.span {(p : ACrisZero K p)}).map (algebraMap (ACrisZero K p) (ACris K p)) =
      Ideal.span {(p : ACris K p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [h'] at h
  exact h
theorem span_p_le_comap_phiZero :
    Ideal.span {(p : ACrisZero K p)} ≤ (Ideal.span {(p : ACris K p)}).comap
      ((algebraMap (ACrisZero K p) (ACris K p)).comp (phiZero K p)) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _
variable (K p) in

def phi : ACris K p →+* ACris K p :=
  AdicCompletion.extendRingHom _ _ ((algebraMap (ACrisZero K p) (ACris K p)).comp (phiZero K p))
    span_p_le_comap_phiZero
end Frobenius
end ACris
end GroundTheory.PAdicHodge


