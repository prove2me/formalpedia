-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
-- name    : GroundTheory_PAdicHodge_ACrisLog
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:45.023609+00:00
-- url     : https://prove2.me/theorems/7db40852-eb31-54cf-90df-20d08b0cbd48
-- title:
--   ACris Log
-- statement:
--   Definitions and structural lemmas for ACris Log, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_mu

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
section AdicSum
variable {R : Type*} [CommRing R] (I : Ideal R)
def IsAdicSum (a : ℕ → R) (s : R) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ M, N ≤ M → s - ∑ n ∈ Finset.range M, a n ∈ I ^ k
variable {I}
theorem sum_Ico_mem_of_forall {J : Ideal R} {a : ℕ → R} {N : ℕ} (h : ∀ n, N ≤ n → a n ∈ J)
    (M : ℕ) : ∑ n ∈ Finset.Ico N M, a n ∈ J :=
  Ideal.sum_mem _ fun n hn => h n (Finset.mem_Ico.1 hn).1
theorem exists_isAdicSum [IsPrecomplete I R] {a : ℕ → R}
    (ha : ∀ k, ∃ N, ∀ n, N ≤ n → a n ∈ I ^ k) : ∃ s, IsAdicSum I a s := by
  choose g hg using ha
  set G : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), g j
  have hG : ∀ k, g k ≤ G k := fun k =>
    Finset.single_le_sum (f := g) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
  have hGm : Monotone G := fun m n hmn =>
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hmn))
  have hdiff : ∀ k M, G k ≤ M →
      ∑ n ∈ Finset.range M, a n - ∑ n ∈ Finset.range (G k), a n ∈ I ^ k := fun k M hM => by
    rw [← Finset.sum_range_add_sum_Ico _ hM, add_sub_cancel_left]
    exact sum_Ico_mem_of_forall (fun n hn => hg k n ((hG k).trans hn)) M
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance
    (f := fun k => ∑ n ∈ Finset.range (G k), a n) (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have := hdiff m (G n) (hGm hmn)
      rw [← neg_sub]
      exact neg_mem this)
  refine ⟨L, fun k => ⟨G k, fun M hM => ?_⟩⟩
  have h1 := hL k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hdiff k M hM
  have := add_mem (neg_mem h1) (neg_mem h2)
  convert this using 1
  ring
theorem IsAdicSum.map {S : Type*} [CommRing S] {J : Ideal S} (f : R →+* S) (hf : I ≤ J.comap f)
    {a : ℕ → R} {s : R} (hs : IsAdicSum I a s) : IsAdicSum J (fun n => f (a n)) (f s) := fun k => by
  obtain ⟨N, hN⟩ := hs k
  refine ⟨N, fun M hM => ?_⟩
  rw [← map_sum, ← map_sub]
  exact (Ideal.pow_right_mono hf k).trans (Ideal.le_comap_pow f k) (hN M hM)
end AdicSum
namespace ACris
section Log
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
omit [IsPerfectoidField K p] in

theorem pow_dvd_factorial {k n : ℕ} (h : p * k ≤ n) : p ^ k ∣ n.factorial :=
  ((pow_dvd_pow p (by rw [padicValNat_factorial_mul]; omega)).trans pow_padicValNat_dvd).trans
    (Nat.factorial_dvd_factorial h)
theorem natCast_mem_pow {k n : ℕ} (h : p ^ k ∣ n) :
    (n : ACrisZero K p) ∈ Ideal.span {(p : ACrisZero K p)} ^ k := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, Nat.cast_pow, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
theorem map_span_p_pow (k : ℕ) :
    (Ideal.span {(p : ACrisZero K p)} ^ k).map (algebraMap (ACrisZero K p) (ACris K p)) = 𝔭 ^ k := by
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]
theorem algebraMap_mem_pow {k : ℕ} {y : ACrisZero K p} (hy : y ∈ Ideal.span {(p : ACrisZero K p)} ^ k) :
    algebraMap (ACrisZero K p) (ACris K p) y ∈ 𝔭 ^ k := by
  rw [← map_span_p_pow]
  exact Ideal.mem_map_of_mem _ hy
def dpowZero {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) : ACrisZero K p :=
  ⟨dpow n x, dpow_mem hx n⟩
def logTermZero {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) : ACrisZero K p :=
  (-1) ^ n * (n.factorial : ACrisZero K p) * dpowZero hx (n + 1)
def logTerm {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) : ACris K p :=
  algebraMap (ACrisZero K p) (ACris K p) (logTermZero hx n)
theorem logTermZero_mem {x : AInf K p} (hx : x ∈ RingHom.ker θ) {k n : ℕ} (h : p * k ≤ n) :
    logTermZero hx n ∈ Ideal.span {(p : ACrisZero K p)} ^ k :=
  Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (natCast_mem_pow (pow_dvd_factorial h)))
theorem logTerm_mem {x : AInf K p} (hx : x ∈ RingHom.ker θ) {k n : ℕ} (h : p * k ≤ n) :
    logTerm hx n ∈ 𝔭 ^ k :=
  algebraMap_mem_pow (logTermZero_mem hx h)
theorem exists_isAdicSum_logTerm {x : AInf K p} (hx : x ∈ RingHom.ker θ) :
    ∃ s, IsAdicSum 𝔭 (logTerm hx) s :=
  exists_isAdicSum fun k => ⟨p * k, fun _ hn => logTerm_mem hx hn⟩
def log {x : AInf K p} (hx : x ∈ RingHom.ker θ) : ACris K p :=
  (exists_isAdicSum_logTerm hx).choose
theorem mu_mem_ker {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : AInf.mu (K := K) ε ∈ RingHom.ker θ :=
  RingHom.mem_ker.2 (AInf.fontaineTheta_mu hε)
def periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : ACris K p :=
  log (mu_mem_ker hε)
section Theta
variable [CharZero K]
end Theta
end Log
end ACris
namespace ACris
section Divisibility
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
end Divisibility
end ACris
end GroundTheory.PAdicHodge


