-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
-- name    : GroundTheory_PAdicHodge_ExtRobbaTeich
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:10.141728+00:00
-- url     : https://prove2.me/theorems/c246e882-b304-4b24-9e17-f46126067566
-- title:
--   Ext Robba Teich
-- statement:
--   Definitions and structural lemmas for Ext Robba Teich, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean

import Mathlib
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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace GroundTheory.PAdicHodge
open Ideal
structure TeichLift (p : ℕ) (L : Type*) [NormedField L] (Γ : Type*) [CommRing Γ] where

  π : Γ

  red : Γ →+* L
  red_surjective : Function.Surjective red
  ker_red : RingHom.ker red = Ideal.span {π}
  π_mem_nonZeroDivisors : π ∈ nonZeroDivisors Γ
  isAdicComplete : IsAdicComplete (Ideal.span {π}) Γ

  int : Subring Γ
  π_mem_int : π ∈ int
  norm_red_le_one : ∀ x ∈ int, ‖red x‖ ≤ 1
  exists_mem_int : ∀ a : L, ‖a‖ ≤ 1 → ∃ x ∈ int, red x = a
  exists_eq_π_mul : ∀ x ∈ int, red x = 0 → ∃ y ∈ int, x = π * y
  mem_int_of_approx : ∀ x, (∀ N : ℕ, ∃ y ∈ int, x - y ∈ Ideal.span {π ^ N}) → x ∈ int
namespace TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
abbrev I : Ideal Γ := Ideal.span {T.π}
theorem mem_span_pow {x : Γ} {n : ℕ} : x ∈ Ideal.span {T.π ^ n} ↔ ∃ y, x = T.π ^ n * y := by
  rw [Ideal.mem_span_singleton']
  exact ⟨fun ⟨a, h⟩ => ⟨a, by rw [← h, mul_comm]⟩, fun ⟨a, h⟩ => ⟨a, by rw [h, mul_comm]⟩⟩
theorem I_pow (n : ℕ) : T.I ^ n = Ideal.span {T.π ^ n} := Ideal.span_singleton_pow _ _
theorem red_eq_zero_iff {x : Γ} : T.red x = 0 ↔ ∃ y, x = T.π * y := by
  rw [← RingHom.mem_ker, T.ker_red, ← pow_one T.π, T.mem_span_pow]
theorem π_pow_mul_mem {m n : ℕ} (h : n ≤ m) (x : Γ) : T.π ^ m * x ∈ Ideal.span {T.π ^ n} :=
  T.mem_span_pow.2 ⟨T.π ^ (m - n) * x, by rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]⟩
def quotEquiv : (Γ ⧸ T.I) ≃+* L :=
  (Ideal.quotEquivOfEq T.ker_red.symm).trans (RingHom.quotientKerEquivOfSurjective T.red_surjective)
theorem quotEquiv_mk (x : Γ) : T.quotEquiv (Ideal.Quotient.mk T.I x) = T.red x := rfl
instance charP_quot : CharP (Γ ⧸ T.I) p :=
  charP_of_injective_ringHom (f := T.quotEquiv.symm.toRingHom) T.quotEquiv.symm.injective p
variable (p) in

def toPerfection : L →+* Perfection (Γ ⧸ T.I) p :=
  Perfection.lift p L (Γ ⧸ T.I) T.quotEquiv.symm.toRingHom
def teich : L →*₀ Γ :=
  haveI := T.isAdicComplete
  (Perfection.teichmuller₀ p T.I).comp (T.toPerfection p).toMonoidWithZeroHom
theorem coeff_toPerfection (a : L) (n : ℕ) :
    Perfection.coeff (Γ ⧸ T.I) p n (T.toPerfection p a) =
      T.quotEquiv.symm ((((frobeniusEquiv L p).symm : L →+* L))^[n] a) := rfl
theorem red_teich (a : L) : T.red (T.teich a) = a := by
  haveI := T.isAdicComplete
  rw [← quotEquiv_mk]
  show T.quotEquiv (Ideal.Quotient.mk T.I (Perfection.teichmuller₀ p T.I (T.toPerfection p a))) = a
  rw [Perfection.mk_teichmuller₀, coeff_toPerfection]
  simp
@[simp] theorem teich_zero : T.teich 0 = 0 := map_zero _
@[simp] theorem teich_one : T.teich 1 = 1 := map_one _
theorem red_sub_teich_red (x : Γ) : T.red (x - T.teich (T.red x)) = 0 := by
  rw [map_sub, red_teich, sub_self]
def tail (x : Γ) : Γ := (T.red_eq_zero_iff.1 (T.red_sub_teich_red x)).choose
def coeff (x : Γ) (n : ℕ) : L := T.red (T.tail^[n] x)
@[simp] theorem coeff_zero (x : Γ) : T.coeff x 0 = T.red x := rfl
def finSum (a : ℕ → L) (n : ℕ) : Γ := ∑ i ∈ Finset.range n, T.π ^ i * T.teich (a i)
@[simp] theorem finSum_zero (a : ℕ → L) : T.finSum a 0 = 0 := by simp [finSum]
theorem finSum_succ (a : ℕ → L) (n : ℕ) :
    T.finSum a (n + 1) = T.finSum a n + T.π ^ n * T.teich (a n) := by
  simp [finSum, Finset.sum_range_succ]
theorem finSum_sub_finSum_mem (a : ℕ → L) {m n : ℕ} (h : m ≤ n) :
    T.finSum a n - T.finSum a m ∈ Ideal.span {T.π ^ m} := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [finSum_succ, add_sub_right_comm]
    exact add_mem ih (T.π_pow_mul_mem hmn _)
def partialSum (x : Γ) (n : ℕ) : Γ := T.finSum (T.coeff x) n
def ofCoeff (a : ℕ → L) : Γ :=
  haveI := T.isAdicComplete
  (IsPrecomplete.prec' (I := T.I) (T.finSum a) fun {m n} hmn => by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow, ← neg_sub]
    exact neg_mem (T.finSum_sub_finSum_mem a hmn)).choose
def PrefixLe (x : Γ) (n : ℕ) (b : ℝ) : Prop := ∀ m ≤ n, ‖T.coeff x m‖ ≤ b
def coeffHolderExp (p n : ℕ) : ℝ := ((p ^ (∑ i ∈ Finset.range (n + 1), i) : ℕ) : ℝ)⁻¹
end TeichLift
end GroundTheory.PAdicHodge


