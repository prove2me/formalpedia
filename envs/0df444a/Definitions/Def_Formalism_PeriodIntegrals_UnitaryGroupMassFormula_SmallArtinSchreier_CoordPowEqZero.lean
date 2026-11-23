-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_CoordPowEqZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_CoordPowEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:37.363945+00:00
-- url     : https://prove2.me/theorems/07901d1a-8e22-4ac2-adae-bf1839c10738
-- title:
--   Coord Pow Eq Zero
-- statement:
--   Definitions and structural lemmas for Coord Pow Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmallArtinSchreier/CoordPowEqZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitaryGroupMassFormula.ASSmall
section Alg
variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
theorem coeff_pow_pow (f : Perfection R p) (m n : ℕ) :
    Perfection.coeff R p (m + n) f ^ p ^ n = Perfection.coeff R p m f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, ← map_pow, Perfection.coeff_pow_p, ih]
theorem coord_pow_eq_zero (f : Perfection R p) {K : ℕ}
    (hK : Perfection.coeff R p 0 f ^ K = 0) (m n : ℕ) (hn : m + K ≤ n) :
    Perfection.coeff R p m f ^ p ^ n = 0 := by
  have h1 := coeff_pow_pow f 0 m
  rw [zero_add] at h1
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  rw [pow_add, pow_mul, h1]
  have hd : d < p ^ d := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
  exact pow_eq_zero_of_le (by omega) hK
theorem neg_sum_pow_p (s : Finset ℕ) (g : ℕ → R) :
    (-∑ n ∈ s, g n) ^ p = -∑ n ∈ s, g n ^ p := by
  rw [← frobenius_def, map_neg, map_sum]
  simp only [frobenius_def]
theorem sum_stable (f : Perfection R p) {K : ℕ}
    (hK : Perfection.coeff R p 0 f ^ K = 0) (m j : ℕ) :
    ∑ n ∈ Finset.range (m + K + j), Perfection.coeff R p m f ^ p ^ n
      = ∑ n ∈ Finset.range (m + K), Perfection.coeff R p m f ^ p ^ n := by
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range j)
    (fun x _ => coord_pow_eq_zero f hK m (m + K + x) (by omega)),
    add_zero]
noncomputable def sol (f : Perfection R p) (K m : ℕ) : R :=
  -∑ n ∈ Finset.range (m + K), Perfection.coeff R p m f ^ p ^ n
theorem sol_succ_pow (f : Perfection R p) {K : ℕ}
    (hK : Perfection.coeff R p 0 f ^ K = 0) (m : ℕ) :
    sol f K (m + 1) ^ p = sol f K m := by
  rw [sol, sol, neg_sum_pow_p, ← sum_stable f hK m 1, show m + 1 + K = m + K + 1 by omega]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, ← map_pow, Perfection.coeff_pow_p]
noncomputable def solPerf (f : Perfection R p) {K : ℕ}
    (hK : Perfection.coeff R p 0 f ^ K = 0) : Perfection R p :=
  ⟨fun m => sol f K m, fun m => sol_succ_pow f hK m⟩
end Alg
end PI.UnitaryGroupMassFormula.ASSmall


