-- Prove2me | Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
-- name    : Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:56.088799+00:00
-- url     : https://prove2.me/theorems/03b87a2d-f747-4e22-87ac-1e9a780d9935
-- title:
--   Coeff Frob Of Not Dvd
-- statement:
--   Definitions and structural lemmas for Coeff Frob Of Not Dvd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/CoeffFrobOfNotDvd.lean

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
namespace Formalism.BaseCaseIdentities
variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}
theorem le_add_coe_iff (x : WithTop ℝ) (w c : ℝ) :
    (w : WithTop ℝ) ≤ x + (c : WithTop ℝ) ↔ ((w - c : ℝ) : WithTop ℝ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe y => rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]
theorem hasWt_iff : HasWt v r w f ↔
    ∀ A : Z →₀ ℕ, ((w - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) ≤ v (coeff A f) := by
  unfold HasWt
  exact forall_congr' fun A => le_add_coe_iff _ _ _
theorem HasWt.X (d : Z) : HasWt v r r (X d : MvPowerSeries Z k) := by
  classical
  rw [hasWt_iff]
  intro A
  rw [coeff_X]
  split_ifs with h
  · subst h; simp
  · simp
theorem coeff_frob_of_dvd {N : ℕ} {B : Z →₀ ℕ} (h : ∀ d, N ∣ B d) (f : MvPowerSeries Z k) :
    coeff B (frob N f) = (coeff (B.mapRange (· / N) (Nat.zero_div N)) f) ^ N := by
  show frob N f B = _
  unfold frob
  rw [if_pos h]
theorem coeff_frob_of_not_dvd {N : ℕ} {B : Z →₀ ℕ} (h : ¬ ∀ d, N ∣ B d) (f : MvPowerSeries Z k) :
    coeff B (frob N f) = 0 := by
  show frob N f B = _
  unfold frob
  rw [if_neg h]
theorem smul_mapRange_div {N : ℕ} {B : Z →₀ ℕ} (h : ∀ d, N ∣ B d) :
    N • (B.mapRange (· / N) (Nat.zero_div N)) = B := by
  ext d
  simp only [Finsupp.coe_smul, Pi.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact Nat.mul_div_cancel' (h d)
theorem HasWt.frob (hf : HasWt v r w f) (N : ℕ) : HasWt v r ((N : ℝ) * w) (frob N f) := by
  rw [hasWt_iff] at *
  intro B
  by_cases h : ∀ d, N ∣ B d
  · rw [coeff_frob_of_dvd h, v.map_pow]
    set B' := B.mapRange (· / N) (Nat.zero_div N) with hB'
    have hB : B = N • B' := (smul_mapRange_div h).symm
    have hd : ((B.degree : ℕ) : ℝ) = (N : ℝ) * ((B'.degree : ℕ) : ℝ) := by
      rw [hB, map_nsmul]; simp
    have h1 := nsmul_le_nsmul_right (hf B') N
    refine le_trans (le_of_eq ?_) h1
    rw [← WithTop.coe_nsmul, hd]
    congr 1
    rw [nsmul_eq_mul]; ring
  · rw [coeff_frob_of_not_dvd h]; simp
end Formalism.BaseCaseIdentities


