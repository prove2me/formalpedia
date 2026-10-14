-- Prove2me | solution 1 for ActuarialFoundations.fa_S_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-12T16:27:17.680739+00:00
-- url     : https://prove2.me/submissions/bdb9e764-0a47-4f2d-b7cb-30e2e36bdb2e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_actuarial_faAnnuityArrearsOriginal
import Definitions.Def_actuarial_faAnnuityOriginal
import Definitions.Def_actuarial_faAssuranceOriginal
import Definitions.Def_actuarial_faDeaths
import Definitions.Def_actuarial_faDeferredAnnuityOriginal
import Definitions.Def_actuarial_faDeferredAssuranceOriginal
import Definitions.Def_actuarial_faDeferredMortality
import Definitions.Def_actuarial_faDiscountedDeaths
import Definitions.Def_actuarial_faDiscountedLives
import Definitions.Def_actuarial_faEndowmentAssuranceOriginal
import Definitions.Def_actuarial_faFiniteCohortValid
import Definitions.Def_actuarial_faIncreasingAnnuityOriginal
import Definitions.Def_actuarial_faIncreasingAssuranceOriginal
import Definitions.Def_actuarial_faIncreasingTemporaryAnnuityOriginal
import Definitions.Def_actuarial_faIncreasingTermAssuranceOriginal
import Definitions.Def_actuarial_faM
import Definitions.Def_actuarial_faMultiYearMortality
import Definitions.Def_actuarial_faN
import Definitions.Def_actuarial_faOneYearMortality
import Definitions.Def_actuarial_faPureEndowmentOriginal
import Definitions.Def_actuarial_faR
import Definitions.Def_actuarial_faRAbsolute
import Definitions.Def_actuarial_faS
import Definitions.Def_actuarial_faSurvival
import Definitions.Def_actuarial_faTemporaryAnnuityOriginal
import Definitions.Def_actuarial_faTermAssuranceOriginal

namespace FaCoreScratch

private theorem tail_succ (f : ℕ → ℝ) (ω x : ℕ) (hx : x < ω) :
    (∑ k ∈ Finset.range (ω-x), f (x+k)) = f x + ∑ k ∈ Finset.range (ω-(x+1)), f (x+1+k) := by
  obtain ⟨m, hm⟩ : ∃ m, ω - x = m + 1 := ⟨ω - x - 1, by omega⟩
  have h2 : ω - (x+1) = m := by omega
  rw [hm, h2, Finset.sum_range_succ']
  simp only [add_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1; omega

private theorem tail_split (f : ℕ → ℝ) (ω x n : ℕ) (h : x + n ≤ ω) :
    (∑ k ∈ Finset.range (ω-x), f (x+k)) =
      (∑ k ∈ Finset.range n, f (x+k)) + ∑ k ∈ Finset.range (ω-(x+n)), f (x+n+k) := by
  have h1 : ω - x = n + (ω - (x+n)) := by omega
  rw [h1, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1; omega

private theorem double_sum (n : ℕ) : ∀ g : ℕ → ℝ,
    (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (n-k), g (k+j)) =
      ∑ m ∈ Finset.range n, ((m+1 : ℕ) : ℝ) * g m := by
  induction n with
  | zero => intro g; simp
  | succ n ih =>
    intro g
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun m => ((m+1 : ℕ) : ℝ) * g m)]
    have e1 : ∀ k ∈ Finset.range n,
        (∑ j ∈ Finset.range (n + 1 - (k+1)), g (k + 1 + j)) =
          ∑ j ∈ Finset.range (n - k), (fun i => g (i+1)) (k + j) := by
      intro k _
      have : n + 1 - (k+1) = n - k := by omega
      rw [this]
      refine Finset.sum_congr rfl fun j _ => ?_
      (try simp only); congr 1; omega
    rw [Finset.sum_congr rfl e1, ih (fun i => g (i+1))]
    simp only [Nat.sub_zero, zero_add, Finset.sum_range_succ' (fun j => g j)]
    have e2 : ∀ m ∈ Finset.range n, ((m + 1 + 1 : ℕ) : ℝ) * g (m + 1) =
        ((m+1 : ℕ) : ℝ) * g (m+1) + g (m+1) := by
      intro m _; push_cast; ring
    rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib]
    push_cast
    ring

private theorem tail_tail (f : ℕ → ℝ) (ω x : ℕ) :
    (∑ k ∈ Finset.range (ω-x), ∑ j ∈ Finset.range (ω-(x+k)), f (x+k+j)) =
      ∑ k ∈ Finset.range (ω-x), ((k+1 : ℕ) : ℝ) * f (x+k) := by
  have := double_sum (ω - x) (fun m => f (x+m))
  rw [← this]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ω - (x+k) = ω - x - k := by omega
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  show f _ = f _; congr 1; omega

private theorem tail_tail_finite (f : ℕ → ℝ) (ω x n : ℕ) (h : x + n ≤ ω) :
    (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (ω-(x+k)), f (x+k+j)) =
      (∑ k ∈ Finset.range n, ((k+1 : ℕ) : ℝ) * f (x+k)) +
        (n : ℝ) * ∑ j ∈ Finset.range (ω-(x+n)), f (x+n+j) := by
  have e : ∀ k ∈ Finset.range n,
      (∑ j ∈ Finset.range (ω-(x+k)), f (x+k+j)) =
        (∑ j ∈ Finset.range (n-k), (fun m => f (x+m)) (k+j)) +
          ∑ j ∈ Finset.range (ω-(x+n)), f (x+n+j) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [tail_split f ω (x+k) (n-k) (by omega)]
    have : x + k + (n - k) = x + n := by omega
    rw [this]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    (try simp only); congr 1; omega
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, double_sum n (fun m => f (x+m))]
  simp

end FaCoreScratch

open FaCoreScratch

namespace ActuarialFoundations

private theorem faSol_N_rec (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hx : x < ω) :
    faN l v ω x = faDiscountedLives l v x + faN l v ω (x+1) := by
  unfold faN; exact tail_succ _ ω x hx

private theorem faSol_M_rec (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hx : x < ω) :
    faM l v ω x = faDiscountedDeaths l v x + faM l v ω (x+1) := by
  unfold faM; exact tail_succ _ ω x hx

private theorem faSol_S_rec (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hx : x < ω) :
    faS l v ω x = faN l v ω x + faS l v ω (x+1) := by
  unfold faS; exact tail_succ (fun y => faN l v ω y) ω x hx

private theorem faSol_R_rec (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hx : x < ω) :
    faR l v ω x = faM l v ω x + faR l v ω (x+1) := by
  unfold faR; exact tail_succ (fun y => faM l v ω y) ω x hx

private theorem faSol_N_split (l : ℕ → ℝ) (v : ℝ) (ω x n : ℕ) (h : x + n ≤ ω) :
    faN l v ω x - faN l v ω (x+n) = ∑ k ∈ Finset.range n, faDiscountedLives l v (x+k) := by
  unfold faN; rw [tail_split _ ω x n h]; ring

private theorem faSol_M_split (l : ℕ → ℝ) (v : ℝ) (ω x n : ℕ) (h : x + n ≤ ω) :
    faM l v ω x - faM l v ω (x+n) = ∑ k ∈ Finset.range n, faDiscountedDeaths l v (x+k) := by
  unfold faM; rw [tail_split _ ω x n h]; ring

private theorem faSol_S_weighted (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) :
    faS l v ω x = ∑ k ∈ Finset.range (ω-x), ((k+1 : ℕ) : ℝ) * faDiscountedLives l v (x+k) := by
  unfold faS faN; exact tail_tail _ ω x

private theorem faSol_R_weighted (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) :
    faR l v ω x = ∑ k ∈ Finset.range (ω-x), ((k+1 : ℕ) : ℝ) * faDiscountedDeaths l v (x+k) := by
  unfold faR faM; exact tail_tail _ ω x

private theorem faSol_S_split (l : ℕ → ℝ) (v : ℝ) (ω x n : ℕ) (h : x + n ≤ ω) :
    faS l v ω x - faS l v ω (x+n) - (n : ℝ) * faN l v ω (x+n) =
      ∑ k ∈ Finset.range n, ((k+1 : ℕ) : ℝ) * faDiscountedLives l v (x+k) := by
  have h1 : faS l v ω x = (∑ k ∈ Finset.range n, faN l v ω (x+k)) + faS l v ω (x+n) := by
    unfold faS; exact tail_split (fun y => faN l v ω y) ω x n h
  have h2 := tail_tail_finite (faDiscountedLives l v) ω x n h
  have h3 : (∑ k ∈ Finset.range n, faN l v ω (x+k)) =
      ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (ω-(x+k)), faDiscountedLives l v (x+k+j) := rfl
  have h4 : faN l v ω (x+n) = ∑ j ∈ Finset.range (ω-(x+n)), faDiscountedLives l v (x+n+j) := rfl
  rw [h1, h3, h2, h4]; ring

private theorem faSol_R_split (l : ℕ → ℝ) (v : ℝ) (ω x n : ℕ) (h : x + n ≤ ω) :
    faR l v ω x - faR l v ω (x+n) - (n : ℝ) * faM l v ω (x+n) =
      ∑ k ∈ Finset.range n, ((k+1 : ℕ) : ℝ) * faDiscountedDeaths l v (x+k) := by
  have h1 : faR l v ω x = (∑ k ∈ Finset.range n, faM l v ω (x+k)) + faR l v ω (x+n) := by
    unfold faR; exact tail_split (fun y => faM l v ω y) ω x n h
  have h2 := tail_tail_finite (faDiscountedDeaths l v) ω x n h
  have h3 : (∑ k ∈ Finset.range n, faM l v ω (x+k)) =
      ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (ω-(x+k)), faDiscountedDeaths l v (x+k+j) := rfl
  have h4 : faM l v ω (x+n) = ∑ j ∈ Finset.range (ω-(x+n)), faDiscountedDeaths l v (x+n+j) := rfl
  rw [h1, h3, h2, h4]; ring

private theorem faSol_R_absolute (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) :
    faRAbsolute l v ω x = faR l v ω x + (x : ℝ) * faM l v ω x := by
  rw [faSol_R_weighted]; unfold faRAbsolute faM
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

/-- Telescoping of `C + (1-v) D`. -/
private theorem faSol_MN_telescope (l : ℕ → ℝ) (v : ℝ) (x m : ℕ) :
    (∑ k ∈ Finset.range m, (faDiscountedDeaths l v (x+k) + (1-v) * faDiscountedLives l v (x+k)))
      = faDiscountedLives l v x - faDiscountedLives l v (x+m) := by
  have e : ∀ k ∈ Finset.range m,
      faDiscountedDeaths l v (x+k) + (1-v) * faDiscountedLives l v (x+k) =
        faDiscountedLives l v (x+k) - faDiscountedLives l v (x+(k+1)) := by
    intro k _
    unfold faDiscountedDeaths faDiscountedLives faDeaths
    rw [show x + (k+1) = x + k + 1 by ring, pow_succ]; ring
  rw [Finset.sum_congr rfl e, Finset.sum_range_sub' (fun k => faDiscountedLives l v (x+k))]
  simp

private theorem faSol_antitone (l : ℕ → ℝ) (ω : ℕ) (h : faFiniteCohortValid l ω) (x : ℕ) :
    ∀ n, x + n ≤ ω → l (x+n) ≤ l x := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := h.2.2 (x+n) (by omega)
    have h2 := ih (by omega)
    rw [← add_assoc]; linarith

private theorem faSol_deaths_sum (l : ℕ → ℝ) (x m : ℕ) :
    (∑ k ∈ Finset.range m, faDeaths l (x+k)) = l x - l (x+m) := by
  unfold faDeaths
  have := Finset.sum_range_sub' (fun k => l (x+k)) m
  simpa [add_assoc] using this

private theorem faSol_term (v L c : ℝ) (hv : v ≠ 0) (hL : L ≠ 0) (x a : ℕ) :
    v^a * (c / L) = v^(x+a) * c / (v^x * L) := by
  field_simp
  try ring


private theorem faSol_fundamental_raw (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hx : x ≤ ω) (hl : l x ≠ 0)
    (hω : l ω = 0) :
    faAssuranceOriginal l v ω x + (1-v)*faAnnuityOriginal l v ω x = 1 := by
  unfold faAssuranceOriginal faAnnuityOriginal
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have e : ∀ k ∈ Finset.range (ω-x),
      v^(k+1) * (faDeaths l (x+k) / l x) + (1-v) * (v^k * (l (x+k) / l x)) =
        (fun i => v^i * (l (x+i) / l x)) k - (fun i => v^i * (l (x+i) / l x)) (k+1) := by
    intro k _
    simp only [faDeaths, show x + (k+1) = x + k + 1 by ring, pow_succ]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_range_sub', show x + (ω - x) = ω by omega, hω]
  simp [hl]

section Valuation
variable (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hv : v ≠ 0) (hl : l x ≠ 0)
include hv hl

private theorem faSol_annuity : faAnnuityOriginal l v ω x = faN l v ω x / faDiscountedLives l v x := by
  unfold faAnnuityOriginal faN faDiscountedLives
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  try ring

private theorem faSol_assurance : faAssuranceOriginal l v ω x = faM l v ω x / faDiscountedLives l v x := by
  unfold faAssuranceOriginal faM faDiscountedLives faDiscountedDeaths
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  try ring

private theorem faSol_inc_annuity :
    faIncreasingAnnuityOriginal l v ω x = faS l v ω x / faDiscountedLives l v x := by
  rw [faSol_S_weighted]
  unfold faIncreasingAnnuityOriginal faDiscountedLives
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  try ring

private theorem faSol_inc_assurance :
    faIncreasingAssuranceOriginal l v ω x = faR l v ω x / faDiscountedLives l v x := by
  rw [faSol_R_weighted]
  unfold faIncreasingAssuranceOriginal faDiscountedLives faDiscountedDeaths
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  try ring

private theorem faSol_pure_endowment (n : ℕ) :
    faPureEndowmentOriginal l v x n = faDiscountedLives l v (x+n) / faDiscountedLives l v x := by
  unfold faPureEndowmentOriginal faSurvival faDiscountedLives
  field_simp
  try ring

private theorem faSol_temp_annuity (n : ℕ) (h : x + n ≤ ω) :
    faTemporaryAnnuityOriginal l v x n =
      (faN l v ω x - faN l v ω (x+n)) / faDiscountedLives l v x := by
  rw [faSol_N_split l v ω x n h]
  unfold faTemporaryAnnuityOriginal faDiscountedLives
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  try ring

private theorem faSol_term_assurance (n : ℕ) (h : x + n ≤ ω) :
    faTermAssuranceOriginal l v x n =
      (faM l v ω x - faM l v ω (x+n)) / faDiscountedLives l v x := by
  rw [faSol_M_split l v ω x n h]
  unfold faTermAssuranceOriginal faDiscountedLives faDiscountedDeaths
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  try ring

private theorem faSol_endowment (n : ℕ) (h : x + n ≤ ω) :
    faEndowmentAssuranceOriginal l v x n =
      (faM l v ω x - faM l v ω (x+n) + faDiscountedLives l v (x+n)) / faDiscountedLives l v x := by
  unfold faEndowmentAssuranceOriginal
  rw [faSol_term_assurance l v ω x hv hl n h, faSol_pure_endowment l v x hv hl n, add_div]

private theorem faSol_inc_temp_annuity (n : ℕ) (h : x + n ≤ ω) :
    faIncreasingTemporaryAnnuityOriginal l v x n =
      (faS l v ω x - faS l v ω (x+n) - (n : ℝ) * faN l v ω (x+n)) / faDiscountedLives l v x := by
  rw [faSol_S_split l v ω x n h]
  unfold faIncreasingTemporaryAnnuityOriginal faDiscountedLives
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  try ring

private theorem faSol_inc_term_assurance (n : ℕ) (h : x + n ≤ ω) :
    faIncreasingTermAssuranceOriginal l v x n =
      (faR l v ω x - faR l v ω (x+n) - (n : ℝ) * faM l v ω (x+n)) / faDiscountedLives l v x := by
  rw [faSol_R_split l v ω x n h]
  unfold faIncreasingTermAssuranceOriginal faDiscountedLives faDiscountedDeaths
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  try ring

private theorem faSol_deferred_annuity (m : ℕ) :
    faDeferredAnnuityOriginal l v ω x m = faN l v ω (x+m) / faDiscountedLives l v x := by
  unfold faDeferredAnnuityOriginal faN faDiscountedLives
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  try ring

private theorem faSol_deferred_assurance (m : ℕ) :
    faDeferredAssuranceOriginal l v ω x m = faM l v ω (x+m) / faDiscountedLives l v x := by
  unfold faDeferredAssuranceOriginal faM faDiscountedLives faDiscountedDeaths
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  try ring

private theorem faSol_arrears (hω : l ω = 0) (hx : x < ω) :
    faAnnuityArrearsOriginal l v ω x =
      (faN l v ω x - faDiscountedLives l v x) / faDiscountedLives l v x := by
  rw [faSol_N_rec l v ω x hx, add_sub_cancel_left]
  obtain ⟨m, hm⟩ : ∃ m, ω - x = m + 1 := ⟨ω - x - 1, by omega⟩
  have h2 : ω - (x+1) = m := by omega
  have h3 : x + m + 1 = ω := by omega
  unfold faAnnuityArrearsOriginal faN faDiscountedLives
  rw [hm, h2, Finset.sum_range_succ, h3, hω, zero_div, mul_zero, add_zero, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show x + 1 + k = x + k + 1 by ring]
  field_simp
  try ring

end Valuation

end ActuarialFoundations

open ActuarialFoundations

theorem solution (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hx : x < ω) : faS l v ω x = faN l v ω x + faS l v ω (x+1) := by
  exact faSol_S_rec l v ω x hx
