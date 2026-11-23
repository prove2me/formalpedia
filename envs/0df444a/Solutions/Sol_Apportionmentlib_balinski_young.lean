-- Prove2me | solution 1 for Apportionmentlib.balinski_young
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:44:04.968374+00:00
-- url     : https://prove2.me/submissions/264ae83f-a3f0-4211-b327-d2d6a9c11ede

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Rat.Floor
public import Definitions.Def_Apportionmentlib_Utils
public import Definitions.Def_Apportionmentlib_Basic
public import Theorems.Thm_Apportionmentlib_Rule_seats_le
public import Theorems.Thm_Apportionmentlib_Rule_le_seats
public import Theorems.Thm_Vector_sum_four

section
@[expose] public section
open BigOperators
namespace Apportionmentlib
section BalinskiYoung
variable (rule : Rule) {a b c : ℕ} {App : Apportionment 4}
private lemma large_votes_sum (h : a + b + c = 24) : (large a b c).votes.sum = 96 := by
  rw [Vector.sum_four]
  change 72 + a + b + c = 96
  omega
private lemma small_votes_sum (h : a + b + c = 14) : (small a b c).votes.sum = 85 := by
  rw [Vector.sum_four]
  change 71 + a + b + c = 85
  omega
private lemma seats_sum {e : Election 4} (h : (e.houseSize : ℕ) = 12)
    (h_App : App ∈ rule.res e) : App[0] + App[1] + App[2] + App[3] = 12 := by
  rw [← Vector.sum_four, rule.house_size_feasibility e App h_App, h]
variable [IsQuotaRule rule]
private lemma large_seats (h_App : App ∈ rule.res (large a b c)) (h : a + b + c = 24 := by decide) :
    App[0] = 9 ∧ App[1] + App[2] + App[3] = 3 := by
  have h_le : App[0] ≤ 9 := rule.seats_le (large a b c) 0 9
    (by rw [Election.quota, large_votes_sum h]; norm_num [large]) App h_App
  have h_ge : 9 ≤ App[0] := rule.le_seats (large a b c) 0 9
    (by rw [Election.quota, large_votes_sum h]; norm_num [large]) App h_App
  have h_sum := seats_sum rule (e := large a b c) rfl h_App
  omega
private lemma small_seats (h_App : App ∈ rule.res (small a b c)) (h : a + b + c = 14 := by decide) :
    10 ≤ App[0] ∧ App[1] + App[2] + App[3] ≤ 2 := by
  have h_ge : 10 ≤ App[0] := rule.le_seats (small a b c) 0 10
    (by rw [Election.quota, small_votes_sum h]; norm_num [small]) App h_App
  have h_sum := seats_sum rule (e := small a b c) rfl h_App
  omega
private lemma large_two_seats (i : Fin 4) (h_App : App ∈ rule.res (large a b c))
    (h : a + b + c = 24 := by decide) (h_votes : (large a b c).votes[i] = 16 := by decide) :
    App[i] = 2 := by
  have h_le := rule.seats_le (large a b c) i 2
    (by rw [Election.quota, h_votes, large_votes_sum h]; norm_num [large]) App h_App
  have h_ge := rule.le_seats (large a b c) i 2
    (by rw [Election.quota, h_votes, large_votes_sum h]; norm_num [large]) App h_App
  omega
private lemma small_one_seat (i : Fin 4) (h_App : App ∈ rule.res (small a b c))
    (h : a + b + c = 14 := by decide) (h_votes : (small a b c).votes[i] = 8 := by decide) :
    1 ≤ App[i] :=
  rule.le_seats (small a b c) i 1
    (by rw [Election.quota, h_votes, small_votes_sum h]; norm_num [small]) App h_App
private lemma seats_le_of_votes_le (h_mono : IsPopulationMonotone rule) {a' b' c' : ℕ}
    {AppL AppS : Apportionment 4} (i : Fin 4) (h_AppL : AppL ∈ rule.res (large a b c))
    (h_AppS : AppS ∈ rule.res (small a' b' c'))
    (hl : a + b + c = 24 := by decide) (hs : a' + b' + c' = 14 := by decide)
    (h_pos : 0 < (small a' b' c').votes[i] := by decide)
    (h_votes : (large a b c).votes[i] ≤ (small a' b' c').votes[i] := by decide) :
    AppL[i] ≤ AppS[i] := by
  have h_ratio : (small a' b' c').votes[i] * (large a b c).votes[(0 : Fin 4)] >
      (small a' b' c').votes[(0 : Fin 4)] * (large a b c).votes[i] := by
    change (small a' b' c').votes[i] * 72 > 71 * (large a b c).votes[i]
    omega
  have h_par := h_mono.population_monotone (large a b c) (small a' b' c') i 0 rfl h_ratio
    AppL h_AppL AppS h_AppS
  have hL : AppL[(0 : Fin 4)] = 9 := (large_seats rule h_AppL hl).1
  have hS : 10 ≤ AppS[(0 : Fin 4)] := (small_seats rule h_AppS hs).1
  omega
end BalinskiYoung
end Apportionmentlib
end
end

set_option autoImplicit false
@[expose] public section
public section
open BigOperators
open Apportionmentlib
variable (rule : Rule) {a b c : ℕ} {App : Apportionment 4}
variable [IsQuotaRule rule]
namespace Apportionmentlib
theorem _root_.solution : ¬IsPopulationMonotone rule := by
  by_contra h_mono
  -- `A = (72, 16, 4, 4)`: parties 0 and 1 take 9 and 2 seats, so one of parties 2 and 3 takes the
  -- last one. The two chains refuting the two choices are mirror images in parties 2 and 3.
  obtain ⟨A, hA⟩ := rule.non_emptiness (large 16 4 4)
  have hA1 : A[1] = 2 := large_two_seats rule 1 hA
  have hA123 : A[1] + A[2] + A[3] = 3 := (large_seats rule hA).2
  rcases (show A[2] = 1 ∨ A[3] = 1 by omega) with hA2 | hA3
  · -- `P = (71, 2, 4, 8)`: party 2 keeps its seat, party 3's quota exceeds 1; party 1 gets none.
    obtain ⟨P, hP⟩ := rule.non_emptiness (small 2 4 8)
    have hP2 : A[2] ≤ P[2] := seats_le_of_votes_le rule h_mono 2 hA hP
    have hP3 : 1 ≤ P[3] := small_one_seat rule 3 hP
    have hP1 : P[1] = 0 := by have := (small_seats rule hP).2; omega
    -- `B = (72, 2, 16, 6)`: party 1 has nothing in `P`, party 2 has quota 2; party 3 takes one.
    obtain ⟨B, hB⟩ := rule.non_emptiness (large 2 16 6)
    have hB1 : B[1] ≤ P[1] := seats_le_of_votes_le rule h_mono 1 hB hP
    have hB2 : B[2] = 2 := large_two_seats rule 2 hB
    have hB3 : B[3] = 1 := by have := (large_seats rule hB).2; omega
    -- `Q = (71, 4, 4, 6)`: parties 2 and 3 keep the seats they hold in `A` and `B`.
    obtain ⟨Q, hQ⟩ := rule.non_emptiness (small 4 4 6)
    have hQ2 : A[2] ≤ Q[2] := seats_le_of_votes_le rule h_mono 2 hA hQ
    have hQ3 : B[3] ≤ Q[3] := seats_le_of_votes_le rule h_mono 3 hB hQ
    have hQ1 : Q[1] = 0 := by have := (small_seats rule hQ).2; omega
    -- `C = (72, 4, 16, 4)`: party 1 has nothing in `Q`, party 2 has quota 2; party 3 takes one.
    obtain ⟨C, hC⟩ := rule.non_emptiness (large 4 16 4)
    have hC1 : C[1] ≤ Q[1] := seats_le_of_votes_le rule h_mono 1 hC hQ
    have hC2 : C[2] = 2 := large_two_seats rule 2 hC
    have hC3 : C[3] = 1 := by have := (large_seats rule hC).2; omega
    -- `R = (71, 8, 2, 4)`: party 3 keeps its seat, party 1's quota exceeds 1; party 2 gets none.
    obtain ⟨R, hR⟩ := rule.non_emptiness (small 8 2 4)
    have hR3 : C[3] ≤ R[3] := seats_le_of_votes_le rule h_mono 3 hC hR
    have hR1 : 1 ≤ R[1] := small_one_seat rule 1 hR
    have hR2 : R[2] = 0 := by have := (small_seats rule hR).2; omega
    -- `D = (72, 6, 2, 16)`: party 2 has nothing in `R`, party 3 has quota 2; party 1 takes one.
    obtain ⟨D, hD⟩ := rule.non_emptiness (large 6 2 16)
    have hD2 : D[2] ≤ R[2] := seats_le_of_votes_le rule h_mono 2 hD hR
    have hD3 : D[3] = 2 := large_two_seats rule 3 hD
    have hD1 : D[1] = 1 := by have := (large_seats rule hD).2; omega
    -- `S = (71, 6, 4, 4)`: parties 3 and 1 keep the seats they hold in `C` and `D`.
    obtain ⟨S, hS⟩ := rule.non_emptiness (small 6 4 4)
    have hS3 : C[3] ≤ S[3] := seats_le_of_votes_le rule h_mono 3 hC hS
    have hS1 : D[1] ≤ S[1] := seats_le_of_votes_le rule h_mono 1 hD hS
    have hS2 : S[2] = 0 := by have := (small_seats rule hS).2; omega
    -- the contradiction
    have : A[2] ≤ S[2] := seats_le_of_votes_le rule h_mono 2 hA hS
    omega
  · -- The mirror image of the chain above, with parties 2 and 3 swapped throughout.
    obtain ⟨P, hP⟩ := rule.non_emptiness (small 2 8 4)
    have hP3 : A[3] ≤ P[3] := seats_le_of_votes_le rule h_mono 3 hA hP
    have hP2 : 1 ≤ P[2] := small_one_seat rule 2 hP
    have hP1 : P[1] = 0 := by have := (small_seats rule hP).2; omega
    obtain ⟨B, hB⟩ := rule.non_emptiness (large 2 6 16)
    have hB1 : B[1] ≤ P[1] := seats_le_of_votes_le rule h_mono 1 hB hP
    have hB3 : B[3] = 2 := large_two_seats rule 3 hB
    have hB2 : B[2] = 1 := by have := (large_seats rule hB).2; omega
    obtain ⟨Q, hQ⟩ := rule.non_emptiness (small 4 6 4)
    have hQ3 : A[3] ≤ Q[3] := seats_le_of_votes_le rule h_mono 3 hA hQ
    have hQ2 : B[2] ≤ Q[2] := seats_le_of_votes_le rule h_mono 2 hB hQ
    have hQ1 : Q[1] = 0 := by have := (small_seats rule hQ).2; omega
    obtain ⟨C, hC⟩ := rule.non_emptiness (large 4 4 16)
    have hC1 : C[1] ≤ Q[1] := seats_le_of_votes_le rule h_mono 1 hC hQ
    have hC3 : C[3] = 2 := large_two_seats rule 3 hC
    have hC2 : C[2] = 1 := by have := (large_seats rule hC).2; omega
    obtain ⟨R, hR⟩ := rule.non_emptiness (small 8 4 2)
    have hR2 : C[2] ≤ R[2] := seats_le_of_votes_le rule h_mono 2 hC hR
    have hR1 : 1 ≤ R[1] := small_one_seat rule 1 hR
    have hR3 : R[3] = 0 := by have := (small_seats rule hR).2; omega
    obtain ⟨D, hD⟩ := rule.non_emptiness (large 6 16 2)
    have hD3 : D[3] ≤ R[3] := seats_le_of_votes_le rule h_mono 3 hD hR
    have hD2 : D[2] = 2 := large_two_seats rule 2 hD
    have hD1 : D[1] = 1 := by have := (large_seats rule hD).2; omega
    obtain ⟨S, hS⟩ := rule.non_emptiness (small 6 4 4)
    have hS2 : C[2] ≤ S[2] := seats_le_of_votes_le rule h_mono 2 hC hS
    have hS1 : D[1] ≤ S[1] := seats_le_of_votes_le rule h_mono 1 hD hS
    have hS3 : S[3] = 0 := by have := (small_seats rule hS).2; omega
    have : A[3] ≤ S[3] := seats_le_of_votes_le rule h_mono 3 hA hS
    omega
end Apportionmentlib
