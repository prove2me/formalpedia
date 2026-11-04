-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
-- name    : Submission_ThreeSum_TernaryCoefficientCodes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:02:33.797243+00:00
-- url     : https://prove2.me/theorems/bcb7d89b-bb3f-47e2-9e73-4ea53d4342c2
-- title:
--   Ternary Coefficient Codes
-- statement:
--   Definitions and structural lemmas for Ternary Coefficient Codes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoefficientCodes.lean

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
def coefficientCode {d : ℕ} (a : Fin d → ZMod p) : ℕ :=
  Nat.ofDigits p (List.ofFn fun i => (a i).val)
def coefficientVector (d code : ℕ) : Fin d → ZMod p :=
  fun i => ((code/p^i.val%p : ℕ) : ZMod p)
theorem coefficientCode_lt {d : ℕ} (a : Fin d → ZMod p) : coefficientCode a<p^d := by
  have h := Nat.ofDigits_lt_base_pow_length (Fact.out : p.Prime).one_lt
    (l := List.ofFn fun i => (a i).val) (by
      intro n hn
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
      exact ZMod.val_lt _)
  simpa only [coefficientCode,List.length_ofFn] using h
theorem coefficientCode_digit {d : ℕ} (a : Fin d → ZMod p) (i : Fin d) :
    coefficientCode a/p^i.val%p=(a i).val := by
  let xs := List.ofFn fun j => (a j).val
  have hb : ∀ n∈xs, n<p := by
    intro n hn
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hn
    exact ZMod.val_lt _
  have hh : (xs.drop i.val).head?=some ((a i).val) := by
    simp [xs,List.head?_drop,i.isLt]
  change Nat.ofDigits p xs/p^i.val%p=_
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i.val (Fact.out : p.Prime).pos xs hb,
    Nat.ofDigits_mod_eq_head!,List.head!_of_head? hh,Nat.mod_eq_of_lt (ZMod.val_lt _)]
theorem coefficientVector_code {d : ℕ} (a : Fin d → ZMod p) :
    coefficientVector d (coefficientCode a)=a := by
  funext i
  simp only [coefficientVector,coefficientCode_digit,ZMod.natCast_zmod_val]
theorem coefficientCode_injective (d : ℕ) :
    Function.Injective (coefficientCode (p := p) (d := d)) := by
  intro a b h
  rw [← coefficientVector_code a,← coefficientVector_code b,h]
def coefficientEquiv (d : ℕ) : (Fin d → ZMod p) ≃ Fin (p^d) :=
  Equiv.ofBijective (fun a => ⟨coefficientCode a,coefficientCode_lt a⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a b h => coefficientCode_injective d (congrArg Fin.val h),by simp⟩)
def monicOfCode (d code : ℕ) : (ZMod p)[X] := monicCandidate (coefficientVector d code)
end ThreeSum.TernaryExtensionEncoding


