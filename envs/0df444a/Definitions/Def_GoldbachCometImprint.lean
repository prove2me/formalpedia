-- Prove2me | Definitions.Def_GoldbachCometImprint
-- name    : GoldbachCometImprint
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-05T08:38:22.65377+00:00
-- url     : https://prove2.me/theorems/0e3d61f4-4d3c-47f3-8340-20b83e60864a
-- title:
--   Singular series factor and normalized counts
-- statement:
--   Defines the Hardy–Littlewood prime part `singularSeriesPrimes n = ∏_{p|n, 2<p} (p-1)/(p-2)` and `normalizedOrderedCount`, matching docs/captain/goldbach/experiments/race_imprint.py and FRESH-PERSPECTIVES §1.
-- source:
--   docs/goldbach-comet/LAYER3-NEXT.md

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Positivity

import Definitions.Def_GoldbachComet

set_option autoImplicit false

namespace GoldbachCometImprint

open GoldbachComet

/-- Hardy–Littlewood local factor for an odd prime `p`: `(p-1)/(p-2)`. -/
def hlLocalFactor (p : ℕ) : ℚ :=
  ((p - 1 : ℕ) : ℚ) / ((p - 2 : ℕ) : ℚ)

theorem hlLocalFactor_pos {p : ℕ} (_hp : p.Prime) (hodd : 2 < p) :
    0 < hlLocalFactor p := by
  unfold hlLocalFactor
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt (by omega : 1 < p)
  have hp2 : 0 < p - 2 := Nat.sub_pos_of_lt hodd
  exact div_pos (mod_cast hp1) (mod_cast hp2)

/-- Prime part of the Goldbach singular series:
`∏_{p | n, 2 < p} (p-1)/(p-2)` (matches `race_imprint.py` and FRESH-PERSPECTIVES §1). -/
def singularSeriesPrimes (n : ℕ) : ℚ :=
  (n.primeFactorsList.filter fun p => 2 < p).foldl (fun acc p => acc * hlLocalFactor p) 1

private lemma foldl_mul_pos (l : List ℕ) (init : ℚ) (hinit : 0 < init)
    (h : ∀ p ∈ l, p.Prime ∧ 2 < p) :
    0 < l.foldl (fun acc p => acc * hlLocalFactor p) init := by
  induction l generalizing init with
  | nil => simpa using hinit
  | cons p ps ih =>
      simp only [List.foldl]
      have ⟨hpp, hodd⟩ := h p (by simp)
      exact ih _ (mul_pos hinit (hlLocalFactor_pos hpp hodd)) fun q hq => h q (by simp [hq])

theorem singularSeriesPrimes_pos (n : ℕ) :
    0 < singularSeriesPrimes n := by
  unfold singularSeriesPrimes
  refine foldl_mul_pos _ 1 (by norm_num) ?_
  intro p hp
  obtain ⟨hmem, hodd⟩ := List.mem_filter.mp hp
  exact ⟨Nat.prime_of_mem_primeFactorsList hmem, of_decide_eq_true hodd⟩

/-- Empirical normalization uses `r(n) / S(n)` with the same prime part as `singularSeriesPrimes`. -/
def normalizedOrderedCount (n : ℕ) : ℚ :=
  (orderedReprCount n : ℚ) / singularSeriesPrimes n

end GoldbachCometImprint


