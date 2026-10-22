-- Prove2me | Definitions.Def_SensitivityProfileWord
-- name    : SensitivityProfileWord
-- status  : Definition
-- author  : @dmilosch
-- created : 2026-10-21T22:36:30.93521+00:00
-- url     : https://prove2.me/theorems/285261c1-73b2-41bb-8fdd-f06f34e32ee2
-- title:
--   Finite recipe words evaluated from the all-ones profile
-- statement:
--   A recipe word is a finite sequence of the recipes in `SensitivityProfileCycle`. Its evaluation normalizes an input profile and then applies the fixed transfer map from `SensitivityProfileSearch` once for each recipe, in order.
--
--   The canonical input has both matrices equal to one on and above the diagonal and zero below it. The height of a profile is the largest entry of either matrix, clamped below by two:
--
--   $$h(P)=\max\{2,\max_{i,j}P^0_{ij},\max_{i,j}P^1_{ij}\}.$$
--
--   A word is admissible when each recipe is valid and all positive tolerances used on its ordinary states are at most five. `Crosses215` requires a nonempty admissible word of length $L$ whose canonical output satisfies
--
--   $$h(P_L)^{43}<14055^{20L}.$$
--
--   No initial matrices or return factor are free parameters in this test. Its definitions contain no existence claim. Existence statements using this interface require a positive number of states; the types in the associated theorem enforce that condition.
-- source:
--   Original complete all-ones normalization of the deterministic recurrence in https://prove2.me/theorems/c3770ecd-d493-4b1b-8809-72b030b1f260 (SensitivityProfileSearch.exists_215_orbit), based on monotonicity, integer homogeneity, repeated recipe words, and absorption of fixed overhead by a strict power gap. The raw recurrence is from accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a, SensitivityNQ.rawOne and rawZeroSourceCombined, by yousofy with Codex, retaining OpenAI/math, Robin Kothari with Codex, and community attribution. No crossing word is supplied or claimed to be known.

import Definitions.Def_SensitivityProfileSearch

/-!
Finite recipe words and a canonical all-ones starting profile.
These definitions add no existence assumption. The transfer step and fixed
labeling parameters are those of SensitivityProfileSearch.
-/

set_option autoImplicit false
namespace SensitivityProfileWord
open SensitivityProfileCycle SensitivityProfileSearch

def unitProfile (n : ℕ) : Profile n :=
  ⟨fun i j => if i ≤ j then 1 else 0,
   fun i j => if i ≤ j then 1 else 0⟩

/-- A profile bound, clamped at two to meet the target's radius condition. -/
def height {n : ℕ} (P : Profile n) : ℕ :=
  max 2 (Finset.univ.sup fun ij : Fin n × Fin n =>
    max (P.zero ij.1 ij.2) (P.one ij.1 ij.2))

/-- Evaluate a finite recipe word after normalizing its input. -/
def run {n : ℕ} (word : List (Recipe n)) (P : Profile n) : Profile n :=
  word.foldl (fun Q C => step C Q) (normalize P)

def Admissible {n : ℕ} (word : List (Recipe n)) : Prop :=
  ∀ C ∈ word, C.Valid ∧ ∀ i, 3 ≤ i.val → 0 < C.tol i → C.tol i < 6

def Crosses215 {n : ℕ} (word : List (Recipe n)) : Prop :=
  word ≠ [] ∧ Admissible word ∧
    height (run word (unitProfile n)) ^ 43 < 14055 ^ (20 * word.length)

end SensitivityProfileWord


