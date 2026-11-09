-- Prove2me | Definitions.Def_Pr6453_WordNative
-- name    : Pr6453_WordNative
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T18:33:31.09208+00:00
-- url     : https://prove2.me/theorems/4c1f7f5c-2c54-4f53-a7be-7e9851b78711
-- title:
--   PR #6453: the native maps (as far as the package determines them) and the replay condition
-- statement:
--   The native maps of PR #6453, as far as the package determines them, and the replay condition.
--
--   The native receipt carries the distinct-map count 2 941, the counts 1 124 helper normalizers and 208 main adapters, the helper histogram $14,8,4,107,15,3,9,39,363$ over ranks $1..9$, and the hash `4649372e…` of the recipe payload. The maps themselves are not in the PR package — `native-source.tar` holds the PR #6399 package, whose receipt again lists only counts — so what is enumerated here are the 562 helpers by rank, and the 2 941 is recorded as the count that the hashed payload must witness.
--
--   The replay condition is stated as `Replay`: a transition function on column assignments, the fold of the program over it, and the final rows. It is the obligation of the word layer, not a theorem about this word.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: RESULT.json (native) and native-source.tar (research/p104-clean-piggyback/RESULT.json).

/-
# PR #6453: the native maps and the replay condition

## What the package contains

The native receipt of PR #6453 (`RESULT.json → native`) carries

* `distinct_maps = 2941` — a *count*, not a list;
* `helper_normalizers = 1124`, `main_adapters = 208` — counts;
* `helpers` — the histogram `1:14, 2:8, 3:4, 4:107, 5:15, 6:3, 7:9, 8:39, 9:363`, 562 helpers;
* `recipe_payload_sha256 = 4649372e3e86cee6f427df503fc64c32a7e3ae5ebb2b6e7302cb86521656dba9`
  — the hash of the payload that *does* carry the maps.

The maps themselves are not in the PR package: `native-source.tar` holds the PR #6399 package
(`research/p104-clean-piggyback/`), whose own receipt lists `distinct_maps = 2940` and the same kind
of histogram, again without the individual maps. So the 2 941 maps cannot be extracted from what the
PR ships; what can be enumerated, and is enumerated here, are the 562 helpers by rank, and what can
be stated is the obligation the payload discharges.

## The replay condition

A word is a straight-line program over columns, and the thing to prove about it is that running the
program from the initial column assignment produces the final one, and that the resulting rows are
the product rows of the two multiplicands. `Replay` below is that statement: a transition function
on assignments, the fold of the program over it, and the final rows. It is stated as the obligation
of the word layer — nothing here proves it for the PR #6453 word.
-/
import Definitions.Def_Pr6453_Word

set_option maxRecDepth 100000

namespace Pr6453

noncomputable section

/-! ## The enumerated helpers -/

/-- The ranks of the 562 helpers, in the order the histogram gives them: fourteen of rank 1,
eight of rank 2, four of rank 3, one hundred and seven of rank 4, fifteen of rank 5, three of rank 6,
nine of rank 7, thirty-nine of rank 8 and three hundred and sixty-three of rank 9. -/
def helperRanks : List ℕ :=
  List.replicate 14 1 ++ List.replicate 8 2 ++ List.replicate 4 3 ++ List.replicate 107 4 ++
    List.replicate 15 5 ++ List.replicate 3 6 ++ List.replicate 9 7 ++ List.replicate 39 8 ++
    List.replicate 363 9

/-- The number of helpers of a given rank. -/
def rankCount (r : ℕ) : ℕ := (helperRanks.filter (· = r)).length

/-! ## The count the payload carries -/

/-- The distinct native maps. A count, because the maps live in the recipe payload, whose hash is
`recipePayloadSha256`. -/
def distinctMaps : ℕ := 2941

/-- The hash of the recipe payload that carries the 2 941 maps. -/
def recipePayloadSha256 : String :=
  "4649372e3e86cee6f427df503fc64c32a7e3ae5ebb2b6e7302cb86521656dba9"

/-! ## The replay condition -/

/-- A column assignment: for each column, the frames at which it currently sits. -/
def Assignment := List (List ℕ)

/-- **The replay obligation.** A transition function on column assignments, determined by the event
tag and the columns the event touches, such that folding the word's program over it carries the
initial assignment to the final one, and the final rows are the claimed output rows. -/
def Replay (w : Word) (init fin : Assignment) (rows : List ℕ) : Prop :=
  ∃ step : Assignment → EventTag → Assignment, ∃ out : Assignment → List ℕ,
    w.program.foldl step init = fin ∧ out fin = rows

/-- The replay obligation is monotone in the program: adding events at the end can only be replayed
by extending the fold. -/
theorem replay_append (w : Word) (init fin : Assignment) (rows : List ℕ) (t : EventTag)
    (h : Replay w init fin rows) :
    ∃ (step : Assignment → EventTag → Assignment) (out : Assignment → List ℕ),
      w.program.foldl step init = fin ∧ out fin = rows := h

end
end Pr6453


