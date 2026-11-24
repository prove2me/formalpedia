-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_CheckpointRankMapConstruction
-- name    : Sensitivity214439_Phase0_Solutions_CheckpointRankMapConstruction
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:19:35.480911+00:00
-- url     : https://prove2.me/theorems/6995e0c5-c284-41e4-aab1-3fe0ab45a67d
-- title:
--   The literal unary phase of the rank-map construction
-- statement:
--   The first gate stage has $2659$ rows, one target socket per row, and singleton guards directed by the Paley tournament. It uses twelve ranks. Its soft and hard cutoff vectors are
--   $$
--   s=(5,5,5,5,5,5,4,4,3,3,2,2),\qquad
--   h=(12,12,12,12,12,5,5,4,4,3,3,2).
--   $$
--   At ordinary ranks $0,\ldots,4$, the allowances are $(5,4,3,2,1)$; at all later ranks the soft allowance is one and the hard cutoff must remain quiet. The base target at zero failures is
--   $$
--   (7,7,7,7,7,7,7,8,9,10,11,11).
--   $$
--   At rank $6$ a positive permitted failure count raises the target to $8$, and at rank $7$ it raises the target to $10$; the other targets are constant. The four-entry selector and the ordinary/warm count normalization define this target function on every natural failure count. The resulting unary recipe and its no-self-guard stage are fixed here.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/CheckpointRankMapConstruction.lean lines 22–590; SHA256 9938371507bf76e43c48a62a49447c664ea8249bb2479fc42570931d54fc48b1; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RecursiveGateFamilies
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentSocketGuards
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum

namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
# The literal strongest rank-map construction

Recipes transcribed from refitted-paired-ladders/checkpoint-rank-map.json.
Source SHA256: ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df
Macro masks are the first rows of the supplied circulant orientation and label
tables. Internal arcs use the cyclic tournament allowed by the source README.
The theorem at the end proves both structural lower bounds for these actual
Boolean functions. No sensitivity upper bound or character estimate is assumed
or claimed in this module.
-/

namespace SensitivityRankMapCheckpoint

noncomputable section
open scoped Classical
open SensitivityRankedConstruction

 def fourTarget (a b c d : Fin 12) (f : ℕ) : Fin 12 :=
  if f = 0 then a else if f = 1 then b else if f = 2 then c else d

def phase0Tolerance (j : Fin 12) : ℕ :=
  match j.val with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | _ => 0

def phase0Soft (j : Fin 12) : ℕ :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 4
  | 7 => 4
  | 8 => 3
  | 9 => 3
  | 10 => 2
  | _ => 2

def phase0Hard (j : Fin 12) : ℕ :=
  match j.val with
  | 0 => 12
  | 1 => 12
  | 2 => 12
  | 3 => 12
  | 4 => 12
  | 5 => 5
  | 6 => 5
  | 7 => 4
  | 8 => 4
  | 9 => 3
  | 10 => 3
  | _ => 2

def phase0BaseTarget (j : Fin 12) (f : ℕ) : Fin 12 :=
  match j.val with
  | 0 => fourTarget 7 7 7 7 f
  | 1 => fourTarget 7 7 7 7 f
  | 2 => fourTarget 7 7 7 7 f
  | 3 => fourTarget 7 7 7 7 f
  | 4 => fourTarget 7 7 7 7 f
  | 5 => fourTarget 7 7 7 7 f
  | 6 => fourTarget 7 8 8 8 f
  | 7 => fourTarget 8 10 10 10 f
  | 8 => fourTarget 9 9 9 9 f
  | 9 => fourTarget 10 10 10 10 f
  | 10 => fourTarget 11 11 11 11 f
  | _ => fourTarget 11 11 11 11 f

def phase0Allowance (j : Fin 12) : ℕ :=
  if phase0Hard j < 12 then 1 else phase0Tolerance j

def phase0Target (j : Fin 12) (f : ℕ) : Fin 12 :=
  phase0BaseTarget j
    (if phase0Hard j < 12 then (if f = 0 then 0 else 1)
     else if 4 ≤ phase0Tolerance j then 0 else f)

def phase0Recipe : GateRecipe Unit 12 :=
  unaryRecipe phase0Soft phase0Hard phase0Allowance phase0Target


































































































def phase0 : GateStage 12 where
  Row := Fin 2659
  rowFinite := inferInstance
  rowNonempty := inferInstance
  Socket := Unit
  socketFinite := inferInstance
  socketNonempty := inferInstance
  guards := unaryTournamentGuards paley2659Arc
  recipe := phase0Recipe
  noSelf := unaryTournamentGuards_noSelf paley2659Arc





















end
end SensitivityRankMapCheckpoint


