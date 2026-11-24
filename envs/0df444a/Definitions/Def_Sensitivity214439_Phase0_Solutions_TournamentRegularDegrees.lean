-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentRegularDegrees
-- name    : Sensitivity214439_Phase0_Solutions_TournamentRegularDegrees
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:20.081797+00:00
-- url     : https://prove2.me/theorems/c7170607-05a7-4d2b-9df7-4d5859013bf2
-- title:
--   Outgoing-neighbor sets and nonzero mask support
-- statement:
--   For a finite vertex type and arc relation, the outgoing-neighbor set of $v$ is
--   $$
--   N^+(v)=\{w:w\ne v\land v\to w\}.
--   $$
--   For a natural bit mask modulo $n$, its residue support is the finite set of nonzero residues $d<n$ whose mask bit is true. These sets express regular degree calculations for literal circulant tournaments.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/TournamentRegularDegrees.lean lines 11–17; SHA256 3248ab61a2fda8b29a7f527d5be3c7e9f0f9f9597df9ae58e1ed3f0dcf94d052; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGuardCardinality
end SensitivityGuardCardinality
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! Regular degrees of the literal circulant and Paley guard graphs. -/

namespace SensitivityGuardCardinality

open SensitivityRankedConstruction SensitivityRankMapCheckpoint
open scoped Fin.CommRing

noncomputable def outNeighbors {V : Type} [Fintype V] (arc : V → V → Prop) (v : V) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun w => w ≠ v ∧ arc v w)

def residueSupport (n mask : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun d => d.val ≠ 0 ∧ mask.testBit d.val = true)







set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

















end SensitivityGuardCardinality


