-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentRegularDegrees
-- name    : Sensitivity214439_PairedSemantic_Solutions_TournamentRegularDegrees
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:46:50.064336+00:00
-- url     : https://prove2.me/theorems/a4741979-194e-449f-bb57-6d8c86c1f179
-- title:
--   Cyclic displacement support
-- statement:
--   The cyclic support at modulus $n$ is the finite set of nonzero displacements whose value is at most $\lfloor n/2\rfloor$. Translation identifies this support with the outgoing neighbors of any vertex in the cyclic relation, giving its regular outdegree.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/TournamentRegularDegrees.lean lines 19–20; SHA256 3248ab61a2fda8b29a7f527d5be3c7e9f0f9f9597df9ae58e1ed3f0dcf94d052; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentRegularDegrees
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





def cyclicSupport (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun d => d.val ≠ 0 ∧ 0 < d.val ∧ d.val ≤ n / 2)





set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

















end SensitivityGuardCardinality


