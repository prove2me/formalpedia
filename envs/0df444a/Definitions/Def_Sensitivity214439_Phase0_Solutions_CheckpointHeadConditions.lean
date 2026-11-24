-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_CheckpointHeadConditions
-- name    : Sensitivity214439_Phase0_Solutions_CheckpointHeadConditions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:28.020807+00:00
-- url     : https://prove2.me/theorems/133d7fd4-05b7-4407-b149-5d985c9a7b9b
-- title:
--   Effective head cutoffs and scalar head conditions
-- statement:
--   For a gate with $L$ ranks, define its effective head cutoff at rank $j$ as the hard cutoff if that cutoff is below $L$, and otherwise as the soft cutoff:
--   $$
--   h_j^{\rm head}=
--   \begin{cases}h_j,&h_j<L,\\s_j,&h_j\ge L.\end{cases}
--   $$
--   Scalar head conditions with count bound $B$ and core $c$ require $q_j<B$, every legal target to be at least $\max(c,h_j^{\rm head})$, and targets monotone in the legal failure count. These conditions are stated over the finite count range $0,\ldots,B-1$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/CheckpointHeadConditions.lean lines 14–23; SHA256 2d075f30faf1aa1afeec7e762380d97a9c24348d377dd56c3aa798c7548939fa; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! Finite target monotonicity and threshold conditions for actual head rows. -/
namespace SensitivityOperativeHeads

noncomputable section
open scoped Classical
open SensitivityRankedConstruction
set_option autoImplicit false

variable {L bound : ℕ}

def headCutoff {S : Type} (recipe : GateRecipe S L) (j : Fin L) : ℕ :=
  if recipe.hard j < L then recipe.hard j else recipe.soft j

def ScalarHeadConditions (bound core : ℕ)
    (soft hard allowance : Fin L → ℕ) (target : Fin L → ℕ → Fin L) : Prop :=
  (∀ j, allowance j < bound) ∧
  (∀ (j : Fin L) (f : Fin bound), f.val ≤ allowance j →
    max core (if hard j < L then hard j else soft j) ≤ (target j f.val).val) ∧
  ∀ (j : Fin L) (f g : Fin bound), f.val ≤ g.val → g.val ≤ allowance j →
    target j f.val ≤ target j g.val















end
end SensitivityOperativeHeads

namespace SensitivityRankMapCheckpoint

open SensitivityOperativeHeads
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000











































end SensitivityRankMapCheckpoint


