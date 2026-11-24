-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_OperativeHeadSemantics
-- name    : Sensitivity214439_Phase0_Solutions_OperativeHeadSemantics
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T17:59:32.250521+00:00
-- url     : https://prove2.me/theorems/6514cd22-b575-4e05-ba1c-120eac634e74
-- title:
--   Operative rows, repair types, and low-count prefixes
-- statement:
--   A parent row is operative at rank $j$ when some single bit flip makes it accept. A target repair restricts that bit to one of the row's own sockets; a guard repair restricts it to a socket of one of its checks.
--
--   A row is high at cutoff $a$ when every own child socket passes $a$. The operative high and low sets split operative rows according to this predicate. A low prefix of tolerance $q$ further selects low rows with at most $q$ active checks at the cutoff.
--
--   Failure monotonicity requires each target assignment permitted at a larger legal count to dominate an assignment permitted at every smaller count. The target-floor predicate requires every legal assignment to reach at least a specified cutoff at every side. These are structural properties of the gate recipe.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/OperativeHeadSemantics.lean lines 21–65; SHA256 6ad2e0139831807588d2b3baa359ff3594893814bd98bfa2f64d0db4779ee500; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_SensitivitySeparation
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

namespace Sensitivity213981Formal
end Sensitivity213981Formal
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates



/-!
The actual repairable heads used by the global upward transfer. Types record
which own-target and guard repairs are possible, together with exact original
guard counts. Inoperative rows are never inserted merely because their child
heights satisfy a numerical necessary condition.
-/
namespace SensitivityOperativeHeads

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityStrictGateStates SensitivitySocketEventSupport
open Sensitivity213981Formal
set_option autoImplicit false

variable {V S I Color : Type} {L : ℕ}

def Operative (row : RowFamily I Color L) (guards : GuardFamily V S) (recipe : GateRecipe S L)
    (v : V) (j : Fin L) (x : ((V × S) × I) → Bool) : Prop :=
  ∃ bit : (V × S) × I, gateRow row guards recipe v j (OAI.Paper320.flip x {bit})

def TargetRepair (row : RowFamily I Color L) (guards : GuardFamily V S) (recipe : GateRecipe S L)
    (v : V) (j : Fin L) (x : ((V × S) × I) → Bool) : Prop :=
  ∃ s i, gateRow row guards recipe v j (OAI.Paper320.flip x {((v,s),i)})

def GuardRepair (row : RowFamily I Color L) (guards : GuardFamily V S) (recipe : GateRecipe S L)
    (v : V) (j : Fin L) (x : ((V × S) × I) → Bool) : Prop :=
  ∃ check ∈ guards v, ∃ socket ∈ check, ∃ i,
    gateRow row guards recipe v j (OAI.Paper320.flip x {(socket,i)})

def HighAt (row : RowFamily I Color L) (cutoff : ℕ) (v : V)
    (x : ((V × S) × I) → Bool) : Prop := ∀ s, passes row cutoff (socketInput x (v,s))

def operativeHighHeads [Fintype V]
    (row : RowFamily I Color L) (guards : GuardFamily V S) (recipe : GateRecipe S L)
    (j : Fin L) (cutoff : ℕ) (x : ((V × S) × I) → Bool) : Finset V :=
  Finset.univ.filter fun v => HighAt row cutoff v x ∧ Operative row guards recipe v j x

def operativeLowHeads [Fintype V]
    (row : RowFamily I Color L) (guards : GuardFamily V S) (recipe : GateRecipe S L)
    (j : Fin L) (cutoff : ℕ) (x : ((V × S) × I) → Bool) : Finset V :=
  Finset.univ.filter fun v => ¬ HighAt row cutoff v x ∧ Operative row guards recipe v j x



def lowPrefix [Fintype V]
    (row : RowFamily I Color L) (guards : GuardFamily V S) (recipe : GateRecipe S L)
    (j : Fin L) (cutoff q : ℕ) (x : ((V × S) × I) → Bool) : Finset V :=
  (operativeLowHeads row guards recipe j cutoff x).filter fun v =>
    guardCount row guards v cutoff x ≤ q

/-- More affordable guard counts never require stronger target assignments. -/
def FailureMonotone (recipe : GateRecipe S L) (j : Fin L) : Prop :=
  ∀ f g, f ≤ g → g ≤ recipe.allowance j →
    ∀ assignment ∈ recipe.targets j g,
      ∃ weaker ∈ recipe.targets j f, ∀ s, weaker s ≤ assignment s

def TargetsAbove (recipe : GateRecipe S L) (j : Fin L) (cutoff : ℕ) : Prop :=
  ∀ f, f ≤ recipe.allowance j → ∀ assignment ∈ recipe.targets j f,
    ∀ s, cutoff ≤ (assignment s).val





















end
end SensitivityOperativeHeads


