-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroIncomingHeads
-- name    : Sensitivity214439_PairedSemantic_Solutions_MacroIncomingHeads
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:42.96537+00:00
-- url     : https://prove2.me/theorems/f8820a98-5529-4415-8ee3-a995e5a79b7b
-- title:
--   Incoming source macros capped at two
-- statement:
--   Defines incomingMacros(G,arc,w) as the distinct macros of sources in G that point to w and lie outside w's own macro. incomingLevel is the cardinality of that set capped at two, matching the three high-head price slots.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MacroIncomingHeads.lean lines 18–23; SHA256 1c73378aa20db03a89980c5e420f3cf870a4bea858c71f69cc8698b46fdfadc6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityMacroIncomingHeads
end SensitivityMacroIncomingHeads
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
The refined incoming count is the number of different external source
macros, capped at two. Heads in one source macro inspect the same child at
the destination. A positive one/two-incoming field therefore witnesses at
least two/three different macros among the actual high heads.
-/
namespace SensitivityMacroIncomingHeads

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
set_option autoImplicit false

variable {M B : Type}

def incomingMacros (G : Finset (M × B)) (arc : (M × B) → (M × B) → Prop)
    (w : M × B) : Finset M :=
  (G.filter fun v => v.1 ≠ w.1 ∧ arc v w).image Prod.fst

def incomingLevel (G : Finset (M × B)) (arc : (M × B) → (M × B) → Prop)
    (w : M × B) : ℕ := min 2 (incomingMacros G arc w).card























end
end SensitivityMacroIncomingHeads


