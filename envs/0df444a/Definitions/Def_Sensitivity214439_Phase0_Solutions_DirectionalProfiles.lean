-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_DirectionalProfiles
-- name    : Sensitivity214439_Phase0_Solutions_DirectionalProfiles
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:11:59.355167+00:00
-- url     : https://prove2.me/theorems/a81c74f0-580c-4c31-ae64-b2f9a26e5234
-- title:
--   Directional color-switch profile bounds
-- statement:
--   Let $F_c(j,x)$ be a colored row family, let $\to$ be an orientation on its colors, and fix a core rank $k$. Directional bounds consist of two real-valued functions $R(a,n)$ and $D(a,n)$. For all $a,n\ge k$, acceptance by color $c$ at $a$ bounds gains by another color $d$ at $n$ as follows:
--   $$
--   c\to d\ \Longrightarrow\
--   |\operatorname{rowGain}_d(n,x)|\le R(a,n),
--   $$
--   $$
--   d\to c\ \Longrightarrow\
--   |\operatorname{rowGain}_d(n,x)|\le D(a,n).
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/DirectionalProfiles.lean lines 19–24; SHA256 cdf8ae0f95c474d8706fa4b968e9fe3f43cab8d8a38599dd7c39e189b9a3aa14; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_Profile456
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
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

namespace SensitivityDirectionalProfiles
end SensitivityDirectionalProfiles
namespace SensitivityGateSwitchBounds
end SensitivityGateSwitchBounds
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
The two directions of a strict identity switch have different child prices.
Two mismatched paired children switch their identities in opposite directions,
so a single orientation choice controls both prices simultaneously.
-/
namespace SensitivityDirectionalProfiles

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGateSwitchBounds
open SensitivityHighHeadGuardBridge
set_option autoImplicit false

variable {V S I Color : Type} {L core : ℕ}

structure DirectionalBounds [Fintype I] (row : RowFamily I Color L) (core : ℕ)
    (arc : Color → Color → Prop) (rise fall : Fin L → Fin L → ℝ) : Prop where
  rise : ∀ c d x a n, core ≤ a.val → core ≤ n.val → arc c d → row c a x →
    ((rowGainEvents row d n x).card : ℝ) ≤ rise a n
  fall : ∀ c d x a n, core ≤ a.val → core ≤ n.val → arc d c → row c a x →
    ((rowGainEvents row d n x).card : ℝ) ≤ fall a n















end
end SensitivityDirectionalProfiles


