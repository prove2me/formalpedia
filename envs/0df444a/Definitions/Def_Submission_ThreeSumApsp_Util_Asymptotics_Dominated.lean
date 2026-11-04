-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
-- name    : Submission_ThreeSumApsp_Util_Asymptotics_Dominated
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:50:36.011664+00:00
-- url     : https://prove2.me/theorems/a35f68c0-52a1-4574-8553-f735c7da29e5
-- title:
--   Dominated
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
set_option autoImplicit false
@[expose] public section
open Filter Asymptotics
namespace ThreeSumApsp
def Dominated {α : Type*} (dom : α → Prop) (f g : α → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, dom x → f x ≤ C * g x
namespace Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}
end Dominated
end ThreeSumApsp


