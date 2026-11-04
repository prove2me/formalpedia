-- Prove2me | Definitions.Def_Submission_ThreeSum_Subset
-- name    : Submission_ThreeSum_Subset
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:34.447696+00:00
-- url     : https://prove2.me/theorems/a7f9cc73-0707-4055-b9cb-8e6c679d318e
-- title:
--   Subset
-- statement:
--   Definitions and structural lemmas for Subset, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Aesop
set_option autoImplicit false
namespace ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
def zeta (f : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, f s
def mobius (f : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, (-1 : ℤ) ^ (q.card - s.card) * f s
def unionConvolution (f g : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, ∑ v ∈ q.powerset,
    if s ∪ v = q then f s * g v else 0
def disjointConvolution (f g : Finset α → ℤ) (q : Finset α) : ℤ :=
  ∑ s ∈ q.powerset, f s * g (q \ s)
def partialZeta (processed : Finset α) (f : Finset α → ℤ) (u : Finset α) : ℤ :=
  ∑ x ∈ (u ∩ processed).powerset, f ((u \ processed) ∪ x)
def zetaStep (a : α) (F : Finset α → ℤ) (u : Finset α) : ℤ :=
  if a ∈ u then F u + F (u.erase a) else F u
def runZeta : List α → (Finset α → ℤ) → Finset α → ℤ
  | [], f => f
  | a :: coords, f => zetaStep a (runZeta coords f)
def forcedInput (f : Finset α → ℤ) (pre suffix x : Finset α) : ℤ :=
  if x ⊆ suffix then f (pre ∪ x) else 0
def fiberMass {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (label : β → γ) (weight : β → ℕ) (value : γ) : ℕ :=
  ∑ p ∈ domain with label p = value, weight p
end ThreeSum.Subset


