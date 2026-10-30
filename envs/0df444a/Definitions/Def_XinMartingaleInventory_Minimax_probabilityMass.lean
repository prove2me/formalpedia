-- Prove2me | Definitions.Def_XinMartingaleInventory_Minimax_probabilityMass
-- name    : XinMartingaleInventory_Minimax_probabilityMass
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:56:08.462279+00:00
-- url     : https://prove2.me/theorems/9514eddd-b201-4332-8233-7f31bd56bcef
-- title:
--   Probability masses, expectations and finite histories
-- statement:
--   A probability mass is a nonnegative real function with sum one. Expectations are weighted countable sums. History rules map finite lists to actions. Lists store the most recent observation first; a chronological prefix is the corresponding suffix of that list. Prefix atom probabilities sum the masses of all extensions, and conditional atom probabilities divide the extended-prefix mass by the prefix mass. Conditional ratios are used only when the denominator is positive. These generic objects add no inventory, independence or finite-support assumptions.
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, §§2.1–3 and §7.2, p.7 (PDF p.7)

import Mathlib

noncomputable section

namespace XinMartingaleInventory.Minimax

/-- Nonnegative, summable masses of total mass one. No finite-support restriction. -/
def probabilityMass {α : Type*} (q : α → ℝ) : Prop :=
  (∀ a, 0 ≤ q a) ∧ HasSum q 1

/-- Expectation of a bounded observable under a countably supported probability mass. -/
def expectation {α : Type*} (q : α → ℝ) (f : α → ℝ) : ℝ := ∑' a, q a * f a

/-- A deterministic history rule; the list stores the most recent observation first. -/
abbrev HistoryRule (S A : Type*) := List S → A

/-- Chronological historyPrefix of length n, still stored in reverse order. -/
def historyPrefix {α : Type*} (w : List α) (n : ℕ) : List α := w.drop (w.length - n)

/-- Atom probability of a finite historyPrefix, obtained by summing the full path law. -/
def prefixMass {α : Type*} (Q : List α → ℝ) (h : List α) : ℝ :=
  by
    classical
    exact ∑' w : List α, if h.length ≤ w.length ∧ historyPrefix w h.length = h then Q w else 0

/-- Conditional atom ratio, used only at positive-mass prefixes. -/
def conditionalMass {α : Type*} (Q : List α → ℝ) (h : List α) (d : α) : ℝ :=
  prefixMass Q (d :: h) / prefixMass Q h

end XinMartingaleInventory.Minimax


