-- Prove2me | Definitions.Def_HouseAllocLT_LowerBound_Preference
-- name    : HouseAllocLT_LowerBound_Preference
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:43.816247+00:00
-- url     : https://prove2.me/theorems/7d68dabe-61f3-4626-aeca-118b42118fab
-- title:
--   Weak-order reports and profiles
-- statement:
--   A report on $m$ objects is an ordered finite list of nonempty pairwise disjoint indifference classes. Its acceptable set is their union. Ties, incomplete lists and the empty list are permitted. A profile supplies one such report for every agent.
--
--   $$Q_i=\bigcup_{j=1}^{r_i} C_j^i.$$
--
--   The class function is empty beyond its declared length. Lexicographic comparison means equality of every entry, or a larger entry at the first difference. This vocabulary is shared by both truthfulness and the benchmark.
--
--   **Formalization Note** Objects and agents use zero-based finite indices. Classes also use zero-based indices, so class $j$ in the code is rank $j+1$ in the source. A class function with a finite length and the stated laws is exactly the source's finite list.
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), §2, reports, profiles and lexicographic comparison, PDF p. 6 (printed p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Mathlib

namespace HouseAllocLT.LowerBound

/-- §2, PDF p.6. Classes are indexed from zero; all entries beyond length are empty.
This is a finite list of nonempty disjoint indifference classes, including the empty list. -/
structure Preference (m : ℕ) where
  length : ℕ
  classes : ℕ → Finset (Fin m)
  nonempty_iff : ∀ j, (classes j).Nonempty ↔ j < length
  disjoint : ∀ j k, j ≠ k → Disjoint (classes j) (classes k)

/-- The union of the reported classes. -/
def Acceptable {m : ℕ} (p : Preference m) (a : Fin m) : Prop :=
  ∃ j < p.length, a ∈ p.classes j

abbrev Profile (n m : ℕ) := Fin n → Preference m

/-- Equality or a strict advantage at the first differing zero-based index. -/
def LexGE {α : Type*} [LT α] (r : ℕ) (x y : ℕ → α) : Prop :=
  (∀ j < r, x j = y j) ∨
    ∃ j < r, y j < x j ∧ ∀ k < j, x k = y k

end HouseAllocLT.LowerBound


