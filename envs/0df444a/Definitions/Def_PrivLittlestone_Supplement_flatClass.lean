-- Prove2me | Definitions.Def_PrivLittlestone_Supplement_flatClass
-- name    : PrivLittlestone_Supplement_flatClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:57:54.917272+00:00
-- url     : https://prove2.me/theorems/d13e985c-b3e8-4342-b0d7-7f02fb675d35
-- title:
--   The class $H_r(M)$ of flats of rank at most $r$ of a matroid
-- statement:
--   Let $M$ be a matroid on a ground set $E$, with rank function $\mathrm{rk}$ and closure operator $\mathrm{cl}$; a **flat** is a set $F \subseteq E$ with $\mathrm{cl}(F) = F$. For an integer $r \ge 0$, the **class of flats of rank at most $r$** is the set of binary classifiers
--   $$
--   H_r(M) = \{\, x \mapsto \mathbf 1\{x \in F\} \;:\; F \text{ a flat of } M,\ \mathrm{rk}(F) \le r \,\}.
--   $$
--
--   This is the hypothesis class of the proper adaptive learner of Theorem 1.2; a learner for $H_r(M)$ is **proper** when every classifier it releases belongs to $H_r(M)$.
--
--   **Formalization Note** Mathlib's `Matroid α` carries its ground set `M.E` inside a type `α`, and the classifiers are functions on `α`. Flats are subsets of `M.E`, so every member of the class labels the elements of `α` outside `M.E` with $0$. The rank is Mathlib's `M.eRk`, valued in $\mathbb N \cup \{\infty\}$, and $\{0,1\}$ is `Bool`.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §1.1, p.1 (definition of $H_r(M)$) and §6, p.10

import Mathlib

namespace PrivLittlestone.Supplement

open Classical in
/-- The **class of flats of rank at most `r`** of a matroid, `H_r(M) = {x ↦ 1{x ∈ F} : F is a flat
of `M`, rk(F) ≤ r}` (He–He, *Private Online Learning of Littlestone Classes and Matroid Flats*,
STOC 2027 submission manuscript (sha256 21480556…c562), §1.1, p.1, and §6, p.10), as a set of
binary classifiers on the element type `α` of the matroid.

**Formalization Note** Mathlib's `Matroid α` has its ground set `M.E ⊆ α`; flats are subsets of
`M.E`, so every member of the class labels the elements outside `M.E` with `0` (`false`). The rank
is Mathlib's `M.eRk F : ℕ∞`; `{0,1}` is `Bool`. -/
def flatClass {α : Type*} (M : Matroid α) (r : ℕ) : Set (α → Bool) :=
  {g | ∃ F : Set α, M.IsFlat F ∧ M.eRk F ≤ (r : ℕ∞) ∧ g = fun x => decide (x ∈ F)}

end PrivLittlestone.Supplement


