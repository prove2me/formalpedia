-- Prove2me | Definitions.Def_MatroidOptGame_minBaseWeight
-- name    : MatroidOptGame_minBaseWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:50.75771+00:00
-- url     : https://prove2.me/theorems/72bb8d68-a84d-4110-afbb-d2c550e1887e
-- title:
--   Minimum base weight $w(B_{\min}(M,w))$
-- statement:
--   For a matroid $M$ and weights $w : E \to \mathbb N$, $w(B_{\min}(M, w))$ is the minimum weight of a base of $M$:
--   $$
--   w(B_{\min}(M, w)) = \min\{ w(B) : B \text{ a base of } M \}.
--   $$
--   The paper fixes an arbitrary minimum-weight base $B_{\min}(M, w)$; every statement uses it only through this number. MAX's excess payoff and the excess value subtract it.
--
--   **Formalization Note** Defined as the infimum in $\mathbb N$ of the set of base weights. A finite matroid has a base, so the set is nonempty and the infimum is attained.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib
import Definitions.Def_MatroidOptGame_weight

namespace MatroidOptGame

/-- `w(B_min(M, w))`: the minimum weight of a base of `M`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 ("let B_min(M, w) denote any fixed minimum-weight base of M").
The paper's fixed minimum-weight base enters every statement only through its weight.

**Formalization Note.** This is `sInf` of the set of base weights in `ℕ`. On a finite type the
set is nonempty (every matroid has a base, and it is finite), so the infimum is the minimum and
no junk value arises. -/
noncomputable def minBaseWeight {α : Type*} (M : Matroid α) (w : α → ℕ) : ℕ :=
  sInf {x : ℕ | ∃ B : Finset α, M.IsBase (B : Set α) ∧ weight w B = x}

end MatroidOptGame


