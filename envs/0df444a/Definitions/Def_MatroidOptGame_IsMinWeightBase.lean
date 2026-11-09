-- Prove2me | Definitions.Def_MatroidOptGame_IsMinWeightBase
-- name    : MatroidOptGame_IsMinWeightBase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:38.718795+00:00
-- url     : https://prove2.me/theorems/0b007af2-c8e5-42ee-a50c-7e2b2ad60259
-- title:
--   Minimum-weight base of a matroid
-- statement:
--   Let $M$ be a matroid and $w : E \to \mathbb N$ a weight function. A set $B$ is a **minimum-weight base** of $M$ with respect to $w$ if $B$ is a base of $M$ and
--   $$
--   w(B) \le w(B') \quad \text{for every base } B' \text{ of } M .
--   $$
--   The paper writes $B_{\min}(M, w)$ for any fixed such base; the set of all of them is $\mathcal B(M, w)$.
--
--   **Formalization Note** Bases are finite sets (`Finset`) coerced to sets; on a finite ground type nothing is lost.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 (B_min(M, w)); Section 2.1.1, p.5 (B(M, w)); Appendix A, Theorem 22, p.20

import Mathlib
import Definitions.Def_MatroidOptGame_weight

namespace MatroidOptGame

/-- `B` is a minimum-weight base of `M` with respect to `w`: a base whose weight is at most the
weight of every base.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 (`B_min(M, w)`, "any fixed minimum-weight base"), and
Appendix A, Theorem 22, p.20.

**Formalization Note.** Bases are `Finset`s coerced to `Set`s; on a finite type every set is a
`Finset`, so nothing is lost. -/
def IsMinWeightBase {α : Type*} (M : Matroid α) (w : α → ℕ) (B : Finset α) : Prop :=
  M.IsBase (B : Set α) ∧ ∀ B' : Finset α, M.IsBase (B' : Set α) → weight w B ≤ weight w B'

end MatroidOptGame


