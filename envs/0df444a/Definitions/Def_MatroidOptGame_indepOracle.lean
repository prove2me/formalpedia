-- Prove2me | Definitions.Def_MatroidOptGame_indepOracle
-- name    : MatroidOptGame_indepOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:46.339861+00:00
-- url     : https://prove2.me/theorems/7548fe14-c9fb-4eae-a418-8b8a81d8bbc4
-- title:
--   Independence oracle of a matroid on $\{0,\dots,n-1\}$
-- statement:
--   For a matroid $M$ whose ground set is labelled $\{0, \dots, n-1\}$, the **independence oracle** is the function on subsets
--   $$
--   O(F) = \begin{cases} 1 & F \text{ independent in } M,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   This is the paper's black-box oracle $O : 2^E \to \{\text{true}, \text{false}\}$ with true and false written as $1$ and $0$. Programs access the matroid only through this oracle.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.4

import Mathlib

namespace MatroidOptGame

open Classical in
/-- The independence oracle of a matroid on `Fin n`: `O(F) = 1` if `F` is independent and `0`
otherwise.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.4 ("a black-box independence oracle O : 2^E → {true, false} (with
O(F) = true iff F ∈ I, for all F ⊆ E)").

**Formalization Note.** `true`/`false` are encoded as `1`/`0`, the integer answers of the oracle
RAM `LSWNewArcAudit.NewArc`. Programs reach the matroid only through this oracle. -/
noncomputable def indepOracle {n : ℕ} (M : Matroid (Fin n)) : Finset (Fin n) → ℤ :=
  fun S => if M.Indep (S : Set (Fin n)) then 1 else 0

end MatroidOptGame


