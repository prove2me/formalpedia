-- Prove2me | Definitions.Def_MatroidOptGame_rankOf
-- name    : MatroidOptGame_rankOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:46.525201+00:00
-- url     : https://prove2.me/theorems/09e90aee-d9e9-415b-933e-edc18e1fbc03
-- title:
--   Rank $r_M(F)$ of a set
-- statement:
--   For a matroid $M$ and a finite set $F$, the **rank** $r_M(F)$ is the maximum size of an independent set of $M$ contained in $F$. In particular $r_M(E)$ is the size of a base of $M$.
--
--   **Formalization Note** Computed from Mathlib's extended-natural rank `Matroid.eRk`, which is finite (at most $|F|$) on a finite set. With ground set the whole type, $r_M(E)$ is the rank of `Finset.univ`.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, p.19

import Mathlib

namespace MatroidOptGame

/-- The rank `r_M(F)` of a finite set `F`: the maximum size of an independent subset of `F`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, p.19 ("The rank function r_M : 2^E → ℕ of M assigns to every
subset F of E the maximum size of an independent set of M contained in F").

**Formalization Note.** Mathlib's `Matroid.eRk` is `ℕ∞`-valued; on a finite set it is finite
(at most `|F|`), so `toNat` loses nothing. With `M.E = Set.univ`, `rankOf M Finset.univ` is
`r_M(E)`. -/
noncomputable def rankOf {α : Type*} (M : Matroid α) (F : Finset α) : ℕ :=
  (M.eRk (F : Set α)).toNat

end MatroidOptGame


