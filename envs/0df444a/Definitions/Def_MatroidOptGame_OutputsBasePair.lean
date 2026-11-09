-- Prove2me | Definitions.Def_MatroidOptGame_OutputsBasePair
-- name    : MatroidOptGame_OutputsBasePair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:59.974956+00:00
-- url     : https://prove2.me/theorems/b70c5176-86d3-4fbd-9724-243905f2cf32
-- title:
--   Oracle program outputs a pair of sets
-- statement:
--   A program $P$ of the oracle RAM **outputs the pair** $(B_1, B_2)$ of disjoint subsets of $\{0, \dots, n-1\}$ on input $x$ within work $T$ (relative to $M$) if its run halts within work $T$ with a pointer $p$ such that, for every element $i$, integer memory cell $p + i$ holds $1$ if $i \in B_1$, $2$ if $i \in B_2$, and $0$ otherwise.
--
--   This is how an algorithm returns a pair of disjoint bases (Lemma 4).
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 4, p.5

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM
import Definitions.Def_MatroidOptGame_indepOracle

namespace MatroidOptGame

/-- Oracle-RAM program `P`, run on input `x` with the independence oracle of `M`, halts within
work `T` with a pointer `p` such that integer cell `p + i` holds `1` if `i ∈ B₁`, `2` if
`i ∈ B₂`, and `0` otherwise: it outputs the pair `(B₁, B₂)` of disjoint sets.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 4, p.5 ("there is an efficient algorithm to find a pair of disjoint bases
of minimum total weight"). -/
noncomputable def OutputsBasePair (P : LSWNewArcAudit.NewArc.OracleProgram) {n : ℕ}
    (M : Matroid (Fin n)) (x : LSWNewArcAudit.NewArc.RAMInput) (T : ℕ)
    (B₁ B₂ : Finset (Fin n)) : Prop :=
  ∃ t : ℕ, ∃ p : ℤ, (LSWNewArcAudit.NewArc.oracleRun P (indepOracle M) x t).output = some p ∧
    (LSWNewArcAudit.NewArc.oracleRun P (indepOracle M) x t).work ≤ T ∧
    ∀ i : Fin n, (LSWNewArcAudit.NewArc.oracleRun P (indepOracle M) x t).integerMemory (p + i) =
      if i ∈ B₁ then 1 else if i ∈ B₂ then 2 else 0

end MatroidOptGame


