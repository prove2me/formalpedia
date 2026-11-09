-- Prove2me | Definitions.Def_MatroidOptGame_ComputesWithin
-- name    : MatroidOptGame_ComputesWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:48.187001+00:00
-- url     : https://prove2.me/theorems/dca1f429-ae8f-43e7-90a9-43e888a0b90b
-- title:
--   Oracle program computes a value within a work bound
-- statement:
--   A program $P$ of the exact-arithmetic oracle RAM (the published model `LSWNewArcAudit.NewArc`) **computes** the integer $\mathit{out}$ on input $x$ **within work** $T$, relative to a matroid $M$, if its run on $x$ with the independence oracle of $M$ halts with output $\mathit{out}$ after at most $T$ units of work. Every instruction, including each oracle query and the halting instruction, costs one unit.
--
--   This is the notion of an efficient computation used for algorithms and strategies: the paper seeks tractability with respect to $|E|$ with the matroid given by an independence oracle.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 1, p.1; Section 2, p.4

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM
import Definitions.Def_MatroidOptGame_indepOracle

namespace MatroidOptGame

/-- Oracle-RAM program `P`, run on input `x` with the independence oracle of `M`, halts with
output `out` after at most `T` units of work.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 1, p.1 ("We seek tractability with respect to |E| … implicitly given
by oracle access") and Section 2, p.4 (the independence oracle `O`).

**Formalization Note.** "Efficient" is formalized on the published exact-arithmetic oracle RAM
`LSWNewArcAudit.NewArc` (every instruction, oracle query and the halt costs one unit of work;
after halting the state stutters, so the output is the one written at the halt). -/
noncomputable def ComputesWithin (P : LSWNewArcAudit.NewArc.OracleProgram) {n : ℕ}
    (M : Matroid (Fin n)) (x : LSWNewArcAudit.NewArc.RAMInput) (T : ℕ) (out : ℤ) : Prop :=
  ∃ t : ℕ, (LSWNewArcAudit.NewArc.oracleRun P (indepOracle M) x t).output = some out ∧
    (LSWNewArcAudit.NewArc.oracleRun P (indepOracle M) x t).work ≤ T

end MatroidOptGame


