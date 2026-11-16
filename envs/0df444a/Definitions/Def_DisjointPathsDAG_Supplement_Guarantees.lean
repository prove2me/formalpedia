-- Prove2me | Definitions.Def_DisjointPathsDAG_Supplement_Guarantees
-- name    : DisjointPathsDAG_Supplement_Guarantees
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:00:46.147292+00:00
-- url     : https://prove2.me/theorems/f76b93e9-7cc5-4f15-860e-c89fb2eea77a
-- title:
--   Las Vegas reporting and expected-time decision guarantees
-- statement:
--   Two guarantees of a randomized program on the machine of Section 2.1, for a fixed input, word width and field.
--
--   1. **Las Vegas reporting within $T$.** The running time is a measurable function of the random tape, its expectation is at most $T$, and every halting run outputs a solution (never "no" and never an invalid tuple). A finite expected running time forces the program to halt with probability one.
--   2. **Decision within expected time $T$ with success probability $p$.** The running time is measurable with expectation at most $T$; on an infeasible instance no halting run answers "yes"; on a feasible instance the program halts with answer "yes" with probability at least $p$.
--
--   They complement the Monte Carlo reporting guarantee and the worst-case decision guarantee of the base mission: Theorem 5.12 adds a Las Vegas algorithm under a feasibility promise, and the decision clause of Theorem 6.8 has an expected rather than a worst-case time bound.
--
--   **Formalization Note** Expected time is the lower Lebesgue integral of `haltTime` (value $\infty$ on a run that never halts) against `tapeLaw`.
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 5.12, p.33 (Las Vegas clause) and Theorem 6.8, p.43 (decision clause)

import Mathlib
import Definitions.Def_DisjointPathsDAG_Machine
import Definitions.Def_DisjointPathsDAG_Encoding

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DisjointPathsDAG.Supplement

/-!
# Las Vegas reporting and expected-time decision

Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 5.12, p.33 ("Under a feasibility
promise, root resampling gives a Las Vegas algorithm with the same expected running time") and
Theorem 6.8, p.43 ("Evaluating only the root circuit decides feasibility within the same time bound",
where the time bound of Theorem 6.8 is an expected one).

**Formalization Note** Two guarantee predicates next to `DisjointPathsDAG.ReportsWithin` and
`DisjointPathsDAG.DecidesWithin` (worst case), on the machine `DisjointPathsDAG.Machine`. Expected
running time is the lower Lebesgue integral of `haltTime` (`⊤` on runs that never halt) against the tape
law; measurability of the running time is required. A finite expected time forces halting with
probability one.
-/

/-- Las Vegas guarantee of a reporting algorithm `Prog` (width `w`, field `F`, input `I`): measurable
running time with expectation at most `T`, and **every** halting run outputs a solution (`Sol`), never
"no". It is used under a feasibility promise. -/
def LasVegasWithin (k : ℕ) (Prog : Program) (w : ℕ) (F : Type) [Field F] [Finite F] (I : Input F)
    (T : ℝ) (Sol : (Fin k → List ℕ) → Prop) : Prop :=
  Measurable (fun ω => (haltTime w F Prog I ω : ℝ≥0∞)) ∧
  ∫⁻ ω, (haltTime w F Prog I ω : ℝ≥0∞) ∂(tapeLaw F) ≤ ENNReal.ofReal T ∧
  ∀ (ω : Tape F) (t : ℕ), HaltsAt w F Prog I ω t →
    ∃ P, decodePaths k (outWords I (stateAt w F Prog I ω t)) = some P ∧ Sol P

/-- Guarantees of a decision algorithm `Prog` with an **expected** time bound (width `w`, field `F`,
input `I`): measurable running time with expectation at most `T`; on an infeasible instance no halting
run answers "yes"; on a feasible one it halts with "yes" with probability at least `p`. -/
def DecidesExpWithin (Prog : Program) (w : ℕ) (F : Type) [Field F] [Finite F] (I : Input F) (T : ℝ)
    (feasible : Prop) (p : ℝ) : Prop :=
  Measurable (fun ω => (haltTime w F Prog I ω : ℝ≥0∞)) ∧
  ∫⁻ ω, (haltTime w F Prog I ω : ℝ≥0∞) ∂(tapeLaw F) ≤ ENNReal.ofReal T ∧
  (¬ feasible → ∀ (ω : Tape F) (t : ℕ), HaltsAt w F Prog I ω t →
    ¬ answerYes I (stateAt w F Prog I ω t)) ∧
  (feasible →
    MeasurableSet {ω : Tape F | ∃ t, HaltsAt w F Prog I ω t ∧ answerYes I (stateAt w F Prog I ω t)} ∧
    ENNReal.ofReal p ≤
      tapeLaw F {ω : Tape F | ∃ t, HaltsAt w F Prog I ω t ∧ answerYes I (stateAt w F Prog I ω t)})

end DisjointPathsDAG.Supplement


