-- Prove2me | Definitions.Def_QGraphColl_eventProb
-- name    : QGraphColl_eventProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:28.775649+00:00
-- url     : https://prove2.me/theorems/d8470cd2-b2aa-4576-b92b-b5d2624b4343
-- title:
--   Output events of a $T$-query algorithm and promise domains
-- statement:
--   A $T$-query algorithm with standard queries to the input bits $x\in\{0,1\}^V$ starts from a fixed unit vector, applies fixed unitaries $U_0,\dots,U_T$, and between consecutive unitaries one oracle call $|v,b\rangle\mapsto|v,b\oplus x_v\rangle$ (tensored with the identity on a finite workspace); it then measures in the computational basis and applies a classical output map to the outcome.
--
--   $\Pr_x[E]$ denotes the probability, on input $x$, that the output satisfies the event $E$. For a predicate $P$ on inputs, $D_P=\{x\in\{0,1\}^V: P(x)\}$ is the corresponding promise domain.
--
--   These two notions express every guarantee of the mission: a test "accepts every positive input and rejects negative inputs satisfying a bound" computes $\mathrm{gc}_G$ with small error on the domain of positive inputs and bounded negative inputs, and procedures whose outputs are counts, samples or graphs are judged through $\Pr_x[E]$.
--
--   **Formalization Note.** The algorithm model is the published `QAlgorithms.QueryAlg ι Bool W T` with `QAlgorithms.xorOracle`, and `eventProb A x out E` is `QAlgorithms.probEvent` of the final state for the event `E (out z)`. `dom P` is a `Finset` usable as the domain of `QAlgorithms.QueryAlg.ComputesWithError`.
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), §2 p.12 (query model, Q2(f) with error at most 1/3 on every input); p.14 ('fixed query limits', 'the assigned error probability')

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace QGraphColl

open QAlgorithms

/-!
# Output events of a query algorithm, and promise domains

A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…),
§2, p.12 (query model: queries to the input bits, error "on every input"); p.14 ("fixed query
limits", "the assigned error probability").

**Formalization Note.**
* The query model is the published `QAlgorithms.QueryAlg ι Bool W T` (unit start vector,
  input-independent unitaries, exactly `T` standard queries `|v, b⟩ ↦ |v, b ⊕ x_v⟩`, workspace `W`),
  with the oracle `QAlgorithms.xorOracle x`.
* `eventProb A x out E` is the probability that, run on the input `x`, the algorithm's final state,
  measured in the computational basis, gives an outcome `z` whose classical output `out z`
  satisfies the event `E`. Outputs of any type are allowed (a Boolean answer, a count, a list of
  samples, a graph).
* `dom P` is the finite set of inputs satisfying `P`, used as the promise domain `D` of
  `QAlgorithms.QueryAlg.ComputesWithError`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- p.12, p.14: the probability that the `T`-query algorithm `A`, run with standard queries to the
input `x`, produces an outcome whose output `out z` satisfies `E`. -/
noncomputable def eventProb {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ} {β : Type*}
    (A : QueryAlg V Bool W T) (x : V → Bool) (out : (V × Bool) × W → β) (E : β → Prop) : ℝ := by
  classical exact probEvent (A.finalState (xorOracle x)) fun z => E (out z)

/-- The promise domain `{x ∈ {0,1}^V : P x}` as a `Finset`. -/
noncomputable def dom (P : (V → Bool) → Prop) : Finset (V → Bool) := by
  classical exact Finset.univ.filter P

theorem mem_dom {P : (V → Bool) → Prop} {x : V → Bool} : x ∈ dom P ↔ P x := by
  unfold dom
  simp

end QGraphColl


