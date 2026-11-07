-- Prove2me | Definitions.Def_MonoTestDAG_Tester
-- name    : MonoTestDAG_Tester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:09:28.129196+00:00
-- url     : https://prove2.me/theorems/05ae8471-fcf3-438d-8315-8d75eb1add7c
-- title:
--   Randomized non-adaptive testers with one-sided and two-sided error
-- statement:
--   Fix a DAG on $V$. A **randomized non-adaptive tester** has a probability space of internal randomness, a finite query set $Q_\omega\subseteq V$ depending only on the seed $\omega$, and a decision, accept or reject, computed from $\omega$ and the answers $f|_{Q_\omega}$. Its query count is worst case: it makes at most $q$ queries if $|Q_\omega|\le q$ for every $\omega$.
--
--   An **$\varepsilon$-tester with two-sided error** accepts every monotone $f$ with probability at least $2/3$, and rejects every $\varepsilon$-far $f$ with probability at least $2/3$. It has **one-sided error** if it accepts every monotone $f$ with probability $1$.
--
--   The massively parameterized model is built in: a tester is defined for one known graph, so any computation on the graph is free, and only oracle queries are counted.
--
--   **Formalization Note.** The structure `Tester` has an arbitrary probability space on a type in `Type`, so a lower bound over all testers covers every randomized tester. For each fixed $f$ the acceptance event is required to be measurable, which is what makes its probability defined. Non-adaptivity and locality are in the types: `query` takes only the seed, and `rule` receives only the answers on the queried vertices. The module also defines `Tester.acceptProb`, `Tester.QueriesAtMost`, `IsOneSidedTester` and `IsTwoSidedTester`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §1.1, p.1 and §2.4, p.11

import Mathlib
import Definitions.Def_MonoTestDAG_dmon

namespace MonoTestDAG

open MeasureTheory

/-- A randomized non-adaptive tester with oracle access to `f : V → ℝ`, for one fixed input DAG
on `V` (massively parameterized model: the DAG is known, computation on it is free, only oracle
queries to `f` are counted).

* `Ω`, `P`: the tester's internal randomness, an arbitrary probability space;
* `query ω`: the set of vertices queried under the seed `ω`; it depends on `ω` alone
  (non-adaptivity);
* `rule ω x`: the output (`true` = accept) computed from the seed and the answers `x` on the
  queried vertices only.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §1.1, p.1 and §2.4, p.11.

**Formalization Note.** Non-adaptivity and the oracle model are built into the type: the query set
is a function of the seed, and the decision sees `f` only through its restriction to that set.
The randomness space is arbitrary (any probability space in `Type`), so lower bounds over all
testers cover every randomized tester. For each fixed `f` the acceptance event must be measurable,
so that its probability is defined. -/
structure Tester (V : Type) where
  /-- The internal randomness. -/
  Ω : Type
  [instMeas : MeasurableSpace Ω]
  /-- The law of the internal randomness. -/
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  /-- The (non-adaptive) query set under the seed `ω`. -/
  query : Ω → Finset V
  /-- The decision (`true` = accept) from the seed and the answers on the queried vertices. -/
  rule : (ω : Ω) → (↥(query ω) → ℝ) → Bool
  /-- The acceptance event of every input is measurable. -/
  measurable_accept : ∀ f : V → ℝ, MeasurableSet {ω | rule ω (fun v => f v) = true}

attribute [instance] Tester.instMeas Tester.isProb

/-- The probability that the tester accepts the input `f`. -/
noncomputable def Tester.acceptProb {V : Type} (T : Tester V) (f : V → ℝ) : ENNReal :=
  T.P {ω | T.rule ω (fun v => f v) = true}

/-- The tester makes at most `q` queries on every seed (worst-case query complexity). -/
def Tester.QueriesAtMost {V : Type} (T : Tester V) (q : ℝ) : Prop :=
  ∀ ω, ((T.query ω).card : ℝ) ≤ q

/-- `T` is an `ε`-tester for monotonicity with one-sided error on the DAG `E`: every monotone `f`
is accepted with probability `1`, every `ε`-far `f` is accepted with probability at most `1/3`.
Yoshida, arXiv:2602.15341 (sha256 454609db…), §2.4, p.11. -/
def IsOneSidedTester {V : Type} [Fintype V] (E : V → V → Prop) (ε : ℝ) (T : Tester V) : Prop :=
  (∀ f, IsMonotone E f → T.acceptProb f = 1) ∧
  (∀ f, IsFar E ε f → T.acceptProb f ≤ 1 / 3)

/-- `T` is an `ε`-tester for monotonicity with two-sided error on the DAG `E`: every monotone `f`
is accepted with probability at least `2/3`, every `ε`-far `f` with probability at most `1/3`.
Yoshida, arXiv:2602.15341 (sha256 454609db…), §2.4, p.11. -/
def IsTwoSidedTester {V : Type} [Fintype V] (E : V → V → Prop) (ε : ℝ) (T : Tester V) : Prop :=
  (∀ f, IsMonotone E f → 2 / 3 ≤ T.acceptProb f) ∧
  (∀ f, IsFar E ε f → T.acceptProb f ≤ 1 / 3)

end MonoTestDAG


