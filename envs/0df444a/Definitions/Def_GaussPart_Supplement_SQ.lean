-- Prove2me | Definitions.Def_GaussPart_Supplement_SQ
-- name    : GaussPart_Supplement_SQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:04:38.231506+00:00
-- url     : https://prove2.me/theorems/914ec9f5-c817-4bf6-a7a3-692998917c5a
-- title:
--   Statistical-query conventions: tolerance bounds, success mass, query counts, two oracles
-- statement:
--   Statistical-query (SQ) algorithms are the published randomized adaptive algorithms (`PrivLearn_SQSim_SQAlg`) with adversarial oracles: a query is a function $g:X\to[-1,1]$ with tolerance $\tau$, and a valid answer $v$ satisfies $|v-\mathbb E[g]|\le\tau$.
--
--   - An algorithm makes **no query of tolerance at most $\tau_0$** if every query it can ask is a measurable $[-1,1]$-valued function with tolerance $\tau>\tau_0$.
--   - Its **success mass** for a set $G$ of outputs is the probability that it stops with an output in $G$.
--   - It **makes at least $Q$ queries** against an oracle if, with positive probability, some trajectory has answered at least $Q$ queries.
--   - **Two oracles** (training and test): queries are functions on $(\mathbb R^d\times\mathbb R)\sqcup\mathbb R^d$ vanishing on one summand, answered against the training law on the first summand and the test law on the second.
--
--   These conventions state the SQ lower bounds of Theorems 5.4, 5.14, 7.3 and E.2.
--
--   **Formalization Note** A bound imposed on every state of the algorithm is equivalent to one on the states a run can reach, since unreachable states can be changed without changing any run.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Definition A.4, p.70 (PDF p.72); Theorem 7.3, p.64 (PDF p.66)

import Mathlib
import Definitions.Def_PrivLearn_SQSim_SQAlg
import Definitions.Def_GaussPart_Cell

open MeasureTheory

namespace GaussPart

namespace Supplement

open PrivLearn.SQSim

/-- The number of statistical queries answered along a trajectory of the published
`PrivLearn.SQSim.SQAlg` (states newest first): every state before the current one asked a query
and was answered, so a trajectory `s :: h` has made `|h|` queries. -/
def queriesMade {St : Type*} : List St → ℕ
  | [] => 0
  | _ :: h => h.length

/-- **Statistical queries of tolerance above `τ₀`** (Definition A.4, arXiv:2611.05264, sha256
7e0ca6d4…, p.70, PDF p.72): every query `(g, τ)` that `B` can ask is a measurable function
`g : X → [−1, 1]` with tolerance `τ > τ₀`. Each query carries its own tolerance.

**Formalization Note.** The condition is imposed on every state of `B`. A state no valid oracle
ever leads to can be changed without changing any run, so this is the paper's "makes no query of
tolerance at most `τ₀`". -/
def TolAbove {Dom Out St : Type*} [MeasurableSpace Dom] (B : SQAlg Dom Out St) (τ₀ : ℝ) : Prop :=
  ∀ (s : St) (g : Dom → ℝ) (τ : ℝ) (k : ℝ → PMF St), B.step s = .inr (g, τ, k) →
    Measurable g ∧ (∀ u, |g u| ≤ 1) ∧ τ₀ < τ

/-- The probability that `B`, run against the oracle `O`, stops with an output in `G`. -/
noncomputable def successMass {Dom Out St : Type*} (B : SQAlg Dom Out St) (O : List St → ℝ)
    (G : Set Out) : ENNReal :=
  ∑' o, G.indicator (B.outputLaw O) o

/-- **Some run makes at least `Q` queries**: against the oracle `O`, with positive probability
the trajectory at some time `N` has made at least `Q` queries. -/
def MakesManyQueries {Dom Out St : Type*} (B : SQAlg Dom Out St) (O : List St → ℝ) (Q : ℝ) :
    Prop :=
  ∃ (N : ℕ) (traj : List St), B.run O N (.inr traj) ≠ 0 ∧ Q ≤ (queriesMade traj : ℝ)

/-- **Two SQ oracles** (Theorem 7.3, p.64, PDF p.66: "SQ access to the labeled training
distribution and the unlabeled test distribution"). A query of a two-oracle algorithm is a function
on `(ℝᵈ × ℝ) ⊕ ℝᵈ` that vanishes on one summand: it is a query to the training oracle if it
vanishes on `ℝᵈ`, to the test oracle if it vanishes on `ℝᵈ × ℝ`. -/
def OneSided {d : ℕ} {Out St : Type*} (B : SQAlg ((Vec d × ℝ) ⊕ Vec d) Out St) : Prop :=
  ∀ (s : St) (g : (Vec d × ℝ) ⊕ Vec d → ℝ) (τ : ℝ) (k : ℝ → PMF St),
    B.step s = .inr (g, τ, k) → (∀ u, g (.inr u) = 0) ∨ (∀ u, g (.inl u) = 0)

/-- The measure against which the two oracles answer: `train` on the left summand plus `test` on
the right. For a one-sided query `g`, `∫ g` is `E_train[g]` or `E_test[g]`, so an oracle valid for
this measure is a valid training oracle and a valid test oracle at once. -/
noncomputable def twoOracleMeasure {d : ℕ} (train : Measure (Vec d × ℝ)) (test : Measure (Vec d)) :
    Measure ((Vec d × ℝ) ⊕ Vec d) :=
  train.map Sum.inl + test.map Sum.inr

end Supplement

end GaussPart


