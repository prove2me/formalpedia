-- Prove2me | Definitions.Def_MetricalTaskSystem_Randomized_TaskDistribution
-- name    : MetricalTaskSystem_Randomized_TaskDistribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:17:39.062185+00:00
-- url     : https://prove2.me/theorems/e24d1569-1742-442d-96c1-0409e0475009
-- title:
--   Random task sequences, $m_j$, $E(c_0(\mathbf T^j))$, unit elementary tasks and the coupon-collector time
-- statement:
--   This file defines the quantities used in the lower-bound half of Theorem 7.1 (Yao's principle).
--
--   Tasks are drawn from a finite alphabet: a letter $a\in\alpha$ stands for the task $U_a\in\mathbb R_{\ge 0}^S$, and an infinite task sequence is a sequence of letters $\omega=(\omega_0,\omega_1,\dots)$ distributed according to a probability measure $D$. For $j\ge 0$, $\mathbf T^j$ denotes the first $j$ tasks $U_{\omega_0},\dots,U_{\omega_{j-1}}$. For an initial state $s_0$:
--
--   1. $E(c_A(\mathbf T^j))=\int c_A(\mathbf T^j)\,dD$ is the expected cost of a deterministic on-line algorithm $A$;
--   2. $E(c_0(\mathbf T^j))=\int c_0(\mathbf T^j)\,dD$ is the expected off-line optimum;
--   3. $m_j=\inf_A E(c_A(\mathbf T^j))$, the infimum over all deterministic on-line algorithms.
--
--   For $s\in S$, the **unit elementary task** $U_s$ has processing cost $1$ in state $s$ and $0$ in every other state. The **uniform task distribution** generates the successive tasks independently and uniformly from the unit elementary tasks; identifying $U_s$ with $s$, it is the law of an i.i.d. sequence of uniformly distributed states. Finally, the **coupon-collector time** of a sequence $\omega$ of states is the least $k$ such that $\omega_0,\dots,\omega_{k-1}$ contains every state of $S$ (and $+\infty$ if there is no such $k$).
--
--   **Formalization Note** Restricting to a finite task alphabet makes $\omega\mapsto c_A(\mathbf T^j)$ depend on finitely many coordinates and take finitely many values, so every expectation above is a genuine (finite) integral for every deterministic algorithm $A$. The alphabet and the state set carry measurable spaces in which singletons are measurable (required in the statements that use them). The uniform distribution is `Measure.infinitePi` of the uniform `PMF` on `S`. The coupon-collector time is valued in $[0,\infty]$.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), pp. 759-760, Section 7, Lemma 7.2 and proof of the lower bound

import Mathlib
import Definitions.Def_MetricalTaskSystem_Randomized_Model

namespace MetricalTaskSystem.Randomized

open MeasureTheory

/-- The first `j` tasks `Tʲ` (p. 759) of an infinite task sequence drawn from a finite task
alphabet: `ω : ℕ → α` is a sequence of letters and `U a` is the task (a cost vector) of the
letter `a`, so the `i`th task of `Tʲ` is `U (ω i)`. -/
def prefixTasks {S α : Type} (U : α → S → ℝ) (ω : ℕ → α) (j : ℕ) : Fin j → S → ℝ :=
  fun i => U (ω i)

/-- `E(c_A(Tʲ))` (p. 759): the expected cost of the deterministic on-line algorithm `A` on the
first `j` tasks, when the infinite task sequence is distributed according to `D`. -/
noncomputable def expOnlineCost {S α : Type} [MeasurableSpace α] (d : S → S → ℝ)
    (A : OnlineAlgorithm S) (s₀ : S) (U : α → S → ℝ) (D : Measure (ℕ → α)) (j : ℕ) : ℝ :=
  ∫ ω, onlineCost d A s₀ (prefixTasks U ω j) ∂D

/-- `E(c₀(Tʲ))` (p. 759): the expected optimal off-line cost of the first `j` tasks. -/
noncomputable def expOfflineCost {S α : Type} [Fintype S] [DecidableEq S] [MeasurableSpace α]
    (d : S → S → ℝ) (s₀ : S) (U : α → S → ℝ) (D : Measure (ℕ → α)) (j : ℕ) : ℝ :=
  ∫ ω, offlineOpt d s₀ (prefixTasks U ω j) ∂D

/-- `m_j` (p. 759): the minimum over all deterministic on-line algorithms `A` of `E(c_A(Tʲ))`,
written as an infimum. -/
noncomputable def minDetExpCost {S α : Type} [MeasurableSpace α] (d : S → S → ℝ) (s₀ : S)
    (U : α → S → ℝ) (D : Measure (ℕ → α)) (j : ℕ) : ℝ :=
  ⨅ A : OnlineAlgorithm S, expOnlineCost d A s₀ U D j

/-- The **unit elementary task** `U_s` (p. 760): processing cost `1` in state `s` and `0` in every
other state. -/
def unitTask {S : Type} [DecidableEq S] (s : S) : S → ℝ :=
  fun t => if t = s then 1 else 0

/-- The law of an infinite sequence of independent states, each uniformly distributed on `S`
(p. 760: "generating each successive task independently and uniformly from the unit
elementary tasks", identifying `U_s` with `s`). -/
noncomputable def uniformStateSeq (S : Type) [Fintype S] [Nonempty S] [MeasurableSpace S] :
    Measure (ℕ → S) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype S).toMeasure)

/-- The coupon-collector time (p. 760): the number of terms of `ω 0, ω 1, …` needed until every
state of `S` has appeared, i.e. the least `k` with `{ω 0, …, ω (k−1)} = S`; it is `⊤` if some
state never appears. -/
noncomputable def collectTime {S : Type} (ω : ℕ → S) : ENNReal :=
  ⨅ (k : ℕ) (_ : ∀ s : S, ∃ i < k, ω i = s), (k : ENNReal)

end MetricalTaskSystem.Randomized


