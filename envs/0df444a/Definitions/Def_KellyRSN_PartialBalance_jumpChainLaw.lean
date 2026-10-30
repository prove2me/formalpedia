-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_jumpChainLaw
-- name    : KellyRSN_PartialBalance_jumpChainLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:35:26.04125+00:00
-- url     : https://prove2.me/theorems/8f41d26d-c30c-4196-84a2-9b48c4a8827a
-- title:
--   Law of the jump chain started at a state $j$
-- statement:
--   Let $q$ be transition rates on a countable state space $\mathcal S$ and $p(j,k)$ the jump probabilities of (1.4). The **jump chain** $X^J(0), X^J(1), \dots$ of the Markov process records its successive states: $X^J(0) = X(0)$, $X^J(1)$ is the next state visited, and so on. It is the discrete-time Markov chain with transition probabilities $p$.
--
--   For $j \in \mathcal S$, $\mathbb P_j$ denotes the law of the jump chain started at $j$: the probability measure on paths $\omega = (\omega_0, \omega_1, \dots) \in \mathcal S^{\mathbb N}$ with $\omega_0 = j$ and
--   $$
--   \mathbb P_j(\omega_1 = k_1, \dots, \omega_n = k_n) = p(j,k_1)\, p(k_1,k_2) \cdots p(k_{n-1},k_n).
--   $$
--
--   It is used to express non-explosion and to define the chains observed at the exit and entry instants of a set.
--
--   **Formalization Note** Built with the Ionescu–Tulcea theorem (`ProbabilityTheory.Kernel.traj`) from the time-homogeneous kernel $p$; $\mathcal S$ carries the discrete σ-algebra (countable with measurable singletons).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 3 (PDF p. 6), §1.1, definition of the jump chain and equation (1.4)

import Mathlib
import Definitions.Def_KellyRSN_PartialBalance_jumpProb

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace KellyRSN.PartialBalance

variable {S : Type*} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The row `k ↦ jumpProb q j k` as a probability mass function (auxiliary). -/
noncomputable def jumpPMF (q : S → S → ℝ≥0∞) (j : S) : PMF S :=
  ⟨jumpProb q j, by rw [← tsum_jumpProb q j]; exact ENNReal.summable.hasSum⟩

/-- The jump-chain transition kernel `j ↦ p(j, ·)` (auxiliary). -/
noncomputable def jumpKernel (q : S → S → ℝ≥0∞) : Kernel S S :=
  Kernel.ofFunOfCountable (fun j => (jumpPMF q j).toMeasure)

instance (q : S → S → ℝ≥0∞) : IsMarkovKernel (jumpKernel q) :=
  ⟨fun j => by
    change IsProbabilityMeasure (jumpPMF q j).toMeasure
    infer_instance⟩

/-- **Law of the jump chain started at `j`.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, §1.1, p. 3 (PDF p. 6): "There is thus
a natural way to associate a Markov chain `X^J(t)` with a Markov process `X(t)`. Let `X^J(0)` be
`X(0)`, let `X^J(1)` be the next state the Markov process `X(t)` moves to after time `t = 0`, let
`X^J(2)` be the next state after that, and so on. The Markov chain `X^J(t)` is called the jump
chain of the Markov process `X(t)`, and its transition probabilities are given by the relation
(1.4)."

`jumpChainLaw q j` is the probability measure on paths `ω : ℕ → S` of the time-homogeneous Markov
chain with transition probabilities `jumpProb q` and `ω 0 = j`.

**Formalization Note.** Built with the Ionescu–Tulcea theorem (`ProbabilityTheory.Kernel.traj`)
from the kernels `x ↦ p(x n, ·)`, which depend only on the current state. `S` is countable with
measurable singletons, so its σ-algebra is discrete. -/
noncomputable def jumpChainLaw (q : S → S → ℝ≥0∞) (j : S) : Measure (ℕ → S) :=
  Kernel.traj (X := fun _ => S)
    (fun n => (jumpKernel q).comap (fun x : (Π _ : Iic n, S) => x ⟨n, mem_Iic.2 le_rfl⟩)
      (measurable_pi_apply _))
    0 (fun _ => j)

end KellyRSN.PartialBalance


