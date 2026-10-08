-- Prove2me | Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
-- name    : RiskSensMDP_AverageCost_HarrisRecurrence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:19.553983+00:00
-- url     : https://prove2.me/theorems/d2931a90-0c4b-453b-bdf7-71e416c116cd
-- title:
--   Harris recurrence and positive Harris recurrence of a Markov kernel (Meyn–Tweedie)
-- statement:
--   Let $P$ be a Markov kernel on a measurable space $E$. For $x\in E$ write $\mathbb P_x$ for the law, on the path space $E^{\mathbb N_0}$, of the Markov chain $(X_n)_{n\ge 0}$ with transition kernel $P$ and $X_0=x$ (constructed by the Ionescu-Tulcea theorem).
--
--   1. The chain is **Harris recurrent** if there is a nonzero $\sigma$-finite measure $\varphi$ on $E$ such that for every measurable $B\subseteq E$ with $\varphi(B)>0$ and every $x\in E$,
--   $$
--   \mathbb P_x\big(X_n\in B \text{ for infinitely many } n\big)=1 .
--   $$
--   2. The chain is **positive Harris recurrent** if it is Harris recurrent and admits an invariant probability measure $\mu$, that is, $\mu P=\mu$, where $(\mu P)(B)=\int P(x,B)\,\mu(dx)$.
--
--   These are the notions of Meyn and Tweedie, *Markov Chains and Stochastic Stability* (2nd ed., 2009), §9.1 and §10.1, which Bäuerle and Rieder invoke in §5 without restating them. Positive Harris recurrence is the hypothesis under which the law of large numbers for additive functionals (Meyn–Tweedie, Theorem 17.0.1) holds from every initial state. It does not require aperiodicity.
--
--   **Formalization Note** Meyn and Tweedie define a Harris recurrent chain as a $\psi$-irreducible chain in which every set of positive $\psi$-measure is visited infinitely often from every starting point. The definition above asks for one nonzero $\sigma$-finite $\varphi$ with that property; such a $\varphi$ makes the chain $\varphi$-irreducible, so the two definitions agree. The kernel $P$ is generic: the definition is reusable for any Markov chain on a measurable space. It is not the platform's `MarkovErgodicity` (total-variation convergence $\|P^n(x,\cdot)-\pi\|\to 0$), which also forces aperiodicity and is strictly stronger.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), p. 17, §5 (the notion used in Theorems 5.1 and 5.2); definitions from Meyn & Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge University Press, 2009, §9.1 (Harris recurrence) and §10.1 (positive Harris recurrence)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Finset

namespace RiskSensMDP.AverageCost

/-- One step of a time-homogeneous Markov chain with transition kernel `P`, written as a kernel
from the path `(x₀, …, x_n)` (indexed by `Finset.Iic n`) to the next state `x_{n+1}`: it applies
`P` to the current state `x_n`. -/
noncomputable def chainStep {E : Type*} [MeasurableSpace E] (P : Kernel E E) (n : ℕ) :
    Kernel (Π _ : Iic n, E) E :=
  P.comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance {E : Type*} [MeasurableSpace E] (P : Kernel E E) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (chainStep P n) := by
  unfold chainStep; exact Kernel.IsMarkovKernel.comap _ _

/-- The law `P_x` of the Markov chain `(X_n)_{n ∈ ℕ₀}` with transition kernel `P` started at
`X₀ = x`, a probability measure on the path space `ℕ → E`, built by the Ionescu-Tulcea theorem
(`Kernel.trajMeasure`). -/
noncomputable def chainLaw {E : Type*} [MeasurableSpace E] (P : Kernel E E) [IsMarkovKernel P]
    (x : E) : Measure (ℕ → E) :=
  Kernel.trajMeasure (X := fun _ => E) (Measure.dirac x) (chainStep P)

/-- **Harris recurrence** (Meyn & Tweedie 2009, §9.1): there is a nonzero σ-finite measure `φ` on
`E` such that for every measurable `B` with `φ(B) > 0` and every starting state `x`, the chain
started at `x` visits `B` infinitely often almost surely,
`P_x(X_n ∈ B for infinitely many n) = 1`. -/
def IsHarrisRecurrent {E : Type*} [MeasurableSpace E] (P : Kernel E E) [IsMarkovKernel P] :
    Prop :=
  ∃ φ : Measure E, SigmaFinite φ ∧ φ ≠ 0 ∧
    ∀ B : Set E, MeasurableSet B → 0 < φ B → ∀ x : E,
      chainLaw P x {ω | ∃ᶠ n in atTop, ω n ∈ B} = 1

/-- **Positive Harris recurrence** (Meyn & Tweedie 2009, §10.1): the chain is Harris recurrent and
admits an invariant probability measure `μ`, i.e. `μ P = μ`. -/
def IsPositiveHarrisRecurrent {E : Type*} [MeasurableSpace E] (P : Kernel E E)
    [IsMarkovKernel P] : Prop :=
  IsHarrisRecurrent P ∧ ∃ μ : Measure E, IsProbabilityMeasure μ ∧ Kernel.Invariant P μ

end RiskSensMDP.AverageCost


