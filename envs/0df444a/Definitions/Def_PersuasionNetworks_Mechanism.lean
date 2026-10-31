-- Prove2me | Definitions.Def_PersuasionNetworks_Mechanism
-- name    : PersuasionNetworks_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:56.526837+00:00
-- url     : https://prove2.me/theorems/5b502a23-a1c5-433e-a7d3-e2e7e755ac58
-- title:
--   State, public signaling mechanisms, posterior means, level mechanisms
-- statement:
--   The state $T$ has law $\mu$ on a closed subinterval $\mathcal T$ of $\mathbb R$, with an absolutely continuous distribution function and $\mathbb E[|T|]<\infty$.
--
--   A public signaling mechanism consists of a signal space $\mathcal S$ and a family of distributions $\{\pi(\cdot;t)\}_{t}$ on it: a Markov kernel from states to signals. Given the signal $S$, this item defines:
--
--   1. the posterior mean $\mathbb E[T\mid S=s]$;
--   2. the designer's expected payoff $\mathbb E[\nu(\mathbb E[T\mid S])]$, for a payoff function $\nu$ of the posterior mean;
--   3. for integer signals, the tuple $p_k=\mathbb P(S=k)$ and $z_k=\mathbb E[T\cdot\mathbf 1\{S=k\}]$;
--   4. **level mechanisms**: the signal set is $\{1,\dots,K\}$ and each signal $k$ of positive probability induces a posterior mean in $[b_k,b_{k-1})$;
--   5. **consistency** with a tuple $(p_k,z_k)$: $\mathbb P(S=k)=p_k$, $\mathbb E[T\cdot\mathbf 1\{S=k\}]=z_k$, and $\mathbb E[T\mid S=k]=z_k/p_k$ when $p_k>0$.
--
--   The signal space is arbitrary, so optimality statements range over all mechanisms and not only finite or deterministic ones.
--
--   **Formalization Note** That $\mu$ is a probability measure is a separate instance argument. The posterior is Mathlib's `ProbabilityTheory.posterior`, which needs standard Borel structure only on the state space. The kernel is defined on all of $\mathbb R$; since $\mu(\mathcal T^c)=0$ this changes nothing. The signal set $\{1,\dots,K\}$ is encoded in $\mathbb N$ with all mass on $\{1,\dots,K\}$.
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, §2, pp.9–10 and footnote 7; §3.1, p.16

import Mathlib
import Definitions.Def_PersuasionNetworks_StepPayoff

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **The state** (standing assumptions of the model). `μ` is the law of the state `T`, supported on
`𝒯`. Candogan, SSRN 3346144 (preprint), §2, p.9: "`𝒯` is a closed subinterval of `ℝ`", "`F` is
absolutely continuous", "`E[|T|] < ∞`".

**Formalization Note.** That `μ` is a probability measure is the separate instance
`[IsProbabilityMeasure μ]` of each statement. `𝒯` may be `ℝ`, a half-line or a bounded interval, and
need not be the exact support of `μ`; `F` need not be strictly increasing. -/
structure IsState (μ : Measure ℝ) (𝒯 : Set ℝ) : Prop where
  absolutelyContinuous : μ ≪ volume
  integrable : Integrable id μ
  isClosed : IsClosed 𝒯
  ordConnected : 𝒯.OrdConnected
  measure_compl : μ 𝒯ᶜ = 0

/-- The **posterior mean** `E[T | S = s]` of a mechanism. A public signaling mechanism is a signal
space `S` together with a family `{π(·; t)}` of distributions on `S`, here the kernel `κ`; `κ†μ` is
the conditional law of the state given the signal. Candogan, SSRN 3346144 (preprint), §2.1, p.10
and footnote 7.

**Formalization Note.** `S` is an arbitrary measurable space: Mathlib's `posterior` needs standard
Borel structure only on the state space `ℝ`. The kernel is defined on all of `ℝ` rather than on `𝒯`,
which is harmless since `μ 𝒯ᶜ = 0`. As a conditional expectation, the value is pinned down only for
`κ ∘ₘ μ`-almost every `s`, and at every `s` of positive `κ ∘ₘ μ`-mass when `S` has measurable
singletons. -/
noncomputable def posteriorMean (μ : Measure ℝ) [IsFiniteMeasure μ] {S : Type*}
    [MeasurableSpace S] (κ : Kernel ℝ S) [IsFiniteKernel κ] (s : S) : ℝ :=
  ∫ t, t ∂(posterior κ μ s)

/-- The **designer's expected payoff** `E[ν(E[T | S])]` under mechanism `κ`, where `ν` is the payoff
as a function of the posterior mean. Candogan, SSRN 3346144 (preprint), §3, p.14, and Proposition 3,
p.15. The signal law is `κ ∘ₘ μ`. -/
noncomputable def designerPayoff (μ : Measure ℝ) [IsFiniteMeasure μ] (ν : ℝ → ℝ) {S : Type*}
    [MeasurableSpace S] (κ : Kernel ℝ S) [IsFiniteKernel κ] : ℝ :=
  ∫ s, ν (posteriorMean μ κ s) ∂(κ ∘ₘ μ)

/-- `p_k = P(S = k)`, the first component of the tuple attached to a mechanism with integer signals.
Candogan, SSRN 3346144 (preprint), §3.1, p.16. -/
noncomputable def signalProb (μ : Measure ℝ) (κ : Kernel ℝ ℕ) (k : ℕ) : ℝ :=
  (κ ∘ₘ μ).real {k}

/-- `z_k = E[T · 1{S = k}]`, the second component of the tuple attached to a mechanism with integer
signals. Candogan, SSRN 3346144 (preprint), §3.1, p.16. -/
noncomputable def signalMoment (μ : Measure ℝ) (κ : Kernel ℝ ℕ) (k : ℕ) : ℝ :=
  ∫ t, t * (κ t).real {k} ∂μ

/-- A **level mechanism**: its signal set is `{1, …, K}`, and every signal `k` of positive probability
induces a posterior mean in `[b_k, b_{k-1})`. Candogan, SSRN 3346144 (preprint), §3, p.16.

**Formalization Note.** The signal space `{1, …, K}` is encoded as `ℕ`, with all mass on
`{1, …, K}`. -/
structure IsLevelMechanism (μ : Measure ℝ) [IsFiniteMeasure μ] (K : ℕ) (b : ℕ → EReal)
    (κ : Kernel ℝ ℕ) [IsFiniteKernel κ] : Prop where
  signal_mem : ∀ t, κ t {k | k ∉ Finset.Icc 1 K} = 0
  band : ∀ k ∈ Finset.Icc 1 K, 0 < signalProb μ κ k → InBand b k (posteriorMean μ κ k)

/-- A mechanism with integer signals is **consistent** with `(p_k, z_k)`: `P(S = k) = p_k`,
`E[T · 1{S = k}] = z_k`, and `E[T | S = k] = z_k / p_k` when `p_k > 0`. Candogan, SSRN 3346144
(preprint), §3.1, p.16.

**Formalization Note.** The page states the first and third clauses; the second is the definition
of `z_k` on the same page. It adds content only at `p_k = 0`, where it says `z_k = 0`. -/
def IsConsistent (μ : Measure ℝ) [IsFiniteMeasure μ] (K : ℕ) (p z : ℕ → ℝ)
    (κ : Kernel ℝ ℕ) [IsFiniteKernel κ] : Prop :=
  ∀ k ∈ Finset.Icc 1 K, signalProb μ κ k = p k ∧ signalMoment μ κ k = z k ∧
    (0 < p k → posteriorMean μ κ k = z k / p k)

end PersuasionNetworks


