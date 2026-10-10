-- Prove2me | Definitions.Def_RiskSensMFG_Nash_Game
-- name    : RiskSensMFG_Nash_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:22.516338+00:00
-- url     : https://prove2.me/theorems/5c180b12-507c-4e26-ba1f-e5bdc12e4823
-- title:
--   §2 and Definition 2, pp. 4–7, 24 — the N-agent game: empirical measure, joint law, costs J^(N)_i and J^(N),n_i, ε-Markov-Nash equilibrium
-- statement:
--   This file defines the $N$-agent game of the paper for Markov policies.
--
--   1. **Empirical measure.** For states $x_1,\dots,x_N$, $e^{(N)}=\frac1N\sum_{i=1}^N\delta_{x_i}\in\mathcal P(\mathsf X)$; it is a continuous function of $(x_1,\dots,x_N)$.
--   2. **Joint law.** For a profile $\boldsymbol\pi^{(N)}=(\pi^1,\dots,\pi^N)$ of Markov policies, the states $x^N_i(0)$ are i.i.d. $\mu_0$; at each time $t$, the actions are drawn independently as $a^N_i(t)\sim\pi^i_t(\cdot\mid x^N_i(t))$, and the next states independently as
--   $$\prod_{i=1}^Np\big(dx^N_i(t+1)\mid x^N_i(t),a^N_i(t),e^{(N)}_t\big),\qquad e^{(N)}_t=\frac1N\sum_{i=1}^N\delta_{x^N_i(t)} .$$
--   3. **Costs.** Agent $i$'s infinite-horizon and finite-horizon risk-sensitive costs are
--   $$J^{(N)}_i(\boldsymbol\pi^{(N)})=E^{\boldsymbol\pi^{(N)}}\Big[e^{\lambda\sum_{t=0}^\infty\beta^tc(x^N_i(t),a^N_i(t),e^{(N)}_t)}\Big],\qquad J^{(N),n}_i(\boldsymbol\pi^{(N)})=E^{\boldsymbol\pi^{(N)}}\Big[e^{\lambda\sum_{t=0}^n\beta^tc(x^N_i(t),a^N_i(t),e^{(N)}_t)}\Big],$$
--   and the finite-horizon mean-field cost is $J^n_{\boldsymbol\mu}(\pi)=E^\pi\big[e^{\lambda\sum_{t=0}^n\beta^tc(x(t),a(t),\mu_t)}\big]$.
--   4. **ε-Markov-Nash equilibrium (Definition 2).** For $\varepsilon>0$, $\boldsymbol\pi^{(N)}$ is an $\varepsilon$-Markov-Nash equilibrium if for every agent $i$
--   $$J^{(N)}_i(\boldsymbol\pi^{(N)})\le\inf_{\pi^i\in\mathsf M_i}J^{(N)}_i(\boldsymbol\pi^{(N)}_{-i},\pi^i)+\varepsilon ,$$
--   where $\mathsf M_i$ is the set of Markov policies.
--
--   **Formalization Note** The joint law is built with Mathlib's Ionescu-Tulcea construction on $(\mathsf X\times\mathsf A)^N$, with a one-step kernel that is the product of the $N$ agents' kernels (defined here by recursion on $N$, since Mathlib has no product of kernels over a finite index). The definition of an $\varepsilon$-Markov-Nash equilibrium is written as "for every agent $i$ and every Markov policy $\sigma$, $J^{(N)}_i(\boldsymbol\pi^{(N)})\le J^{(N)}_i(\boldsymbol\pi^{(N)}_{-i},\sigma)+\varepsilon$", which is equivalent to the infimum form. For $N=0$ the empirical measure is set to $\mu_0$; no statement depends on that value. Agents are indexed by $\{0,\dots,N-1\}$, so the paper's Agent 1 is index $0$.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, pp. 4–6, §2, (1)–(2), J^(N)_i (p. 6); p. 7, Definition 2; p. 24, J^(N),n_1 and J^n_µ

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BoundedContinuousFunction

namespace RiskSensMFG.Nash

/-- The product `⊗_{i < n} κ_i` of finitely many kernels with a common source: given `a`, the
coordinates of the output are drawn independently, the `i`-th from `κ_i(a)`. -/
noncomputable def kernelPi {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    (n : ℕ) → (Fin n → Kernel α β) → Kernel α (Fin n → β)
  | 0, _ => Kernel.deterministic (fun _ => (Fin.elim0 : Fin 0 → β)) measurable_const
  | n + 1, κ => ((κ 0) ×ₖ kernelPi n (fun i => κ i.succ)).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => β) 0).symm

instance isMarkovKernel_kernelPi {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    ∀ (n : ℕ) (κ : Fin n → Kernel α β) [∀ i, IsMarkovKernel (κ i)],
      IsMarkovKernel (kernelPi n κ)
  | 0, _, _ => by unfold kernelPi; infer_instance
  | n + 1, κ, _ => by
    have := isMarkovKernel_kernelPi n (fun i => κ i.succ)
    unfold kernelPi
    exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)

/-- The empirical measure `(1/N) ∑_i δ_{x_i}` of a configuration `x : Fin N → E`. -/
noncomputable def empMeasure {E : Type*} [MeasurableSpace E] {N : ℕ} (x : Fin N → E) :
    Measure E :=
  (N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

lemma isProbabilityMeasure_empMeasure {E : Type*} [MeasurableSpace E] {N : ℕ} (hN : N ≠ 0)
    (x : Fin N → E) : IsProbabilityMeasure (empMeasure x) := by
  constructor
  simp [empMeasure]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN) (ENNReal.natCast_ne_top N)

/-- The empirical measure of a nonempty configuration, as an element of `P(E)`. -/
noncomputable def empPM {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] {N : ℕ} (hN : N ≠ 0) (x : Fin N → E) : RiskSensMFG.Existence.PM E :=
  (⟨empMeasure x, isProbabilityMeasure_empMeasure hN x⟩ : ProbabilityMeasure E)

/-- The empirical distribution `e^{(N)} = (1/N) ∑_i δ_{x_i} ∈ P(E)`; for `N = 0` (no agents)
it is the fixed default `d`. -/
noncomputable def emp {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] (d : RiskSensMFG.Existence.PM E) {N : ℕ} (x : Fin N → E) : RiskSensMFG.Existence.PM E :=
  if hN : N = 0 then d else empPM hN x

lemma continuous_emp {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] (d : RiskSensMFG.Existence.PM E) (N : ℕ) :
    Continuous (fun x : Fin N → E => emp d x) := by
  by_cases hN : N = 0
  · subst hN
    exact continuous_const.congr (fun x => by unfold emp; rw [dif_pos rfl])
  · have h : ∀ (f : E →ᵇ ℝ) (x : Fin N → E),
        ∫ ω, f ω ∂(empMeasure x) = (N : ℝ)⁻¹ * ∑ i, f (x i) := by
      intro f x
      rw [empMeasure, integral_smul_measure, integral_finsetSum_measure
        (fun i _ => f.integrable _)]
      simp [integral_dirac' _ _ f.continuous.stronglyMeasurable, ENNReal.toReal_inv]
    have hc : @Continuous (Fin N → E) (ProbabilityMeasure E) _ _ (fun x =>
        ⟨empMeasure x, isProbabilityMeasure_empMeasure hN x⟩) := by
      refine ProbabilityMeasure.continuous_iff_forall_continuous_integral.2 fun f => ?_
      simp only [ProbabilityMeasure.coe_mk, h]
      fun_prop
    exact hc.congr (fun x => by unfold emp; rw [dif_neg hN]; rfl)

lemma measurable_emp {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [SecondCountableTopology E] [OpensMeasurableSpace E] (d : RiskSensMFG.Existence.PM E) (N : ℕ) :
    Measurable (fun x : Fin N → E => emp d x) :=
  (continuous_emp d N).measurable

variable {X A : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] [MeasurableSpace A]

/-- One step of agent `i` in the `N`-agent game at time `n`: given the configuration
`z = (x_j, a_j)_j`, draw `x' ∼ p(· | x_i, a_i, e^{(N)})` and then `a' ∼ σ_{n+1}(· | x')`. -/
noncomputable def agentStep (M : Model X A) {N : ℕ} (σ : MarkovPolicy X A) (n : ℕ)
    (i : Fin N) : Kernel (Fin N → X × A) (X × A) :=
  (M.p.comap (fun z : Fin N → X × A => ((z i).1, (z i).2, emp M.μ₀ (fun j => (z j).1)))
      (((measurable_pi_apply i).fst).prodMk (((measurable_pi_apply i).snd).prodMk
        ((measurable_emp M.μ₀ N).comp (measurable_pi_lambda _ fun j =>
          (measurable_pi_apply j).fst))))) ⊗ₖ
    ((σ.π (n + 1)).comap Prod.snd measurable_snd)

instance (M : Model X A) {N : ℕ} (σ : MarkovPolicy X A) (n : ℕ) (i : Fin N) :
    IsMarkovKernel (agentStep M σ n i) := by
  unfold agentStep; infer_instance

/-- The law of all states and actions of the `N`-agent game under the Markov profile `πs`:
`x_i(0)` i.i.d. `μ₀`, `a_i(t) ∼ π^i_t(· | x_i(t))` and
`x_i(t+1) ∼ p(· | x_i(t), a_i(t), e^{(N)}_t)`, independently over `i` given the past. -/
noncomputable def lawN (M : Model X A) (N : ℕ) (πs : Fin N → MarkovPolicy X A) :
    Measure (ℕ → (Fin N → X × A)) :=
  Kernel.trajMeasure (X := fun _ : ℕ => Fin N → X × A)
    (Measure.pi (fun i => (M.μ₀ : Measure X) ⊗ₘ (πs i).π 0))
    (fun n => (kernelPi N (fun i => agentStep M (πs i) n i)).comap
      (fun h : (Π _ : Iic n, Fin N → X × A) => h ⟨n, Finset.mem_Iic.2 le_rfl⟩)
      (measurable_pi_apply _))

/-- Agent `i`'s infinite-horizon risk-sensitive cost in the `N`-agent game,
`J^{(N)}_i(π^{(N)}) = E[exp(λ ∑_t β^t c(x_i(t), a_i(t), e^{(N)}_t))]`. -/
noncomputable def JN (M : Model X A) (N : ℕ) (πs : Fin N → MarkovPolicy X A) (i : Fin N) : ℝ :=
  ∫ ω, Real.exp (M.lam * ∑' t, M.β ^ t *
      M.c ((ω t i).1, (ω t i).2, emp M.μ₀ (fun j => (ω t j).1))) ∂(lawN M N πs)

/-- The finite-horizon cost `J^{(N),n}_i(π^{(N)}) = E[exp(λ ∑_{t=0}^n β^t c(…))]`. -/
noncomputable def JNfin (M : Model X A) (N : ℕ) (πs : Fin N → MarkovPolicy X A) (i : Fin N)
    (n : ℕ) : ℝ :=
  ∫ ω, Real.exp (M.lam * ∑ t ∈ Finset.range (n + 1), M.β ^ t *
      M.c ((ω t i).1, (ω t i).2, emp M.μ₀ (fun j => (ω t j).1))) ∂(lawN M N πs)

/-- The finite-horizon mean-field cost `J^n_μ(σ) = E^σ[exp(λ ∑_{t=0}^n β^t c(x(t), a(t), μ_t))]`. -/
noncomputable def Jfin (M : Model X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (σ : Policy X A) (n : ℕ) : ℝ :=
  ∫ ω, Real.exp (M.lam * ∑ t ∈ Finset.range (n + 1), M.β ^ t * M.c ((ω t).1, (ω t).2, μ t))
    ∂(law M μ σ)

/-- Definition 2: `πs` is an `ε`-Markov-Nash equilibrium of the `N`-agent game when no agent can
lower its cost by more than `ε` by switching to any Markov policy. -/
def IsEpsMarkovNash (M : Model X A) (N : ℕ) (πs : Fin N → MarkovPolicy X A) (ε : ℝ) : Prop :=
  ∀ i : Fin N, ∀ σ : MarkovPolicy X A, JN M N πs i ≤ JN M N (Function.update πs i σ) i + ε

end RiskSensMFG.Nash


