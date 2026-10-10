-- Prove2me | Definitions.Def_RiskSensMFG_Nash_Augmented
-- name    : RiskSensMFG_Nash_Augmented
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:44:28.790985+00:00
-- url     : https://prove2.me/theorems/1a52634f-119e-45ee-96f9-d92985fdb5d6
-- title:
--   §5, pp. 24–28 — the augmented model (S, A, P_t, C_t, κ0), the flow ∆, the kernels P^π_t, the augmented N-agent game and the costs Ĵ
-- statement:
--   The augmented model adds the accumulated discounted cost to the state, so that the multiplicative risk-sensitive cost becomes a terminal cost.
--
--   1. **States.** $\mathsf S=\mathsf X\times\mathbb R$, $s=(x,c)$; for $\Delta\in\mathcal P(\mathsf S)$, $\Delta_1$ is its marginal on $\mathsf X$; $L=K/(1-\beta)$.
--   2. **Transition.** $P_t(B\times D\mid s,a,\Delta)=p(B\mid x,a,\Delta_1)\otimes\delta_{c+\beta^tc(x,a,\Delta_1)}(D)$.
--   3. **Terminal cost and initial law.** $C_{n+1}(x,c)=e^{\lambda c}$ for $c\in[0,L]$, and $\kappa_0=\mu_0\otimes\delta_0$.
--   4. **Mean-field flow.** For the equilibrium pair $(\pi,\boldsymbol\mu)$,
--   $$\Delta_t=\mathcal L\Big(x(t),\ \sum_{k=0}^{t-1}\beta^kc(x(k),a(k),\mu_k)\Big)\quad\text{under }P^\pi ,$$
--   and $P^\pi_t(\cdot\mid s,\Delta)=\int_{\mathsf A}P_t(\cdot\mid s,a,\Delta)\,\pi_t(da\mid x)$.
--   5. **Single-agent augmented model.** For a flow $\boldsymbol\Delta$ and a Markov policy $\sigma$: $s(0)\sim\kappa_0$, $a(t)\sim\sigma_t(\cdot\mid x(t))$, $s(t+1)\sim P_t(\cdot\mid s(t),a(t),\Delta_t)$, and $\hat J^n_{\boldsymbol\Delta}(\sigma)=E[C_{n+1}(s(n+1))]$.
--   6. **Augmented $N$-agent game.** $s^N_i(0)$ i.i.d. $\kappa_0$, $a^N_i(t)\sim\pi^i_t(\cdot\mid x^N_i(t))$, and $s^N_i(t+1)$ drawn independently from $P_t(\cdot\mid s^N_i(t),a^N_i(t),\Delta^{(N)}_t)$ with $\Delta^{(N)}_t=\frac1N\sum_i\delta_{s^N_i(t)}$; $\hat J^{(N),n}_i(\boldsymbol\pi^{(N)})=E[C_{n+1}(s^N_i(n+1))]$.
--
--   These objects carry the proof of the finite-horizon approximation (Theorem 4).
--
--   **Formalization Note** Two corrections of the printed text. (i) The paper writes the cost coordinate of $s(t)$ and of $\Delta_t$ as $\sum_{k=0}^{t-1}c(\cdot)$ without $\beta^k$, while $P_t$ adds $\beta^tc$ and p. 25 calls $c(t)$ the discounted total; the discounted sum is used, without which Lemma 5 fails. (ii) $\mathsf S=\mathsf X\times[0,L]$ is not invariant under $P_t$, so the cost coordinate is taken in $\mathbb R$, and the terminal cost is $e^{\lambda\max(0,\min(c,L))}$, which equals $e^{\lambda c}$ on every reachable state (where $0\le c\le L$) and is bounded and continuous on $\mathsf S$. The measurability of $c$ is an explicit argument of these constructions (it is part of the standing assumptions). Policies of the original game act on the augmented state through its $\mathsf X$-coordinate. For $N=0$ the empirical measure is $\kappa_0$.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, pp. 24–25 (augmented model, P_t, C_t, κ0), p. 26 (∆, P^π_t), p. 27 (∆^(N)_t), p. 28 (ŝ^N(t)), p. 29 (17)

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model
import Definitions.Def_RiskSensMFG_Nash_Game

open MeasureTheory ProbabilityTheory Finset

set_option linter.unusedSectionVars false

namespace RiskSensMFG.Nash

variable {X A : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MeasurableSpace A]

/-- The standing assumptions give the measurability of the cost `c`. -/
theorem Model.Standing.measurable_c {M : Model X A} (h : M.Standing) : Measurable M.c :=
  h.2.2.2.1

instance isProbabilityMeasure_law (M : Model X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (σ : Policy X A) :
    IsProbabilityMeasure (law M μ σ) := by
  unfold law; infer_instance

/-- The marginal `Δ_1` on `X` of a measure `Δ ∈ P(X × ℝ)`. -/
noncomputable def marg (Δ : RiskSensMFG.Existence.PM (X × ℝ)) : RiskSensMFG.Existence.PM X :=
  ProbabilityMeasure.map Δ continuous_fst.measurable.aemeasurable

lemma measurable_marg : Measurable (marg : RiskSensMFG.Existence.PM (X × ℝ) → RiskSensMFG.Existence.PM X) := by
  have h : Continuous (marg : RiskSensMFG.Existence.PM (X × ℝ) → RiskSensMFG.Existence.PM X) :=
    ProbabilityMeasure.continuous_map continuous_fst
  exact h.measurable

/-- The bound `L = K / (1 - β)` on the accumulated discounted cost. -/
noncomputable def augL (M : Model X A) : ℝ := M.K / (1 - M.β)

/-- The terminal cost `C_{n+1}(x, c) = e^{λ c}` of the augmented model, written with the cost
coordinate clamped to `[0, L]` (it agrees with `e^{λ c}` for `c ∈ [0, L]`). -/
noncomputable def Cterm (M : Model X A) (s : X × ℝ) : ℝ :=
  Real.exp (M.lam * max 0 (min s.2 (augL M)))

/-- The initial measure `κ₀ = μ₀ ⊗ δ_0` of the augmented model. -/
noncomputable def kappa0 (M : Model X A) : RiskSensMFG.Existence.PM (X × ℝ) :=
  ProbabilityMeasure.map M.μ₀ (measurable_id.prodMk measurable_const :
    Measurable fun x : X => (x, (0 : ℝ))).aemeasurable

/-- The augmented transition kernel
`P_t(B × D | (x, c), a, Δ) = p(B | x, a, Δ_1) ⊗ δ_{c + β^t c(x, a, Δ_1)}(D)`. -/
noncomputable def augStep (M : Model X A) (hc : Measurable M.c) (t : ℕ) :
    Kernel ((X × ℝ) × A × RiskSensMFG.Existence.PM (X × ℝ)) (X × ℝ) :=
  (M.p.comap (fun q : (X × ℝ) × A × RiskSensMFG.Existence.PM (X × ℝ) => (q.1.1, q.2.1, marg q.2.2))
      (measurable_fst.fst.prodMk (measurable_snd.fst.prodMk
        (measurable_marg.comp measurable_snd.snd)))) ×ₖ
    Kernel.deterministic
      (fun q : (X × ℝ) × A × RiskSensMFG.Existence.PM (X × ℝ) => q.1.2 + M.β ^ t * M.c (q.1.1, q.2.1, marg q.2.2))
      (measurable_fst.snd.add (measurable_const.mul (hc.comp (measurable_fst.fst.prodMk
        (measurable_snd.fst.prodMk (measurable_marg.comp measurable_snd.snd))))))

instance (M : Model X A) (hc : Measurable M.c) (t : ℕ) : IsMarkovKernel (augStep M hc t) := by
  unfold augStep; infer_instance

/-- The accumulated discounted cost `∑_{k<t} β^k c(x(k), a(k), μ_k)` along a trajectory. -/
noncomputable def accCost (M : Model X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (ω : ℕ → X × A) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range t, M.β ^ k * M.c ((ω k).1, (ω k).2, μ k)

lemma measurable_accCost (M : Model X A) (hc : Measurable M.c) (μ : ℕ → RiskSensMFG.Existence.PM X) (t : ℕ) :
    Measurable (fun ω : ℕ → X × A => accCost M μ ω t) :=
  Finset.measurable_sum _ fun k _ => measurable_const.mul (hc.comp
    (((measurable_pi_apply k).fst).prodMk (((measurable_pi_apply k).snd).prodMk
      measurable_const)))

/-- The augmented mean-field flow `Δ_t = L(x(t), ∑_{k<t} β^k c(x(k), a(k), μ_k))` under the law
`P^π` of the single agent using `π` against the flow `μ`. -/
noncomputable def augFlow (M : Model X A) (hc : Measurable M.c) (μ : ℕ → RiskSensMFG.Existence.PM X)
    (π : MarkovPolicy X A) (t : ℕ) : RiskSensMFG.Existence.PM (X × ℝ) :=
  ProbabilityMeasure.map (⟨law M μ π.toPolicy, inferInstance⟩ : ProbabilityMeasure _)
    ((((measurable_pi_apply t).fst).prodMk (measurable_accCost M hc μ t) :
      Measurable fun ω : ℕ → X × A => ((ω t).1, accCost M μ ω t)).aemeasurable)

/-- The augmented kernel under a Markov policy,
`P^π_t(· | s, Δ) = ∫_A P_t(· | s, a, Δ) π_t(da | x)` for `s = (x, c)`. -/
noncomputable def augPolicyKernel (M : Model X A) (hc : Measurable M.c) (π : MarkovPolicy X A)
    (t : ℕ) (Δ : RiskSensMFG.Existence.PM (X × ℝ)) : Kernel (X × ℝ) (X × ℝ) :=
  ((augStep M hc t).comap (fun sa : (X × ℝ) × A => (sa.1, sa.2, Δ))
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))) ∘ₖ
    (Kernel.id ×ₖ ((π.π t).comap Prod.fst measurable_fst))

/-- The law of the augmented single-agent state-action process facing the flow `Δ` under the
Markov policy `σ`: `s(0) ∼ κ₀`, `a(t) ∼ σ_t(· | x(t))`, `s(t+1) ∼ P_t(· | s(t), a(t), Δ_t)`. -/
noncomputable def augLaw (M : Model X A) (hc : Measurable M.c) (Δ : ℕ → RiskSensMFG.Existence.PM (X × ℝ))
    (σ : MarkovPolicy X A) : Measure (ℕ → (X × ℝ) × A) :=
  Kernel.trajMeasure (X := fun _ : ℕ => (X × ℝ) × A)
    (ProbabilityMeasure.toMeasure (kappa0 M) ⊗ₘ ((σ.π 0).comap Prod.fst measurable_fst))
    (fun n =>
      ((augStep M hc n).comap (fun h : (Π _ : Iic n, (X × ℝ) × A) =>
          ((h ⟨n, Finset.mem_Iic.2 le_rfl⟩).1, (h ⟨n, Finset.mem_Iic.2 le_rfl⟩).2, Δ n))
        (((measurable_pi_apply _).fst).prodMk (((measurable_pi_apply _).snd).prodMk
          measurable_const))) ⊗ₖ
      ((σ.π (n + 1)).comap (fun hs : (Π _ : Iic n, (X × ℝ) × A) × (X × ℝ) => hs.2.1)
        measurable_snd.fst))

/-- The finite-horizon cost of the augmented single-agent model, `Ĵ^n_Δ(σ) = E[C_{n+1}(s(n+1))]`. -/
noncomputable def Jhat (M : Model X A) (hc : Measurable M.c) (Δ : ℕ → RiskSensMFG.Existence.PM (X × ℝ))
    (σ : MarkovPolicy X A) (n : ℕ) : ℝ :=
  ∫ ω, Cterm M (ω (n + 1)).1 ∂(augLaw M hc Δ σ)

/-- One step of agent `i` in the augmented `N`-agent game at time `n`: given the configuration
`z = (s_j, a_j)_j`, draw `s' ∼ P_n(· | s_i, a_i, Δ^{(N)})` and then `a' ∼ σ_{n+1}(· | x')`. -/
noncomputable def augAgentStep (M : Model X A) (hc : Measurable M.c) {N : ℕ}
    (σ : MarkovPolicy X A) (n : ℕ) (i : Fin N) :
    Kernel (Fin N → (X × ℝ) × A) ((X × ℝ) × A) :=
  ((augStep M hc n).comap
      (fun z : Fin N → (X × ℝ) × A => ((z i).1, (z i).2, emp (kappa0 M) (fun j => (z j).1)))
      (((measurable_pi_apply i).fst).prodMk (((measurable_pi_apply i).snd).prodMk
        ((measurable_emp (kappa0 M) N).comp (measurable_pi_lambda _ fun j =>
          (measurable_pi_apply j).fst))))) ⊗ₖ
    ((σ.π (n + 1)).comap (fun zs : (Fin N → (X × ℝ) × A) × (X × ℝ) => zs.2.1)
      measurable_snd.fst)

instance (M : Model X A) (hc : Measurable M.c) {N : ℕ} (σ : MarkovPolicy X A) (n : ℕ)
    (i : Fin N) : IsMarkovKernel (augAgentStep M hc σ n i) := by
  unfold augAgentStep; infer_instance

/-- The law of the augmented `N`-agent game under the Markov profile `πs`: `s_i(0)` i.i.d. `κ₀`,
`a_i(t) ∼ π^i_t(· | x_i(t))`, `s_i(t+1) ∼ P_t(· | s_i(t), a_i(t), Δ^{(N)}_t)` independently
over `i`, with `Δ^{(N)}_t` the empirical measure of the augmented states. -/
noncomputable def augLawN (M : Model X A) (hc : Measurable M.c) (N : ℕ)
    (πs : Fin N → MarkovPolicy X A) : Measure (ℕ → (Fin N → (X × ℝ) × A)) :=
  Kernel.trajMeasure (X := fun _ : ℕ => Fin N → (X × ℝ) × A)
    (Measure.pi (fun i => ProbabilityMeasure.toMeasure (kappa0 M) ⊗ₘ
      (((πs i).π 0).comap Prod.fst measurable_fst)))
    (fun n => (kernelPi N (fun i => augAgentStep M hc (πs i) n i)).comap
      (fun h : (Π _ : Iic n, Fin N → (X × ℝ) × A) => h ⟨n, Finset.mem_Iic.2 le_rfl⟩)
      (measurable_pi_apply _))

/-- Agent `i`'s finite-horizon cost in the augmented `N`-agent game,
`Ĵ^{(N),n}_i(π^{(N)}) = E[C_{n+1}(s_i(n+1))]`. -/
noncomputable def JhatN (M : Model X A) (hc : Measurable M.c) (N : ℕ)
    (πs : Fin N → MarkovPolicy X A) (i : Fin N) (n : ℕ) : ℝ :=
  ∫ ω, Cterm M (ω (n + 1) i).1 ∂(augLawN M hc N πs)

end RiskSensMFG.Nash


