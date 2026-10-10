-- Prove2me | Definitions.Def_RiskSensMFG_Nash_Model
-- name    : RiskSensMFG_Nash_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:42:44.965642+00:00
-- url     : https://prove2.me/theorems/2da18f22-b1ae-48b1-b93c-4b56128734f0
-- title:
--   §§2–3 and Assumption 1, pp. 4–10 — the risk-sensitive mean-field game model (X, A, p, c, µ0, β, λ), policies, the law P^π, J_µ and the flow Λ
-- statement:
--   This file fixes the model of a discrete-time **risk-sensitive mean-field game** and the single-agent objects built from it.
--
--   1. **Measures.** For a topological measurable space $E$, $\mathcal P(E)$ is the set of Borel probability measures on $E$ with the topology of weak convergence and its Borel $\sigma$-field.
--   2. **Model.** The data are a state space $\mathsf X$, an action space $\mathsf A$, a stochastic kernel $p(\cdot\mid x,a,\mu)$ on $\mathsf X$ given $\mathsf X\times\mathsf A\times\mathcal P(\mathsf X)$, a one-stage cost $c:\mathsf X\times\mathsf A\times\mathcal P(\mathsf X)\to\mathbb R$, an initial distribution $\mu_0\in\mathcal P(\mathsf X)$, a discount factor $\beta$, a risk factor $\lambda$ and a cost bound $K$. The **standing assumptions** are $\beta\in(0,1)$, $\lambda>0$, and $c$ measurable with values in $[0,\infty)$.
--   3. **Moment function.** $w:\mathsf X\to\mathbb R$ is a moment function if there are compact sets $K_1\subseteq K_2\subseteq\cdots$ with $\bigcup_n K_n=\mathsf X$ such that $\inf_{x\notin K_n}w(x)\to\infty$, i.e. for every $R$ there is $n$ with $w\ge R$ off $K_n$.
--   4. **Assumption 1.** (a) $c$ is continuous and $|c|\le K$; (b) $(x,a,\mu)\mapsto p(\cdot\mid x,a,\mu)$ is weakly continuous; (c) $\mathsf A$ is compact; (d) there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with
--   $$\sup_{(a,\mu)}\int_{\mathsf X}w(y)\,p(dy\mid x,a,\mu)\le\alpha\,w(x)\quad\text{for all }x;$$
--   (e) $\int w\,d\mu_0<\infty$.
--   5. **Policies.** A Markov policy is a sequence $\pi=\{\pi_t\}$ of stochastic kernels $\pi_t(da\mid x)$; a policy is a sequence of stochastic kernels $\pi_t(da\mid g(t))$ on $\mathsf A$ given the history $g(t)\in(\mathsf X\times\mathsf A)^t\times\mathsf X$. A Markov policy is **weakly continuous** if every $x\mapsto\pi_t(\cdot\mid x)\in\mathcal P(\mathsf A)$ is continuous.
--   6. **Law and cost.** Given a state-measure flow $\boldsymbol\mu=(\mu_t)_{t\ge0}$ and a policy $\pi$, $P^\pi$ is the law on $(\mathsf X\times\mathsf A)^{\infty}$ (Ionescu-Tulcea) of $x(0)\sim\mu_0$, $a(t)\sim\pi_t(\cdot\mid g(t))$, $x(t+1)\sim p(\cdot\mid x(t),a(t),\mu_t)$, and
--   $$J_{\boldsymbol\mu}(\pi)=E^{\pi}\Big[e^{\lambda\sum_{t=0}^{\infty}\beta^tc(x(t),a(t),\mu_t)}\Big].$$
--   7. **Flow.** For a Markov policy $\pi$, $\Lambda(\pi)=\boldsymbol\mu$ is defined by $\mu_0$ and $\mu_{t+1}(\cdot)=\int_{\mathsf X\times\mathsf A}p(\cdot\mid x,a,\mu_t)\,\pi_t(da\mid x)\,\mu_t(dx)$.
--
--   These are the objects in which the mean-field equilibrium and the $N$-agent game of the paper are stated.
--
--   **Formalization Note** $\mathcal P(E)$ is a type synonym of Mathlib's `ProbabilityMeasure E` that carries the Borel $\sigma$-field of the weak topology (Mathlib's default is the Giry $\sigma$-field). The kernel $p$ is a Mathlib `Kernel`, which asks for measurability into the Giry $\sigma$-field of `Measure X`; for Polish $\mathsf X$ this is the paper's measurability. Compactness of $\mathsf A$ is a typeclass binder of each theorem rather than a clause of `Assumption1`. The moment-function definition is recalled from Hernández-Lerma & Lasserre (1996, Definition E.7), cited by the paper, and stated without an infimum. Time is 0-based. A Markov policy is turned into a policy by ignoring the past.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, pp. 4–10, §2 (pp. 4–6), §3 (pp. 8–9), Assumption 1 (p. 10)

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model

open MeasureTheory ProbabilityTheory Finset

namespace RiskSensMFG.Nash

instance (E : Type*) [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E] : BorelSpace (RiskSensMFG.Existence.PM E) := ⟨rfl⟩

/-- The model data `(X, A, p, c, μ₀, β, λ)` together with the cost bound `K`. -/
structure Model (X A : Type*) [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [MeasurableSpace A] where
  /-- transition kernel `p(· | x, a, μ)` -/
  p : Kernel (X × A × RiskSensMFG.Existence.PM X) X
  [isMarkovKernel_p : IsMarkovKernel p]
  /-- one-stage cost `c(x, a, μ)` -/
  c : X × A × RiskSensMFG.Existence.PM X → ℝ
  /-- initial state distribution -/
  μ₀ : ProbabilityMeasure X
  /-- discount factor -/
  β : ℝ
  /-- risk factor `λ` -/
  lam : ℝ
  /-- the bound `‖c‖ ≤ K` of Assumption 1-(a) -/
  K : ℝ

attribute [instance] Model.isMarkovKernel_p

variable {X A : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace A]

/-- Standing assumptions: `β ∈ (0,1)`, `λ > 0`, `c` measurable with values in `[0, ∞)`. -/
def Model.Standing (M : Model X A) : Prop :=
  0 < M.β ∧ M.β < 1 ∧ 0 < M.lam ∧ Measurable M.c ∧ ∀ q, 0 ≤ M.c q

/-- Assumption 1 (a), (b), (d), (e); (c), the compactness of `A`, is a typeclass binder. -/
def Assumption1 [TopologicalSpace A] (M : Model X A) : Prop :=
  (Continuous M.c ∧ ∀ q, |M.c q| ≤ M.K) ∧
  @Continuous _ (ProbabilityMeasure X) _ _ (fun q => ⟨M.p q, inferInstance⟩) ∧
  ∃ (α : ℝ) (w : X → ℝ), 0 ≤ α ∧ Continuous w ∧ (∀ x, 1 ≤ w x) ∧ RiskSensMFG.Existence.IsMomentFunction w ∧
    (∀ x a μ, ∫⁻ y, ENNReal.ofReal (w y) ∂(M.p (x, a, μ)) ≤ ENNReal.ofReal (α * w x)) ∧
    ∫⁻ x, ENNReal.ofReal (w x) ∂(M.μ₀ : Measure X) < ⊤

/-- A Markov policy: a sequence of Markov kernels `π_t(da | x)`. -/
structure MarkovPolicy (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  π : ℕ → Kernel X A
  [isMarkovKernel : ∀ t, IsMarkovKernel (π t)]

attribute [instance] MarkovPolicy.isMarkovKernel

/-- A (history-dependent) policy: `π_t(da | g(t))` with `g(t) ∈ G_t = (X × A)^t × X`. -/
structure Policy (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  π : (t : ℕ) → Kernel ((Fin t → X × A) × X) A
  [isMarkovKernel : ∀ t, IsMarkovKernel (π t)]

attribute [instance] Policy.isMarkovKernel

/-- A Markov policy as a policy that ignores the past. -/
noncomputable def MarkovPolicy.toPolicy (σ : MarkovPolicy X A) : Policy X A where
  π t := (σ.π t).comap Prod.snd measurable_snd

/-- Weak continuity of a Markov policy: each `x ↦ π_t(· | x)` is continuous into `P(A)`. -/
def MarkovPolicy.WeaklyContinuous [TopologicalSpace A] [OpensMeasurableSpace A]
    (σ : MarkovPolicy X A) : Prop :=
  ∀ t, @Continuous _ (ProbabilityMeasure A) _ _ (fun x => ⟨σ.π t x, inferInstance⟩)

/-- The law `P^σ` on `(X × A)^ℕ` of the single agent facing the measure flow `μ`
(Ionescu-Tulcea): `x(0) ∼ μ₀`, `a(t) ∼ σ_t(· | g(t))`, `x(t+1) ∼ p(· | x(t), a(t), μ_t)`. -/
noncomputable def law (M : Model X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (σ : Policy X A) :
    Measure (ℕ → X × A) :=
  Kernel.trajMeasure (X := fun _ : ℕ => X × A)
    ((M.μ₀ : Measure X) ⊗ₘ ((σ.π 0).comap (fun x : X => ((Fin.elim0 : Fin 0 → X × A), x))
      (measurable_const.prodMk measurable_id)))
    (fun n =>
      (M.p.comap (fun h : (Π _ : Iic n, X × A) =>
          ((h ⟨n, Finset.mem_Iic.2 le_rfl⟩).1, (h ⟨n, Finset.mem_Iic.2 le_rfl⟩).2, μ n))
        (((measurable_pi_apply _).fst).prodMk (((measurable_pi_apply _).snd).prodMk
          measurable_const))) ⊗ₖ
      ((σ.π (n + 1)).comap
        (fun hx : (Π _ : Iic n, X × A) × X =>
          ((fun (j : Fin (n + 1)) => hx.1 ⟨j, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 j.2)⟩), hx.2))
        ((measurable_pi_lambda _ (fun _ => (measurable_pi_apply _).comp measurable_fst)).prodMk
          measurable_snd)))

/-- The infinite-horizon risk-sensitive cost `J_μ(σ) = E^σ[exp(λ ∑_t β^t c(x(t), a(t), μ_t))]`. -/
noncomputable def J (M : Model X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (σ : Policy X A) : ℝ :=
  ∫ ω, Real.exp (M.lam * ∑' t, M.β ^ t * M.c ((ω t).1, (ω t).2, μ t)) ∂(law M μ σ)

/-- The state-measure flow `Λ(σ)` of a Markov policy:
`μ_0 = μ₀`, `μ_{t+1}(·) = ∫ p(· | x, a, μ_t) σ_t(da | x) μ_t(dx)`. -/
noncomputable def flow (M : Model X A) (σ : MarkovPolicy X A) : ℕ → RiskSensMFG.Existence.PM X
  | 0 => M.μ₀
  | t + 1 =>
    (⟨(M.p.comap (fun xa : X × A => (xa.1, xa.2, flow M σ t))
        (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))) ∘ₘ
        (ProbabilityMeasure.toMeasure (flow M σ t) ⊗ₘ σ.π t), by
          have : IsProbabilityMeasure (ProbabilityMeasure.toMeasure (flow M σ t)) :=
            ProbabilityMeasure.instIsProbabilityMeasureToMeasure _
          infer_instance⟩ :
      ProbabilityMeasure X)

end RiskSensMFG.Nash


