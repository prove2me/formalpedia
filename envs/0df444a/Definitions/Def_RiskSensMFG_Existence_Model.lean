-- Prove2me | Definitions.Def_RiskSensMFG_Existence_Model
-- name    : RiskSensMFG_Existence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:45:51.650688+00:00
-- url     : https://prove2.me/theorems/0a5eef77-d62c-4686-8751-ff8dd6b486c1
-- title:
--   §§2–3 and Assumption 1, pp. 4–10 — the risk-sensitive mean-field game model, policies, the law $P^\pi$, the cost $J_\mu$ and the flow $\Lambda$
-- statement:
--   This module sets up the discrete-time risk-sensitive mean-field game of Saldi, Başar and Raginsky.
--
--   **Spaces.** $\mathsf X$ (states) and $\mathsf A$ (actions) are topological spaces with σ-fields. For a space $E$, $\mathcal P(E)$ denotes the probability measures on $E$ with the topology of weak convergence and the **Borel σ-field of that topology**.
--
--   **Model.** A model consists of
--   1. a stochastic kernel $p(\cdot\,|\,x,a,\mu)$ on $\mathsf X$ given $\mathsf X\times\mathsf A\times\mathcal P(\mathsf X)$ (the transition probability);
--   2. a one-stage cost $c:\mathsf X\times\mathsf A\times\mathcal P(\mathsf X)\to\mathbb R$;
--   3. an initial distribution $\mu_0\in\mathcal P(\mathsf X)$;
--   4. a discount factor $\beta$, a risk factor $\lambda$ and a constant $K$.
--
--   The **standing assumptions** are $0<\beta<1$, $\lambda>0$, and $c$ measurable with values in $[0,\infty)$.
--
--   **Moment functions.** $w:\mathsf X\to\mathbb R$ is a moment function if there are compact sets $K_0\subseteq K_1\subseteq\cdots$ with $\bigcup_n K_n=\mathsf X$ such that for every $R$ there is $n$ with $w(x)\ge R$ for all $x\notin K_n$ (that is, $\inf_{x\notin K_n}w(x)\to\infty$).
--
--   **Assumption 1.** (a) $c$ is continuous and $|c|\le K$; (b) $(x,a,\mu)\mapsto p(\cdot|x,a,\mu)$ is continuous into $\mathcal P(\mathsf X)$; (c) $\mathsf A$ is compact (a separate hypothesis wherever used); (d) there are $\alpha\ge0$ and a continuous moment function $w\ge1$ with
--   $$\int_{\mathsf X} w(y)\,p(dy\,|\,x,a,\mu)\le\alpha\,w(x)\quad\text{for all }(x,a,\mu);$$
--   (e) $\int_{\mathsf X}w\,d\mu_0<\infty$.
--
--   **Policies.** A Markov policy is a sequence $\pi=(\pi_t)_{t\ge0}$ of stochastic kernels $\pi_t(da\,|\,x)$ on $\mathsf A$ given $\mathsf X$. A (history-dependent) policy is a sequence of stochastic kernels $\sigma_t(da\,|\,g)$ on $\mathsf A$ given the history space $G_t=(\mathsf X\times\mathsf A)^t\times\mathsf X$; a Markov policy is a policy that ignores the past. A Markov policy is weakly continuous if each $x\mapsto\pi_t(\cdot|x)$ is continuous into $\mathcal P(\mathsf A)$.
--
--   **Law and cost.** Given a measure flow $\mu=(\mu_t)_{t\ge0}\subset\mathcal P(\mathsf X)$ and a policy $\sigma$, $P^\sigma$ is the probability measure on $(\mathsf X\times\mathsf A)^\infty$ under which
--   $$x(0)\sim\mu_0,\qquad a(t)\sim\sigma_t(\cdot\,|\,g(t)),\qquad x(t+1)\sim p(\cdot\,|\,x(t),a(t),\mu_t),$$
--   with $g(t)$ the state–action history up to time $t$. The infinite-horizon risk-sensitive cost is
--   $$J_\mu(\sigma)=E^{\sigma}\Big[\exp\Big(\lambda\sum_{t=0}^{\infty}\beta^t c(x(t),a(t),\mu_t)\Big)\Big].$$
--
--   **The flow of a Markov policy.** $\Lambda(\pi)=(\mu_t)_{t\ge0}$ is defined recursively by $\mu_0$ (the model's initial law) and
--   $$\mu_{t+1}(\cdot)=\int_{\mathsf X\times\mathsf A}p(\cdot\,|\,x,a,\mu_t)\,\pi_t(da\,|\,x)\,\mu_t(dx).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathcal P(E)$ is a type synonym `PM E` of `ProbabilityMeasure E` carrying the Borel σ-field of the weak topology (Mathlib's own σ-field on `ProbabilityMeasure` is the Giry σ-field). The kernel $p$ is a Mathlib `Kernel`, which asks for measurability into the Giry σ-field of measures; for Polish $\mathsf X$ this is the paper's Borel measurability. The definition of a moment function is recalled from Hernández-Lerma–Lasserre, *Discrete-Time Markov Control Processes* (1996), Definition E.7, cited by the paper as [21], not from the paper itself; it is written without an infimum so that compact $\mathsf X$ is not excluded. Time is $0$-based. The law $P^\sigma$ is built with Mathlib's Ionescu–Tulcea construction `Kernel.trajMeasure`, one coordinate $(x(t),a(t))$ per time step. The history spaces carry the product σ-fields. The paper's standing hypothesis that $\mathsf X$ and $\mathsf A$ are Polish is not part of these definitions; every statement using them carries it as typeclass hypotheses, together with the standing assumptions and Assumption 1. The law and the cost accept any sequence $(\mu_t)_{t\ge0}$ as the flow argument; the paper's flows have $\mu_0$ equal to the initial law, and $x(0)\sim\mu_0$ is always the model's initial law here, the flow's time-$0$ entry entering only the first transition. $\Lambda$ is defined for Markov policies only; by Proposition 1 of the paper, $\Lambda(\Pi)=\Lambda(\mathsf M)$. $J_\mu$ is a Bochner integral and an infinite sum that default to $0$ when non-integrable or non-summable; under the standing assumptions and Assumption 1-(a) the integrand lies in $[1,e^{\lambda K/(1-\beta)}]$, so $J_\mu$ is the genuine expectation, and every statement using $J_\mu$ assumes both.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, pp. 4–10, §2 (p. 6), §3 (pp. 8–9), Assumption 1 (p. 10)

import Mathlib

open MeasureTheory ProbabilityTheory Finset

namespace RiskSensMFG.Existence

/-- `P(E)`: the probability measures on `E`, with the topology of weak convergence and the Borel
σ-field of that topology (a type synonym of `ProbabilityMeasure E`, whose own `MeasurableSpace`
instance is the Giry σ-field). -/
def PM (E : Type*) [MeasurableSpace E] [TopologicalSpace E] : Type _ := ProbabilityMeasure E

instance {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E] :
    TopologicalSpace (PM E) :=
  inferInstanceAs (TopologicalSpace (ProbabilityMeasure E))

instance {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E] :
    MeasurableSpace (PM E) :=
  borel (PM E)

instance {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E] :
    BorelSpace (PM E) := ⟨rfl⟩

/-- The mean-field game model `(X, A, p, c, μ₀)` together with the discount factor `β`, the risk
factor `λ` (`lam`) and the cost bound `K` of Assumption 1-(a) (§§2–3, pp. 4–9). -/
structure Model (X A : Type*) [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [MeasurableSpace A] where
  /-- the transition kernel `p(· | x, a, μ)` -/
  p : Kernel (X × A × PM X) X
  hp : IsMarkovKernel p
  /-- the one-stage cost `c(x, a, μ)` -/
  c : X × A × PM X → ℝ
  /-- the initial state distribution `μ₀` -/
  μ₀ : ProbabilityMeasure X
  /-- the discount factor `β` -/
  β : ℝ
  /-- the risk factor `λ` -/
  lam : ℝ
  /-- the cost bound `K` of Assumption 1-(a) -/
  K : ℝ

attribute [instance] Model.hp

variable {X A : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace A]

/-- The standing assumptions of §§2–3: `β ∈ (0, 1)`, `λ > 0`, and `c` is a measurable function
into `[0, ∞)`. -/
def Model.Standing (M : Model X A) : Prop :=
  0 < M.β ∧ M.β < 1 ∧ 0 < M.lam ∧ Measurable M.c ∧ ∀ q, 0 ≤ M.c q

/-- A moment function ([21, Definition E.7]): there are compact sets `K₀ ⊆ K₁ ⊆ ⋯` exhausting
`X` such that `w` tends to `+∞` off them, i.e. `inf_{x ∉ Kₙ} w x → ∞` (written without an
infimum, so an empty complement imposes nothing). -/
def IsMomentFunction (w : X → ℝ) : Prop :=
  ∃ Kn : ℕ → Set X, (∀ n, IsCompact (Kn n)) ∧ Monotone Kn ∧ (⋃ n, Kn n) = Set.univ ∧
    ∀ R : ℝ, ∃ n, ∀ x ∉ Kn n, R ≤ w x

/-- Assumption 1 (p. 10), parts (a), (b), (d), (e). Part (c), compactness of `A`, is the
typeclass `CompactSpace A`. -/
def Assumption1 [TopologicalSpace A] (M : Model X A) : Prop :=
  (Continuous M.c ∧ ∀ q, |M.c q| ≤ M.K) ∧
  Continuous (X := X × A × PM X) (Y := ProbabilityMeasure X) (fun q => ⟨M.p q, inferInstance⟩) ∧
  ∃ (α : ℝ) (w : X → ℝ), 0 ≤ α ∧ Continuous w ∧ (∀ x, 1 ≤ w x) ∧ IsMomentFunction w ∧
    (∀ x a μ, ∫⁻ y, ENNReal.ofReal (w y) ∂(M.p (x, a, μ)) ≤ ENNReal.ofReal (α * w x)) ∧
    ∫⁻ x, ENNReal.ofReal (w x) ∂(M.μ₀ : Measure X) < ⊤

/-- A Markov policy: a sequence of stochastic kernels `πₜ(da | x)` on `A` given `X`. -/
structure MarkovPolicy (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  π : ℕ → Kernel X A
  hπ : ∀ t, IsMarkovKernel (π t)

attribute [instance] MarkovPolicy.hπ

/-- A (history-dependent) policy: a sequence of stochastic kernels `πₜ(da | g(t))` on `A` given
the history space `Gₜ = (X × A)ᵗ × X`. -/
structure Policy (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  π : (t : ℕ) → Kernel ((Fin t → X × A) × X) A
  hπ : ∀ t, IsMarkovKernel (π t)

attribute [instance] Policy.hπ

/-- A Markov policy seen as a policy that ignores the past history. -/
noncomputable def MarkovPolicy.toPolicy (π : MarkovPolicy X A) : Policy X A where
  π t := (π.π t).comap Prod.snd measurable_snd
  hπ t := by infer_instance

/-- A Markov policy is weakly continuous if every `x ↦ πₜ(· | x)` is continuous into `P(A)`. -/
def MarkovPolicy.WeaklyContinuous [TopologicalSpace A] [OpensMeasurableSpace A]
    (π : MarkovPolicy X A) : Prop :=
  ∀ t, Continuous (X := X) (Y := ProbabilityMeasure A) (fun x => ⟨π.π t x, inferInstance⟩)

/-- The law `P^σ` on `(X × A)^∞` (coordinate `t` is `(x(t), a(t))`) of the state–action process of
a generic agent under the measure flow `μ` and the policy `σ` (Ionescu–Tulcea, p. 9):
`x(0) ∼ μ₀`, `a(t) ∼ σₜ(· | g(t))`, `x(t+1) ∼ p(· | x(t), a(t), μₜ)`. -/
noncomputable def law (M : Model X A) (μ : ℕ → PM X) (σ : Policy X A) :
    Measure (ℕ → X × A) :=
  @Kernel.trajMeasure (fun _ : ℕ => X × A) (fun _ => inferInstance)
    ((M.μ₀ : Measure X) ⊗ₘ
      (σ.π 0).comap (fun x => ((Fin.elim0 : Fin 0 → X × A), x)) (by fun_prop))
    (fun n =>
      (M.p.comap (fun h : (Π _ : Iic n, X × A) =>
          ((h ⟨n, mem_Iic.2 le_rfl⟩).1, (h ⟨n, mem_Iic.2 le_rfl⟩).2, μ n)) (by fun_prop)) ⊗ₖ
        (σ.π (n + 1)).comap
          (fun hx : (Π _ : Iic n, X × A) × X =>
            ((fun i : Fin (n + 1) => hx.1 ⟨i.val, mem_Iic.2 (Nat.lt_succ_iff.1 i.isLt)⟩), hx.2))
          (by fun_prop))
    (fun _ => by infer_instance)

/-- The infinite-horizon risk-sensitive cost `J_μ(σ) = E^σ[exp(λ ∑ₜ βᵗ c(x(t), a(t), μₜ))]`
(p. 9). -/
noncomputable def J (M : Model X A) (μ : ℕ → PM X) (σ : Policy X A) : ℝ :=
  ∫ ω, Real.exp (M.lam * ∑' t, M.β ^ t * M.c ((ω t).1, (ω t).2, μ t)) ∂(law M μ σ)

/-- The flow `Λ(π)` of a Markov policy (p. 9): `μ₀` at time `0` and
`μₜ₊₁(·) = ∫ p(· | x, a, μₜ) πₜ(da | x) μₜ(dx)`. -/
noncomputable def flow (M : Model X A) (π : MarkovPolicy X A) : ℕ → PM X
  | 0 => M.μ₀
  | t + 1 =>
    (⟨(M.p.comap (fun xa : X × A => (xa.1, xa.2, flow M π t)) (by fun_prop)) ∘ₘ
        (ProbabilityMeasure.toMeasure (flow M π t) ⊗ₘ π.π t), by
      have : IsProbabilityMeasure (ProbabilityMeasure.toMeasure (flow M π t)) :=
        (show ProbabilityMeasure X from flow M π t).prop
      infer_instance⟩ :
      ProbabilityMeasure X)

end RiskSensMFG.Existence


