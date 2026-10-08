-- Prove2me | Definitions.Def_BertsekasShreve_BorelInfinite_Policy
-- name    : BertsekasShreve_BorelInfinite_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:11.675929+00:00
-- url     : https://prove2.me/theorems/9a0b3a73-bd4f-461d-b779-7dee0c867f22
-- title:
--   Universally measurable policies, the cost J_π, the optimal cost J*, T_μ and the DP algorithm (Defs 8.2, 8.4, 9.2, 9.3, 9.10)
-- statement:
--   Fix a model (SM) $(S, C, U, W, p, f, \alpha, g)$.
--
--   1. **Universally measurable stochastic kernel.** A family $q(dy \mid x)$ of probability measures on $Y$, indexed by $x \in X$, such that $x \mapsto q(B \mid x)$ is universally measurable for every Borel set $B \subseteq Y$.
--   2. **Policy** (Definition 9.2). A sequence $\pi = (\mu_0, \mu_1, \dots)$ where each $\mu_k(du_k \mid x_0, u_0, \dots, u_{k-1}, x_k)$ is a universally measurable stochastic kernel on $C$ given $SC \cdots CS$ with
--   $$\mu_k(U(x_k) \mid x_0, u_0, \dots, u_{k-1}, x_k) = 1$$
--   for every history. $\Pi'$ is the set of all policies. $\pi$ is **Markov** if each $\mu_k$ depends only on $x_k$; a Markov policy $\pi = (\mu, \mu, \dots)$ is **stationary**; $\pi$ is **nonrandomized** if every $\mu_k(\cdot \mid h)$ is a point mass. $U(C \mid S)$ is the set of universally measurable stochastic kernels $\mu$ on $C$ given $S$ with $\mu(U(x) \mid x) = 1$ for all $x$.
--   3. **State–control laws.** For an initial distribution $p$ of $x_0$, draw $u_k \sim \mu_k(\cdot \mid h_k)$ and $x_{k+1} \sim t(\cdot \mid x_k, u_k)$. This defines the law of $(x_0, u_0, \dots, x_k, u_k)$, the marginal of $r(\pi, p)$ of Proposition 7.45, and its marginal $q_k(\pi, p)$ on $S_kC_k$.
--   4. **Cost** (Definition 9.3, Eq. (5) of Chapter 9). With $p_x$ the point mass at $x$,
--   $$J_\pi(x) = \sum_{k=0}^\infty \alpha^k \int_{S_kC_k} g\, dq_k(\pi, p_x).$$
--   For a stationary $\pi = (\mu, \mu, \dots)$ one writes $J_\mu$.
--   5. **Optimal cost** (Eq. (2) of Chapter 9).
--   $$J^*(x) = \inf_{\pi \in \Pi'} J_\pi(x).$$
--   A policy $\pi$ is **optimal** if $J_\pi(x) = J^*(x)$ for every $x \in S$.
--   6. **The operator $T_\mu$** (Definition 8.4). For $\mu \in U(C \mid S)$ and $J : S \to R^*$,
--   $$T_\mu(J)(x) = \int_C \Big[ g(x, u) + \alpha \int_S J(x')\, t(dx' \mid x, u) \Big] \mu(du \mid x).$$
--   7. **Dynamic programming algorithm** (Definition 9.10). $J_0(x) = 0$ and $J_{k+1}(x) = T(J_k)(x)$, i.e. $J_k = T^k(J_0)$.
--
--   These are the objects in which the optimality equation and the convergence results of Chapter 9 are stated.
--
--   **Formalization Note** A history $(x_0, u_0, \dots, x_{k-1}, u_{k-1}, x_k)$ is the pair of a tuple $(x_i, u_i)_{i<k}$ and $x_k$. The laws of the histories are built recursively by integrating the kernels against the previous law. The cost is computed as $\sum_k \alpha^k \int g^+ dq_k - \sum_k \alpha^k \int g^- dq_k$ with $\infty - \infty = \infty$. Under each of (P), (N), (D) this equals both expressions of Eq. (1) of Chapter 9: under (P) the second series vanishes, under (N) the first does, and under (D) both are finite. $J^*$ is an infimum over all policies (history-dependent and randomized), and it is neither defined as a fixed point of $T$ nor as a limit of $T^k(0)$. The measure of $U(x)$ is the outer measure, which equals the completion measure because $U(x)$ is a section of the analytic set $\Gamma$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 134, Definition 7.12; pp. 190–192, Definition 8.2 and Eqs. (4), (7) of Chapter 8; p. 194, Definition 8.4; pp. 214–216, Definitions 9.2, 9.3 and Eqs. (1), (2), (5) of Chapter 9; p. 229, Definition 9.10

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_BertsekasShreve_BorelInfinite_Model

namespace BertsekasShreve.BorelInfinite

open MeasureTheory ProbabilityTheory

/-- **Definition 7.12** (p. 134), universally measurable version: a *universally measurable
stochastic kernel* `q(dy | x)` on `Y` given `X` assigns to each `x` a probability measure `q(· | x)`
on the Borel sets of `Y` such that `x ↦ q(B | x)` is universally measurable for every Borel set
`B ⊆ Y` (equivalently, `x ↦ q(dy | x)` is universally measurable from `X` to `P(Y)`). -/
structure UKernel (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  /-- the measure `q(· | x)` -/
  toFun : X → Measure Y
  isProbability : ∀ x, IsProbabilityMeasure (toFun x)
  univMeasurable : ∀ B : Set Y, MeasurableSet B →
    IsUniversallyMeasurableFun (fun x => toFun x B)

/-- The history space `S₀C₀ ⋯ S_{k−1}C_{k−1}S_k` of the first `k` stages: a history
`h = (x₀, u₀, …, x_{k−1}, u_{k−1}, x_k)` is stored as the pair of the past state–control pairs
`(i ↦ (x_i, u_i))_{i < k}` and the current state `x_k`. -/
abbrev Hist (S C : Type*) (k : ℕ) := (Fin k → S × C) × S

namespace Model

variable {S C W : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W]

/-- **Definition 9.2** (p. 214). A *policy* for (SM) is a sequence `π = (μ₀, μ₁, …)` such that
for each `k`, `μ_k(du_k | x₀, u₀, …, u_{k−1}, x_k)` is a universally measurable stochastic kernel
on `C` given `SC ⋯ CS` satisfying `μ_k(U(x_k) | x₀, u₀, …, u_{k−1}, x_k) = 1` for every history.
(`U(x_k)` is a section of the analytic set `Γ`, hence universally measurable; the measure of it is
the completion measure, which Mathlib's outer-measure evaluation `μ (U x)` computes.) The set of
all policies is `Π'`. -/
structure Policy (M : Model S C W) where
  /-- the kernel `μ_k` used at stage `k` -/
  μ : (k : ℕ) → UKernel (Hist S C k) C
  admissible : ∀ k (h : Hist S C k), (μ k).toFun h (M.U h.2) = 1

/-- `U(C|S)` (p. 194): the universally measurable stochastic kernels `μ` on `C` given `S` with
`μ(U(x) | x) = 1` for every `x ∈ S`. -/
structure UCS (M : Model S C W) where
  /-- the kernel `μ(du | x)` -/
  κ : UKernel S C
  admissible : ∀ x, κ.toFun x (M.U x) = 1

namespace Policy

variable {M : Model S C W}

/-- **Definition 8.2 / 9.2**: `π` is a *Markov* policy if each `μ_k` is parameterized only by
the current state `x_k`, i.e. `μ_k(· | x₀, …, x_k) = ν_k(· | x_k)` for some universally measurable
stochastic kernels `ν_k` on `C` given `S`. The set of Markov policies is `Π`. -/
def IsMarkov (π : M.Policy) : Prop :=
  ∃ ν : ℕ → UKernel S C, ∀ k (h : Hist S C k), (π.μ k).toFun h = (ν k).toFun h.2

/-- **Definition 9.2**: a Markov policy of the form `π = (μ, μ, …)` is *stationary*. -/
def IsStationary (π : M.Policy) : Prop :=
  ∃ ν : UKernel S C, ∀ k (h : Hist S C k), (π.μ k).toFun h = ν.toFun h.2

/-- **Definition 8.2 / 9.2**: `π` is *nonrandomized* if every `μ_k(· | h)` assigns mass one to
some point of `C`. -/
def IsNonrandomized (π : M.Policy) : Prop :=
  ∀ k (h : Hist S C k), ∃ u : C, (π.μ k).toFun h = Measure.dirac u

/-- The joint law of the history `h_k` and the control `u_k`, i.e. the marginal of `r(π, p)` on
`S₀C₀ ⋯ S_kC_k` (Proposition 7.45), defined by the recursion of Eq. (4) of Chapter 8: start from
the initial distribution `p` of `x₀`, draw `u_k` from `μ_k(· | h_k)`, then `x_{k+1}` from
`t(· | x_k, u_k)`. -/
noncomputable def jointLaw (π : M.Policy) (p : Measure S) : (k : ℕ) → Measure (Hist S C k × C)
  | 0 =>
      (p.map (fun x : S => ((fun i : Fin 0 => i.elim0), x))).bind
        (fun h => ((π.μ 0).toFun h).map (fun u => (h, u)))
  | k + 1 =>
      ((jointLaw π p k).bind (fun hu =>
          (M.t (hu.1.2, hu.2)).map
            (fun x' => ((Fin.snoc (α := fun _ => S × C) hu.1.1 (hu.1.2, hu.2)), x')))).bind
        (fun h => ((π.μ (k + 1)).toFun h).map (fun u => (h, u)))

/-- `q_k(π, p)` (p. 192 and p. 216): the marginal of `r(π, p)` on `S_kC_k`, the joint law of the
state–control pair `(x_k, u_k)`. -/
noncomputable def q (π : M.Policy) (p : Measure S) (k : ℕ) : Measure (S × C) :=
  (π.jointLaw p k).map (fun hu => (hu.1.2, hu.2))

/-- **Definition 9.3** (p. 214), in the form of Eq. (1)/(5) of Chapter 9: the infinite-horizon
cost of `π` at `x ∈ S`,
`J_π(x) = Σ_{k=0}^∞ α^k ∫_{S_kC_k} g dq_k(π, p_x)`,
where `p_x` is the point mass at `x`. It is computed as
`Σ_k α^k ∫ g⁺ dq_k − Σ_k α^k ∫ g⁻ dq_k` with `∞ − ∞ = ∞`; under each of (P), (N) and (D) at most
one of the two series is nonzero or both are finite, and the expression equals both sides of
Eq. (1) of Chapter 9 (the interchange of sum and integral is justified there by monotone resp.
bounded convergence). -/
noncomputable def cost (π : M.Policy) (x : S) : EReal :=
  bsub (∑' k : ℕ, ENNReal.ofReal (M.α ^ k) *
          ∫⁻ z, (M.g z.1 z.2).toENNReal ∂(π.q (Measure.dirac x) k))
       (∑' k : ℕ, ENNReal.ofReal (M.α ^ k) *
          ∫⁻ z, (-(M.g z.1 z.2)).toENNReal ∂(π.q (Measure.dirac x) k))

end Policy

/-- The stationary policy `(μ, μ, …)` generated by `μ ∈ U(C|S)`. -/
def UCS.toPolicy {M : Model S C W} (μ : M.UCS) : M.Policy where
  μ := fun k =>
    { toFun := fun h => μ.κ.toFun h.2
      isProbability := fun h => μ.κ.isProbability h.2
      univMeasurable := fun B hB => by
        intro A hA
        have h := μ.κ.univMeasurable B hB A hA
        intro P hP
        have hm : Measurable (fun h : Hist S C k => h.2) := measurable_snd
        have := (h (P.map (fun h : Hist S C k => h.2))
          (Measure.isProbabilityMeasure_map hm.aemeasurable))
        exact this.preimage ⟨hm, Measure.AbsolutelyContinuous.rfl⟩ }
  admissible := fun _ h => μ.admissible h.2

/-- `J_μ` (p. 215): the cost of the stationary policy `(μ, μ, …)`. -/
noncomputable def Jmu (M : Model S C W) (μ : M.UCS) : S → EReal := μ.toPolicy.cost

/-- Eq. (2) of Chapter 9 (p. 215): the optimal cost `J*(x) = inf_{π ∈ Π'} J_π(x)`, the infimum
over all policies of Definition 9.2. -/
noncomputable def Jstar (M : Model S C W) (x : S) : EReal := ⨅ π : M.Policy, π.cost x

/-- p. 215: `π` is *optimal* if `J_π(x) = J*(x)` for every `x ∈ S`. -/
def IsOptimal (M : Model S C W) (π : M.Policy) : Prop := ∀ x, π.cost x = M.Jstar x

/-- **Definition 8.4** (p. 194). For `J : S → R*` and `μ ∈ U(C|S)`,
`T_μ(J)(x) = ∫_C [g(x, u) + α ∫_S J(x') t(dx' | x, u)] μ(du | x)`. -/
noncomputable def Tmu (M : Model S C W) (μ : M.UCS) (J : S → EReal) : S → EReal :=
  fun x => DupacovaWets.Consistency.expect (μ.κ.toFun x) (fun u => M.H x u J)

/-- **Definition 9.10** (p. 229). The dynamic programming algorithm for (SM):
`J₀(x) = 0`, `J_{k+1}(x) = T(J_k)(x)`; so `J_k = T^k(J₀)`. -/
noncomputable def dpIter (M : Model S C W) (k : ℕ) : S → EReal := (M.T)^[k] (fun _ => 0)

end Model

end BertsekasShreve.BorelInfinite


