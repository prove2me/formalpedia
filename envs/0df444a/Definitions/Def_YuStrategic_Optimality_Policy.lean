-- Prove2me | Definitions.Def_YuStrategic_Optimality_Policy
-- name    : YuStrategic_Optimality_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:23:00.004008+00:00
-- url     : https://prove2.me/theorems/22f801bb-22fb-4318-8394-2bca6ac4119e
-- title:
--   Universally measurable policies and the classes $\Pi',\Pi_m,\Pi_{sm},\Pi_s,\Pi_{ss}$
-- statement:
--   A **universally measurable policy** (a *policy*) is a sequence $\pi=(\mu_0,\mu_1,\dots)$ where, for each $n\ge0$, $\mu_n(da_n\mid h_n)$ is a universally measurable stochastic kernel on $\mathbb A$ given $H_n$ satisfying the control constraint
--   $$\mu_n\big(A(x_n)\mid h_n\big)=1\qquad\forall\,h_n=(x_0,a_0,\dots,a_{n-1},x_n)\in H_n. \tag{2.4}$$
--   A kernel is universally measurable if $h\mapsto\mu(B\mid h)$ is universally measurable for every Borel $B$.
--
--   Policy classes:
--   1. $\pi$ is **nonrandomized** if every $\mu_n(\cdot\mid h_n)$ is a Dirac measure.
--   2. $\pi$ is **Markov** (resp. **semi-Markov**) if for every $n$, $\mu_n(\cdot\mid h_n)$ depends only on $x_n$ (resp. on $(x_0,x_n)$).
--   3. $\pi$ is **stationary** if it is Markov with identical kernels, $\pi=(\mu,\mu,\dots)$.
--   4. $\pi$ is **semi-stationary** if there is a kernel $\tilde\mu$ on $\mathbb A$ given $\mathbb X^2$ with $\mu_0(da_0\mid x_0)=\tilde\mu(da_0\mid x_0,x_0)$ and $\mu_n(da_n\mid h_n)=\tilde\mu(da_n\mid x_0,x_n)$ for all $n\ge1$.
--
--   $\Pi,\Pi_{sm},\Pi_m,\Pi_{ss},\Pi_s$ denote all, semi-Markov, Markov, semi-stationary and stationary policies, and $\Pi'_\star$ the nonrandomized members of $\Pi_\star$. The three pairs $(\mathcal S_\star,\Pi_\star)$ used in Theorem 3.3 and Proposition 3.1 are recorded by a label $\kappa\in\{\text{all},\text{markov},\text{stationary}\}$: $\kappa$ selects the class generating $\mathcal S_\star$ ($\Pi,\Pi_m,\Pi_s$) and the matching class $\Pi_\star$ ($\Pi,\Pi_{sm},\Pi_{ss}$).
--
--   **Formalization Note.** Kernels are the published `BertsekasShreve.BorelInfinite.UKernel`. "Depends only on $x_n$ (resp. $(x_0,x_n)$)" is encoded as $\mu_n(\cdot\mid h_n)=\nu_n(\cdot\mid x_n)$ (resp. $\nu_n(\cdot\mid x_0,x_n)$) for universally measurable kernels $\nu_n$ on $\mathbb A$ given $\mathbb X$ (resp. $\mathbb X^2$); the two formulations agree because restricting a universally measurable kernel along a Borel map gives a universally measurable kernel. The control constraint evaluates $\mu_n(\cdot\mid h_n)$ at the analytic set $A(x_n)$ (Mathlib: outer measure, equal to the completion's value).
-- source:
--   Yu, arXiv:2206.06492v3, §2.2, p. 6, eq. (2.4) and the paragraph after it; (S⋆, Π⋆) pairs from Theorem 3.3, p. 8

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy
import Definitions.Def_YuStrategic_Optimality_PathSpace
import Definitions.Def_YuStrategic_Optimality_Model

namespace YuStrategic.Optimality

open MeasureTheory ProbabilityTheory BertsekasShreve.BorelInfinite

variable {X A : Type} [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace A] [MeasurableSpace A]

/-- A universally measurable policy (Yu, arXiv:2206.06492v3, §2.2, p. 6, eq. (2.4)): a sequence
`π = (μ₀, μ₁, …)` where each `μₙ(daₙ | hₙ)` is a universally measurable stochastic kernel on `A`
given `Hₙ = (X × A)^n × X` that satisfies the control constraint
`μₙ(A(xₙ) | hₙ) = 1` for every `hₙ = (x₀, a₀, …, xₙ) ∈ Hₙ`.

**Formalization Note.** Universally measurable kernels are the published
`BertsekasShreve.BorelInfinite.UKernel` (a probability measure for each argument, with
`h ↦ μ(B | h)` universally measurable for every Borel `B`). `A(xₙ)` is analytic, hence
universally measurable, so evaluating the measure at it (Mathlib: outer measure) gives the
completion's value, as on the page. -/
structure Policy (M : Model X A) where
  /-- the kernel `μₙ(daₙ | hₙ)` -/
  μ : (n : ℕ) → UKernel (Hist X A n) A
  /-- the control constraint (2.4) -/
  admissible : ∀ (n : ℕ) (h : Hist X A n), (μ n).toFun h (M.adm h.2) = 1

namespace Policy

variable {M : Model X A}

/-- `π` is *nonrandomized* (§2.2, p. 6): every `μₙ(· | hₙ)` is a Dirac measure. -/
def IsNonrandomized (π : Policy M) : Prop :=
  ∀ (n : ℕ) (h : Hist X A n), ∃ a : A, (π.μ n).toFun h = Measure.dirac a

/-- `π` is *Markov* (§2.2, p. 6): for every `n`, `μₙ(· | hₙ)` depends only on `xₙ`, i.e.
`μₙ(· | hₙ) = νₙ(· | xₙ)` for universally measurable kernels `νₙ` on `A` given `X`. -/
def IsMarkov (π : Policy M) : Prop :=
  ∃ ν : ℕ → UKernel X A, ∀ (n : ℕ) (h : Hist X A n), (π.μ n).toFun h = (ν n).toFun h.2

/-- `π` is *semi-Markov* (§2.2, p. 6): for every `n`, `μₙ(· | hₙ)` depends only on `(x₀, xₙ)`,
i.e. `μₙ(· | hₙ) = νₙ(· | x₀, xₙ)` for universally measurable kernels `νₙ` on `A` given `X²`. -/
def IsSemiMarkov (π : Policy M) : Prop :=
  ∃ ν : ℕ → UKernel (X × X) A, ∀ (n : ℕ) (h : Hist X A n),
    (π.μ n).toFun h = (ν n).toFun (x0 h, h.2)

/-- `π` is *stationary* (§2.2, p. 6): a Markov policy with identical kernels,
`π = (μ, μ, …)`, i.e. `μₙ(· | hₙ) = μ(· | xₙ)` for all `n`. -/
def IsStationary (π : Policy M) : Prop :=
  ∃ ν : UKernel X A, ∀ (n : ℕ) (h : Hist X A n), (π.μ n).toFun h = ν.toFun h.2

/-- `π` is *semi-stationary* (§2.2, p. 6): there is a stochastic kernel `μ̃` on `A` given `X²` with
`μ₀(da₀ | x₀) = μ̃(da₀ | x₀, x₀)` and `μₙ(daₙ | hₙ) = μ̃(daₙ | x₀, xₙ)` for all `n ≥ 1`. -/
def IsSemiStationary (π : Policy M) : Prop :=
  ∃ ν : UKernel (X × X) A, ∀ (n : ℕ) (h : Hist X A n), (π.μ n).toFun h = ν.toFun (x0 h, h.2)

end Policy

/-- The three pairs `(S⋆, Π⋆) = (S, Π), (S_m, Π_sm), (S_s, Π_ss)` of Yu, arXiv:2206.06492v3,
Theorem 3.3 (p. 8) and Proposition 3.1 (p. 8): `all` (all policies), `markov`, `stationary`. -/
inductive PolicyClass
  | all
  | markov
  | stationary
  deriving DecidableEq

namespace PolicyClass

variable {M : Model X A}

/-- Membership in the policy class that generates `S⋆` (p. 7): `Π`, `Π_m` or `Π_s`. -/
def mem : PolicyClass → Policy M → Prop
  | all, _ => True
  | markov, π => π.IsMarkov
  | stationary, π => π.IsStationary

/-- Membership in the matching class `Π⋆` of Theorem 3.3 and Proposition 3.1 (p. 8): `Π`,
`Π_sm` (semi-Markov) or `Π_ss` (semi-stationary). -/
def semiMem : PolicyClass → Policy M → Prop
  | all, _ => True
  | markov, π => π.IsSemiMarkov
  | stationary, π => π.IsSemiStationary

end PolicyClass

end YuStrategic.Optimality


