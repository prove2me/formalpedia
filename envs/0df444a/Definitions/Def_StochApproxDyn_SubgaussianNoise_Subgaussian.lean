-- Prove2me | Definitions.Def_StochApproxDyn_SubgaussianNoise_Subgaussian
-- name    : StochApproxDyn_SubgaussianNoise_Subgaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:46:05.279205+00:00
-- url     : https://prove2.me/theorems/384a059b-5138-4853-8404-4a19b7808e4f
-- title:
--   Subgaussian martingale noise (§4.2)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $\{\mathcal F_n\}_{n\ge0}$ a nondecreasing sequence of sub-$\sigma$-algebras of $\mathcal F$, and $\{U_n\}_{n\ge1}$ a sequence of random vectors in $\mathbb R^d$. For $\Gamma\in\mathbb R$, say that $\{U_n\}$ is **subgaussian with constant $\Gamma$** if for every $n\ge0$ and every $\theta\in\mathbb R^d$ the random variable $\exp\langle\theta,U_{n+1}\rangle$ is integrable and, almost surely,
--   $$E\big(\exp\langle\theta,U_{n+1}\rangle\,\big|\,\mathcal F_n\big)\le\exp\Big(\frac{\Gamma}{2}\|\theta\|^2\Big).$$
--   The sequence $\{U_n\}$ is **subgaussian** if it is subgaussian with some constant $\Gamma>0$.
--
--   This is the noise condition of Benaïm's Proposition 4.4: it controls every exponential moment of the noise, conditionally on the past, uniformly in time, and so gives Gaussian-type tail bounds for weighted sums of the noise. It holds, for instance, when $\|U_n\|\le\sqrt\Gamma$ and $E(U_{n+1}\mid\mathcal F_n)=0$ (by Hoeffding's lemma).
--
--   **Formalization Note** The integrability of $\exp\langle\theta,U_{n+1}\rangle$ is part of the definition: Lean's conditional expectation of a non-integrable function is $0$, which would make the inequality hold vacuously. $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` (the paper writes $\mathbb R^m$). The paper indexes $U$ from $1$; $U_0$ is not used. Mathlib's `HasCondSubgaussianMGF` is a scalar notion for a single random variable and a single sub-$\sigma$-algebra; the present condition is vector-valued with one constant for all $n$ and $\theta$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.2, p. 16 (PDF p. 17), definition of a subgaussian sequence {U_n}

import Mathlib

namespace StochApproxDyn.SubgaussianNoise

open MeasureTheory
open scoped InnerProductSpace

/-- Subgaussian noise with a given constant `Γ` (Benaïm 1999, §4.2, p. 16): for every `n ≥ 0`
and every `θ ∈ ℝ^d`, `exp ⟨θ, U_{n+1}⟩` is integrable and
`E(exp ⟨θ, U_{n+1}⟩ | ℱ_n) ≤ exp((Γ/2)‖θ‖²)` almost surely.
The integrability clause makes the conditional expectation the genuine one (Lean's `condExp`
of a non-integrable function is `0`, which would make the bound vacuous). -/
def IsSubgaussianWith {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (Γ : ℝ) : Prop :=
  ∀ (n : ℕ) (θ : EuclideanSpace ℝ (Fin d)),
    Integrable (fun ω => Real.exp ⟪θ, U (n + 1) ω⟫_ℝ) P ∧
    P[fun ω => Real.exp ⟪θ, U (n + 1) ω⟫_ℝ | ℱ n] ≤ᵐ[P] fun _ => Real.exp (Γ / 2 * ‖θ‖ ^ 2)

/-- The sequence `{U_n}` is **subgaussian** (Benaïm 1999, §4.2, p. 16) if there exists a positive
number `Γ` such that for all `θ ∈ ℝ^d` and all `n`,
`E(exp ⟨θ, U_{n+1}⟩ | ℱ_n) ≤ exp((Γ/2)‖θ‖²)`. -/
def IsSubgaussian {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ Γ : ℝ, 0 < Γ ∧ IsSubgaussianWith P ℱ U Γ

end StochApproxDyn.SubgaussianNoise


