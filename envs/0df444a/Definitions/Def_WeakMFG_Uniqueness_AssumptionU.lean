-- Prove2me | Definitions.Def_WeakMFG_Uniqueness_AssumptionU
-- name    : WeakMFG_Uniqueness_AssumptionU
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:17.324988+00:00
-- url     : https://prove2.me/theorems/68f8a305-19d0-42ed-8337-5054c1c29435
-- title:
--   Assumption (U) — unique maximizers, no mean field in the drift, separable reward, Lasry–Lions monotonicity
-- statement:
--   Assumption (U) of Carmona and Lacker (p. 11) consists of four conditions.
--
--   1. **(U.1)** For each $(t,x,\mu,z)$, the set $A(t,x,\mu,z)$ of maximizers of the Hamiltonian is a singleton.
--   2. **(U.2)** $b = b(t,x,a)$ has no mean field term.
--   3. **(U.3)** $f(t,x,\mu,q,a) = f_1(t,x,\mu) + f_2(t,\mu,q) + f_3(t,x,a)$ for some $f_1,f_2,f_3$.
--   4. **(U.4)** For all $\mu,\mu'\in\mathcal P_\psi(\mathcal C)$,
--   $$\int_{\mathcal C}\Big[g(x,\mu)-g(x,\mu')+\int_0^T\big(f_1(t,x,\mu)-f_1(t,x,\mu')\big)\,dt\Big](\mu-\mu')(dx)\le 0.$$
--
--   (U.4) is the Lasry–Lions monotonicity condition: the population-dependent part of the reward penalizes moving towards a crowded configuration. Together with (U.1) it is the hypothesis of the uniqueness theorem (Theorem 3.8).
--
--   **Formalization Note.** (U.3) as printed writes $f(t,x,\mu,a)$ on the left, omitting $q$; since $f$ always takes $(t,x,\mu,q,a)$ and $f_2$ carries $q$, the $q$-argument is restored. The function $f_1$ of (U.4) is that of (U.3) (one existential). The integral against $\mu-\mu'$ is $\int G\,d\mu-\int G\,d\mu'$ for the bracket $G$; the integrability that the page presupposes is stated: $t\mapsto f_1(t,x,\mu)-f_1(t,x,\mu')$ is integrable on $[0,T]$ for each $x$, and $G$ is integrable against $\mu$ and $\mu'$ (Lean's integral of a non-integrable function is $0$, which would otherwise weaken (U.4)). (U.1) is quantified over the $\mathcal P(A)$ argument of the maximizer set, on which it does not depend under (S.5).
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §3.2, Assumption (U), p. 11

import Mathlib
import Definitions.Def_WeakMFG_Uniqueness_Reward

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Uniqueness

variable {d : ℕ} {T : ℝ≥0}
  {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
  {ψ : WeakMFG.Existence.Path d T → ℝ}

/-- (U.1), p. 11: for each `(t, x, μ, z)` the set of maximizers `A(t, x, μ, z)` is a singleton
(quantified over the `q` argument, on which the set does not depend under (S.5)). -/
def U1 (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) : Prop :=
  ∀ t x μ q z, ∃ a, Amax A σ b f t x μ q z = {a}

/-- (U.2), p. 11: `b = b(t, x, a)` has no mean field term. -/
def U2 (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ)) : Prop :=
  ∃ b₀ : ℝ≥0 → WeakMFG.Existence.Path d T → EA → (Fin d → ℝ), ∀ t x μ a, b t x μ a = b₀ t x a

/-- The decomposition of (U.3), p. 11: `f(t, x, μ, q, a) = f₁(t, x, μ) + f₂(t, μ, q) + f₃(t, x, a)`.
The page writes `f(t, x, μ, a)` on the left, without `q`; `f` always takes `(t, x, μ, q, a)`
((S.3), (S.5)) and `f₂` carries `q`, so the `q`-argument is restored. -/
def IsU3Decomp {A : Set EA} (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ)
    (f₁ : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) (f₂ : ℝ≥0 → Ppsi ψ → PA A → ℝ)
    (f₃ : ℝ≥0 → WeakMFG.Existence.Path d T → EA → ℝ) : Prop :=
  ∀ t x μ q a, f t x μ q a = f₁ t x μ + f₂ t μ q + f₃ t x a

/-- The Lasry–Lions integrand of (U.4):
`G_{μ,μ'}(x) = g(x, μ) − g(x, μ') + ∫₀ᵀ (f₁(t, x, μ) − f₁(t, x, μ')) dt`. -/
noncomputable def lmGap (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) (f₁ : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (μ μ' : Ppsi ψ) (x : WeakMFG.Existence.Path d T) : ℝ :=
  g x μ - g x μ' + ∫ t in Set.Icc (0 : ℝ) T, (f₁ t.toNNReal x μ - f₁ t.toNNReal x μ')

/-- (U.4), p. 11, for the `f₁` of (U.3): for all `μ, μ' ∈ P_ψ(𝒞)`,
`∫_𝒞 [g(x, μ) − g(x, μ') + ∫₀ᵀ (f₁(t, x, μ) − f₁(t, x, μ')) dt] (μ − μ')(dx) ≤ 0`.
**Formalization Note.** The integral against the signed measure `μ − μ'` is
`∫ G dμ − ∫ G dμ'`. The page presupposes that the integrals exist; this is stated explicitly
(`t ↦ f₁(t, x, μ) − f₁(t, x, μ')` is integrable on `[0, T]` for each `x`, and `G` is integrable
against `μ` and `μ'`), since Lean's Bochner integral of a non-integrable function is `0`. -/
def U4 (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) (f₁ : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) : Prop :=
  ∀ μ μ' : Ppsi ψ,
    (∀ x, IntegrableOn (fun t : ℝ => f₁ t.toNNReal x μ - f₁ t.toNNReal x μ') (Set.Icc 0 T)) ∧
    Integrable (lmGap g f₁ μ μ') μ.toMeasure ∧ Integrable (lmGap g f₁ μ μ') μ'.toMeasure ∧
    ∫ x, lmGap g f₁ μ μ' x ∂μ.toMeasure - ∫ x, lmGap g f₁ μ μ' x ∂μ'.toMeasure ≤ 0

/-- Assumption (U), p. 11: (U.1), (U.2), and some `f₁, f₂, f₃` with the decomposition (U.3) for
which (U.4) holds (one existential, so that the `f₁` of (U.4) is that of (U.3)). -/
def AssumptionU (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) : Prop :=
  U1 A σ b f ∧ U2 b ∧
    ∃ (f₁ : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) (f₂ : ℝ≥0 → Ppsi ψ → PA A → ℝ)
      (f₃ : ℝ≥0 → WeakMFG.Existence.Path d T → EA → ℝ), IsU3Decomp f f₁ f₂ f₃ ∧ U4 g f₁

end WeakMFG.Uniqueness


