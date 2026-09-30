-- Prove2me | Definitions.Def_Avram2004_Canadized_canadizedProblem
-- name    : Avram2004_Canadized_canadizedProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:18:27.359989+00:00
-- url     : https://prove2.me/theorems/71aeb184-6a14-49cd-a51e-0da7ec292f5c
-- title:
--   Canadized Russian problem (32): admissible stopping times, the exponential clock η(λ), the value w^CR, the level κ_* and the function h
-- statement:
--   This definition file fixes the objects of the Canadized Russian optimal stopping problem of Avram, Kyprianou and Pistorius (§7). Throughout, $X$ is a spectrally negative Lévy process started at $0$, $\mathbf F=\{\mathcal F_t\}_{t\ge0}$ a filtration, $\mathbb P^1$ the Esscher measure, and $Y=\overline X-X$ the reflected process; under $\mathbb P^1_{-z}$ it starts at $Y_0=z\ge0$.
--
--   1. **Admissible stopping times.** An admissible exercise rule is an $\mathbf F$-stopping time $\tau$ with values in $[0,\infty]$ that is $\mathbb P^1$-almost surely finite.
--   2. **The exponential clock.** $\eta=\eta(\lambda)$ is a real random variable whose law under $\mathbb P^1$ is exponential with rate $\lambda>0$ (density $\lambda e^{-\lambda t}$ on $[0,\infty)$), and which under $\mathbb P^1$ is independent of $\mathcal F_\infty=\bigvee_{t\ge0}\mathcal F_t$.
--   3. **Payoff and value.** For an admissible $\tau$, the holder receives $e^{-\alpha(\tau\wedge\eta)+Y_{\tau\wedge\eta}}$, and the value function is
--   $$
--   w^{CR}(z)=\sup_{\tau}\ \mathbb E^1_{-z}\Big[e^{-\alpha(\tau\wedge\eta(\lambda))+Y_{\tau\wedge\eta(\lambda)}}\Big],
--   $$
--   the supremum over all admissible $\tau$.
--   4. **Running integral.** For a random time $T$, $\int_0^T e^{-at+Y_t}\,dt$ (over $(0,\infty)$ when $T=\infty$).
--   5. **The level and the candidate value.** With $p=\alpha+\lambda+r$ and the scale functions $W^{(p)},Z^{(p)}$ of $(X,\mathbb P)$,
--   $$
--   \kappa_*=\inf\{x\ge0:\ Z^{(p)}(x)-pW^{(p)}(x)\le-\lambda/(p-\lambda)\},\qquad h(z)=\frac{(p-\lambda)e^zZ^{(p)}(\kappa_*-z)}{p}+\frac{\lambda e^z}{p}.
--   $$
--   6. **The process of Lemma 4.** Under $\mathbb P^1_{s,x}$ ($Y_0=s-x$), $U_t=e^{-(\alpha+\lambda)t}h(Y_t)+\lambda\int_0^te^{-(\alpha+\lambda)u+Y_u}\,du$.
--
--   Theorem 3 of the paper identifies $w^{CR}$ with $h$ and shows that the passage time $\tau_{\kappa_*}$ of $Y$ above $\kappa_*$ is optimal.
--
--   **Formalization Note** Payoffs and value are computed in $[0,\infty]$ (lower Lebesgue integrals and an extended-real supremum), so no expectation takes a default value. The payoff at a random time $T$ is $0$ on $\{T=\infty\}$, a $\mathbb P^1$-null event for admissible times. The random time $\tau\wedge\eta$ uses $\max(\eta,0)$; $\eta<0$ has probability $0$. The law and the independence of $\eta$ are required under $\mathbb P^1$, because (32) is a $\mathbb P^1$-expectation, and $\eta$ is independent of the whole filtration, not only of $X$, so an admissible $\tau$ cannot see $\eta$. The parameter $\lambda$ is the rate. $\kappa_*$ is a real infimum; its set is nonempty because $Z^{(p)}-pW^{(p)}$ decreases to $-\infty$ (Lemma 2 (i) with $q=p>r$), and $p-\lambda=\alpha+r>0$, so no division by zero occurs.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, pp. 231–234: §7 first paragraph and Eq. (32) (pp. 231–232), "From now we write p = α + λ + r" (p. 232), definition of κ_* (p. 233, display before Theorem 3), Theorem 3 (h), proof of Lemma 4 (U_t, p. 234)

import Mathlib
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Avram2004.Canadized

/-- The admissible exercise rules of (32): the `𝓕`-stopping times that are almost surely finite
under `Q` (= `ℙ^1`). -/
def Admissible {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) (Q : Measure Ω) :
    Set (Ω → WithTop ℝ≥0) :=
  {τ | IsStoppingTime 𝓕 τ ∧ ∀ᵐ ω ∂Q, τ ω ≠ ⊤}

/-- §7, p. 231: `η = η(λ)` is an `F`-independent exponential random variable with parameter (rate)
`λ > 0`, under `Q` (= `ℙ^1`): `η` is measurable, its law under `Q` is the exponential law with density
`λ e^{-λ t}` on `[0, ∞)`, and `η` is independent under `Q` of the whole filtration
`𝓕_∞ = ⋁_t 𝓕_t`. -/
def IsExpClock {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) (Q : Measure Ω)
    (η : Ω → ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧ Measurable η ∧ Q.map η = expMeasure lam ∧
    Indep (MeasurableSpace.comap η (inferInstance : MeasurableSpace ℝ)) (⨆ t, 𝓕 t) Q

/-- The random time `τ ∧ η(λ)` (finite whenever `η` is: `η` is real valued, and a negative value
of `η`, which has probability `0`, is read as `0`). -/
noncomputable def minTime {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (η : Ω → ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  min (τ ω) (((η ω).toNNReal : ℝ≥0) : WithTop ℝ≥0)

/-- The discounted payoff `e^{-a T + Y_T}` at a random time `T` of a process `Y`, as an extended
nonnegative real, with the value `0` on `{T = ∞}`. -/
noncomputable def payoffAt {Ω : Type*} (a : ℝ) (Y : ℝ≥0 → Ω → ℝ) (T : Ω → WithTop ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  match T ω with
  | none => 0
  | some t => ENNReal.ofReal (Real.exp (-a * (t : ℝ) + Y t ω))

/-- The Canadized payoff of (32) under `ℙ^1_{-z}` (so `Y = refl 0 (-z) X`, `Y_0 = z`):
`e^{-α(τ ∧ η(λ)) + Y_{τ ∧ η(λ)}}`. -/
noncomputable def crPayoff {Ω : Type*} (α z : ℝ) (X : ℝ≥0 → Ω → ℝ) (η : Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  payoffAt α (Shared.refl 0 (-z) X) (minTime τ η) ω

/-- The value function of the Canadized Russian optimal stopping problem (32):
`w^{CR}(z) = sup_τ 𝔼^1_{-z}[e^{-α(τ ∧ η(λ)) + Y_{τ ∧ η(λ)}}]`, the supremum over all `Q`-almost surely
finite `𝓕`-stopping times `τ`, computed in `[0, ∞]`. -/
noncomputable def valueCR {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (Q : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (η : Ω → ℝ) (α z : ℝ) : ℝ≥0∞ :=
  ⨆ τ ∈ Admissible 𝓕 Q, ∫⁻ ω, crPayoff α z X η τ ω ∂Q

/-- The running integral `∫_0^T e^{-a t + Y_t} dt` up to a random time `T` (over `(0, T]`, and over
`(0, ∞)` when `T = ∞`), as an extended nonnegative real. -/
noncomputable def runIntegral {Ω : Type*} (a : ℝ) (Y : ℝ≥0 → Ω → ℝ) (T : Ω → WithTop ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t in {t : ℝ | 0 < t ∧ (((t.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ T ω)},
    ENNReal.ofReal (Real.exp (-a * t + Y t.toNNReal ω))

/-- The level of §7, p. 233 (display before Theorem 3):
`κ_* = inf {x ≥ 0 : Z^{(p)}(x) - p W^{(p)}(x) ≤ -λ/(p - λ)}`, with the scale functions of `(X, P)`. -/
noncomputable def kappaLow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (p lam : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ Shared.Z P X 0 p x - p * Shared.W P X 0 p x ≤ -lam / (p - lam)}

/-- Theorem 3: `h(z) = (p - λ) e^z Z^{(p)}(κ_* - z)/p + λ e^z/p`. -/
noncomputable def hCR {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (p lam z : ℝ) : ℝ :=
  (p - lam) * Real.exp z * Shared.Z P X 0 p (kappaLow P X p lam - z) / p + lam * Real.exp z / p

/-- The process of Lemma 4's proof (p. 234) under `ℙ^1_{s,x}` (`Y = refl s x X`):
`U_t = e^{-(α+λ)t} h(Y_t) + λ ∫_0^t e^{-(α+λ)u + Y_u} du`. Here `p = α + λ + r` is passed as `p`. -/
noncomputable def U {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (α lam p s x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(α + lam) * (t : ℝ)) * hCR P X p lam (Shared.refl s x X t ω)
    + lam * ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-(α + lam) * u + Shared.refl s x X u.toNNReal ω)

end Avram2004.Canadized


