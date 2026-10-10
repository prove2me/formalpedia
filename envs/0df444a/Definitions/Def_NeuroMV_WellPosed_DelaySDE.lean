-- Prove2me | Definitions.Def_NeuroMV_WellPosed_DelaySDE
-- name    : NeuroMV_WellPosed_DelaySDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:11.980286+00:00
-- url     : https://prove2.me/theorems/8780540c-3fb6-48ed-ae4e-747d9d5c633b
-- title:
--   Appendix A, pp. 22–23 — the path-dependent delay SDE (20) with jumps, Hypothesis A.1 (C1)–(C4), the Euler approximation (21)
-- statement:
--   This module sets up the general stochastic delay equation of Appendix A,
--
--   $$dX^{\omega'}_t = f(t,\omega,X^{\omega'}_{(t-\tau)^-:t^-},\omega')dt + g(t,\omega,X^{\omega'}_{(t-\tau)^-:t^-},\omega')dW_t + \int_U h(t,\omega,X^{\omega'}_{(t-\tau)^-:t^-},\omega',\xi)\tilde N(dt,d\xi),\qquad X^{\omega'}_t = z^{\omega'}_t,\ t\in[-\tau,0], \tag{20}$$
--
--   driven by an $m$-dimensional $(\mathcal F_t)$-Brownian motion $W$ and an $(\mathcal F_t)$-Poisson random measure $N$ on $[0,\infty)\times U$ with intensity $dt\otimes\nu$, $\nu$ σ-finite. The initial condition $z^{\omega'}$ is jointly measurable in $(t,\omega,\omega')$ and belongs to $L^2(\Omega;\text{Càdlàg}([-\tau,0];\mathbb R^d))$. The coefficients $f, g$ are progressively measurable and $h$ is predictable (jointly with the path argument, $\omega'$ and $\xi$).
--
--   **Hypothesis A.1.** There are a probability measure $\lambda$ on $[-\tau,0]$ and nonnegative measurable rates $K_t(\omega')$, $L_t(R,\omega')$, $\tilde K_t(R,\omega')$, locally integrable in $t$, such that for càglàd segments $x, y$ on $[-\tau,0]$:
--   1. (C1) for $|x|_{L^\infty}, |y|_{L^\infty} \le R$: $2\langle x_0-y_0, f(x)-f(y)\rangle + |g(x)-g(y)|^2 + \int_U|h(x)-h(y)|^2d\nu \le L_t(R,\omega')\int_{-\tau}^0\big[|x_s-y_s|^2 + 1_{s<0}|x_{s+}-y_{s+}|^2\big]\lambda(ds)$;
--   2. (C2) $2\langle x_0, f(x)\rangle + |g(x)|^2 + \int_U|h(x)|^2d\nu \le K_t(\omega')\big(1+\int_{-\tau}^0[|x_s|^2 + 1_{s<0}|x_{s+}|^2]\lambda(ds)\big)$;
--   3. (C3) $x \mapsto f(t,\omega,x,\omega')$ is continuous for the supremum norm;
--   4. (C4) $\sup_{|x|_{L^\infty}\le R}\big[|f(x)| + |g(x)|^2 + \int_U|h(x)|^2d\nu\big] \le \tilde K_t(R,\omega')$.
--
--   A strong solution of (20) is an adapted process with càdlàg paths, equal to $z^{\omega'}$ on $[-\tau,0]$, satisfying the integral form of (20) almost surely at each $t \ge 0$. The Euler approximation (21) is the process with $X^{n,\omega'}_t = z^{\omega'}_t$ on $[-\tau,0]$ and, on each $]k\tau/n,(k+1)\tau/n]$,
--
--   $$X^{n,\omega'}_t = X^{n,\omega'}_{k\tau/n} + \int_{k\tau/n}^t f(s,\omega,X^{n,\omega'}_{\kappa(n,(s-\tau):s)},\omega')ds + \int_{k\tau/n}^t g(\cdots)dW_s + \int_{k\tau/n}^t\!\!\int_U h(\cdots,\xi)\tilde N(ds,d\xi).$$
--
--   **Formalization Note.** Progressive measurability is: for every $t$, measurability on $[0,t]\times\Omega\times\text{paths}\times\Omega'$ for $\mathcal B([0,t])\otimes\mathcal F_t\otimes\mathcal B(\text{paths})\otimes\mathcal F'$; predictability uses Mathlib's predictable σ-algebra; paths carry the cylinder σ-algebra (a mild added requirement). The independence of $z$ from $W$ and $N$ is encoded by $\mathcal F_0$-measurability of $z$. The $\nu$-integrals are asserted finite and the $\lambda$-integrals (finite for càglàd segments) are compared as real numbers. Stochastic integrals are the published `EthierKurtz.HasBrownianItoIntegral` and `JacodTodorov10.LLN.HasCompInt`, coordinatewise; (21) is encoded in its global integral form.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, Appendix A, (20), Hypothesis A.1 (C1)–(C4) and (21), p. 22; κ(n, t), p. 23

import Mathlib
import Definitions.Def_NeuroMV_WellPosed_Setting
import Definitions.Def_NeuroMV_WellPosed_Scheme

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

/-- The **coefficients of the delay equation (20)** (Mehri–Scheutzow–Stannat–Zangeneh,
arXiv:1805.01654v3, Appendix A, p. 22): `f, g, h` depend on time `t ≥ 0`, the sample point
`ω ∈ Ω`, a path segment `x_{−τ:0}` (a path `ℝ → ℝ^d` read on `[−τ, 0]`), the disorder `ω' ∈ Ω'`
and (for `h`) a mark `ξ ∈ U`. -/
structure CoeffsA (d m : ℕ) (Ω U Ω' : Type*) where
  f : ℝ≥0 → Ω → (ℝ → SDEState d) → Ω' → SDEState d
  g : ℝ≥0 → Ω → (ℝ → SDEState d) → Ω' → Matrix (Fin d) (Fin m) ℝ
  h : ℝ≥0 → Ω → (ℝ → SDEState d) → Ω' → U → SDEState d

variable {d m : ℕ} {U Ω Ω' : Type*}

/-- **Measurability of the coefficients of (20)** (p. 22): `f` and `g` (entrywise) are
progressively measurable — for every `t`, measurable on `[0, t] × Ω × paths × Ω'` w.r.t.
`𝓑([0, t]) ⊗ 𝓕_t ⊗ 𝓑(paths) ⊗ 𝓕'` — and `h` is measurable w.r.t.
`𝒫 ⊗ 𝓑(paths) ⊗ 𝓕' ⊗ 𝒰`, `𝒫` the predictable σ-algebra on `[0, ∞) × Ω` (Mathlib's
`Filtration.predictable`). Paths carry the product (cylinder) σ-algebra of `ℝ → ℝ^d`. -/
def CoeffsA.Regular [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (A : CoeffsA d m Ω U Ω') : Prop :=
  (∀ t : ℝ≥0, Measurable[MeasurableSpace.prod inferInstance
      (MeasurableSpace.prod (𝓕 t) inferInstance)]
    (fun p : Set.Iic t × Ω × (ℝ → SDEState d) × Ω' => A.f p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧
  (∀ (t : ℝ≥0) (i : Fin d) (j : Fin m), Measurable[MeasurableSpace.prod inferInstance
      (MeasurableSpace.prod (𝓕 t) inferInstance)]
    (fun p : Set.Iic t × Ω × (ℝ → SDEState d) × Ω' => A.g p.1 p.2.1 p.2.2.1 p.2.2.2 i j)) ∧
  Measurable[MeasurableSpace.prod 𝓕.predictable inferInstance]
    (fun p : (ℝ≥0 × Ω) × (ℝ → SDEState d) × Ω' × U => A.h p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

/-- **Hypothesis A.1** (p. 22), for given data: `λ` is a probability measure on `[−τ, 0]`; `K` and,
for every `R > 0`, `L(R)` and `K̃(R)` (`Kt R`) are rates (nonnegative, measurable, `L¹_loc`); and
for all `t ≥ 0`, `ω`, `ω'` and càglàd segments `x, y` on `[−τ, 0]`:
* (C1) if `|x|_{L∞}, |y|_{L∞} ≤ R` then
  `2⟨x_0 − y_0, f(x) − f(y)⟩ + |g(x) − g(y)|² + ∫_U |h(x) − h(y)|² dν
    ≤ L_t(R) ∫_{−τ}^0 [|x_s − y_s|² + 1_{s<0}|x_{s+} − y_{s+}|²] λ(ds)`;
* (C2) `2⟨x_0, f(x)⟩ + |g(x)|² + ∫_U |h(x)|² dν ≤ K_t (1 + ∫_{−τ}^0 [|x_s|² + 1_{s<0}|x_{s+}|²] λ(ds))`;
* (C3) `x ↦ f(t, ω, x, ω')` is continuous for the supremum norm on `[−τ, 0]`;
* (C4) if `|x|_{L∞} ≤ R` then `|f(x)| + |g(x)|² + ∫_U |h(x)|² dν ≤ K̃_t(R)`.
The `ν`-integrals are finite (the inequalities assert it) and the `λ`-integrals are finite for
càglàd segments; both are compared as real numbers. -/
def HypA1 [MeasurableSpace U] [MeasurableSpace Ω'] (A : CoeffsA d m Ω U Ω') (ν : Measure U)
    (τ : ℝ) (lam : Measure ℝ) (K : ℝ≥0 → Ω' → ℝ) (L Kt : ℝ → ℝ≥0 → Ω' → ℝ) : Prop :=
  IsProbabilityMeasure lam ∧ lam (Set.Icc (-τ) 0)ᶜ = 0 ∧
  IsRate K ∧ (∀ R : ℝ, 0 < R → IsRate (L R)) ∧ (∀ R : ℝ, 0 < R → IsRate (Kt R)) ∧
  -- (C1)
  (∀ R : ℝ, 0 < R → ∀ (t : ℝ≥0) (ω : Ω) (x y : ℝ → SDEState d) (ω' : Ω'),
    IsCagladOn x (-τ) 0 → IsCagladOn y (-τ) 0 →
    (∀ s ∈ Set.Icc (-τ) 0, ‖x s‖ ≤ R) → (∀ s ∈ Set.Icc (-τ) 0, ‖y s‖ ≤ R) →
    ∫⁻ ξ, ‖A.h t ω x ω' ξ - A.h t ω y ω' ξ‖ₑ ^ 2 ∂ν < ⊤ ∧
    2 * inner ℝ (x 0 - y 0) (A.f t ω x ω' - A.f t ω y ω') +
        frobSq (A.g t ω x ω' - A.g t ω y ω') +
        (∫⁻ ξ, ‖A.h t ω x ω' ξ - A.h t ω y ω' ξ‖ₑ ^ 2 ∂ν).toReal
      ≤ L R t ω' * (delayInt lam x y).toReal) ∧
  -- (C2)
  (∀ (t : ℝ≥0) (ω : Ω) (x : ℝ → SDEState d) (ω' : Ω'), IsCagladOn x (-τ) 0 →
    ∫⁻ ξ, ‖A.h t ω x ω' ξ‖ₑ ^ 2 ∂ν < ⊤ ∧
    2 * inner ℝ (x 0) (A.f t ω x ω') + frobSq (A.g t ω x ω') +
        (∫⁻ ξ, ‖A.h t ω x ω' ξ‖ₑ ^ 2 ∂ν).toReal
      ≤ K t ω' * (1 + (delayInt lam x 0).toReal)) ∧
  -- (C3)
  (∀ (t : ℝ≥0) (ω : Ω) (ω' : Ω') (x : ℝ → SDEState d), IsCagladOn x (-τ) 0 →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ → SDEState d, IsCagladOn y (-τ) 0 →
      (∀ s ∈ Set.Icc (-τ) 0, ‖x s - y s‖ ≤ δ) → ‖A.f t ω x ω' - A.f t ω y ω'‖ < ε) ∧
  -- (C4)
  (∀ R : ℝ, 0 < R → ∀ (t : ℝ≥0) (ω : Ω) (x : ℝ → SDEState d) (ω' : Ω'),
    IsCagladOn x (-τ) 0 → (∀ s ∈ Set.Icc (-τ) 0, ‖x s‖ ≤ R) →
    ∫⁻ ξ, ‖A.h t ω x ω' ξ‖ₑ ^ 2 ∂ν < ⊤ ∧
    ‖A.f t ω x ω'‖ + frobSq (A.g t ω x ω') + (∫⁻ ξ, ‖A.h t ω x ω' ξ‖ₑ ^ 2 ∂ν).toReal
      ≤ Kt R t ω')

/-- The **noise and initial condition of (20)** on a filtered probability space: an
`m`-dimensional Brownian motion `W`, the atoms `N` of a Poisson random measure on `[0, ∞) × U`, and
the initial condition `z^{ω'}_t(ω)`. -/
structure NoiseA (d m : ℕ) (U Ω Ω' : Type*) [MeasurableSpace Ω] where
  𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›
  prob : Measure Ω
  W : ℝ≥0 → Ω → SDEState m
  N : Ω → Set (ℝ≥0 × U)
  z : Ω' → ℝ → Ω → SDEState d

/-- **Standing assumptions of Appendix A** (p. 22): `ℙ` is a probability measure; `W` is an
`(𝓕_t)`-Brownian motion in `ℝ^m`; `N` is an `(𝓕_t)`-Poisson random measure with intensity
`dt ⊗ ν`; `z` is jointly measurable in `(t, ω, ω') ∈ [−τ, 0] × Ω × Ω'`, has càdlàg paths on
`[−τ, 0]`, is `𝓕_0`-measurable at each time (which makes it independent of `W` and `N`), and lies in
`L²(Ω, ℙ; Càdlàg([−τ, 0]; ℝ^d))` (supremum norm) for every `ω'`. -/
def IsNoiseA [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace Ω'] (τ : ℝ)
    (ν : Measure U) (Nz : NoiseA d m U Ω Ω') : Prop :=
  IsProbabilityMeasure Nz.prob ∧ IsFBrownianVec Nz.𝓕 Nz.prob Nz.W ∧
  JacodTodorov10.LLN.IsFPoisson Nz.𝓕 Nz.prob ν Nz.N ∧
  Measurable (fun p : Set.Icc (-τ) 0 × Ω × Ω' => Nz.z p.2.2 p.1 p.2.1) ∧
  (∀ ω' ω, IsCadlagOn (fun u => Nz.z ω' u ω) (-τ) 0) ∧
  (∀ ω', ∀ u ∈ Set.Icc (-τ) 0, Measurable[Nz.𝓕 0] (Nz.z ω' u)) ∧
  ∀ ω', ∫⁻ ω, ⨆ u ∈ Set.Icc (-τ) 0, ‖Nz.z ω' u ω‖ₑ ^ 2 ∂Nz.prob < ⊤

/-- `X` **solves an equation of type (20)** on `[−τ, ∞)` at disorder `ω'`, the coefficients being
fed at time `s` with the segment `sg (path of X) s`:
1. `X_t = z^{ω'}_t` for `t ∈ [−τ, 0]`;
2. every path is càdlàg on `[−τ, T]` for every `T`;
3. `X_t` is `𝓕_t`-measurable for `t ≥ 0`;
4. there are processes `Ig, Ih` that are the stochastic integrals `∫ g dW` (coordinate `i` is
   `∑ⱼ ∫ gᵢⱼ dWʲ`, published `HasBrownianItoIntegral`) and `∫∫ h dÑ` (coordinatewise, published
   `HasCompInt`); the drift integrand is locally integrable; and for every `t ≥ 0`, almost surely,
   `X_t = z^{ω'}_0 + ∫_0^t f ds + ∫_0^t g dW + ∫_0^t ∫_U h dÑ`, coordinatewise. -/
def SolvesA [MeasurableSpace U] [MeasurableSpace Ω] (A : CoeffsA d m Ω U Ω')
    (ν : Measure U) (Nz : NoiseA d m U Ω Ω') (τ : ℝ)
    (sg : (ℝ → SDEState d) → ℝ≥0 → ℝ → SDEState d) (ω' : Ω') (X : ℝ → Ω → SDEState d) :
    Prop :=
  (∀ t ∈ Set.Icc (-τ) 0, ∀ ω, X t ω = Nz.z ω' t ω) ∧
  (∀ (T : ℝ) (ω : Ω), IsCadlagOn (fun t => X t ω) (-τ) T) ∧
  (∀ t : ℝ≥0, Measurable[Nz.𝓕 t] (X t)) ∧
  ∃ (Ig : Fin d → Fin m → ℝ≥0 → Ω → ℝ) (Ih : Fin d → ℝ≥0 → Ω → ℝ),
    (∀ i j, HasBrownianItoIntegral Nz.prob (fun t => Nz.𝓕 t) (fun t ω => Nz.W t ω j)
      (fun t ω => A.g t ω (sg (fun v => X v ω) t) ω' i j) (Ig i j)) ∧
    (∀ i, JacodTodorov10.LLN.HasCompInt Nz.prob ν Nz.N
      (fun ω t ξ => A.h t ω (sg (fun v => X v ω) t) ω' ξ i) (Ih i)) ∧
    (∀ (ω : Ω) (t : ℝ≥0), IntervalIntegrable
      (fun s : ℝ => A.f s.toNNReal ω (sg (fun v => X v ω) s.toNNReal) ω') volume 0 (t : ℝ)) ∧
    ∀ t : ℝ≥0, ∀ᵐ ω ∂Nz.prob, ∀ i,
      X t ω i = Nz.z ω' 0 ω i
        + (∫ s in (0 : ℝ)..(t : ℝ), A.f s.toNNReal ω (sg (fun v => X v ω) s.toNNReal) ω') i
        + ∑ j, Ig i j t ω + Ih i t ω

/-- A **strong solution of (20)** (p. 22): `SolvesA` with the segment `X_{(s−τ)⁻:s⁻}`
(`u ↦ X_{(s+u)⁻}`). -/
def IsStrongSol20 [MeasurableSpace U] [MeasurableSpace Ω] (A : CoeffsA d m Ω U Ω')
    (ν : Measure U) (Nz : NoiseA d m U Ω Ω') (τ : ℝ) (ω' : Ω') (X : ℝ → Ω → SDEState d) :
    Prop :=
  SolvesA A ν Nz τ segMap ω' X

/-- The **Euler approximation (21)** (pp. 22–23) with step `τ/n` (`n = ns`): `X^n_t = z^{ω'}_t` on
`[−τ, 0]` and, on each `]kτ/n, (k+1)τ/n]`, `X^n` evolves with all coefficients evaluated at the
sampled segment `X^n_{κ(n,(s−τ):s)}` (`u ↦ X^n_{κ(n, s+u)}`); summed over the steps this is the
integral form of `SolvesA` with `sampledSeg τ ns`. -/
def IsEuler21 [MeasurableSpace U] [MeasurableSpace Ω] (A : CoeffsA d m Ω U Ω')
    (ν : Measure U) (Nz : NoiseA d m U Ω Ω') (τ : ℝ) (ω' : Ω') (ns : ℕ)
    (X : ℝ → Ω → SDEState d) : Prop :=
  SolvesA A ν Nz τ (sampledSeg τ ns) ω' X

end NeuroMV.WellPosed


