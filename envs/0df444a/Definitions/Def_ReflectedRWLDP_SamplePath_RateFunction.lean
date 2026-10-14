-- Prove2me | Definitions.Def_ReflectedRWLDP_SamplePath_RateFunction
-- name    : ReflectedRWLDP_SamplePath_RateFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:14.6139+00:00
-- url     : https://prove2.me/theorems/fd1c417a-e698-4a6f-9272-0950a2c58987
-- title:
--   pp. 6, 9, 12, 14, 18–19 — $\Lambda^*$, $\Psi$, $\mathcal T$, the cost $I_y$, the problems $\mathcal B^*_y$, $\mathcal B^*_\pi$, $\mathcal V^{T*}_y$ and the rate functions $I_Y$, $I_S$, $I_{\mathbf t}$
-- statement:
--   Let $U$ and $p>0$ be as in the model, with $\theta_\pm$ from Assumption 2.1, and let $\mu=\mathbf E(U)$ and $\alpha=1/(1+p)$.
--
--   **Ingredients (p. 6).** $\Lambda^*(y)=\sup_{\theta\in\mathbb R}\{\theta y-\log\mathbf E(e^{\theta U})\}$. The reflection map is $\Psi(\xi)(t)=\xi(t)-\inf_{s\in[0,t]}\{\xi(s)\wedge0\}$ and the exit time is $\mathcal T(\xi)=\inf\{t>0:\Psi(\xi)(t)=0\}$. A path $\xi$ of bounded variation decomposes as $\xi=\xi^{(a)}+\xi^{(u)}+\xi^{(d)}$: an absolutely continuous part, a non-decreasing singular part and a non-increasing singular part, with $\xi^{(u)}(0)=\xi^{(d)}(0)=0$.
--
--   **Cost and the problem $(\mathcal B_y)$.** For $\xi$ in $\mathbb{BV}[0,\infty)$ (càdlàg, of bounded variation on compacts) with $\xi(0)=y$,
--   $$I_y(\xi)=\int_0^{\mathcal T(\xi)}\Lambda^*(\dot\xi^{(a)}(s))\,ds+\theta_+\xi^{(u)}(\mathcal T(\xi))+\theta_-\xi^{(d)}(\mathcal T(\xi)),$$
--   and $I_y(\xi)=\infty$ otherwise. With $B_y=\{\xi\in\mathbb{BV}[0,\infty):\xi(0)=y,\ \int_0^{\mathcal T(\xi)}\Psi(\xi)(s)^p\,ds\ge1\}$,
--   $$\mathcal B^*_y=\inf_{\xi\in B_y}I_y(\xi),\qquad \mathcal B^*_\pi=\inf_{y\in[0,\infty),\ \xi\in B_y}\{\beta y+I_y(\xi)\},\qquad \beta=\sup\{\theta\ge0:\mathbf E(e^{\theta U})\le1\}.$$
--   $B^{\mathbb{AC}}_y=B_y\cap\mathbb{AC}[0,\infty)$ and $\bar y=(|\mu|(p+1))^\alpha$ (p. 18).
--
--   **Finite horizon (p. 19).** For $T>0$, $\Phi_T(\xi)=\int_0^T\Psi(\xi)(s)^p\,ds$ on $\mathbb D[0,T]$, $V^T_y=\{\xi\in\mathbb D[0,T]:\xi(0)=y,\ \Phi_T(\xi)\ge1\}$, $I^{\mathbb{BV}[0,T]}_y$ is $I_y$ with $\mathcal T(\xi)$ replaced by $T$ on $\mathbb{BV}[0,T]$, and $\mathcal V^{T*}_y=\inf_{\xi\in V^T_y}I^{\mathbb{BV}[0,T]}_y(\xi)$.
--
--   **Rate functions.** On $\mathbb D[0,1]$:
--   $$I_Y(\zeta)=I_Z(\zeta)=\begin{cases}\mathcal B^*_0\sum_{t:\zeta(t)\ne\zeta(t-)}(\zeta(t)-\zeta(t-))^\alpha & \zeta\in\mathbb D^{(\lambda)}[0,1],\\ \infty&\text{otherwise,}\end{cases}$$
--   as in (2.1) and (3.13). $I_S(\zeta)=\mathcal B^*_0(\zeta(1)-\zeta(1-))^\alpha$ on $\mathbb D[0,1]^{\leqslant1}=\{x\mathbb 1_{\{1\}}:x\ge0\}$ and $\infty$ elsewhere, as in (3.1). On $\mathbb R^k_+$, $I_{\mathbf t}(x)=\mathcal B^*_0\sum_{i=1}^k(x_i-\lambda\Delta t_i)^\alpha$ if $x_i\ge\lambda\Delta t_i$ for all $i$ and $\infty$ otherwise, as in (3.7).
--
--   These are the constants and rate functions of the paper's main results.
--
--   **Formalization Note** All costs, infima and rate functions take values in $[0,\infty]$; an empty infimum is $\infty$, and $\theta_+\cdot0=0$ when $\theta_+=\infty$ (likewise for $|\theta_-|$). $\Lambda^*$ is `BellWilliams2001.ThresholdPolicy.legendre` of `logMGF` of $U$, read in $[0,\infty]$. $\mathcal T(\xi)\in[0,\infty]$, and $\xi^{(u)}(\infty)$ is the monotone limit. The integrals $\int_0^{\mathcal T}$ are lower Lebesgue integrals over $(0,\mathcal T(\xi))$. The decomposition is not computed: the cost of $\xi$ is the infimum over all representations $\xi(t)=\xi(0)+\int_0^t g+\sigma_u(t)-\sigma_d(t)$, with $g$ locally integrable and $\sigma_u,\sigma_d$ non-decreasing, right-continuous, vanishing on $(-\infty,0]$ and with Lebesgue–Stieltjes measures singular to Lebesgue measure. Any such representation has $g=\dot\xi^{(a)}$ a.e., $\sigma_u\ge\xi^{(u)}$ and $\sigma_d\ge-\xi^{(d)}$ as measures, so the infimum is attained at the Hahn–Jordan decomposition and equals the paper's cost. The downward singular cost is the nonnegative $|\theta_-|\,|\xi^{(d)}|$, which is $\theta_-\xi^{(d)}$ (pp. 6, 19). $\mathbb{AC}[0,\infty)$ means $\xi(t)=\xi(0)+\int_0^tg$ with $g$ integrable on compacts. $\beta\in[0,\infty]$. $\Phi_T$ is the real value of a finite lower integral. $\mathbb D[0,T]$ paths are bounded, so the infimum in $\Psi$ is over a bounded set.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 5 (BV, Lebesgue/Hahn decomposition), p. 6 (Ψ, 𝒯, B_y, Λ*, I_y, (B_y), (B_π), β, (2.1)), p. 9 ((3.1)), p. 12 ((3.7)), p. 14 ((3.13)), p. 18 (B^{𝔸ℂ}_y, ȳ), p. 19 (Φ_T, (𝒱^T_y), V^T_y, I^{𝔹𝕍[0,T]}_y)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_ReflectedRWLDP_SamplePath_Model

namespace ReflectedRWLDP.SamplePath

open MeasureTheory Set
open scoped ENNReal

/-!
Bazhba, Blanchet, Rhee & Zwart, arXiv:2003.14381v3, §2.1–2.2 (pp. 5–6), (2.1), (3.1), (3.7), (3.13),
§4.1 (pp. 18–19): the rate function ingredients. The Legendre transform `Λ*`, the reflection map `Ψ`,
the exit time `𝒯`, the Lebesgue decomposition of a path of bounded variation, the cost `I_y`, the
variational problems `B*_y` and `B*_π`, the finite-horizon problem `𝒱^{T*}_y`, and the rate functions
`I_Y = I_Z`, `I_S`, `I_𝐭` of the LDPs.

Throughout, `U 0` is the paper's generic increment `U` (see `Def_ReflectedRWLDP_SamplePath_Model`).
-/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `Λ*(y) = sup_{θ ∈ ℝ} {θy − log E(e^{θV})}` (p. 6), as an element of `[0, ∞]` (it is `≥ 0` for a
probability measure, by `θ = 0`). -/
noncomputable def LambdaStar (P : Measure Ω) (V : Ω → ℝ) (y : ℝ) : ℝ≥0∞ :=
  (BellWilliams2001.ThresholdPolicy.legendre (BellWilliams2001.ThresholdPolicy.logMGF P V) y).toENNReal

/-- The reflection map `Ψ(ξ)(t) = ξ(t) − inf_{s ∈ [0,t]} {ξ(s) ∧ 0}`, `t ≥ 0` (p. 6). (The infimum is
over the bounded-below values of a càdlàg path on the compact interval `[0,t]`.) -/
noncomputable def reflect (ξ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ξ t - ⨅ s : Icc (0 : ℝ) t, min (ξ s) 0

/-- The exit time `𝒯(ξ) = inf {t > 0 : Ψ(ξ)(t) = 0}` (p. 6), in `[0, ∞]` (`= ∞` when `Ψ(ξ)` does not
return to `0`). -/
noncomputable def exitTime (ξ : ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ) (_ : 0 < t) (_ : reflect ξ t = 0), ENNReal.ofReal t

/-- The open time window `(0, τ)` for `τ ∈ [0, ∞]` (`= (0, ∞)` when `τ = ∞`). -/
def window (τ : ℝ≥0∞) : Set ℝ := {s | 0 < s ∧ ENNReal.ofReal s < τ}

/-- The value `σ(τ)` of a nondecreasing path at `τ ∈ [0, ∞]`, computed as `sup_{0 ≤ t ≤ τ} σ(t)`
(the monotone limit `σ(∞) = lim_{t→∞} σ(t)` when `τ = ∞`). -/
noncomputable def upTo (σ : ℝ → ℝ) (τ : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 ≤ t) (_ : ENNReal.ofReal t ≤ τ), ENNReal.ofReal (σ t)

/-- A Lebesgue decomposition of `ξ` on the time set `H` (`H = [0,∞)` or `H = [0,T]`, p. 5):
`ξ(t) = ξ(0) + ∫_0^t g(s) ds + σ_u(t) − σ_d(t)` for `t ∈ H`, where `g` is integrable on every `[0,t]`,
`t ∈ H`, and `σ_u`, `σ_d` are nondecreasing right-continuous functions vanishing on `(−∞, 0]` whose
Lebesgue–Stieltjes measures are singular with respect to Lebesgue measure. (Then `ξ^{(a)} =
ξ(0) + ∫_0^· g`, `ξ̇^{(a)} = g` a.e., and `ξ^{(s)} = σ_u − σ_d`; the Hahn–Jordan choice
`σ_u = ξ^{(u)}`, `σ_d = −ξ^{(d)}` is the minimal one.) -/
def IsLebRep (H : Set ℝ) (ξ g : ℝ → ℝ) (σu σd : StieltjesFunction ℝ) : Prop :=
  (∀ t ∈ H, IntegrableOn g (Icc 0 t)) ∧
  (∀ t : ℝ, t ≤ 0 → σu t = 0) ∧ (∀ t : ℝ, t ≤ 0 → σd t = 0) ∧
  σu.measure.MutuallySingular volume ∧ σd.measure.MutuallySingular volume ∧
  ∀ t ∈ H, ξ t = ξ 0 + (∫ s in (0 : ℝ)..t, g s) + σu t - σd t

/-- The cost on the horizon `τ ∈ [0, ∞]` of a decomposition `(g, σ_u, σ_d)`:
`∫_0^τ Λ*(g(s)) ds + θ₊ σ_u(τ) + |θ₋| σ_d(τ)`, i.e. `… + θ₊ ξ^{(u)}(τ) + θ₋ ξ^{(d)}(τ)` (p. 6) for the
Hahn–Jordan decomposition, with `θ₊ · 0 = 0` when `θ₊ = ∞` and `|θ₋| · 0 = 0` when `θ₋ = −∞`. -/
noncomputable def cost (P : Measure Ω) (U : ℕ → Ω → ℝ) (τ : ℝ≥0∞) (g : ℝ → ℝ)
    (σu σd : StieltjesFunction ℝ) : ℝ≥0∞ :=
  (∫⁻ s in window τ, LambdaStar P (U 0) (g s)) +
    (thetaPlus P (U 0)).toENNReal * upTo σu τ +
    (-thetaMinus P (U 0)).toENNReal * upTo σd τ

/-- `ξ ∈ 𝔹𝕍[0,∞)` (p. 5): `ξ` is càdlàg on `[0,∞)` and of bounded variation on every `[0,t]`. -/
def IsBVFrom0 (ξ : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt ξ (Ici t) t) ∧
  (∀ t : ℝ, 0 < t → ∃ l : ℝ, Filter.Tendsto ξ (nhdsWithin t (Iio t)) (nhds l)) ∧
  ∀ t : ℝ, 0 ≤ t → BoundedVariationOn ξ (Icc 0 t)

open Classical in
/-- The rate `I_y(ξ)` (p. 6):
`∫_0^{𝒯(ξ)} Λ*(ξ̇^{(a)}(s)) ds + θ₊ ξ^{(u)}(𝒯(ξ)) + θ₋ ξ^{(d)}(𝒯(ξ))` if `ξ(0) = y` and
`ξ ∈ 𝔹𝕍[0,∞)`, and `∞` otherwise. The cost is the infimum over all Lebesgue decompositions of `ξ` on
`[0,∞)`, which is attained at (and equal to the cost of) the Hahn–Jordan decomposition. -/
noncomputable def rateI (P : Measure Ω) (U : ℕ → Ω → ℝ) (y : ℝ) (ξ : ℝ → ℝ) : ℝ≥0∞ :=
  if ξ 0 = y ∧ IsBVFrom0 ξ then
    ⨅ (g : ℝ → ℝ) (σu : StieltjesFunction ℝ) (σd : StieltjesFunction ℝ)
      (_ : IsLebRep (Ici 0) ξ g σu σd), cost P U (exitTime ξ) g σu σd
  else ⊤

/-- `∫_0^{𝒯(ξ)} Ψ(ξ)(s)^p ds`, in `[0, ∞]`. -/
noncomputable def areaToExit (p : ℝ) (ξ : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ s in window (exitTime ξ), ENNReal.ofReal (reflect ξ s ^ p)

/-- `B_y = {ξ ∈ 𝔹𝕍[0,∞) : ξ(0) = y, ∫_0^{𝒯(ξ)} Ψ(ξ)(s)^p ds ≥ 1}` (p. 6). -/
def Bset (p y : ℝ) : Set (ℝ → ℝ) :=
  {ξ | IsBVFrom0 ξ ∧ ξ 0 = y ∧ 1 ≤ areaToExit p ξ}

/-- `B*_y = inf_{ξ ∈ B_y} I_y(ξ)` (problem `(B_y)`, p. 6), in `[0, ∞]`. -/
noncomputable def Bstar (P : Measure Ω) (U : ℕ → Ω → ℝ) (p y : ℝ) : ℝ≥0∞ :=
  ⨅ ξ ∈ Bset p y, rateI P U y ξ

/-- `ξ ∈ 𝔸ℂ[0,∞)`: `ξ` is absolutely continuous on every compact interval of `[0,∞)`, i.e.
`ξ(t) = ξ(0) + ∫_0^t g(s) ds` for `t ≥ 0`, with `g` integrable on every `[0,t]`. -/
def IsACFrom0 (ξ : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, (∀ t : ℝ, 0 ≤ t → IntegrableOn g (Icc 0 t)) ∧
    ∀ t : ℝ, 0 ≤ t → ξ t = ξ 0 + ∫ s in (0 : ℝ)..t, g s

/-- `B^{𝔸ℂ}_y = B_y ∩ 𝔸ℂ[0,∞)` (p. 18). -/
def BsetAC (p y : ℝ) : Set (ℝ → ℝ) := Bset p y ∩ {ξ | IsACFrom0 ξ}

/-- `β = sup {θ ≥ 0 : E(e^{θU}) ≤ 1}` (p. 6), in `[0, ∞]`. -/
noncomputable def beta (P : Measure Ω) (V : Ω → ℝ) : ℝ≥0∞ :=
  ⨆ (θ : ℝ) (_ : 0 ≤ θ) (_ : expMoment P V θ ≤ 1), ENNReal.ofReal θ

/-- `B*_π = inf_{y ∈ [0,∞), ξ ∈ B_y} {βy + I_y(ξ)}` (problem `(B_π)`, p. 6). -/
noncomputable def BstarPi (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ) : ℝ≥0∞ :=
  ⨅ (y : ℝ) (_ : 0 ≤ y) (ξ : ℝ → ℝ) (_ : ξ ∈ Bset p y),
    beta P (U 0) * ENNReal.ofReal y + rateI P U y ξ

/-- `ȳ = (|µ|(p + 1))^α` with `µ = E(U)` (Lemma 4.1, p. 18). -/
noncomputable def ybar (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ) : ℝ :=
  (|∫ ω, U 0 ω ∂P| * (p + 1)) ^ alpha p

/-- `Φ_T(ξ) = ∫_0^T (Ψ(ξ)(s))^p ds` on `𝔻[0,T]` (p. 19), a real number (finite: a càdlàg path is
bounded on `[0,T]`). -/
noncomputable def PhiT (p : ℝ) {T : ℝ} (ξ : DPath T) : ℝ :=
  (∫⁻ s in Ioo 0 T, ENNReal.ofReal (reflect ξ s ^ p)).toReal

open Classical in
/-- `I^{𝔹𝕍[0,T]}_y(ξ)` (p. 19): `∫_0^T Λ*(ξ̇^{(a)}(s)) ds + θ₊ ξ^{(u)}(T) + θ₋ ξ^{(d)}(T)` if `ξ(0) = y`
and `ξ ∈ 𝔹𝕍[0,T]`, and `∞` otherwise (as for `rateI`, the infimum over Lebesgue decompositions on
`[0,T]`). -/
noncomputable def rateIT (P : Measure Ω) (U : ℕ → Ω → ℝ) (T y : ℝ) (ξ : DPath T) : ℝ≥0∞ :=
  if ξ 0 = y ∧ BoundedVariationOn ξ (Icc 0 T) then
    ⨅ (g : ℝ → ℝ) (σu : StieltjesFunction ℝ) (σd : StieltjesFunction ℝ)
      (_ : IsLebRep (Icc 0 T) ξ g σu σd), cost P U (ENNReal.ofReal T) g σu σd
  else ⊤

/-- `V^T_y = {ξ ∈ 𝔻[0,T] : ξ(0) = y, Φ_T(ξ) ≥ 1}` (p. 19). -/
def VTset (p T y : ℝ) : Set (DPath T) := {ξ | ξ 0 = y ∧ 1 ≤ PhiT p ξ}

/-- `𝒱^{T*}_y = inf_{ξ ∈ V^T_y} I^{𝔹𝕍[0,T]}_y(ξ)` (problem `(𝒱^T_y)`, p. 19). -/
noncomputable def VTstar (P : Measure Ω) (U : ℕ → Ω → ℝ) (p T y : ℝ) : ℝ≥0∞ :=
  ⨅ ξ ∈ VTset p T y, rateIT P U T y ξ

open Classical in
/-- The rate function `I_Y` of Theorem 2.1, (2.1) (p. 6), with `T = 1`; it is also the rate function
`I_Z` of (3.13) (p. 14):
`I_Y(ζ) = B*₀ ∑_{t : ζ(t) ≠ ζ(t−)} (ζ(t) − ζ(t−))^α` if `ζ ∈ 𝔻^{(λ)}[0,1]`, and `∞` otherwise
(`ζ(0−) = 0`, so a jump at `0` counts). -/
noncomputable def rateY (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ) (ζ : DPath 1) : ℝ≥0∞ :=
  if ζ ∈ DLambda 1 (lam P U p) then Bstar P U p 0 * jumpPowSum ζ (alpha p) else ⊤

/-- `𝔻[0,1]^{⩽1} = {ξ ∈ 𝔻[0,1] : ξ = x𝟙_{{1}} for some x ≥ 0}` (p. 9). -/
def DOne : Set (DPath 1) :=
  {ξ | ∃ x : ℝ, 0 ≤ x ∧ ∀ t ∈ Icc (0 : ℝ) 1, ξ t = x * Set.indicator {1} (fun _ => (1 : ℝ)) t}

open Classical in
/-- The rate function `I_S` of Lemma 3.1, (3.1) (p. 9): `I_S(ζ) = B*₀ (ζ(1) − ζ(1−))^α` if
`ζ ∈ 𝔻[0,1]^{⩽1}`, and `∞` otherwise. -/
noncomputable def rateS (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ) (ζ : DPath 1) : ℝ≥0∞ :=
  if ζ ∈ DOne then
    Bstar P U p 0 * ENNReal.ofReal ((ζ 1 - Function.leftLim ζ 1) ^ alpha p)
  else ⊤

open Classical in
/-- The rate function `I_𝐭` of Lemma 3.3, (3.7) (p. 12), on `ℝ^k_+`, for `t : Fin (k+1) → ℝ` with
`Δt_i = t_i − t_{i−1}`: `I_𝐭(x) = B*₀ ∑_{i=1}^k (x_i − λΔt_i)^α` if `x_i ≥ λΔt_i` for all `i`, and
`∞` otherwise. -/
noncomputable def rateBlock (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ) {k : ℕ}
    (t : Fin (k + 1) → ℝ) (x : NonnegVec k) : ℝ≥0∞ :=
  if ∀ i : Fin k, lam P U p * (t i.succ - t i.castSucc) ≤ x.1 i then
    Bstar P U p 0 *
      ∑ i : Fin k, ENNReal.ofReal ((x.1 i - lam P U p * (t i.succ - t i.castSucc)) ^ alpha p)
  else ⊤

end ReflectedRWLDP.SamplePath


