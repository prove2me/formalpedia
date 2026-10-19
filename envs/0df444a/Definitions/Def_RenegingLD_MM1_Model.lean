-- Prove2me | Definitions.Def_RenegingLD_MM1_Model
-- name    : RenegingLD_MM1_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:35.115745+00:00
-- url     : https://prove2.me/theorems/406237f6-2f9d-44e6-a312-9c3a5e1afb49
-- title:
--   §2.1–§2.2, pp. 6–7 — the Skorohod map (2.1), the controls U(ξ, ζ) (2.4), ℓ (2.5), the rate function I_T (2.6), the values (2.8) and C(γ) (2.9)–(2.10)
-- statement:
--   This file sets up the large-deviation rate function of the fluid-scaled $M/M/1+M$ queue (single server, Poisson arrivals at rate $\lambda$, exponential service at rate $\mu$, each waiting customer reneging at rate $\theta$) and the three variational quantities whose long-time behaviour is the subject of the mission. Throughout, $\lambda,\mu,\theta>0$, $x_0\ge 0$ is the initial (scaled) queue length and $T>0$ is the horizon.
--
--   1. **Skorohod map (2.1).** For $\psi:[0,T]\to\mathbb R$,
--   $$\Gamma(\psi)(t)=\psi(t)-\inf_{0\le s\le t}\,[\psi(s)\wedge 0],\qquad t\in[0,T].$$
--   2. **Local cost (2.5).** $\ell(x)=x\log x-x+1$ for $x\ge 0$, with $\ell(0)=1$.
--   3. **Paths.** A path is a pair $(\xi,\zeta)$ of continuous functions $[0,T]\to\mathbb R_+$: $\xi$ is the queue length and $\zeta$ the cumulative reneging.
--   4. **Controls (2.4).** $\mathcal U(\xi,\zeta)$ is the set of triples $\varphi=(\varphi_1,\varphi_2,\varphi_3)$ of measurable maps $[0,T]\to\mathbb R_+$ such that, for all $t\in[0,T]$,
--   $$\xi(t)=\Gamma\Big(x_0+\lambda\int_0^{\cdot}\varphi_1(s)\,ds-\mu\int_0^{\cdot}\varphi_2(s)\,ds-\theta\int_0^{\cdot}\varphi_3(s)\xi(s)\,ds\Big)(t),\qquad \zeta(t)=\theta\int_0^t\varphi_3(s)\xi(s)\,ds .$$
--   5. **Rate function (2.6).**
--   $$I_T(\xi,\zeta)=\inf_{\varphi\in\mathcal U(\xi,\zeta)}\Big\{\lambda\int_0^T\ell(\varphi_1(s))\,ds+\mu\int_0^T\ell(\varphi_2(s))\,ds+\theta\int_0^T\xi(s)\ell(\varphi_3(s))\,ds\Big\},$$
--   with $I_T(\xi,\zeta)=\infty$ if $\mathcal U(\xi,\zeta)=\emptyset$ or $(\xi,\zeta)$ is not a continuous nonnegative path.
--   6. **Variational values (2.8).** $I^*_{\gamma,T}=\inf\{I_T(\xi,\zeta):\zeta(T)=\gamma T\}$, $I_{\gamma,T}=\inf\{I_T(\xi,\zeta):\zeta(T)\ge\gamma T\}$ and $\tilde I_{\gamma,T}=\inf\{I_T(\xi,\zeta):\zeta(T)\le\gamma T\}$.
--   7. **The decay rate (2.9)–(2.10).**
--   $$z_\gamma=\frac{\sqrt{\gamma^2+4\lambda\mu}-\gamma}{2\mu},\qquad C(\gamma)=\lambda\big(1-z_\gamma^{-1}\big)+\mu\,(1-z_\gamma)-\gamma\log z_\gamma .$$
--
--   $I_T$ is the rate function of the sample-path large deviation principle for the pair (queue length, cumulative reneging) proved in the paper (Theorem 2.1), and $I^*_{\gamma,T}$ is the rate for observing $\gamma T$ reneged customers over $[0,T]$. Note that $\theta$ enters $I_T$, while $z_\gamma$ and $C(\gamma)$ involve only $\lambda$, $\mu$ and $\gamma$.
--
--   **Formalization Note.** `lam`, `mu` stand for $\lambda$, $\mu$ ($\lambda$ is a Lean keyword). Paths and controls are functions $\mathbb R\to\mathbb R$ of which only $[0,T]$ is used. $\mathcal U$ additionally requires $\varphi_1$, $\varphi_2$ and $\varphi_3\xi$ to be integrable on $[0,T]$; without this the Lean (Bochner) integrals of a non-integrable control would be $0$ and fake membership, and the page's integrals presuppose it. Costs and $I_T$ take values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative integrands); an infimum over an empty set is $\infty$, as on the page. The real infimum in $\Gamma$ is the paper's infimum whenever $\psi$ is bounded below on $[0,t]$, which holds for the continuous $\psi$ of (2.4). The infima in (2.8) range over all pairs of functions; non-paths have $I_T=\infty$, so this agrees with the paper's infimum over $\mathcal D([0,T]:\mathbb R^2_+)$.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, pp. 5–7, (2.1), (2.4)–(2.6), (2.8)–(2.10)

import Mathlib

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The one-dimensional Skorohod map (2.1):
`Γ(ψ)(t) = ψ(t) − inf_{0 ≤ s ≤ t} [ψ(s) ∧ 0]`.
The real infimum is the paper's infimum whenever `ψ` is bounded below on `[0, t]`
(in particular whenever `ψ` is continuous there). -/
noncomputable def skorokhod (ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ψ t - ⨅ s : Set.Icc (0 : ℝ) t, min (ψ s) 0

/-- The local rate (2.5): `ℓ(x) = x log x − x + 1` (with `ℓ(0) = 1`). -/
noncomputable def ell (x : ℝ) : ℝ := x * Real.log x - x + 1

/-- `(ξ, ζ) ∈ C([0, T] : ℝ²₊)`: both coordinates are continuous and nonnegative on `[0, T]`. -/
def IsPath (T : ℝ) (ξ ζ : ℝ → ℝ) : Prop :=
  ContinuousOn ξ (Set.Icc 0 T) ∧ ContinuousOn ζ (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T, 0 ≤ ξ t ∧ 0 ≤ ζ t

/-- The control set `U(ξ, ζ)` of (2.4): measurable controls `ϕ = (ϕ₁, ϕ₂, ϕ₃)`, nonnegative on
`[0, T]`, with `ϕ₁`, `ϕ₂` and `ϕ₃ ξ` integrable on `[0, T]`, such that for all `t ∈ [0, T]`
`ξ(t) = Γ(x₀ + λ∫₀^· ϕ₁ − µ∫₀^· ϕ₂ − θ∫₀^· ϕ₃ ξ)(t)` and `ζ(t) = θ∫₀^t ϕ₃ ξ`. -/
def U (lam mu θ x0 T : ℝ) (ξ ζ : ℝ → ℝ) : Set ((ℝ → ℝ) × (ℝ → ℝ) × (ℝ → ℝ)) :=
  {ϕ | Measurable ϕ.1 ∧ Measurable ϕ.2.1 ∧ Measurable ϕ.2.2 ∧
    (∀ s ∈ Set.Icc 0 T, 0 ≤ ϕ.1 s ∧ 0 ≤ ϕ.2.1 s ∧ 0 ≤ ϕ.2.2 s) ∧
    IntervalIntegrable ϕ.1 volume 0 T ∧ IntervalIntegrable ϕ.2.1 volume 0 T ∧
    IntervalIntegrable (fun s => ϕ.2.2 s * ξ s) volume 0 T ∧
    ∀ t ∈ Set.Icc 0 T,
      ξ t = skorokhod (fun r => x0 + lam * (∫ s in (0)..r, ϕ.1 s)
              - mu * (∫ s in (0)..r, ϕ.2.1 s) - θ * (∫ s in (0)..r, ϕ.2.2 s * ξ s)) t ∧
      ζ t = θ * (∫ s in (0)..t, ϕ.2.2 s * ξ s)}

/-- The cost inside (2.6):
`λ∫₀ᵀ ℓ(ϕ₁) + µ∫₀ᵀ ℓ(ϕ₂) + θ∫₀ᵀ ξ ℓ(ϕ₃)`, as a lower Lebesgue integral in `[0, ∞]`. -/
noncomputable def cost (lam mu θ T : ℝ) (ξ : ℝ → ℝ) (ϕ : (ℝ → ℝ) × (ℝ → ℝ) × (ℝ → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal lam * ∫⁻ s in Set.Icc 0 T, ENNReal.ofReal (ell (ϕ.1 s))
    + ENNReal.ofReal mu * ∫⁻ s in Set.Icc 0 T, ENNReal.ofReal (ell (ϕ.2.1 s))
    + ENNReal.ofReal θ * ∫⁻ s in Set.Icc 0 T, ENNReal.ofReal (ξ s * ell (ϕ.2.2 s))

/-- The rate function `I_T(ξ, ζ)` of (2.6): the infimum of the cost over `U(ξ, ζ)` for a
continuous nonnegative path, and `∞` if `U(ξ, ζ)` is empty or `(ξ, ζ)` is not such a path. -/
noncomputable def IT (lam mu θ x0 T : ℝ) (ξ ζ : ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ (_ : IsPath T ξ ζ), ⨅ ϕ ∈ U lam mu θ x0 T ξ ζ, cost lam mu θ T ξ ϕ

/-- `I*_{γ,T} = inf{I_T(ξ, ζ) : ζ(T) = γT}` (2.8). -/
noncomputable def Istar (lam mu θ x0 γ T : ℝ) : ℝ≥0∞ :=
  ⨅ ξ : ℝ → ℝ, ⨅ ζ : ℝ → ℝ, ⨅ (_ : ζ T = γ * T), IT lam mu θ x0 T ξ ζ

/-- `I_{γ,T} = inf{I_T(ξ, ζ) : ζ(T) ≥ γT}` (2.8). -/
noncomputable def Iup (lam mu θ x0 γ T : ℝ) : ℝ≥0∞ :=
  ⨅ ξ : ℝ → ℝ, ⨅ ζ : ℝ → ℝ, ⨅ (_ : γ * T ≤ ζ T), IT lam mu θ x0 T ξ ζ

/-- `Ĩ_{γ,T} = inf{I_T(ξ, ζ) : ζ(T) ≤ γT}` (2.8). -/
noncomputable def Idown (lam mu θ x0 γ T : ℝ) : ℝ≥0∞ :=
  ⨅ ξ : ℝ → ℝ, ⨅ ζ : ℝ → ℝ, ⨅ (_ : ζ T ≤ γ * T), IT lam mu θ x0 T ξ ζ

/-- `z_γ = (√(γ² + 4λµ) − γ)/(2µ)` (2.10). -/
noncomputable def z (lam mu γ : ℝ) : ℝ := (Real.sqrt (γ ^ 2 + 4 * lam * mu) - γ) / (2 * mu)

/-- `C(γ) = λ(1 − z_γ⁻¹) + µ(1 − z_γ) − γ log z_γ` (2.9). -/
noncomputable def C (lam mu γ : ℝ) : ℝ :=
  lam * (1 - (z lam mu γ)⁻¹) + mu * (1 - z lam mu γ) - γ * Real.log (z lam mu γ)

end RenegingLD.MM1


