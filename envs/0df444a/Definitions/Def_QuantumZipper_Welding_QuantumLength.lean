-- Prove2me | Definitions.Def_QuantumZipper_Welding_QuantumLength
-- name    : QuantumZipper_Welding_QuantumLength
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:31.811503+00:00
-- url     : https://prove2.me/theorems/bac43fd1-b899-441a-afae-86b17836a9c5
-- title:
--   Quantum boundary length $\nu_h$ (1.2), quantum area $\mu_h$ (1.1), canonical description (1.8)
-- statement:
--   Let $\varphi(z,\varepsilon)=h_\varepsilon(z)$ be the arc averages of a field $h$ on $\mathbb H$, and $\gamma\in(0,2)$.
--
--   1. **Quantum boundary length (1.2).** On an open set $U\subseteq\mathbb R$, $\nu_h$ is the measure on $\mathbb R$, null outside $U$ and finite on compact subsets of $U$, such that for every continuous $f$ with compact support in $U$
--   $$\int f(x)\,\varepsilon_n^{\gamma^2/4}e^{\gamma h_{\varepsilon_n}(x)/2}\,dx\longrightarrow\int f\,d\nu_h,\qquad\varepsilon_n=2^{-n},$$
--   where $h_\varepsilon(x)$ is the mean of $h$ on the upper semicircle $\partial B_\varepsilon(x)\cap\mathbb H$; the approximating densities are locally integrable on $U$ for all large $n$.
--   2. **Quantum area (1.1).** On an open set $V\subseteq\mathbb C$, $\mu_h$ is defined in the same way from $\varepsilon_n^{\gamma^2/2}e^{\gamma h_{\varepsilon_n}(z)}\,dz$ with circle averages $h_\varepsilon(z)$.
--   3. **Regular field.** The arc averages $(z,\varepsilon)\mapsto h_\varepsilon(z)$ are continuous on $\{\operatorname{Im}z\ge0,\ \varepsilon>0\}$. This selects the version of the field from which $\mu_h$ and $\nu_h$ are built.
--   4. **Canonical description (p. 21).** A doubly marked surface $(\mathbb H,h)$ (marked at $0$ and $\infty$) is rescaled by $(\mathbb H,h)\mapsto(\mathbb H,h(a\cdot)+Q\log a)$ (1.8). This pushes $\mu_h$ forward under $z\mapsto z/a$, and $a$ is chosen with $\mu_h(B_a(0))=1$, i.e. $a=\inf\{r>0:\mu_h(B_r(0))\ge1\}$. The canonical description then has $\mu(B_1(0))=1$ and arc averages $h_{a\varepsilon}(az)+Q\log a$.
--
--   The limits are taken along powers of two, as on p. 7 ("The limit exists almost surely, at least if $\varepsilon$ is restricted to powers of two [DS11a]").
--
--   **Formalization Note** A measure null outside $U$ and finite on compacts of $U$ is determined by its integrals of compactly supported continuous functions, so $\nu_h$ is unique if it exists; its existence is [DS11a]. Since the densities are integrable, $\nu\equiv0$ qualifies only if the explicit approximations really converge to $0$. If $\mu(B_r(0))<1$ for every $r$, the canonical radius is the junk value $0$.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §1.2, p. 7, (1.1), (1.2); §1.6, p. 21, (1.8) and the canonical description; p. 41 (continuity of h_ε(z))

import Mathlib
import Definitions.Def_QuantumZipper_Welding_Setting

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace QuantumZipper.Welding

/-! # Quantum boundary length `ν_h` (1.2), quantum area `μ_h` (1.1), canonical description (p. 21)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797v2, §1.2, p. 7 and §1.6, p. 21. -/

/-- The dyadic radii `ε_n = 2⁻ⁿ` along which the limits (1.1), (1.2) are taken (p. 7: "The limit
exists almost surely, at least if `ε` is restricted to powers of two [DS11a]"). -/
noncomputable def dyadic (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

/-- The arc-average function of a field realization: `(z, ε) ↦ h_ε(z) = (h, σ_{z,ε})`. -/
noncomputable def arcAvg (ψ : Measure ℂ → ℝ) (z : ℂ) (ε : ℝ) : ℝ :=
  ψ (arcMeasure z ε)

/-- A field realization is **regular** if its arc averages `(z, ε) ↦ h_ε(z)` are continuous on
`{Im z ≥ 0, ε > 0}` (p. 41: "the map `h ↦ h_ε(z)` is an a.s. Hölder continuous function of `ε` and
`z` [DS11a]"). This selects the version of the field from which `μ_h` and `ν_h` are built. -/
def IsRegularArcField (ψ : Measure ℂ → ℝ) : Prop :=
  ContinuousOn (fun p : ℂ × ℝ => arcAvg ψ p.1 p.2) {p : ℂ × ℝ | 0 ≤ p.1.im ∧ 0 < p.2}

/-- **Quantum boundary length** (arXiv:1012.4797v2, (1.2), p. 7) on an open set `U ⊆ ℝ` of the
boundary: `ν = lim_{ε→0} ε^{γ²/4} e^{γ h_ε(x)/2} dx`, where `h_ε(x) = φ x ε` is the mean of `h` on
the upper semicircle `ℍ ∩ ∂B_ε(x)`. `ν` is a measure on `ℝ`, null outside `U`, finite on compact
subsets of `U`, and for every continuous `f` with compact support in `U`,
`∫ f(x) ε_n^{γ²/4} e^{γ h_{ε_n}(x)/2} dx → ∫ f dν` along `ε_n = 2⁻ⁿ`.

**Formalization Note** The limit is vague convergence on `U` ("weak convergence on compact
subsets"), along powers of two as on p. 7. The approximating densities are required to be locally
integrable on `U` for all large `n` (for a field on a subdomain, coarse semicircles may leave the
domain, where the field is not defined), so no Bochner integral in the limit is a junk `0`; with this, `ν ≡ 0` satisfies the predicate
only if the explicit approximations really converge to `0`. A measure null outside `U` and finite on
compacts of `U` is determined by its integrals of `C_c(U)` functions, so `ν` is unique if it exists.
Existence (for the fields of this paper, almost surely) is [DS11a]. -/
structure IsBoundaryLengthOn (γ : ℝ) (U : Set ℝ) (φ : ℝ → ℝ → ℝ) (ν : Measure ℝ) : Prop where
  null_outside : ν Uᶜ = 0
  finite_on_compact : ∀ K : Set ℝ, IsCompact K → K ⊆ U → ν K < ∞
  density_integrable : ∀ K : Set ℝ, IsCompact K → K ⊆ U →
    ∀ᶠ n : ℕ in atTop, IntegrableOn (fun x => Real.exp (γ * φ x (dyadic n) / 2)) K
  tendsto : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
    Tendsto (fun n : ℕ => ∫ x, f x * (dyadic n ^ (γ ^ 2 / 4) * Real.exp (γ * φ x (dyadic n) / 2)))
      atTop (𝓝 (∫ x, f x ∂ν))

/-- **Quantum area measure** (arXiv:1012.4797v2, (1.1), p. 7) on an open set `V ⊆ ℂ`:
`μ = lim_{ε→0} ε^{γ²/2} e^{γ h_ε(z)} dz` with `h_ε(z) = φ z ε` the circle average, as a vague limit
on `V` along `ε_n = 2⁻ⁿ`, with the same conventions as `IsBoundaryLengthOn`. -/
structure IsAreaMeasureOn (γ : ℝ) (V : Set ℂ) (φ : ℂ → ℝ → ℝ) (μ : Measure ℂ) : Prop where
  null_outside : μ Vᶜ = 0
  finite_on_compact : ∀ K : Set ℂ, IsCompact K → K ⊆ V → μ K < ∞
  density_integrable : ∀ K : Set ℂ, IsCompact K → K ⊆ V →
    ∀ᶠ n : ℕ in atTop, IntegrableOn (fun z => Real.exp (γ * φ z (dyadic n))) K
  tendsto : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ V →
    Tendsto (fun n : ℕ => ∫ z, f z * (dyadic n ^ (γ ^ 2 / 2) * Real.exp (γ * φ z (dyadic n))))
      atTop (𝓝 (∫ z, f z ∂μ))

/-- The radius `a` with `μ(B_a(0)) = 1`: `a = inf {r > 0 : μ(B_r(0)) ≥ 1}` (p. 21). -/
noncomputable def canonicalRadius (μ : Measure ℂ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ 1 ≤ μ (Metric.ball (0 : ℂ) r)}

/-- **Canonical description** (arXiv:1012.4797v2, (1.8) and p. 21). The rescaling
`(ℍ, h) ↦ (ℍ, h(a·) + Q log |a|)` maps the area measure `μ_h` to its push-forward under `z ↦ z/a`;
choosing `a` with `μ_h(B_a(0)) = 1` gives the area measure of the canonical description, which has
`μ(B₁(0)) = 1` ("We will let `µ_h` be zero on the negative half plane so that we write this slightly
more compactly as `µ_h(B₁(0)) = 1`").

**Formalization Note** If `μ(B_r(0)) < 1` for every `r` (total mass `< 1`), the radius is the junk
`sInf ∅ = 0` and the result is the push-forward under `z ↦ z/0 = 0`. -/
noncomputable def canonicalMeasure (μ : Measure ℂ) : Measure ℂ :=
  μ.map (fun z => z / (canonicalRadius μ : ℂ))

/-- The canonical description's arc averages: `(h(a·) + Q log a, σ_{z,ε}) = h_{aε}(az) + Q log a`,
where `a = canonicalRadius μ_h` (p. 21, (1.8)). -/
noncomputable def canonicalArcAvg (Q : ℝ) (ψ : Measure ℂ → ℝ) (μ : Measure ℂ) (z : ℂ) (ε : ℝ) :
    ℝ :=
  arcAvg ψ ((canonicalRadius μ : ℂ) * z) (canonicalRadius μ * ε) + Q * Real.log (canonicalRadius μ)

end QuantumZipper.Welding


