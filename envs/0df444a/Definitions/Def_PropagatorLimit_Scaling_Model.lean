-- Prove2me | Definitions.Def_PropagatorLimit_Scaling_Model
-- name    : PropagatorLimit_Scaling_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:23.921979+00:00
-- url     : https://prove2.me/theorems/b8a9d3fa-42d0-4cea-8a21-e5f0ae3c69a1
-- title:
--   Definition 2.1 p. 4, (3.1) p. 6, Theorem 3.3 p. 7 — the nonlinear propagator model, its scaling, the coefficients λ, χ, ζ, h, θ and the linear impact model (3.2)
-- statement:
--   This file defines the discrete nonlinear propagator model and its candidate continuous-time limit.
--
--   1. **Impact functions.** $g:\mathbb R\to\mathbb R$ is odd, $C^1$ and concave on $[0,\infty)$ (p. 6), and satisfies the growth bound $|g(x)|+|g'(x)|\le C(1+|x|)$ for some constant $C$.
--   2. **The scaled impact** (3.1): $g^N(x)=\sqrt{\Delta t^N}\,g\big(x/\sqrt{\Delta t^N}\big)$ with $\Delta t^N=T/N$.
--   3. **The nonlinear propagator model** (2.1): $I^N_0=0$ and, for $n\ge1$,
--   $$\Delta I^N_n=-\beta I^N_{n-1}\Delta t^N+g^N\big(\Delta F^N_n\big),$$
--   and its step path $t\mapsto I^N_{\lceil t/\Delta t^N\rceil\wedge N}$.
--   4. **The coefficients** of Theorem 3.3, for a level $v>0$, where $\phi_v$ is the density of the centred Gaussian law with standard deviation $v$:
--   $$\lambda=\int g'(x)\phi_v(x)\,dx,\quad \chi=\tfrac12\int(v^{-2}x^2-1)g'(x)\phi_v(x)\,dx,\quad \zeta=\sqrt{\int g^2(x)\phi_v(x)\,dx},\quad h=\int xg(x)\phi_v(x)\,dx,$$
--   $$\theta=\sqrt{\lambda^2v^2+\zeta^2-2\lambda h},\qquad \rho=\frac1\theta\Big(\frac hv-\lambda v\Big).$$
--   Evaluated at $v=v_t$ they give the processes $\lambda_t,\chi_t,\zeta_t,h_t,\theta_t$ and the covariation density $\rho_t$ of $d[W,W']_t$.
--   5. **The linear impact model** (3.2). On an extension $(\Omega',(\mathcal G_t),P',\pi)$ carrying a process $W'$, a process $I$ solves
--   $$dI_t=-\beta I_t\,dt+\lambda_t\,dF_t+\eta_t\chi_t\,dt+\theta_t\,dW'_t,\qquad I_0=0,$$
--   if $I$ is continuous and $(\mathcal G_t)$-adapted, and almost surely for all $t$
--   $$I_t=-\beta\int_0^tI_s\,ds+\int_0^t\lambda_s\mu_s\,ds+\int_0^t\lambda_sv_s\,dW_s+\int_0^t\eta_s\chi_s\,ds+\int_0^t\theta_s\,dW'_s,$$
--   with all coefficients read at $\pi(\omega')$.
--
--   The step path of $I^N$ is the object whose convergence Theorem 3.3 asserts, and the linear model is its limit.
--
--   **Formalization Note** The growth bound in item 1 is **added**: Theorem 3.3 only states that $g$ is odd, $C^1$ and concave on $[0,\infty)$, but its proof applies Theorem A.3 to $F(t,x)=e^{\beta t}g(x)$, whose Assumption A.2(c) (p. 25) requires exactly this bound. The initial value $I^N_0=0$ is the one the explicit solution on p. 27 uses, and $I_0=0$ is the matching initial value of the limit (also stated for (3.2) in §4.1, p. 10). The step path uses $\lceil t/\Delta t^N\rceil$, which is Theorem A.3's $\lceil Nt\rceil$ for a general horizon $T$. Mathlib's `gaussianPDFReal` takes the variance, so $\phi_v$ is `gaussianPDFReal 0 (v^2)`. The integral $\lambda_t\,dF_t$ is expanded as $\lambda_t\mu_t\,dt+\lambda_tv_t\,dW_t$. The formulas for $\theta$ and $\rho$ are kept as printed; in Lean $1/0=0$ and the square root of a negative number is $0$. Under the growth bound every Gaussian integral above is finite.
-- source:
--   Muhle-Karbe, Wang & Webster, Stochastic liquidity as a proxy for nonlinear price impact, SSRN 4286108 (version of November 2, 2023), p. 4, Definition 2.1, (2.1); p. 6, (3.1); p. 7, Theorem 3.3, (3.2); p. 25, Assumption A.2(c); p. 27 (explicit solution)

import Mathlib
import Definitions.Def_PropagatorLimit_Scaling_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace PropagatorLimit.Scaling

/-- The impact function `g` of (3.1), p. 6: odd, `C¹`, concave on `[0, ∞)`, together with the
added growth bound `|g(x)| + |g′(x)| ≤ C (1 + |x|)` (Assumption A.2(c), p. 25, for
`F(t, x) = e^{βt} g(x)`). -/
def IsImpactFn (g : ℝ → ℝ) : Prop :=
  (∀ x, g (-x) = -g x) ∧ ContDiff ℝ 1 g ∧ ConcaveOn ℝ (Set.Ici 0) g ∧
  ∃ C : ℝ, ∀ x, |g x| + |deriv g x| ≤ C * (1 + |x|)

/-- The scaled impact function (3.1): `g^N(x) = √Δt^N g(x / √Δt^N)`. -/
noncomputable def gN (T : ℝ≥0) (N : ℕ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (dt T N) * g (x / Real.sqrt (dt T N))

/-- The discrete impact (2.1) with the scaling (3.1):
`I^N_0 = 0` and `I^N_n = I^N_{n−1} − β I^N_{n−1} Δt^N + g^N(ΔF^N_n)`. -/
noncomputable def INdisc {Ω : Type} (beta : ℝ) (T : ℝ≥0) (g : ℝ → ℝ) (F : ℝ≥0 → Ω → ℝ)
    (N : ℕ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun ω =>
      INdisc beta T g F N n ω - beta * INdisc beta T g F N n ω * dt T N +
        gN T N g (incr T N F (n + 1) ω)

/-- The step path of the discrete impact: `t ↦ I^N_{⌈t/Δt^N⌉ ∧ N}`. -/
noncomputable def INpath {Ω : Type} (beta : ℝ) (T : ℝ≥0) (g : ℝ → ℝ) (F : ℝ≥0 → Ω → ℝ)
    (N : ℕ) (ω : Ω) (t : ℝ≥0) : ℝ :=
  INdisc beta T g F N (nsteps T N t) ω

/-- `φ_v`, the density of the centred Gaussian law with standard deviation `v`
(Mathlib's `gaussianPDFReal` takes the variance `v²`). -/
noncomputable def phi (v : ℝ) (x : ℝ) : ℝ :=
  gaussianPDFReal 0 ⟨v ^ 2, sq_nonneg v⟩ x

/-- `λ = ∫ g′(x) φ_v(x) dx` (Theorem 3.3, p. 7). -/
noncomputable def lam (g : ℝ → ℝ) (v : ℝ) : ℝ := ∫ x, deriv g x * phi v x

/-- `χ = ½ ∫ (v^{−2} x² − 1) g′(x) φ_v(x) dx` (Theorem 3.3, p. 7). -/
noncomputable def chi (g : ℝ → ℝ) (v : ℝ) : ℝ :=
  (1 / 2) * ∫ x, (v⁻¹ ^ 2 * x ^ 2 - 1) * deriv g x * phi v x

/-- `ζ = √(∫ g²(x) φ_v(x) dx)` (Theorem 3.3, p. 7). -/
noncomputable def zeta (g : ℝ → ℝ) (v : ℝ) : ℝ := Real.sqrt (∫ x, g x ^ 2 * phi v x)

/-- `h = ∫ x g(x) φ_v(x) dx` (Theorem 3.3, p. 7). -/
noncomputable def hcoef (g : ℝ → ℝ) (v : ℝ) : ℝ := ∫ x, x * g x * phi v x

/-- `θ = √(λ² v² + ζ² − 2 λ h)` (Theorem 3.3, p. 7). -/
noncomputable def theta (g : ℝ → ℝ) (v : ℝ) : ℝ :=
  Real.sqrt (lam g v ^ 2 * v ^ 2 + zeta g v ^ 2 - 2 * lam g v * hcoef g v)

/-- The covariation density `(1/θ)(h/v − λ v)` of `d[W, W′]` (Theorem 3.3, p. 7). -/
noncomputable def rho (g : ℝ → ℝ) (v : ℝ) : ℝ :=
  (1 / theta g v) * (hcoef g v / v - lam g v * v)

/-- `I` solves the linear impact model (3.2) on the extension `E`, driven by `W ∘ π` and `W′`:
`I` has continuous paths, is `𝓖`-adapted, starts at `I_0 = 0`, and almost surely, for all `t`,
`I_t = −β ∫₀ᵗ I + ∫₀ᵗ λ µ + ∫₀ᵗ λ v d(W∘π) + ∫₀ᵗ η χ + ∫₀ᵗ θ dW′`,
where `λ dF = λ µ dt + λ v dW` and every coefficient is read at `π ω'`. -/
def SolvesLinearImpact {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (beta : ℝ) (g : ℝ → ℝ) (W : ℝ≥0 → Ω → ℝ) (fl : Flow Ω)
    (E : Extension Ω P 𝓕) (Wp : ℝ≥0 → E.Ω' → ℝ) (I : ℝ≥0 → E.Ω' → ℝ) : Prop :=
  (∀ ω', Continuous (I · ω')) ∧ Adapted E.𝓖 I ∧ (∀ ω', I 0 ω' = 0) ∧
  (∀ (t : ℝ≥0) ω', IntervalIntegrable
    (fun u : ℝ => lam g (fl.v u.toNNReal (E.π ω')) * fl.mu u.toNNReal (E.π ω')) volume 0 t.val) ∧
  (∀ (t : ℝ≥0) ω', IntervalIntegrable
    (fun u : ℝ => fl.eta u.toNNReal (E.π ω') * chi g (fl.v u.toNNReal (E.π ω'))) volume 0 t.val) ∧
  ∃ J₁ J₂ : ℝ≥0 → E.Ω' → ℝ,
    (∀ ω', Continuous (J₁ · ω')) ∧ (∀ ω', Continuous (J₂ · ω')) ∧
    EthierKurtz.HasBrownianItoIntegral E.P' (fun t => E.𝓖 t) (fun t ω' => W t (E.π ω'))
      (fun t ω' => lam g (fl.v t (E.π ω')) * fl.v t (E.π ω')) J₁ ∧
    EthierKurtz.HasBrownianItoIntegral E.P' (fun t => E.𝓖 t) Wp
      (fun t ω' => theta g (fl.v t (E.π ω'))) J₂ ∧
    ∀ᵐ ω' ∂E.P', ∀ t : ℝ≥0,
      I t ω' = -beta * (∫ u in (0 : ℝ)..t.val, I u.toNNReal ω') +
        (∫ u in (0 : ℝ)..t.val,
          lam g (fl.v u.toNNReal (E.π ω')) * fl.mu u.toNNReal (E.π ω')) + J₁ t ω' +
        (∫ u in (0 : ℝ)..t.val,
          fl.eta u.toNNReal (E.π ω') * chi g (fl.v u.toNNReal (E.π ω'))) + J₂ t ω'

end PropagatorLimit.Scaling


