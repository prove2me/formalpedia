-- Prove2me | Definitions.Def_MonotoneMVJump_Compare_PDE
-- name    : MonotoneMVJump_Compare_PDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:30:20.791331+00:00
-- url     : https://prove2.me/theorems/0ae60d42-a795-429e-a4ce-f8b30a7b9a80
-- title:
--   pp. 11–18, 22–23 — Conditions of Proposition 1, the solution G = −e^F of (20), ζ, H, the controls (25), (37), (39), the process R of (38), Assumption 1
-- statement:
--   This file collects the objects built from the PDE (20).
--
--   **Conditions of Proposition 1** (p. 13): $b$ is continuously differentiable; $a$, $\sigma$ and $m$ are differentiable; $b^2\ge c>0$; and $a,b,b',\lambda$ are bounded.
--
--   **The solution $G$ of (20)** (pp. 11–12, 18). $G=-e^F$, where $F(z,s)$ is continuous on $\mathbb R\times[0,T]$, $F(\cdot,T)=0$, $F$ is differentiable in $s$ on $(0,T)$ and twice differentiable in $z$ on $[0,T)$, the derivatives $F_t,F_z,F_{zz}$ are continuous, $|F|+|F_t|+|F_z|+|F_{zz}|$ is bounded, and
--   $$G_t+\alpha(z)G_z+\tfrac12 b(z)^2G_{zz}-\beta(z)b(z)^2\frac{G_z^2}{G}+\lambda(z)G=0,\qquad G(z,T)=-1 .$$
--   Write $H=-1/G$ and
--   $$\zeta(z,s)=-\frac{\mu(z)-r-\sigma(z)b(z)\rho_W G_z(z,s)/G(z,s)}{\Sigma(z)} ,$$
--   which equals the paper's $-(\mu-r+\sigma b\rho_WH_z/H)/\Sigma$ of (38).
--
--   **Feedback controls.** Along the factor path $Z$:
--   1. (25): $\eta^*_{1,s}=-\frac{\sigma(Z_s)}{\Sigma(Z_s)}(\mu(Z_s)-r)-\rho_Wb(Z_s)\frac{m(Z_s)}{\Sigma(Z_s)}\frac{G_z}{G}(Z_s,s)$, $\eta^*_{2,s}=-\frac{G_z(Z_s,s)b(Z_s)\bar\rho_W}{G(Z_s,s)}$, $\phi^*_s(p)=-\frac{\gamma(Z_s,p)}{\Sigma(Z_s)}\big[\mu(Z_s)-r-\sigma(Z_s)b(Z_s)\rho_W\frac{G_z}{G}(Z_s,s)\big]$, and $\pi^*_s=-\frac{2Y_{s-}G(Z_s,s)}{\Sigma(Z_s)}[\cdots]$ with $Y=y\mathcal E$;
--   2. Theorem 4's rewritten form: $\pi^*_s=-\frac{X_{s-}-x+2yG(z,t)}{\Sigma(Z_s)}[\cdots]$;
--   3. (37): $\pi^*(D)(s)=-\frac{X_{s-}-D}{\Sigma(Z_s)}\big[\mu(Z_s)-r-\sigma(Z_s)b(Z_s)\rho_W\frac{G_z}{G}(Z_s,s)\big]$;
--   4. the feedback of (39) with target $D$: $-\frac{X_{s-}-D}{\Sigma(Z_s)}\big[\mu(Z_s)-r+\sigma(Z_s)b(Z_s)\rho_W\frac{H_z}{H}(Z_s,s)\big]$. In (39), $D=D^*=x+\frac1\theta\frac{1-\mathbb E[R_T]}{\mathrm{Var}[R_T]}$.
--
--   **The process $R$** ((27) = (38)):
--   $$\mathrm dR_s=R_s\zeta(Z_s,s)(\mu(Z_s)-r)\mathrm ds+R_s\zeta(Z_s,s)\sigma(Z_s)\mathrm dW^1_s+R_{s-}\zeta(Z_s,s)\int_{\mathbb R}\gamma(Z_s,p)\tilde N(\mathrm ds,\mathrm dp),\quad R_t=1 .$$
--
--   **Assumption 1** (p. 17). Let $\Delta L_s$ be the mark of the atom of $N$ at time $s$ (and $0$ if there is none), and let $\tau=\inf\{s>t:\zeta(Z_s,s)\gamma(Z_s,\Delta L_s)\mathbf 1_{\Delta L_s\ne0}=-1\}$. Assumption 1 holds at $(z,t)$ if, almost surely,
--   $$\zeta(Z_{s\wedge\tau},s\wedge\tau)\,\gamma(Z_{s\wedge\tau},\Delta L_{s\wedge\tau})\,\mathbf 1_{\Delta L_{s\wedge\tau}\ne0}\ \ge\ -1\qquad\text{for all }s\in(t,T].$$
--
--   **Formalization Note** Proposition 1 is not used. The solution $G$ of (20) is a hypothesis of each theorem, in the paper's bounded class: $G=-e^F$ with $F$ bounded and $C^{2,1}$, as used on p. 18. Derivatives are Mathlib's `deriv`. The PDE holds on $\mathbb R\times(0,T)$. The infimum defining $\tau$ is taken in $[0,\infty]$ with $\inf\emptyset=\infty$, so $s\wedge\tau=s$ when there is no such time. "Almost surely" is read as holding simultaneously for all $s$: the expression vanishes off the jump times, so "for each fixed $s$, almost surely" would hold trivially. Left limits $X_{s-}$ are Mathlib's `Function.leftLim`. (37) prints $G_z(Z_s,t)/G(Z_s,t)$; it is formalized at $(Z_s,s)$, as everywhere else in the paper. In the theorems, "the control is given by the feedback $f$ on $[t,T]$" means: almost surely, $\pi_s=f(X_{s-},Z_s,s)$ for all $s\in[t,T]$ simultaneously (equality of processes up to indistinguishability, the paper's sense).
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, pp. 11–12 ((20), α, β, λ, Hopf–Cole), p. 13 (Proposition 1's conditions), p. 17 (Assumption 1, (25)), p. 18 (ζ, R, (27), boundedness of F), p. 22 ((37), H), p. 23 ((38), (39))

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_Problems

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The time derivative `u_t(z, s)` of `u : ℝ → ℝ → ℝ` (arguments `(z, s)`). -/
noncomputable def dt (u : ℝ → ℝ → ℝ) (z s : ℝ) : ℝ := deriv (fun v => u z v) s

/-- The factor derivative `u_z(z, s)`. -/
noncomputable def dz (u : ℝ → ℝ → ℝ) (z s : ℝ) : ℝ := deriv (fun w => u w s) z

/-- The second factor derivative `u_zz(z, s)`. -/
noncomputable def dzz (u : ℝ → ℝ → ℝ) (z s : ℝ) : ℝ := deriv (fun w => dz u w s) z

/-- The Conditions of Proposition 1 (p. 13): `b` is continuously differentiable; `a`, `σ` and
`m(z) = ∫ γ(z, p)² ν(dp)` are differentiable; `b²` is bounded below away from `0`; `a, b, b′`
and `λ` are bounded. -/
structure PropOneConditions (M : Market Ω) : Prop where
  b_C1 : ContDiff ℝ 1 M.b
  a_diff : Differentiable ℝ M.a
  σ_diff : Differentiable ℝ M.σ
  m_diff : Differentiable ℝ M.m
  b_sq_lb : ∃ c : ℝ, 0 < c ∧ ∀ z, c ≤ M.b z ^ 2
  bdd : ∃ C : ℝ, ∀ z, |M.a z| ≤ C ∧ |M.b z| ≤ C ∧ |deriv M.b z| ≤ C ∧ |M.lam z| ≤ C

/-- `G = −e^F` is a classical solution of (20) on `ℝ × [0, T)` in the paper's bounded class
(pp. 12, 18): `F(·, T) = 0`; `F` is continuous on `ℝ × [0, T]`; `F` is differentiable in `s` on
`ℝ × (0, T)` and twice differentiable in `z` on `ℝ × [0, T)`, with `F_t`, `F_z`, `F_zz`
continuous there; `|F| + |F_t| + |F_z| + |F_zz|` is bounded; and
`G_t + α G_z + ½ b² G_zz − β b² G_z²/G + λ G = 0` on `ℝ × (0, T)`, `G(z, T) = −1`. -/
structure IsHopfColeSolution (M : Market Ω) (G F : ℝ → ℝ → ℝ) : Prop where
  hopf_cole : ∀ z s, G z s = -Real.exp (F z s)
  terminal_F : ∀ z, F z M.T = 0
  cont : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ Set.Icc 0 (M.T : ℝ))
  diff_t : ∀ z, ∀ s ∈ Set.Ioo 0 (M.T : ℝ), DifferentiableAt ℝ (fun v => F z v) s
  diff_z : ∀ s ∈ Set.Ico 0 (M.T : ℝ), Differentiable ℝ (fun w => F w s)
  diff_zz : ∀ s ∈ Set.Ico 0 (M.T : ℝ), Differentiable ℝ (fun w => dz F w s)
  cont_t : ContinuousOn (Function.uncurry (dt F)) (Set.univ ×ˢ Set.Ioo 0 (M.T : ℝ))
  cont_z : ContinuousOn (Function.uncurry (dz F)) (Set.univ ×ˢ Set.Ico 0 (M.T : ℝ))
  cont_zz : ContinuousOn (Function.uncurry (dzz F)) (Set.univ ×ˢ Set.Ico 0 (M.T : ℝ))
  bdd : ∃ C : ℝ, ∀ z,
    (∀ s ∈ Set.Icc 0 (M.T : ℝ), |F z s| ≤ C) ∧
    (∀ s ∈ Set.Ico 0 (M.T : ℝ), |dz F z s| ≤ C ∧ |dzz F z s| ≤ C) ∧
    ∀ s ∈ Set.Ioo 0 (M.T : ℝ), |dt F z s| ≤ C
  pde : ∀ z, ∀ s ∈ Set.Ioo 0 (M.T : ℝ),
    dt G z s + M.alpha z * dz G z s + 1 / 2 * M.b z ^ 2 * dzz G z s
      - M.beta z * M.b z ^ 2 * dz G z s ^ 2 / G z s + M.lam z * G z s = 0
  terminal : ∀ z, G z M.T = -1

/-- `G` is "the solution of (20)": `G = −e^F` for some `F` as in `IsHopfColeSolution`. -/
def IsGSolution (M : Market Ω) (G : ℝ → ℝ → ℝ) : Prop :=
  ∃ F : ℝ → ℝ → ℝ, IsHopfColeSolution M G F

/-- `H = −1/G` (p. 22). -/
noncomputable def Hf (G : ℝ → ℝ → ℝ) (z s : ℝ) : ℝ := -1 / G z s

/-- `ζ(z, s) = −(μ(z) − r − σ(z) b(z) ρ_W G_z(z, s)/G(z, s)) / Σ(z)` (p. 18; equal to (38)'s
`−(μ − r + σ b ρ_W H_z/H)/Σ`). -/
noncomputable def zeta (M : Market Ω) (G : ℝ → ℝ → ℝ) (w s : ℝ) : ℝ :=
  -(M.μ w - M.r - M.σ w * M.b w * M.ρW * dz G w s / G w s) / M.Sig w

/-- `η*_{1,s}` of (25). -/
noncomputable def etaStar1 (M : Market Ω) (G : ℝ → ℝ → ℝ) (Z : ℝ≥0 → Ω → ℝ) (s : ℝ≥0)
    (ω : Ω) : ℝ :=
  -(M.σ (Z s ω) / M.Sig (Z s ω)) * (M.μ (Z s ω) - M.r)
    - M.ρW * M.b (Z s ω) * (M.m (Z s ω) / M.Sig (Z s ω)) * (dz G (Z s ω) s / G (Z s ω) s)

/-- `η*_{2,s}` of (25). -/
noncomputable def etaStar2 (M : Market Ω) (G : ℝ → ℝ → ℝ) (Z : ℝ≥0 → Ω → ℝ) (s : ℝ≥0)
    (ω : Ω) : ℝ :=
  -(dz G (Z s ω) s * M.b (Z s ω) * M.ρbarW / G (Z s ω) s)

/-- `ϕ*_s(p)` of (25). -/
noncomputable def phiStar (M : Market Ω) (G : ℝ → ℝ → ℝ) (Z : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω)
    (p : ℝ) : ℝ :=
  -(M.γ (Z s ω) p / M.Sig (Z s ω)) *
    (M.μ (Z s ω) - M.r - M.σ (Z s ω) * M.b (Z s ω) * M.ρW * dz G (Z s ω) s / G (Z s ω) s)

/-- `π*_s` of (25) in its `Y`-form, with `Y^{η*,ϕ*} = y ℰ`:
`π*_s = −(2 Y_{s−} G(Z_s, s)/Σ(Z_s)) [μ(Z_s) − r − σ(Z_s) b(Z_s) ρ_W G_z(Z_s, s)/G(Z_s, s)]`. -/
noncomputable def mmvStrategyY (M : Market Ω) (G : ℝ → ℝ → ℝ) (y : ℝ) (Z E : ℝ≥0 → Ω → ℝ)
    (s : ℝ≥0) (ω : Ω) : ℝ :=
  -(2 * (y * Function.leftLim (fun v => E v ω) s) * G (Z s ω) s / M.Sig (Z s ω)) *
    (M.μ (Z s ω) - M.r - M.σ (Z s ω) * M.b (Z s ω) * M.ρW * dz G (Z s ω) s / G (Z s ω) s)

/-- `π*_s` of Theorem 4 in its `X`-form ("Moreover"):
`π*_s = −((X_{s−} − x + 2y G(z, t))/Σ(Z_s)) [μ(Z_s) − r − σ(Z_s) b(Z_s) ρ_W G_z(Z_s, s)/G(Z_s, s)]`. -/
noncomputable def mmvStrategyX (M : Market Ω) (G : ℝ → ℝ → ℝ) (x y z : ℝ) (t : ℝ≥0)
    (Z X : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  -((Function.leftLim (fun v => X v ω) s - x + 2 * y * G z t) / M.Sig (Z s ω)) *
    (M.μ (Z s ω) - M.r - M.σ (Z s ω) * M.b (Z s ω) * M.ρW * dz G (Z s ω) s / G (Z s ω) s)

/-- `π*(D)(s)` of (37), with `G_z/G` evaluated at `(Z_s, s)`:
`π*(D)(s) = −((X_{s−} − D)/Σ(Z_s)) [μ(Z_s) − r − σ(Z_s) b(Z_s) ρ_W G_z(Z_s, s)/G(Z_s, s)]`. -/
noncomputable def problem3Strategy (M : Market Ω) (G : ℝ → ℝ → ℝ) (D : ℝ)
    (Z X : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  -((Function.leftLim (fun v => X v ω) s - D) / M.Sig (Z s ω)) *
    (M.μ (Z s ω) - M.r - M.σ (Z s ω) * M.b (Z s ω) * M.ρW * dz G (Z s ω) s / G (Z s ω) s)

/-- The feedback of (39) with target `D`, in its `H`-form:
`−((X_{s−} − D)/Σ(Z_s)) [μ(Z_s) − r + σ(Z_s) b(Z_s) ρ_W H_z(Z_s, s)/H(Z_s, s)]`; (39) is the case
`D = x + (1/θ)(1 − E_{z,t}[R_T])/Var_{z,t}[R_T]` (`Dstar`). -/
noncomputable def mvStrategy39 (M : Market Ω) (G : ℝ → ℝ → ℝ) (D : ℝ) (Z X : ℝ≥0 → Ω → ℝ)
    (s : ℝ≥0) (ω : Ω) : ℝ :=
  -((Function.leftLim (fun v => X v ω) s - D) / M.Sig (Z s ω)) *
    (M.μ (Z s ω) - M.r
      + M.σ (Z s ω) * M.b (Z s ω) * M.ρW * dz (Hf G) (Z s ω) s / Hf G (Z s ω) s)

/-- `D* = x + (1/θ)(1 − E_{z,t}[R_T])/Var_{z,t}[R_T]` (Theorem 7 and (39)). -/
noncomputable def Dstar (P : Measure Ω) (θ x : ℝ) (R : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : ℝ :=
  x + 1 / θ * ((1 - ∫ ω, R T ω ∂P) / variance (R T) P)

/-- `R` solves (38) on `[t, T]` from `R_t = 1`:
`dR_s = R_s ζ(Z_s, s)(μ(Z_s) − r) ds + R_s ζ(Z_s, s) σ(Z_s) dW¹_s
  + R_{s−} ζ(Z_s, s) ∫_ℝ γ(Z_s, p) Ñ(ds, dp)`. -/
def IsRProcess (M : Market Ω) (G : ℝ → ℝ → ℝ) (t : ℝ≥0) (Z R : ℝ≥0 → Ω → ℝ) : Prop :=
  M.IsJumpIto t 1 (fun u ω => R u ω * zeta M G (Z u ω) u * (M.μ (Z u ω) - M.r))
    (fun u ω => R u ω * zeta M G (Z u ω) u * M.σ (Z u ω)) (fun _ _ => 0)
    (fun u ω p => Function.leftLim (fun v => R v ω) u * zeta M G (Z u ω) u * M.γ (Z u ω) p) R

/-- The jump `ΔL_s(ω)` of the Lévy process `L_s = ∫₀ˢ∫ p N(du, dp)`: the mark `p` of the atom
`(s, p) ∈ N(ω)` if there is one, and `0` otherwise. -/
noncomputable def jumpL (N : Ω → Set (ℝ≥0 × ℝ)) (ω : Ω) (s : ℝ≥0) : ℝ :=
  open Classical in if h : ∃ p, (s, p) ∈ N ω then h.choose else 0

/-- `ζ(Z_s, s) γ(Z_s, ΔL_s) 𝟏_{ΔL_s ≠ 0}`. -/
noncomputable def kappa (M : Market Ω) (G : ℝ → ℝ → ℝ) (Z : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) :
    ℝ :=
  zeta M G (Z s ω) s * M.γ (Z s ω) (jumpL M.N ω s) * (if jumpL M.N ω s ≠ 0 then 1 else 0)

/-- `τ = inf{s > t : ζ(Z_s, s) γ(Z_s, ΔL_s) 𝟏_{ΔL_s ≠ 0} = −1}`, in `[0, ∞]` (`inf ∅ = ∞`). -/
noncomputable def tau (M : Market Ω) (G : ℝ → ℝ → ℝ) (t : ℝ≥0) (Z : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    ℝ≥0∞ :=
  sInf {u : ℝ≥0∞ | ∃ s : ℝ≥0, u = s ∧ t < s ∧ kappa M G Z s ω = -1}

/-- Assumption 1 (p. 17) at the initial data `(z, t)` (through `Z = Z^{z,t}`): almost surely,
`ζ(Z_{s∧τ}, s∧τ) γ(Z_{s∧τ}, ΔL_{s∧τ}) 𝟏_{ΔL_{s∧τ} ≠ 0} ≥ −1` for every `s ∈ (t, T]`. -/
def Assumption1 (M : Market Ω) (G : ℝ → ℝ → ℝ) (t : ℝ≥0) (Z : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t < s → s ≤ M.T →
    -1 ≤ kappa M G Z (min (s : ℝ≥0∞) (tau M G t Z ω)).toNNReal ω

end MonotoneMVJump.Compare


