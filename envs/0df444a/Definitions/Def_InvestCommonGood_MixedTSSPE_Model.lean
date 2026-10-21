-- Prove2me | Definitions.Def_InvestCommonGood_MixedTSSPE_Model
-- name    : InvestCommonGood_MixedTSSPE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:58.49884+00:00
-- url     : https://prove2.me/theorems/01157726-a9f0-4579-b665-cbc3118551e8
-- title:
--   §3.1, §4.3 — standing assumptions, Assumptions 1, 2, 4, 5, and the auxiliary functions S′, m′, L, I, J of the investment game
-- statement:
--   The analytic layer of Kim and Kwon's game of investment in a common good. The stock of the common good is the diffusion $dX_t=\mu(X_t)\,dt+\sigma(X_t)\,dW_t$ on an interval $\mathcal I=(a,b)$, with the data $(\mu,\sigma,\pi,k,r,\mathcal I,x_0)$ of the published model, the characteristic operator $\mathcal A f=\tfrac12\sigma^2f''+\mu f'-rf$ of (3), the resolvent $(R_r\pi)(x)=\mathbb E_x\big[\int_0^\infty \pi(X_t)e^{-rt}\,dt\big]$ and the fundamental solutions $\psi$ (increasing) and $\varphi$ (decreasing) of $\mathcal A f=0$. With $\rho(x)=\pi(x)+k[\mu(x)-rx]$, this file defines the functions of §4.3:
--   $$S'(x)=\exp\Big[-\int_{x_0}^x\frac{2\mu(y)}{\sigma^2(y)}\,dy\Big],\qquad m'(x)=\frac{2}{\sigma^2(x)S'(x)},\qquad L(x)=-\frac{\rho(x)\varphi'(x)}{S'(x)}-r\int_x^b\varphi(y)\rho(y)m'(y)\,dy,$$
--   $$I(x)=\frac{(R_r\pi)'(x)-k}{\varphi'(x)}\ \ (33),\qquad J(x)=(R_r\pi)(x)-kx-I(x)\varphi(x)\ \ (34),$$
--   and the constant $B=(\psi'\varphi-\varphi'\psi)/S'$ of (B.18).
--
--   **Standing assumptions** (§3.1, kept in §4.1):
--   1. $P$ is a probability measure, the filtration satisfies the usual conditions, and $W$ is a Brownian motion for it;
--   2. $\mathcal I$ is a nonempty open interval, bounded below ($a>-\infty$), containing $x_0$;
--   3. $\mu<0$ and $\sigma>0$ on $\mathcal I$, $k>0$, $r>0$; $\mu,\sigma$ are Lipschitz on $\mathcal I$ with $|\mu(x)|+|\sigma(x)|\le\delta(1+|x|)$ for some $\delta>0$;
--   4. for each $x\in\mathcal I$ the uncontrolled process $X^x$ solves (1) from $x$ with continuous paths in $\mathcal I$ (natural boundaries), and the transversality condition (2) $\lim_{t\to\infty}\mathbb E_x[|X_t|e^{-rt}]=0$ holds;
--   5. $\pi$ is continuous and increasing on $\mathcal I$;
--   6. $\psi,\varphi>0$ are $C^2$ solutions of $\mathcal Af=0$, $\psi$ strictly increasing, $\varphi$ strictly decreasing, normalized by $\mathbb E_x[e^{-r\tau_y}]=\psi(x)/\psi(y)$ for $x\le y$ and $=\varphi(x)/\varphi(y)$ for $y\le x$;
--   7. $R_r\pi$ is $C^2$ on $\mathcal I$ with $\mathcal A(R_r\pi)+\pi=0$, and the resolvent representation (B.19)
--   $$(R_rf)(x)=B^{-1}\varphi(x)\int_a^x\psi(y)f(y)m'(y)\,dy+B^{-1}\psi(x)\int_x^b\varphi(y)f(y)m'(y)\,dy$$
--   holds for every continuous $f$ with $\mathbb E_x\int_0^\infty e^{-rt}|f(X_t)|\,dt<\infty$.
--
--   **Assumption 1** (p. 8): $\lim_{x\downarrow a}\pi(x)=\pi_L>-\infty$ and $\mathbb E_x\int_0^\infty|\pi(X_t)|e^{-rt}dt<\infty$ for $x\in\mathcal I$. **Assumption 2** (p. 8), with its point $z^*\in\mathcal I$: $(R_r\pi)'(x)-k>0$ for $x<z^*$ and $<0$ for $x>z^*$. **Assumption 4** (p. 23), with its point $x^*\in\mathcal I$: (i) $\rho\in C^1(\mathcal I)$ with $\rho'>0$ on $(a,x^*)$ and $\rho'<0$ on $(x^*,b)$; (ii) $\lim_{x\to b}\rho(x)\varphi'(x)/S'(x)=0$; (iii) $L(x)<0$ for some $x\in\mathcal I$. **Assumption 5** (p. 24), with its points $\theta^*<z_2$ in $\mathcal I$: $I(z_2)=I(\theta^*)$ (35) and $J(z_2)-J(\theta^*)=c_2$ (36). Finally, $\hat x\in\mathcal I$ is a **Lemma 2 point** if $I'<0<J'$ on $(a,\hat x)$ and $J'<0<I'$ on $(\hat x,b)$.
--
--   These objects carry Theorem 3: Assumption 5 is the single-player optimal impulse policy of Alvarez and Lempa (2008) for the cost $c_2$, and $I$, $J$ parametrize the closed-form payoffs of the mixed equilibrium.
--
--   **Formalization Note.** The existentially quantified points of the assumptions ($z^*$, $x^*$, $\theta^*$, $z_2$) are parameters with their defining properties. Assumption 5 includes $\theta^*<z_2$, which the paper uses ("$\theta^*<\hat x<z_2$ by assumption", EC p. 23) but omits from the display. The facts in item 7 are used by the paper without proof (cited from Alvarez and Lempa 2008) and are stated as standing hypotheses. Assumption 4 requires the improper integral $\int_x^b\varphi\rho m'$ in $L$ to converge absolutely. "Increasing" for $\pi$ is read as nondecreasing.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, pp. 6–8, 23–24, §3.1, §4.3, (1)–(3), (33)–(36), Assumptions 1, 2, 4, 5; EC p. 20–21 (PDF 51–52), (B.18), (B.19)

import Mathlib
import Definitions.Def_VarContrib_RegularMPE_Setting

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace InvestCommonGood.MixedTSSPE

open VarContrib.RegularMPE

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The scale density `S′(x) = exp(−∫_{x₀}^x 2μ(y)/σ²(y) dy)` (§4.3, p. 23). -/
noncomputable def Sp (m : Model) (x : ℝ) : ℝ :=
  Real.exp (-∫ y in m.x₀..x, 2 * m.μ y / m.σ y ^ 2)

/-- The speed density `m′(x) = 2/(σ²(x) S′(x))` (§4.3, p. 23). -/
noncomputable def mp (m : Model) (x : ℝ) : ℝ := 2 / (m.σ x ^ 2 * Sp m x)

/-- `L(x) = −ρ(x)φ′(x)/S′(x) − r ∫_x^b φ(y)ρ(y)m′(y) dy` (§4.3, p. 23), where `ρ = q m` is
`ρ(x) = π(x) + k[μ(x) − r x]` and `∫_x^b` is the integral over `I ∩ (x, ∞) = (x, b)`. -/
noncomputable def Lfun (m : Model) (S : Setting Ω) (x : ℝ) : ℝ :=
  -(q m x * deriv S.φ x / Sp m x) - m.r * ∫ y in m.I ∩ Ioi x, S.φ y * q m y * mp m y

/-- `I(x) = ((R_rπ)′(x) − k)/φ′(x)` (33). -/
noncomputable def Ifun (m : Model) (S : Setting Ω) (x : ℝ) : ℝ :=
  (deriv (R m S m.π) x - m.k) / deriv S.φ x

/-- `J(x) = (R_rπ)(x) − kx − I(x)φ(x)` (34). -/
noncomputable def Jfun (m : Model) (S : Setting Ω) (x : ℝ) : ℝ :=
  R m S m.π x - m.k * x - Ifun m S x * S.φ x

/-- The constant `B = (ψ′(x)φ(x) − φ′(x)ψ(x))/S′(x)` of (B.18), evaluated at `x`. -/
noncomputable def Bw (m : Model) (S : Setting Ω) (x : ℝ) : ℝ :=
  (deriv S.ψ x * S.φ x - deriv S.φ x * S.ψ x) / Sp m x

/-- The standing assumptions of §3.1 (pp. 5–8), kept in §4.1 ("We assume the same properties of
the uncontrolled process X as in Section 3.1.1", p. 17):
1. `P` is a probability measure; `(ℱ_t)` satisfies the usual conditions;
2. `W` is an `(ℱ_t)`-Brownian motion;
3. `I = (a, b)` is a nonempty open interval with `a > −∞` (bounded below), containing `x₀`;
4. `μ < 0`, `σ > 0` on `I`, `k > 0`, `r > 0`;
5. `μ`, `σ` Lipschitz on `I` with `|μ(x)| + |σ(x)| ≤ δ(1 + |x|)`, `δ > 0`;
6. for `x ∈ I`, `X^x` solves (1) from `x`, with continuous paths in `I` (natural boundaries);
7. the transversality condition (2): `E_x[|X_t|e^{−rt}] → 0`;
8. `π` is continuous and increasing on `I` (p. 7);
9. `ψ`, `φ` are the positive increasing / decreasing `C²` solutions of `𝒜f = 0`, pinned by the
   Laplace transforms of hitting times;
10. (disclosed diffusion facts used without proof by the paper) `R_rπ` is `C²` on `I` with
    `𝒜(R_rπ) + π = 0`, and the resolvent representation (B.19) with the constant `B` of (B.18)
    holds for every continuous `f` with `E_x[∫₀^∞ e^{−rt}|f(X_t)|dt] < ∞`. -/
structure Standing (m : Model) (S : Setting Ω) : Prop where
  prob : IsProbabilityMeasure S.P
  filt_rightCont : ∀ t, S.ℱ t = ⨅ s, ⨅ (_ : t < s), S.ℱ s
  filt_complete : ∀ s : Set Ω, S.P s = 0 → MeasurableSet[S.ℱ 0] s
  bm : IsBrownianReal S.W S.P
  bm_cont : ∀ ω, Continuous (S.W · ω)
  bm_adapted : ∀ t, Measurable[S.ℱ t] (S.W t)
  bm_indep : ∀ s t : ℝ≥0, Indep (S.ℱ s)
    (MeasurableSpace.comap (fun ω => S.W (s + t) ω - S.W s ω) inferInstance) S.P
  I_open : IsOpen m.I
  I_ordConnected : m.I.OrdConnected
  I_nonempty : m.I.Nonempty
  I_bddBelow : BddBelow m.I
  x₀_mem : m.x₀ ∈ m.I
  μ_neg : ∀ x ∈ m.I, m.μ x < 0
  σ_pos : ∀ x ∈ m.I, 0 < m.σ x
  k_pos : 0 < m.k
  r_pos : 0 < m.r
  lipschitz : ∃ L : ℝ≥0, LipschitzOnWith L m.μ m.I ∧ LipschitzOnWith L m.σ m.I
  growth : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ m.I, |m.μ x| + |m.σ x| ≤ δ * (1 + |x|)
  uncontrolled : ∀ x ∈ m.I, IsStateSol m S m.μ x (fun _ _ => 0) (S.X x) ∧
    ∀ ω, Continuous (S.X x · ω)
  transversality : ∀ x ∈ m.I, (∀ t : ℝ≥0, Integrable (fun ω => |S.X x t ω|) S.P) ∧
    Tendsto (fun t : ℝ≥0 => ∫ ω, |S.X x t ω| * Real.exp (-(m.r * (t : ℝ))) ∂S.P) atTop (𝓝 0)
  π_cont : ContinuousOn m.π m.I
  π_mono : MonotoneOn m.π m.I
  ψ_pos : ∀ x ∈ m.I, 0 < S.ψ x
  φ_pos : ∀ x ∈ m.I, 0 < S.φ x
  ψ_C2 : ContDiffOn ℝ 2 S.ψ m.I
  φ_C2 : ContDiffOn ℝ 2 S.φ m.I
  ψ_ode : ∀ x ∈ m.I, gen m S.ψ x = 0
  φ_ode : ∀ x ∈ m.I, gen m S.φ x = 0
  ψ_strictMono : StrictMonoOn S.ψ m.I
  φ_strictAnti : StrictAntiOn S.φ m.I
  hit_up : ∀ x ∈ m.I, ∀ y ∈ m.I, x ≤ y →
    ∫ ω, discAt m.r (hitTime S x y ω) ∂S.P = S.ψ x / S.ψ y
  hit_down : ∀ x ∈ m.I, ∀ y ∈ m.I, y ≤ x →
    ∫ ω, discAt m.r (hitTime S x y ω) ∂S.P = S.φ x / S.φ y
  Rπ_C2 : ContDiffOn ℝ 2 (R m S m.π) m.I
  Rπ_ode : ∀ x ∈ m.I, gen m (R m S m.π) x + m.π x = 0
  resolvent : ∀ f : ℝ → ℝ, ContinuousOn f m.I →
    (∀ x ∈ m.I, Integrable (fun p : Ω × ℝ => Real.exp (-(m.r * p.2)) * |f (S.X x p.2.toNNReal p.1)|)
      (S.P.prod (volume.restrict (Ioi (0 : ℝ))))) →
    ∀ x ∈ m.I,
      IntegrableOn (fun y => S.ψ y * f y * mp m y) (m.I ∩ Iic x) ∧
      IntegrableOn (fun y => S.φ y * f y * mp m y) (m.I ∩ Ioi x) ∧
      R m S f x = (S.φ x * (∫ y in m.I ∩ Iic x, S.ψ y * f y * mp m y)
        + S.ψ x * (∫ y in m.I ∩ Ioi x, S.φ y * f y * mp m y)) / Bw m S x

/-- Assumption 1 (p. 8): (i) `lim_{x↓a} π(x) = π_L > −∞`; (ii) `E_x[∫₀^∞ |π(X_t)|e^{−rt}dt] < ∞`
for every `x ∈ I`. -/
def Assumption1 (m : Model) (S : Setting Ω) : Prop :=
  (∃ πL : ℝ, Tendsto m.π (lowerEnd m.I) (𝓝 πL)) ∧
  ∀ x ∈ m.I, Integrable (fun p : Ω × ℝ => Real.exp (-(m.r * p.2)) * |m.π (S.X x p.2.toNNReal p.1)|)
    (S.P.prod (volume.restrict (Ioi (0 : ℝ))))

/-- Assumption 2 (p. 8) with its point `z*`: `z* ∈ I`, `(R_rπ)′(x) − k > 0` for `x < z*` and
`< 0` for `x > z*` (the sign pattern makes `z*` unique). -/
def Assumption2 (m : Model) (S : Setting Ω) (zs : ℝ) : Prop :=
  zs ∈ m.I ∧ ∀ x ∈ m.I, (x < zs → 0 < deriv (R m S m.π) x - m.k) ∧
    (zs < x → deriv (R m S m.π) x - m.k < 0)

/-- Assumption 4 (p. 23) with its point `x*`: (i) `ρ ∈ C¹(I)`, `ρ′ > 0` below `x*`, `ρ′ < 0`
above; (ii) `lim_{x→b} ρ(x)φ′(x)/S′(x) = 0`; (iii) `L(x) < 0` for some `x ∈ I`. The improper
integral `∫_x^b φρm′` in `L` is required to converge absolutely for `x ∈ I`. -/
def Assumption4 (m : Model) (S : Setting Ω) (xs : ℝ) : Prop :=
  ContDiffOn ℝ 1 (q m) m.I ∧ xs ∈ m.I ∧
  (∀ x ∈ m.I, x < xs → 0 < deriv (q m) x) ∧ (∀ x ∈ m.I, xs < x → deriv (q m) x < 0) ∧
  Tendsto (fun x => q m x * deriv S.φ x / Sp m x) (upperEnd m.I) (𝓝 0) ∧
  (∀ x ∈ m.I, IntegrableOn (fun y => S.φ y * q m y * mp m y) (m.I ∩ Ioi x)) ∧
  ∃ x ∈ m.I, Lfun m S x < 0

/-- Assumption 5 (p. 24) with its points `θ*`, `z₂`: `I(z₂) = I(θ*)` (35) and
`J(z₂) − J(θ*) = c₂` (36), with `θ* < z₂` (pinned reading, see the proof of Lemma B.8). -/
def Assumption5 (m : Model) (S : Setting Ω) (c2 θ z2 : ℝ) : Prop :=
  θ ∈ m.I ∧ z2 ∈ m.I ∧ θ < z2 ∧ Ifun m S z2 = Ifun m S θ ∧ Jfun m S z2 - Jfun m S θ = c2

/-- `x̂` is the point of Lemma 2 (i): `x̂ ∈ I`, `I′ < 0 < J′` on `(a, x̂)` and `J′ < 0 < I′` on
`(x̂, b)`. -/
def IsLemma2Point (m : Model) (S : Setting Ω) (xh : ℝ) : Prop :=
  xh ∈ m.I ∧ (∀ x ∈ m.I, x < xh → deriv (Ifun m S) x < 0 ∧ 0 < deriv (Jfun m S) x) ∧
  (∀ x ∈ m.I, xh < x → 0 < deriv (Ifun m S) x ∧ deriv (Jfun m S) x < 0)

end InvestCommonGood.MixedTSSPE


