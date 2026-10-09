-- Prove2me | Definitions.Def_DurmusULA_StrongLC_Model
-- name    : DurmusULA_StrongLC_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:16:48.987432+00:00
-- url     : https://prove2.me/theorems/864aef58-13e4-41d6-9121-9811e76c27bd
-- title:
--   pp. 1–5, 13, 15, 28, 32 — total variation, π, the ULA kernel R_γ and laws δ_xQ^n_γ, L1, H3(M_s), F, G, ω, κ and the diffusion semigroups of (1) and (53)
-- statement:
--   This file fixes the objects of Durmus and Moulines' analysis of the unadjusted Langevin algorithm (ULA) on $\mathbb R^d$, with the Euclidean norm $\|\cdot\|$, inner product $\langle\cdot,\cdot\rangle$ and Lebesgue measure.
--
--   1. **Total variation** (Notations, p. 3). For finite Borel measures $\mu,\nu$,
--   $$\|\mu-\nu\|_{\mathrm{TV}}=\sup\Big\{\Big|\int f\,d\mu-\int f\,d\nu\Big| : f \text{ Borel},\ |f|\le 1\Big\}.$$
--   For probability measures this lies in $[0,2]$ and equals twice $\sup_A|\mu(A)-\nu(A)|$. The supremum is over a nonempty set ($f=0$) bounded by $\mu(\mathbb R^d)+\nu(\mathbb R^d)$.
--   2. **Target** (p. 1). For a potential $U:\mathbb R^d\to\mathbb R$, $\pi(dx)=e^{-U(x)}dx\big/\int e^{-U(y)}dy$.
--   3. **L1** (p. 3). $U$ is differentiable and there is $L\ge 0$ with $\|\nabla U(x)-\nabla U(y)\|\le L\|x-y\|$ for all $x,y$.
--   4. **H3($M_s$)** (p. 15). $U$ is convex, $M_s\ge0$, $m>0$, and $\langle\nabla U(x)-\nabla U(y),x-y\rangle\ge m\|x-y\|^2$ whenever $\|x-y\|\ge M_s$.
--   5. **Euler kernel and ULA laws** (pp. 2, 4). $R_\gamma(x,\cdot)=\mathcal N(x-\gamma\nabla U(x),2\gamma I_d)$, the law of $x-\gamma\nabla U(x)+\sqrt{2\gamma}Z$ with $Z$ standard Gaussian. For a step sequence $(\gamma_k)_{k\ge1}$, $\delta_xQ^0_\gamma=\delta_x$ and $\delta_xQ^{n+1}_\gamma=\delta_xQ^n_\gamma R_{\gamma_{n+1}}$, i.e. $Q^n_\gamma=R_{\gamma_1}\cdots R_{\gamma_n}$: the law of the $n$-th iterate of $X_{k+1}=X_k-\gamma_{k+1}\nabla U(X_k)+\sqrt{2\gamma_{k+1}}Z_{k+1}$ started at $x$.
--   6. **Partial sums** (5). $\Gamma_{n,p}=\sum_{k=n}^p\gamma_k$, which is $0$ when $p<n$.
--   7. **The functions $F$, $G$** ((7), (8)): $F(\lambda,a,c,\gamma,w)=\lambda^aw+c(-\lambda^\gamma\log\lambda)^{-1}$ and $G(\lambda,c,\gamma,w)=w+c(-\lambda^\gamma\log\lambda)^{-1}$.
--   8. **The function $\omega$** (29): $\omega(\varepsilon,R)=R^2/\{2\Phi^{-1}(1-\varepsilon/2)\}^2$, where $\Phi$ is the standard Gaussian distribution function and $\Phi^{-1}(u)=\inf\{z:\Phi(z)\ge u\}$ its quantile function.
--   9. **Rates.** $D(\varepsilon)=(1+e^{\tilde m_s\omega(\varepsilon,\tilde M_s)/2})(1+\tilde M_s)$ (63) and $\kappa_{36}=\exp\{(\tilde m_s/2)\log(1-\varepsilon)(\log D(\varepsilon)-\log(1-\varepsilon))^{-1}\}$ (Theorem 36); and the rate of Theorem 21,
--   $$\kappa_{21}=\exp\Big\{-\tfrac m2\log 2\,\Big[\log\big\{(1+e^{m\,\omega(1/2,\max(1,M_s))/4})(1+\max(1,M_s))\big\}+\log 2\Big]^{-1}\Big\}.$$
--   10. **Diffusion semigroups** (pp. 3–4, 28–29). A family $(P_t)_{t\ge0}$ of measures $P_t(x,\cdot)$ is *the transition semigroup of* $dX_t=b(X_t)dt+s\,dB^d_t$ if, on every probability space carrying a standard $d$-dimensional Brownian motion $B$, every strong solution started at $x$ has time-$t$ law $P_t(x,\cdot)$. The Langevin semigroup is the case $b=-\nabla U$, $s=\sqrt2$ (equation (1)); §5 uses $s=1$ (equation (53)). For an initial law $\mu_0$, $\mu_0P_t=\int P_t(y,\cdot)\,\mu_0(dy)$.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** The state space is the published `EthierKurtz.SDEState d`; Brownian motion and strong solutions are the published `EthierKurtz.IsStandardBrownian` and `EthierKurtz.SolvesBrownianSDE`, the diffusion matrix being $s$ times the flattened identity `idDiffusion d`. The normaliser of $\pi$ carries no integrability hypothesis: under L1 and H3 it is finite and positive. Steps are read from index $1$; $\gamma_0$ is unused. Real powers $\lambda^a$, $\kappa^t$ are `Real.rpow`.
-- source:
--   Durmus and Moulines, Non-asymptotic convergence analysis for the Unadjusted Langevin Algorithm, arXiv:1507.05021v3, p. 1, (1); p. 2, (2); p. 3, Notations and L1; p. 4, (5), R_γ, Q^n_γ; p. 5, (7), (8); p. 13, (29); p. 15, H3; pp. 28–29, (53); p. 32, (63); p. 33, Theorem 36; p. 16, Theorem 21

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SolvesBrownianSDE

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace DurmusULA.StrongLC

/-- Total variation norm `‖μ − ν‖_TV = sup { |∫ f dμ − ∫ f dν| : f Borel, |f| ≤ 1 }` (Notations, p. 3).
For probability measures it takes values in `[0, 2]`; it is twice `sup_A |μ(A) − ν(A)|`. -/
noncomputable def tvNorm {d : ℕ} (μ ν : Measure (EthierKurtz.SDEState d)) : ℝ :=
  sSup {r | ∃ f : EthierKurtz.SDEState d → ℝ, Measurable f ∧ (∀ x, |f x| ≤ 1) ∧
            r = |∫ x, f x ∂μ - ∫ x, f x ∂ν|}

/-- The target `π(dx) = e^{−U(x)} dx / ∫ e^{−U(y)} dy` (p. 1). -/
noncomputable def gibbs {d : ℕ} (U : EthierKurtz.SDEState d → ℝ) : Measure (EthierKurtz.SDEState d) :=
  (∫⁻ x, ENNReal.ofReal (Real.exp (-U x)))⁻¹ •
    volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x)))

/-- Assumption L1 (p. 3): `U` is differentiable with `L`-Lipschitz gradient, `L ≥ 0`
(continuity of `∇U` follows). -/
def L1 {d : ℕ} (U : EthierKurtz.SDEState d → ℝ) (L : ℝ) : Prop :=
  0 ≤ L ∧ Differentiable ℝ U ∧ ∀ x y, ‖gradient U x - gradient U y‖ ≤ L * ‖x - y‖

/-- Assumption H3(M_s) (p. 15): `U` convex, `M_s ≥ 0`, `m > 0`, and
`⟨∇U(x) − ∇U(y), x − y⟩ ≥ m‖x − y‖²` whenever `‖x − y‖ ≥ M_s`. -/
def H3 {d : ℕ} (U : EthierKurtz.SDEState d → ℝ) (m Ms : ℝ) : Prop :=
  ConvexOn ℝ Set.univ U ∧ 0 ≤ Ms ∧ 0 < m ∧
    ∀ x y, Ms ≤ ‖x - y‖ → m * ‖x - y‖ ^ 2 ≤ ⟪gradient U x - gradient U y, x - y⟫

/-- The Euler kernel `R_γ(x, ·) = N(x − γ∇U(x), 2γ I_d)` (p. 4), as the image of the standard
Gaussian under `z ↦ x − γ∇U(x) + √(2γ) z`. -/
noncomputable def eulerStep {d : ℕ} (U : EthierKurtz.SDEState d → ℝ) (γ : ℝ)
    (x : EthierKurtz.SDEState d) : Measure (EthierKurtz.SDEState d) :=
  (stdGaussian (EthierKurtz.SDEState d)).map
    (fun z => x - γ • gradient U x + Real.sqrt (2 * γ) • z)

/-- The ULA laws `δ_x Q^n_γ`, `Q^n_γ = R_{γ_1} ⋯ R_{γ_n}`, `Q^0_γ = Id` (p. 4). The step sequence is
read from index 1; `γ 0` is unused. -/
noncomputable def ulaLaw {d : ℕ} (U : EthierKurtz.SDEState d → ℝ) (γ : ℕ → ℝ)
    (x : EthierKurtz.SDEState d) : ℕ → Measure (EthierKurtz.SDEState d)
  | 0 => Measure.dirac x
  | n + 1 => (ulaLaw U γ x n).bind (eulerStep U (γ (n + 1)))

/-- `Γ_{n,p} = ∑_{k=n}^{p} γ_k` (5), equal to `0` when `p < n` (convention p. 3). -/
def Gam (γ : ℕ → ℝ) (n p : ℕ) : ℝ := ∑ k ∈ Finset.Icc n p, γ k

/-- `F(λ, a, c, γ, w) = λ^a w + c(−λ^γ log λ)^{−1}` (7). -/
noncomputable def F (lam a c γ w : ℝ) : ℝ :=
  lam ^ a * w + c * (-(lam ^ γ) * Real.log lam)⁻¹

/-- `G(λ, c, γ, w) = w + c(−λ^γ log λ)^{−1}` (8). -/
noncomputable def G (lam c γ w : ℝ) : ℝ :=
  w + c * (-(lam ^ γ) * Real.log lam)⁻¹

/-- The standard Gaussian cumulative distribution function `Φ`. -/
noncomputable def Phi (z : ℝ) : ℝ := cdf (gaussianReal 0 1) z

/-- The standard Gaussian quantile `Φ^{−1}(u) = inf { z : u ≤ Φ(z) }`; for `u ∈ (0, 1)` it is the
unique `z` with `Φ(z) = u`. -/
noncomputable def gaussQuantile (u : ℝ) : ℝ := sInf {z : ℝ | u ≤ Phi z}

/-- `ω(ε, R) = R² / {2Φ^{−1}(1 − ε/2)}²` (29). -/
noncomputable def omega (ε R : ℝ) : ℝ := R ^ 2 / (2 * gaussQuantile (1 - ε / 2)) ^ 2

/-- `D(ε) = (1 + e^{m̃_s ω(ε, M̃_s)/2})(1 + M̃_s)` (63). -/
noncomputable def D63 (mt Mt ε : ℝ) : ℝ :=
  (1 + Real.exp (mt * omega ε Mt / 2)) * (1 + Mt)

/-- The rate of Theorem 36: `log κ = (m̃_s/2) log(1 − ε) (log D(ε) − log(1 − ε))^{−1}`. -/
noncomputable def kappa36 (mt Mt ε : ℝ) : ℝ :=
  Real.exp (mt / 2 * Real.log (1 - ε) / (Real.log (D63 mt Mt ε) - Real.log (1 - ε)))

/-- The rate of Theorem 21:
`log κ = −(m/2) log 2 [log{(1 + e^{mω(1/2, max(1,M_s))/4})(1 + max(1, M_s))} + log 2]^{−1}`. -/
noncomputable def kappa21 (m Ms : ℝ) : ℝ :=
  Real.exp (-(m / 2) * Real.log 2 /
    (Real.log ((1 + Real.exp (m * omega (1 / 2) (max 1 Ms) / 4)) * (1 + max 1 Ms)) + Real.log 2))

/-- The identity `d × d` matrix, flattened as an element of `SDEDiffusion d`. -/
noncomputable def idDiffusion (d : ℕ) : EthierKurtz.SDEDiffusion d :=
  WithLp.toLp 2 (fun p : Fin d × Fin d => if p.1 = p.2 then (1 : ℝ) else 0)

/-- `P` is the transition semigroup of `dX_t = b(X_t) dt + s dB^d_t`: on every probability space, every
strong solution started at `x` and driven by a standard `d`-dimensional Brownian motion has time-`t`
law `P t x`. -/
def IsDiffusionSemigroup {d : ℕ} (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d) (s : ℝ)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d)) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (W X : ℝ≥0 → Ω → EthierKurtz.SDEState d) (x : EthierKurtz.SDEState d),
    EthierKurtz.IsStandardBrownian Pr W →
    EthierKurtz.SolvesBrownianSDE Pr (fun _ => s • idDiffusion d) (fun p => b p.2) W (fun _ => x) X →
    ∀ t, Pr.map (X t) = P t x

end DurmusULA.StrongLC


