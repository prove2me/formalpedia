-- Prove2me | Definitions.Def_SGHMCOpt_Euler_Constants
-- name    : SGHMCOpt_Euler_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:38.000982+00:00
-- url     : https://prove2.me/theorems/53c13b0d-e2d9-44d5-abd6-fef85c95986c
-- title:
--   Table 1, p. 13 — the explicit constants of SGHMC1 and the error terms 𝒥̄₀, 𝒥₁, 𝒥₂, 𝒥₃ (3.1)–(3.7), conditions (3.3), (3.4), (A.15)
-- statement:
--   This file collects the explicit constants of Gao, Gürbüzbalaban and Zhu's analysis of SGHMC1 (Table 1, p. 13) and the error terms of Theorem 2 and Corollary 4.
--
--   The scalar data are $m, M, b, A_0, B, \delta$ (Assumption 1), the friction $\gamma$, the inverse temperature $\beta$, the Lyapunov parameter $\lambda$, the drift constant $A$ of (2.2) and the pair $(\alpha_1,\Lambda)$ of (A.15); $d$ is the dimension, $n$ the sample size. Two further real arguments stand for integrals against the initial law $\mu_0$: $\mathsf V=\int\mathcal V\,d\mu_0$ and $\mathsf E=\int e^{\alpha\mathcal V/4}d\mu_0$, and $m_2=\int(\|x\|^2+\|v\|^2)\,d\mu_0$.
--
--   1. **Standing conditions.** $\gamma,\beta>0$ and $0<\lambda<\min\{1/4,\ m/(M+\gamma^2/2)\}$; (A.15): $\alpha_1>0$, $\Lambda=\tfrac{12}{5}(1+2\alpha_1+2\alpha_1^2)(d+A)M\gamma^{-2}\lambda^{-1}(1-2\lambda)^{-1}$ and $\alpha_1=(1+\Lambda^{-1})M\gamma^{-2}$.
--   2. **Table 1.** $\alpha=\lambda(1-2\lambda)/12$, $\alpha_0=\alpha(1-2\lambda)\beta\gamma^2/(64+32\gamma^2)$,
--   $$K_1=\max\Big\{\frac{32M^2(\frac12+\gamma+\delta)}{(1-2\lambda)\beta\gamma^2},\ \frac{8(\frac12M+\frac14\gamma^2-\frac14\gamma^2\lambda+\gamma)}{\beta(1-2\lambda)}\Big\},\qquad K_2=B^2(1+2\gamma+2\delta),$$
--   $C^d_x=(\mathsf V+4(d+A)/\lambda)/(\tfrac18(1-2\lambda)\beta\gamma^2)$, $C^d_v=(\mathsf V+4(d+A)/\lambda)/(\tfrac\beta4(1-2\lambda))$, $\sigma=\sqrt{C^d_x}$,
--   $\hat\gamma=\frac{2\sqrt2}{\sqrt{\alpha_0}}\big(\frac52+\log(\mathsf E+\frac14e^{\alpha(d+A)/(3\lambda)}\alpha\gamma(d+A))\big)^{1/2}$,
--   $C_0=\hat\gamma\,(c+\sqrt c)^{1/2}$ with $c=(M^2C^d_x+B^2)\beta/\gamma$, $C_2=(2\gamma^2C^d_v+(4+2\delta)(M^2C^d_x+B^2)+2\gamma\beta^{-1})^{1/2}$, $C_1=\hat\gamma\,(a+\sqrt a)^{1/2}$ with $a=(M^2\beta/\gamma+\beta\gamma/2)C_2^2$,
--   $\mu_*=\frac{\gamma}{768}\min\{\lambda M\gamma^{-2},\Lambda^{1/2}e^{-\Lambda}M\gamma^{-2},\Lambda^{1/2}e^{-\Lambda}\}$, $\varepsilon_1=4\gamma^{-1}\mu_*/(d+A)$, $R_1=4(6/5)^{1/2}(1+2\alpha_1+2\alpha_1^2)^{1/2}(d+A)^{1/2}\beta^{-1/2}\gamma^{-1}(\lambda-2\lambda^2)^{-1/2}$,
--   $C=\frac{(1+\gamma)\sqrt2e^{1+\Lambda/2}}{\min\{1,\alpha_1\}}\sqrt{\max\{1,4(1+2\alpha_1+2\alpha_1^2)(d+A)\beta^{-1}\gamma^{-1}\mu_*^{-1}/\min\{1,R_1\}\}}$, and
--   $$\overline{\mathcal H}_\rho(\mu_0)=R_1+R_1\varepsilon_1\max\{\beta M+\tfrac12\beta\gamma^2,\tfrac34\beta\}m_2+R_1\varepsilon_1(\beta M+\tfrac12\beta\gamma^2)\frac{b+d/\beta}{m}+R_1\varepsilon_1\tfrac34d+2R_1\varepsilon_1\Big(\beta A_0+\frac{\beta B^2}{2M}\Big).$$
--   3. **Error terms.** $\mathcal J_0=(M\sigma+B)\,C\sqrt H\,\varepsilon$ (with $H=\mathcal H_\rho(\mu_0,\pi_z)$ this is (3.1), with $H=\overline{\mathcal H}_\rho(\mu_0)$ it is $\overline{\mathcal J}_0$ of (3.6)),
--   $$\mathcal J_1(\varepsilon)=(M\sigma+B)\Big(\Big(\frac{C_0}{\mu_*^{3/2}}(\log\tfrac1\varepsilon)^{3/2}\delta^{1/4}+\frac{C_1}{\mu_*^{3/2}}\varepsilon\Big)\sqrt{\log(\mu_*^{-1}\log\varepsilon^{-1})}+\frac{C_2}{\mu_*}\frac{\varepsilon^2}{(\log(1/\varepsilon))^2}\Big),$$
--   $\mathcal J_2=\frac d{2\beta}\log\big(\frac{eM}{m}(\frac{b\beta}d+1)\big)$, $c_{LS}=\frac{2m^2+8M^2}{m^2M\beta}+\frac1{\lambda_0}\big(\frac{6M(d+\beta)}m+2\big)$ and $\mathcal J_3(n)=\frac{4\beta c_{LS}}n\big(\frac{M^2}m(b+d/\beta)+B^2\big)$.
--   4. **Step conditions.** Lemma 16(ii): $0<\eta\le\min\{(\gamma/K_2)(d/\beta+A/\beta),\gamma\lambda/(2K_1),2/(\gamma\lambda)\}$. (3.3): additionally $\eta\le(\varepsilon/(\log(1/\varepsilon))^{3/2})^4$ and $\eta\le1$. (3.4): $k\eta=\mu_*^{-1}\log(1/\varepsilon)\ge e$.
--
--   These are the quantities in which every bound of the mission is stated; each is an explicit closed form in the problem data.
--
--   **Formalization Note** Two constants differ from the printed Table 1, in the direction that enlarges the bounds, because the proofs give these values. $C_1$: the proof of Lemma 18 (pp. 56–57) gives $a=(M^2\beta/\gamma+\beta\gamma/2)C_2^2$, whereas Table 1 prints $\beta M^2C_2^2/(2\gamma)$ and Lemma 18 prints an $\eta$-dependent version. $\overline{\mathcal H}_\rho(\mu_0)$: the proof of Lemma 20 (p. 58) gives the coefficient $\beta M+\frac12\beta\gamma^2$ where (A.18) prints $M+\frac12\beta\gamma^2$. The entry $(\gamma/K_2)(d/\beta+A/\beta)$ of the step condition is written $K_2\eta\le\gamma(d/\beta+A/\beta)$, so that $B=0$ (hence $K_2=0$) imposes no constraint, as the reading $\gamma/0=+\infty$ intends. $c_{LS}$ is evaluated at a positive lower bound $\lambda_0$ of the spectral gap $\lambda_*$ (see `HasPoincare`); $\mathcal J_3$ increases in $c_{LS}$, so this is the printed bound with $\lambda_*$ replaced by $\lambda_0\le\lambda_*$. $C^c_x,C^c_v$ of (A.1)–(A.2) only enter $\sigma$, where Table 1 itself records $\sigma=\sqrt{C^d_x}$; they are not defined.
-- source:
--   arXiv:1809.04618v4, Table 1, p. 13; (A.3)–(A.18), pp. 37–40; (3.1)–(3.7), pp. 11–12; (3.3), (3.4), p. 11; (A.15), p. 39; corrected C1 from the proof of Lemma 18, pp. 56–57; corrected H̄ρ coefficient from the proof of Lemma 20, p. 58

import Mathlib

namespace SGHMCOpt.Euler

/-- The scalar parameters of the paper: the constants `m, M, b, A₀, B, δ` of Assumption 1
(pp. 9–10), the friction `γ`, the inverse temperature `β`, the Lyapunov parameter `λ` of (2.1),
the drift constant `A` of (2.2), and the pair `(α₁, Λ)` of (A.15). The relations between them
are hypotheses (`ParamCond`, `FixedPt`, and the model predicates), not part of this record. -/
structure Params where
  m : ℝ
  M : ℝ
  b : ℝ
  A0 : ℝ
  B : ℝ
  δ : ℝ
  γ : ℝ
  β : ℝ
  lam : ℝ
  A : ℝ
  α1 : ℝ
  Λ : ℝ

/-- Standing parameter conditions (p. 10): `γ, β > 0` and `0 < λ < min(1/4, m/(M + γ²/2))`. -/
def ParamCond (p : Params) : Prop :=
  0 < p.γ ∧ 0 < p.β ∧ 0 < p.lam ∧ p.lam < min (1 / 4) (p.m / (p.M + p.γ ^ 2 / 2))

/-- (A.15), p. 13 / p. 39: `α₁ > 0`, `Λ = (12/5)(1 + 2α₁ + 2α₁²)(d + A)Mγ⁻²λ⁻¹(1 − 2λ)⁻¹`
and `α₁ = (1 + Λ⁻¹)Mγ⁻²`. -/
def FixedPt (p : Params) (d : ℕ) : Prop :=
  0 < p.α1 ∧
  p.Λ = 12 / 5 * (1 + 2 * p.α1 + 2 * p.α1 ^ 2) * ((d : ℝ) + p.A) * p.M * (p.γ ^ 2)⁻¹ *
      p.lam⁻¹ * (1 - 2 * p.lam)⁻¹ ∧
  p.α1 = (1 + p.Λ⁻¹) * p.M * (p.γ ^ 2)⁻¹

/-- `α = λ(1 − 2λ)/12` (A.7). -/
noncomputable def alpha (p : Params) : ℝ := p.lam * (1 - 2 * p.lam) / 12

/-- `K₁` (A.3). -/
noncomputable def K1 (p : Params) : ℝ :=
  max (32 * p.M ^ 2 * (1 / 2 + p.γ + p.δ) / ((1 - 2 * p.lam) * p.β * p.γ ^ 2))
    (8 * (1 / 2 * p.M + 1 / 4 * p.γ ^ 2 - 1 / 4 * p.γ ^ 2 * p.lam + p.γ) / (p.β * (1 - 2 * p.lam)))

/-- `K₂ = B²(1 + 2γ + 2δ)` (A.4). -/
noncomputable def K2 (p : Params) : ℝ := p.B ^ 2 * (1 + 2 * p.γ + 2 * p.δ)

/-- `C^d_x` (A.5); `Vint` stands for `∫ 𝒱 dμ₀`. -/
noncomputable def Cxd (p : Params) (d : ℕ) (Vint : ℝ) : ℝ :=
  (Vint + 4 * ((d : ℝ) + p.A) / p.lam) / (1 / 8 * (1 - 2 * p.lam) * p.β * p.γ ^ 2)

/-- `C^d_v` (A.6); `Vint` stands for `∫ 𝒱 dμ₀`. -/
noncomputable def Cvd (p : Params) (d : ℕ) (Vint : ℝ) : ℝ :=
  (Vint + 4 * ((d : ℝ) + p.A) / p.lam) / (p.β / 4 * (1 - 2 * p.lam))

/-- `σ = √(C^d_x)` (A.20). -/
noncomputable def sigma (p : Params) (d : ℕ) (Vint : ℝ) : ℝ := Real.sqrt (Cxd p d Vint)

/-- `α₀ = α(1 − 2λ)βγ²/(64 + 32γ²)` (A.7). -/
noncomputable def alpha0 (p : Params) : ℝ :=
  alpha p * (1 - 2 * p.lam) * p.β * p.γ ^ 2 / (64 + 32 * p.γ ^ 2)

/-- `γ̂` (A.11); `Eint` stands for `∫ e^{α𝒱/4} dμ₀`. -/
noncomputable def gammaHat (p : Params) (d : ℕ) (Eint : ℝ) : ℝ :=
  2 * Real.sqrt 2 / Real.sqrt (alpha0 p) *
    Real.sqrt (5 / 2 + Real.log (Eint + 1 / 4 * Real.exp (alpha p * ((d : ℝ) + p.A) / (3 * p.lam)) *
      alpha p * p.γ * ((d : ℝ) + p.A)))

/-- `C₀` (A.8). -/
noncomputable def C0 (p : Params) (d : ℕ) (Vint Eint : ℝ) : ℝ :=
  gammaHat p d Eint *
    Real.sqrt ((p.M ^ 2 * Cxd p d Vint + p.B ^ 2) * p.β / p.γ +
      Real.sqrt ((p.M ^ 2 * Cxd p d Vint + p.B ^ 2) * p.β / p.γ))

/-- `C₂` (A.10). -/
noncomputable def C2 (p : Params) (d : ℕ) (Vint : ℝ) : ℝ :=
  Real.sqrt (2 * p.γ ^ 2 * Cvd p d Vint + (4 + 2 * p.δ) * (p.M ^ 2 * Cxd p d Vint + p.B ^ 2) +
    2 * p.γ * p.β⁻¹)

/-- `C₁` (A.9), **corrected**: `C₁ = γ̂ (a + √a)^{1/2}` with `a = (M²β/γ + βγ/2)(C₂)²`, the
constant that the proof of Lemma 18 (pp. 56–57) yields. Table 1 prints `a = βM²(C₂)²/(2γ)`. -/
noncomputable def C1 (p : Params) (d : ℕ) (Vint Eint : ℝ) : ℝ :=
  gammaHat p d Eint *
    Real.sqrt ((p.M ^ 2 * p.β / p.γ + p.β * p.γ / 2) * C2 p d Vint ^ 2 +
      Real.sqrt ((p.M ^ 2 * p.β / p.γ + p.β * p.γ / 2) * C2 p d Vint ^ 2))

/-- `μ_* = (γ/768) min{λMγ⁻², Λ^{1/2}e^{−Λ}Mγ⁻², Λ^{1/2}e^{−Λ}}` (A.13). -/
noncomputable def muStar (p : Params) : ℝ :=
  p.γ / 768 * min (min (p.lam * p.M * (p.γ ^ 2)⁻¹)
    (Real.sqrt p.Λ * Real.exp (-p.Λ) * p.M * (p.γ ^ 2)⁻¹)) (Real.sqrt p.Λ * Real.exp (-p.Λ))

/-- `ε₁ = 4γ⁻¹μ_*/(d + A)` (A.16). -/
noncomputable def eps1 (p : Params) (d : ℕ) : ℝ := 4 * p.γ⁻¹ * muStar p / ((d : ℝ) + p.A)

/-- `R₁ = 4·(6/5)^{1/2}(1 + 2α₁ + 2α₁²)^{1/2}(d + A)^{1/2}β^{−1/2}γ⁻¹(λ − 2λ²)^{−1/2}` (A.17). -/
noncomputable def R1 (p : Params) (d : ℕ) : ℝ :=
  4 * Real.sqrt (6 / 5) * Real.sqrt (1 + 2 * p.α1 + 2 * p.α1 ^ 2) * Real.sqrt ((d : ℝ) + p.A) /
    Real.sqrt p.β * p.γ⁻¹ / Real.sqrt (p.lam - 2 * p.lam ^ 2)

/-- `C` (A.14). -/
noncomputable def Ccoef (p : Params) (d : ℕ) : ℝ :=
  (1 + p.γ) * Real.sqrt 2 * Real.exp (1 + p.Λ / 2) / min 1 p.α1 *
    Real.sqrt (max 1 (4 * (1 + 2 * p.α1 + 2 * p.α1 ^ 2) * ((d : ℝ) + p.A) * p.β⁻¹ * p.γ⁻¹ *
      (muStar p)⁻¹ / min 1 (R1 p d)))

/-- `H̄_ρ(μ₀)` (A.18), **corrected**: the coefficient `M + βγ²/2` printed twice in (A.18) is
replaced by `βM + βγ²/2`, the coefficient derived in the proof of Lemma 20 (p. 58).
`m2` stands for `‖(x, v)‖²_{L²(μ₀)} = ∫ (‖x‖² + ‖v‖²) dμ₀`. -/
noncomputable def Hbar (p : Params) (d : ℕ) (m2 : ℝ) : ℝ :=
  R1 p d + R1 p d * eps1 p d * max (p.β * p.M + 1 / 2 * p.β * p.γ ^ 2) (3 / 4 * p.β) * m2 +
    R1 p d * eps1 p d * (p.β * p.M + 1 / 2 * p.β * p.γ ^ 2) * (p.b + (d : ℝ) / p.β) / p.m +
    R1 p d * eps1 p d * (3 / 4) * (d : ℝ) +
    2 * R1 p d * eps1 p d * (p.β * p.A0 + p.β * p.B ^ 2 / (2 * p.M))

/-- `(Mσ + B)·C·√H·ε`: this is `𝒥₀(z, ε)` of (3.1) when `H = ℋ_ρ(μ₀, π_z)`, and `𝒥̄₀(ε)` of (3.6)
when `H = H̄_ρ(μ₀)`. -/
noncomputable def J0 (p : Params) (d : ℕ) (Vint H ε : ℝ) : ℝ :=
  (p.M * sigma p d Vint + p.B) * Ccoef p d * Real.sqrt H * ε

/-- `𝒥̄₀(ε) = (Mσ + B)·C·√(H̄_ρ(μ₀))·ε` (3.6). -/
noncomputable def J0bar (p : Params) (d : ℕ) (Vint m2 ε : ℝ) : ℝ :=
  J0 p d Vint (Hbar p d m2) ε

/-- `𝒥₁(ε)` (3.2). -/
noncomputable def J1 (p : Params) (d : ℕ) (Vint Eint ε : ℝ) : ℝ :=
  (p.M * sigma p d Vint + p.B) *
    ((C0 p d Vint Eint / muStar p ^ ((3 : ℝ) / 2) * Real.log (1 / ε) ^ ((3 : ℝ) / 2) *
          p.δ ^ ((1 : ℝ) / 4) +
        C1 p d Vint Eint / muStar p ^ ((3 : ℝ) / 2) * ε) *
        Real.sqrt (Real.log ((muStar p)⁻¹ * Real.log ε⁻¹)) +
      C2 p d Vint / muStar p * (ε ^ 2 / Real.log (1 / ε) ^ 2))

/-- `𝒥₂ = (d/(2β)) log((eM/m)(bβ/d + 1))` (3.5). -/
noncomputable def J2 (p : Params) (d : ℕ) : ℝ :=
  (d : ℝ) / (2 * p.β) * Real.log (Real.exp 1 * p.M / p.m * (p.b * p.β / (d : ℝ) + 1))

/-- The printed bound on `c_LS` (p. 12), with a lower bound `λ₀ > 0` of the uniform spectral gap
`λ_*` in place of `λ_*`: `(2m² + 8M²)/(m²Mβ) + λ₀⁻¹(6M(d + β)/m + 2)`. -/
noncomputable def cLS (p : Params) (d : ℕ) (lam0 : ℝ) : ℝ :=
  (2 * p.m ^ 2 + 8 * p.M ^ 2) / (p.m ^ 2 * p.M * p.β) +
    1 / lam0 * (6 * p.M * ((d : ℝ) + p.β) / p.m + 2)

/-- `𝒥₃(n) = (4βc_LS/n)((M²/m)(b + d/β) + B²)` (3.7), with `c_LS` as in `cLS`. -/
noncomputable def J3 (p : Params) (d : ℕ) (lam0 : ℝ) (n : ℕ) : ℝ :=
  4 * p.β * cLS p d lam0 / (n : ℝ) * (p.M ^ 2 / p.m * (p.b + (d : ℝ) / p.β) + p.B ^ 2)

/-- The step-size condition of Lemma 16(ii) (p. 37):
`0 < η ≤ min{(γ/K₂)(d/β + A/β), γλ/(2K₁), 2/(γλ)}`. The entry `(γ/K₂)(d/β + A/β)` is written
`K₂ η ≤ γ(d/β + A/β)`, which is the same condition when `K₂ > 0` and imposes nothing when
`K₂ = 0` (i.e. `B = 0`), matching the reading `γ/0 = +∞`. -/
def StepCondL16 (p : Params) (d : ℕ) (η : ℝ) : Prop :=
  0 < η ∧ K2 p * η ≤ p.γ * ((d : ℝ) / p.β + p.A / p.β) ∧ η ≤ p.γ * p.lam / (2 * K1 p) ∧
    η ≤ 2 / (p.γ * p.lam)

/-- Condition (3.3), p. 11:
`η ≤ min{(ε/(log(1/ε))^{3/2})⁴, 1, (γ/K₂)(d/β + A/β), γλ/(2K₁), 2/(γλ)}`, together with `η > 0`
(which (3.4) forces anyway). -/
def StepCond (p : Params) (d : ℕ) (ε η : ℝ) : Prop :=
  η ≤ (ε / Real.log (1 / ε) ^ ((3 : ℝ) / 2)) ^ 4 ∧ η ≤ 1 ∧ StepCondL16 p d η

/-- Condition (3.4), p. 11: `kη = (1/μ_*) log(1/ε) ≥ e`. -/
def KCond (p : Params) (ε η : ℝ) (k : ℕ) : Prop :=
  (k : ℝ) * η = 1 / muStar p * Real.log (1 / ε) ∧ Real.exp 1 ≤ (k : ℝ) * η

end SGHMCOpt.Euler


