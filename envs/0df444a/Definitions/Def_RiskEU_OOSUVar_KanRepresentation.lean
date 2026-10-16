-- Prove2me | Definitions.Def_RiskEU_OOSUVar_KanRepresentation
-- name    : RiskEU_OOSUVar_KanRepresentation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:12.366263+00:00
-- url     : https://prove2.me/theorems/7689e525-93db-4724-8536-8304f0ace014
-- title:
--   Kan et al. (2022b, Proposition 1) as restated, pp. IA35–IA36 — the twelve auxiliary variables, their laws, y₁, y₂ (IA45)–(IA46), and the right-hand sides of (IA47)–(IA48)
-- statement:
--   This file sets up the auxiliary random variables of the stochastic representation of Kan, Wang and Zhou (2022b, Proposition 1), as restated by Lassance, Martín-Utrera and Simaan on pp. IA35–IA36.
--
--   The chi-squared law $\chi^2_k$ is the law of $\sum_{j=1}^k g_j^2$ for independent standard normals $g_1,\dots,g_k$; for $k=0$ it is the point mass at $0$. Given $N$, $T$ and $\psi^2\ge 0$, the twelve auxiliary variables have the laws
--
--   $$z_2\sim\mathcal N(\sqrt T\psi,1),\ u_0\sim\chi^2_{N-2},\ v_2\sim\chi^2_{T-N+1},\ w_1\sim\chi^2_{T-N+3},\ w_2\sim\chi^2_{T-N+2},\ s_1\sim\chi^2_{N-4},\ s_2\sim\chi^2_{N-3},$$
--
--   and $x_{11},x_{21},a,b,c\sim\mathcal N(0,1)$. A *Kan family* is a family of twelve mutually independent real random variables with these laws.
--
--   Following footnote 6 (p. IA36), $x_{11}$ and $x_{21}$ are replaced by $0$ when $N=2$, and $c$ by $0$ when $N\le 3$. With these conventions,
--
--   $$y_1=\frac{x_{11}}{\sqrt{w_1}}+\frac{b\,x_{21}}{\sqrt{w_1w_2}}+\frac{a\,x_{21}}{\sqrt{v_2w_2}},\qquad y_2=\frac{c}{\sqrt{w_1}}+\frac{b\sqrt{s_2}}{\sqrt{w_1w_2}}+\frac{a\sqrt{s_2}}{\sqrt{v_2w_2}}$$
--
--   ((IA45)–(IA46)). For a market with constants $\mu_g,\sigma_g^2,\psi^2$ and risk aversion $\gamma$ (with $\sigma_g=\sqrt{\sigma_g^2}$, $\psi=\sqrt{\psi^2}$) and an intensity $\kappa$, the two representing expressions are the right-hand sides of (IA47) and (IA48):
--
--   $$\mu_g+\frac{\sigma_g\psi\sqrt{v_2}}{\sqrt{z_2^2+u_0}}\Big(\frac{\sqrt{u_0}\,y_1}{\sqrt{v_2}}+\frac{a z_2}{v_2}\Big)+\frac{\kappa\sqrt T\psi}{\gamma v_2}\Big(\frac{x_{21}\sqrt{u_0}}{\sqrt{w_2}}+z_2\Big),$$
--
--   $$\sigma_g^2\Big(1+y_1^2+y_2^2+\frac{s_1}{w_1}+\frac{a^2}{v_2}\Big)+\frac{\kappa^2T(z_2^2+u_0)}{\gamma^2v_2^2}\Big(1+\frac{x_{21}^2+s_2}{w_2}\Big)+\frac{2\kappa\sqrt T\sigma_g\sqrt{z_2^2+u_0}}{\gamma v_2}\Big(\frac{a}{\sqrt{v_2}}+\frac{x_{21}y_1}{\sqrt{w_2}}+\frac{\sqrt{s_2}\,y_2}{\sqrt{w_2}}\Big).$$
--
--   **Formalization Note.** The twelve variables are indexed by an inductive type `KanVar`. Degrees of freedom such as $N-2$ use natural-number subtraction, so a negative count becomes $0$ and the corresponding $\chi^2$ variable is identically $0$; this realises footnote 6 for $u_0,s_1,s_2$. The normal variables $x_{11},x_{21}$ are multiplied by $\mathbf 1[N\ge3]$ and $c$ by $\mathbf 1[N\ge4]$. Divisions use Lean's convention $x/0=0$; the denominators $v_2,w_1,w_2,z_2^2+u_0$ are almost surely positive, so this does not affect the statements.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Section IA.10, proof of Proposition 1, Kan et al. (2022b, Proposition 1) as restated, (IA45)–(IA48) and footnote 6, pp. IA35–IA36

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory

/-- The chi-squared law χ²_k with `k` degrees of freedom: the law of Σ_{j<k} g_j² for `k`
independent standard normals g_j. For `k = 0` it is the point mass at `0`. -/
noncomputable def chiSq (k : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun g => ∑ j, g j ^ 2)

/-- Labels of the twelve auxiliary random variables of Kan et al. (2022b, Proposition 1), as
restated on pp. IA35–IA36: z₂, u₀, v₂, w₁, w₂, s₁, s₂, x₁₁, x₂₁, a, b, c. -/
inductive KanVar
  | z2 | u0 | v2 | w1 | w2 | s1 | s2 | x11 | x21 | a | b | c
  deriving DecidableEq

/-- The law of each auxiliary variable (p. IA35): z₂ ∼ 𝒩(√T ψ, 1), u₀ ∼ χ²_{N−2},
v₂ ∼ χ²_{T−N+1}, w₁ ∼ χ²_{T−N+3}, w₂ ∼ χ²_{T−N+2}, s₁ ∼ χ²_{N−4}, s₂ ∼ χ²_{N−3}, and
x₁₁, x₂₁, a, b, c ∼ 𝒩(0, 1). Degrees of freedom use natural-number subtraction, so a negative
count is `0` and the variable is identically zero (footnote 6, p. IA36). -/
noncomputable def kanLaw (N T : ℕ) (psi2 : ℝ) : KanVar → Measure ℝ
  | .z2 => gaussianReal (Real.sqrt T * Real.sqrt psi2) 1
  | .u0 => chiSq (N - 2)
  | .v2 => chiSq (T - N + 1)
  | .w1 => chiSq (T - N + 3)
  | .w2 => chiSq (T - N + 2)
  | .s1 => chiSq (N - 4)
  | .s2 => chiSq (N - 3)
  | .x11 => gaussianReal 0 1
  | .x21 => gaussianReal 0 1
  | .a => gaussianReal 0 1
  | .b => gaussianReal 0 1
  | .c => gaussianReal 0 1

/-- A family `X` of auxiliary variables on `(Ω', Q)` that are mutually independent with the laws
`kanLaw N T psi2`. -/
def IsKanFamily (N T : ℕ) (psi2 : ℝ) {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω')
    (X : KanVar → Ω' → ℝ) : Prop :=
  iIndepFun X Q ∧ ∀ i, HasLaw (X i) (kanLaw N T psi2 i) Q

namespace KanVar

variable (N : ℕ) (v : KanVar → ℝ)

/-- x₁₁ after footnote 6 (p. IA36): set to zero when `N = 2`. -/
noncomputable def x11' : ℝ := if 3 ≤ N then v .x11 else 0

/-- x₂₁ after footnote 6 (p. IA36): set to zero when `N = 2`. -/
noncomputable def x21' : ℝ := if 3 ≤ N then v .x21 else 0

/-- c after footnote 6 (p. IA36): set to zero when `N = 2` or `N = 3`. -/
noncomputable def c' : ℝ := if 4 ≤ N then v .c else 0

/-- y₁ = x₁₁/√w₁ + b x₂₁/√(w₁w₂) + a x₂₁/√(v₂w₂), eq. (IA45). -/
noncomputable def y1 : ℝ :=
  x11' N v / Real.sqrt (v .w1) + v .b * x21' N v / Real.sqrt (v .w1 * v .w2) +
    v .a * x21' N v / Real.sqrt (v .v2 * v .w2)

/-- y₂ = c/√w₁ + b√s₂/√(w₁w₂) + a√s₂/√(v₂w₂), eq. (IA46). -/
noncomputable def y2 : ℝ :=
  c' N v / Real.sqrt (v .w1) + v .b * Real.sqrt (v .s2) / Real.sqrt (v .w1 * v .w2) +
    v .a * Real.sqrt (v .s2) / Real.sqrt (v .v2 * v .w2)

end KanVar

namespace Market

open KanVar

variable {N : ℕ} (M : Market N)

/-- The right-hand side of (IA47), the representation of ŵ*(κ)ᵀµ:
µ_g + (σ_g ψ √v₂/√(z₂² + u₀)) (√u₀ y₁/√v₂ + a z₂/v₂) + (κ√T ψ/(γ v₂)) (x₂₁√u₀/√w₂ + z₂),
with σ_g = √σ²_g and ψ = √ψ² computed from the market. -/
noncomputable def kanMeanRep (T : ℕ) (κ : ℝ) (v : KanVar → ℝ) : ℝ :=
  M.muG +
    Real.sqrt M.sigmaG2 * Real.sqrt M.psi2 * Real.sqrt (v .v2) /
        Real.sqrt (v .z2 ^ 2 + v .u0) *
      (Real.sqrt (v .u0) * y1 N v / Real.sqrt (v .v2) + v .a * v .z2 / v .v2) +
    κ * Real.sqrt T * Real.sqrt M.psi2 / (M.gamma * v .v2) *
      (x21' N v * Real.sqrt (v .u0) / Real.sqrt (v .w2) + v .z2)

/-- The right-hand side of (IA48), the representation of ŵ*(κ)ᵀΣŵ*(κ):
σ²_g (1 + y₁² + y₂² + s₁/w₁ + a²/v₂) + (κ²T(z₂² + u₀)/(γ²v₂²)) (1 + (x₂₁² + s₂)/w₂)
+ (2κ√T σ_g √(z₂² + u₀)/(γ v₂)) (a/√v₂ + x₂₁y₁/√w₂ + √s₂ y₂/√w₂). -/
noncomputable def kanVarRep (T : ℕ) (κ : ℝ) (v : KanVar → ℝ) : ℝ :=
  M.sigmaG2 * (1 + y1 N v ^ 2 + y2 N v ^ 2 + v .s1 / v .w1 + v .a ^ 2 / v .v2) +
    κ ^ 2 * T * (v .z2 ^ 2 + v .u0) / (M.gamma ^ 2 * v .v2 ^ 2) *
      (1 + (x21' N v ^ 2 + v .s2) / v .w2) +
    2 * κ * Real.sqrt T * Real.sqrt M.sigmaG2 * Real.sqrt (v .z2 ^ 2 + v .u0) /
        (M.gamma * v .v2) *
      (v .a / Real.sqrt (v .v2) + x21' N v * y1 N v / Real.sqrt (v .w2) +
        Real.sqrt (v .s2) * y2 N v / Real.sqrt (v .w2))

end Market

end RiskEU.OOSUVar


