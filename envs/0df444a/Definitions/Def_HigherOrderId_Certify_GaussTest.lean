-- Prove2me | Definitions.Def_HigherOrderId_Certify_GaussTest
-- name    : HigherOrderId_Certify_GaussTest
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:14:42.345938+00:00
-- url     : https://prove2.me/theorems/07808082-30b1-4428-a982-a86ce09d812c
-- title:
--   The Gaussian energy-testing experiment of Lemma C.1: (ε, δ)-safety, null power, the rule (92) and the constants c_{δ,β}, C_{δ,β}
-- statement:
--   Let $X\sim N(\vartheta,\Sigma)$ on $\mathbb R^D$ with known covariance $\Sigma$, where $\|\vartheta\|_2^2\le R^2$ (88). An acceptance rule $\varphi$ is **$(\varepsilon,\delta)$-safe** (89) if
--   $$\sup_{\vartheta:\ \varepsilon\le\|\vartheta\|_2^2\le R^2}P_\vartheta\{\varphi(X)=1\}\le\delta,$$
--   and its **null power** is $P_0\{\varphi(X)=1\}$. The noise-corrected energy rule (92) is $\phi_\varepsilon(X)=\mathbf 1\{\|X\|_2^2-\operatorname{tr}\Sigma\le\varepsilon/2\}$. The constants of (90)–(91) are
--   $$c_{\delta,\beta}=\big[2\log\{1+4(1-\delta-\beta)^2\}\big]^{1/2},\qquad C_{\delta,\beta}=\max\{\sqrt{8/\beta},\,32/\delta\}.$$
--
--   **Formalization Note.** $N(\vartheta,\Sigma)$ is Mathlib's `multivariateGaussian ϑ Σ` on `EuclideanSpace ℝ (Fin D)`. A rule is real-valued and $P_\vartheta\{\varphi(X)=1\}$ is $\int\varphi\,dN(\vartheta,\Sigma)$ (for an indicator rule this is the probability of acceptance).
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 28, Eqs. (88)–(92)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model

open MeasureTheory ProbabilityTheory

namespace HigherOrderId.Certify

/-!
# The Gaussian energy-testing experiment of Lemma C.1

Zhang, Yan, Qiao, Yu, *The Higher-Order Identifiability Paradox: Learning and Certifying
Hypergraph Order*, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 28, Eqs. (88)–(92).

`X ∼ N(ϑ, Σ)` on `ℝ^D` is Mathlib's `multivariateGaussian ϑ Σ` on `EuclideanSpace ℝ (Fin D)`.
A rule `φ` is an acceptance probability; `P_ϑ{φ(X) = 1}` is `∫ φ dN(ϑ, Σ)`.
-/

/-- `(ε, δ)`-safety (89): `P_ϑ{φ(X) = 1} ≤ δ` for every `ϑ` with `ε ≤ ‖ϑ‖₂² ≤ R²`. -/
def IsSafe {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (R ε δ : ℝ)
    (φ : EuclideanSpace ℝ (Fin D) → ℝ) : Prop :=
  ∀ θ : EuclideanSpace ℝ (Fin D), ε ≤ ‖θ‖ ^ 2 → ‖θ‖ ^ 2 ≤ R ^ 2 →
    ∫ x, φ x ∂(multivariateGaussian θ S) ≤ δ

/-- The null power `P_0{φ(X) = 1}`. -/
noncomputable def nullPower {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ)
    (φ : EuclideanSpace ℝ (Fin D) → ℝ) : ℝ :=
  ∫ x, φ x ∂(multivariateGaussian 0 S)

/-- The noise-corrected energy rule (92): `ϕ_ε(X) = 1{‖X‖₂² − tr(Σ) ≤ ε/2}`. -/
noncomputable def energyRule {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (ε : ℝ) :
    EuclideanSpace ℝ (Fin D) → ℝ :=
  Set.indicator {x | ‖x‖ ^ 2 - S.trace ≤ ε / 2} (fun _ => 1)

/-- `c_{δ,β} = [2 log{1 + 4(1 − δ − β)²}]^{1/2}` of (90). -/
noncomputable def cLower (δ β : ℝ) : ℝ :=
  Real.sqrt (2 * Real.log (1 + 4 * (1 - δ - β) ^ 2))

/-- `C_{δ,β} = max{√(8/β), 32/δ}` of (91). -/
noncomputable def CUpper (δ β : ℝ) : ℝ :=
  max (Real.sqrt (8 / β)) (32 / δ)

end HigherOrderId.Certify


