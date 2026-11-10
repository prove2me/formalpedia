-- Prove2me | Definitions.Def_LRTempElim_Logistic
-- name    : LRTempElim_Logistic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:29.198371+00:00
-- url     : https://prove2.me/theorems/c2e5f204-93ab-45f8-856d-208858efe58f
-- title:
--   Balanced logistic DRE: Hessian $H$, pair gradient $g$, sandwich $V_{\mathrm{NCE}}$, overlap $\omega$, $C_{\mathrm{NCE}}(a)$ and $I_a$
-- statement:
--   Let $\eta:\mathcal X\to\mathbb R$ be a class-probability function, $\phi:\mathcal X\to\mathbb R^k$ a feature map, $\nu$ a query law and $\pi$ the law of a pair $W=(X_0,X_1)$ with $X_0\sim Q$, $X_1\sim P$. The logistic Hessian and the balanced logistic pair gradient at the truth are
--   $$
--   H=\mathbb E_\nu[\eta(1-\eta)\phi\phi^\top],\qquad g(W)=\tfrac12\big[(\eta(X_1)-1)\phi(X_1)+\eta(X_0)\phi(X_0)\big],
--   $$
--   with $S=\mathrm{Var}_W\,g(W)$, the sandwich covariance $V_{\mathrm{NCE}}=H^{-1}SH^{-1}$ and the coefficient $C_{\mathrm{NCE}}=\operatorname{tr}(\Sigma_\nu V_{\mathrm{NCE}})$, $\Sigma_\nu=\mathbb E_\nu[\phi\phi^\top]$.
--
--   For densities $p,q$ with respect to a reference measure $\mu$, the density form is $\eta(x)=p(x)/(p(x)+q(x))$, $\nu=\tfrac12(P+Q)$ with $P=p\,\mu$, $Q=q\,\mu$, the pair law is $Q\otimes P$, and the normalized overlap is
--   $$
--   \omega(P,Q)=\int\frac{2p(x)q(x)}{p(x)+q(x)}\,d\mu(x).
--   $$
--
--   In the Gaussian family, $\eta(x)=\sigma(ax)$ with $\sigma(u)=1/(1+e^{-u})$, features $(1,x,x^2)$, query law $\nu_a$ and pair law $Q_a\otimes P_a$; this gives $V_{\mathrm{NCE}}(a)$ and $C_{\mathrm{NCE}}(a)$. Finally the logistic slope information is
--   $$
--   I_a=\mathbb E_{\nu_a}\big[X^2\sigma(aX)(1-\sigma(aX))\big].
--   $$
--
--   These are the objects whose growth in $a$ the goal theorem bounds below by $\Omega(a^5e^{a^2/8})$.
--
--   **Formalization Note** $H^{-1}$ is the matrix inverse. $\mathrm{Var}_W g(W)$ is the covariance matrix of the law of $g(W)$, computed with the published definition `WassersteinDRO.Guarantees.covarianceMatrix`. On the $\nu$-null set $\{p+q=0\}$ Lean's convention $0/0=0$ applies. $\sigma$ is Mathlib's `Real.sigmoid`.
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §A.2.1 eqs. (33), (37), pp.16–17 (pdf pp.18–19); eq. (52) and the definition of I_a, §A.2.3, p.20 (pdf p.22); p.7 (pdf p.9)

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix
import Definitions.Def_LRTempElim_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LRTempElim

/-!
# Balanced logistic density-ratio estimation: Hessian, pair gradient, sandwich, coefficient

W. Chen, Y. Wu, J. Yang, D. Zeng, *Likelihood-Ratio Learning under Weak Overlap via Analytic
Temporal Elimination*, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee65139…),
§A.2.1, eqs. (33), (37) (pp.16–17, pdf pp.18–19), eq. (52) and the definition of `I_a`
(§A.2.3, p.20, pdf p.22), `C(a) = tr(Σ_{ν_a}V_a)` (p.7, pdf p.9).

"Let `η(x) = p(x)/(p(x) + q(x))`, `w(x) = η(x)(1 − η(x))`, and `H_NCE = E_ν[w(X)ϕ(X)ϕ(X)⊤]`,
`ω(P, Q) = ∫ 2p(x)q(x)/(p(x) + q(x)) dx = 4E_ν[w(X)]`. (33)" (p.16). "For a pair `W = (X₀, X₁)`
with `X₀ ∼ Q` and `X₁ ∼ P`, the balanced logistic gradient at the truth is
`g(W) = ½[(η(X₁) − 1)ϕ(X₁) + η(X₀)ϕ(X₀)]`. (37)" (p.17). "For balanced logistic DRE …, let
`η(x) = σ(ax)` … with `H_a = E_{ν_a}[η(1−η)ϕϕ⊤]` … `S_a = Var_W g(W)`, `V_NCE = H_a⁻¹S_aH_a⁻¹`.
(52) Define `I_a = E_{ν_a}[X²σ(aX)(1 − σ(aX))]`." (p.20).

**Formalization Note.**
* The logistic objects are generic in the class-probability function `η` (so that both the
  density form `η = p/(p + q)` of Proposition A.4 and the Gaussian form `η(x) = σ(ax)` of
  eq. (52) are instances), in the feature map `ϕ : X → ℝᵏ`, in the query law `ν` and in the
  pair law `π` of `W = (X₀, X₁)`.
* `logisticS η ϕ π = Var_W g(W)` is the covariance matrix `E[(g − Eg)(g − Eg)⊤]` of the law of
  `g(W)` (the published `WassersteinDRO.Guarantees.covarianceMatrix`, applied to the pushforward of
  `π` under `g`, viewed in `EuclideanSpace ℝ (Fin k)`), `logisticV = H⁻¹ S H⁻¹` the sandwich,
  `logisticC = tr(Σ_ν V)`.
* `H⁻¹` is `Matrix.inv` (`0` on a singular matrix).
* Density form: `p, q` are densities with respect to a reference measure `μ`;
  `P = p·μ`, `Q = q·μ`, `ν = (P + Q)/2`, pair law `Q ⊗ P`. On `{p + q = 0}` (a `ν`-null set) Lean's
  `0/0 = 0` gives `η = 0` and integrand `0` in `ω`.
* σ is Mathlib's `Real.sigmoid u = (1 + e^{−u})⁻¹`.
-/

section Generic

variable {X : Type*} [MeasurableSpace X] {k : ℕ}

/-- The logistic Hessian `H = E_ν[η(1 − η)ϕϕ⊤]` (eqs. (33), (52)). -/
noncomputable def logisticHess (η : X → ℝ) (ϕ : X → Fin k → ℝ) (ν : Measure X) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∫ x, η x * (1 - η x) * (ϕ x i * ϕ x j) ∂ν

/-- The balanced logistic pair gradient at the truth,
`g(W) = ½[(η(X₁) − 1)ϕ(X₁) + η(X₀)ϕ(X₀)]` with `W = (X₀, X₁)` (eqs. (37), (52)). -/
noncomputable def logisticGrad (η : X → ℝ) (ϕ : X → Fin k → ℝ) (W : X × X) : Fin k → ℝ :=
  fun i => (1 / 2) * ((η W.2 - 1) * ϕ W.2 i + η W.1 * ϕ W.1 i)

/-- `S = Var_W g(W)`, the covariance matrix of the pair gradient under the pair law `π`
(eq. (52)). -/
noncomputable def logisticS (η : X → ℝ) (ϕ : X → Fin k → ℝ) (π : Measure (X × X)) :
    Matrix (Fin k) (Fin k) ℝ :=
  WassersteinDRO.Guarantees.covarianceMatrix
    (π.map fun W => WithLp.toLp 2 (logisticGrad η ϕ W))

/-- The sandwich covariance `V_NCE = H⁻¹ S H⁻¹` (eq. (52); proof of Proposition A.4). -/
noncomputable def logisticV (η : X → ℝ) (ϕ : X → Fin k → ℝ) (ν : Measure X)
    (π : Measure (X × X)) : Matrix (Fin k) (Fin k) ℝ :=
  (logisticHess η ϕ ν)⁻¹ * logisticS η ϕ π * (logisticHess η ϕ ν)⁻¹

/-- The covariance-defined risk coefficient `C_NCE = tr(Σ_ν V_NCE)` (p.7; eq. (34)). -/
noncomputable def logisticC (η : X → ℝ) (ϕ : X → Fin k → ℝ) (ν : Measure X)
    (π : Measure (X × X)) : ℝ :=
  Matrix.trace (secondMoment ϕ ν * logisticV η ϕ ν π)

/-- The class probability `η(x) = p(x)/(p(x) + q(x))` of two densities (eq. (33)). -/
noncomputable def etaD (p q : X → ℝ) (x : X) : ℝ := p x / (p x + q x)

/-- The mixture `ν = (P + Q)/2` of the laws with densities `p, q` against `μ` (§2.2, p.4). -/
noncomputable def nuD (μ : Measure X) (p q : X → ℝ) : Measure X :=
  (2 : ℝ≥0∞)⁻¹ • (μ.withDensity (fun x => ENNReal.ofReal (p x)) +
    μ.withDensity (fun x => ENNReal.ofReal (q x)))

/-- The pair law `Q ⊗ P` of `W = (X₀, X₁)`, `X₀ ∼ Q = q·μ`, `X₁ ∼ P = p·μ` (§A.2.1, p.17). -/
noncomputable def pairLawD (μ : Measure X) (p q : X → ℝ) : Measure (X × X) :=
  (μ.withDensity fun x => ENNReal.ofReal (q x)).prod
    (μ.withDensity fun x => ENNReal.ofReal (p x))

/-- The normalized overlap `ω(P, Q) = ∫ 2p(x)q(x)/(p(x) + q(x)) dμ(x)` (eq. (33)). -/
noncomputable def overlap (μ : Measure X) (p q : X → ℝ) : ℝ :=
  ∫ x, 2 * p x * q x / (p x + q x) ∂μ

end Generic

/-- The Gaussian-family sandwich `V_NCE(a) = H_a⁻¹S_aH_a⁻¹` with `η(x) = σ(ax)`, features
`(1, x, x²)`, query law `ν_a` and pair law `Q_a ⊗ P_a` (eq. (52), p.20). -/
noncomputable def Vnce (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  logisticV (fun x => Real.sigmoid (a * x)) phi3 (nu a) (pairLaw a)

/-- The covariance-defined coefficient `C_NCE(a) = tr(Σ_{ν_a}V_NCE(a))` of balanced logistic DRE
in the Gaussian family (p.7, eq. (52)). -/
noncomputable def Cnce (a : ℝ) : ℝ :=
  logisticC (fun x => Real.sigmoid (a * x)) phi3 (nu a) (pairLaw a)

/-- The logistic slope information `I_a = E_{ν_a}[X²σ(aX)(1 − σ(aX))]` (§A.2.3, p.20;
eq. (134), p.41). -/
noncomputable def Ia (a : ℝ) : ℝ :=
  ∫ x, x ^ 2 * (Real.sigmoid (a * x) * (1 - Real.sigmoid (a * x))) ∂(nu a)

end LRTempElim


