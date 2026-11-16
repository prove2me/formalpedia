-- Prove2me | Definitions.Def_LRTempElim_Supplement_GeometricPath
-- name    : LRTempElim_Supplement_GeometricPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:37:24.589528+00:00
-- url     : https://prove2.me/theorems/f76348f4-76d2-4595-b415-b35355c3d264
-- title:
--   Geometric path $p_t=q^{1-t}p^t/Z_t$, path matrix $G$, $\vec d$, batch statistics $\hat G,\hat d$ (122) and $R_{\log}$
-- statement:
--   Let $p,q$ be probability densities with respect to a reference measure. The **geometric path** is
--   $$
--   p_t(x)=\frac{q(x)^{1-t}p(x)^t}{Z_t},\qquad Z_t=\int q(x)^{1-t}p(x)^t\,dx,\qquad t\in[0,1],
--   $$
--   with time score $s^\star(x,t)=\partial_t\log p_t(x)$ and log-ratio $\ell^\star=\log(p/q)$. For a feature map $\phi:\mathcal X\to\mathbb R^m$ write $\mu(\phi)=\int_0^1\mathbb E_{P_t}[\phi]\,dt$ and
--   $$
--   G=\int_0^1\mathrm{Cov}_{P_t}(\phi)\,dt+\mu(\phi)\mu(\phi)^\top,\qquad \vec d=\mathbb E_P[\phi]-\mathbb E_Q[\phi].
--   $$
--   Given $n$ groups of points $(X_i,X_i',Z_i,W_i,P_i,Q_i)$, with $\Delta_i=\phi(X_i)-\phi(X_i')$,
--   $$
--   \hat G=\frac1n\sum_{i=1}^n\Big[\frac{\Delta_i\Delta_i^\top}{2}+\frac{\phi(Z_i)\phi(W_i)^\top+\phi(W_i)\phi(Z_i)^\top}{2}\Big],\qquad \hat d=\frac1n\sum_{i=1}^n[\phi(P_i)-\phi(Q_i)],
--   $$
--   and the empirical risk is $\hat L_n(\theta)=\theta^\top\hat G\theta-2\theta^\top\hat d$. With $\nu=(P+Q)/2$, $\Sigma_\nu=\mathbb E_\nu[\phi\phi^\top]$ and $R_{\log}(\hat\theta)=\mathbb E_\nu[(\hat\theta^\top\phi(X)-\theta_*^\top\phi(X))^2]$.
--
--   These are the objects of Theorem B.22, the deterministic perturbation bound for the scalar geometric-path estimator.
--
--   **Formalization Note** Powers are real powers; with $0^0=1$ the formula gives $p_0=q/Z_0$ and $p_1=p/Z_1$. $\partial_t$ is Mathlib's `deriv`. Expectations and covariances are entrywise integrals against the reference measure; Theorem B.22 assumes the square-integrability that makes them finite. $\nu$ has density $(p+q)/2$.
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), Assumption B.3 eq. (113), p.31 (pdf p.33); p.32 (pdf p.34); eqs. (120)–(122), pp.33–34 (pdf pp.35–36); p.38 (pdf p.40); §2.2, p.4 (pdf p.6)

import Mathlib

open MeasureTheory Matrix

namespace LRTempElim

namespace Supplement

/-!
# The geometric path, the path moment matrix `G` and the batch statistics (120)–(122)

W. Chen, Y. Wu, J. Yang, D. Zeng, *Likelihood-Ratio Learning under Weak Overlap via Analytic
Temporal Elimination*, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee65139…),
Assumptions B.2–B.3 and eq. (113), p.31 (pdf p.33); path moments, p.32 (pdf p.34); eqs. (120)–(122),
pp.33–34 (pdf pp.35–36); fixed-feature setting and Theorem B.22, p.38 (pdf p.40).

"pₜ(x) = q(x)^{1−t}p(x)^t/Zₜ, Zₜ = ∫ q(x)^{1−t}p(x)^t dx. (113)" "Write µ(f) = ∫₀¹ E_{Pₜ}[f] dt and
d(f) = E_P[f] − E_Q[f]" (p.32). "Define G = ∫₀¹ Cov_{Pₜ}(ϕ) dt + µ(ϕ)µ(ϕ)⊤, d⃗ = E_P[ϕ] − E_Q[ϕ], and
λ = λ_min(G), where Cov_{Pₜ}(ϕ) is the m × m covariance matrix of ϕ(X) under Pₜ, and µ(ϕ) is the
vector of µ(ϕⱼ)." "With fixed features f_θ = θ⊤ϕ, the batch objective is L̂ₙ(θ) = θ⊤Ĝθ − 2θ⊤d̂.
Here ∆ᵢ = ϕ(Xᵢ) − ϕ(X′ᵢ) and d̂ = (1/n)∑ᵢ[ϕ(Pᵢ) − ϕ(Qᵢ)]. The batch matrix is
Ĝ = (1/n)∑ᵢ [∆ᵢ∆ᵢ⊤/2 + (ϕ(Zᵢ)ϕ(Wᵢ)⊤ + ϕ(Wᵢ)ϕ(Zᵢ)⊤)/2]. (122)" "Function risk is measured under
ν = (P + Q)/2" (§2.2, p.4).

**Formalization Note.**
* `p`, `q : X → ℝ` are the densities of `P`, `Q` with respect to a reference measure `ρ` on a
  measurable space `X` (the paper's `dx`). Powers are `Real.rpow`; with Lean's `0 ^ 0 = 1` the
  formula gives `p₀ = q/Z₀` and `p₁ = p/Z₁`, as in (113).
* `geomScore … t x = s⋆(x, t) = ∂ₜ log pₜ(x)` is Mathlib's `deriv` in `t`.
* `ℓ⋆(x) = log p(x) − log q(x)`, which is `log(p/q)` on the common support.
* `pathMeanVec = µ(ϕ)`, `pathCov t = Cov_{Pₜ}(ϕ)` and `matG = G` are entrywise Bochner integrals;
  Theorem B.22 assumes the square-integrability that makes them genuine.
* The batch points are six arbitrary families `Xs, Xs', Zs, Ws, Ps, Qs : Fin n → X`: Theorem B.22
  is a deterministic statement about the statistics they define.
* `ν = (P + Q)/2` has density `(p + q)/2`; `sigmaNu = Σ_ν = E_ν[ϕϕ⊤]` and
  `riskLog θ θ⋆ = E_ν[(θ⊤ϕ(X) − θ⋆⊤ϕ(X))²]`.
-/

variable {X : Type*} [MeasurableSpace X] {m : ℕ}

/-- The normalizer `Zₜ = ∫ q^{1−t}p^t dx` of the geometric path (113). -/
noncomputable def geomZ (ρ : Measure X) (p q : X → ℝ) (t : ℝ) : ℝ :=
  ∫ x, q x ^ (1 - t) * p x ^ t ∂ρ

/-- The geometric path density `pₜ = q^{1−t}p^t/Zₜ` (113). -/
noncomputable def geomDens (ρ : Measure X) (p q : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  q x ^ (1 - t) * p x ^ t / geomZ ρ p q t

/-- The time score `s⋆(x, t) = ∂ₜ log pₜ(x)` of the geometric path (Assumption B.3). -/
noncomputable def geomScore (ρ : Measure X) (p q : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  deriv (fun s => Real.log (geomDens ρ p q s x)) t

/-- The absolute log-ratio `ℓ⋆ = log(p/q) = log p − log q`. -/
noncomputable def logRatioD (p q : X → ℝ) (x : X) : ℝ := Real.log (p x) - Real.log (q x)

/-- `E_{Pₜ}[f]` on the geometric path. -/
noncomputable def geomExp (ρ : Measure X) (p q : X → ℝ) (t : ℝ) (f : X → ℝ) : ℝ :=
  ∫ x, geomDens ρ p q t x * f x ∂ρ

/-- The path mean vector `µ(ϕ) = (∫₀¹ E_{Pₜ}[ϕⱼ] dt)ⱼ` (p.32). -/
noncomputable def pathMeanVec (ρ : Measure X) (p q : X → ℝ) (ϕ : X → Fin m → ℝ) : Fin m → ℝ :=
  fun j => ∫ t in (0 : ℝ)..1, geomExp ρ p q t (fun x => ϕ x j)

/-- The covariance matrix `Cov_{Pₜ}(ϕ)` of `ϕ(X)` under `Pₜ` (p.38). -/
noncomputable def pathCov (ρ : Measure X) (p q : X → ℝ) (ϕ : X → Fin m → ℝ) (t : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => geomExp ρ p q t (fun x => ϕ x i * ϕ x j) -
    geomExp ρ p q t (fun x => ϕ x i) * geomExp ρ p q t (fun x => ϕ x j)

/-- `G = ∫₀¹ Cov_{Pₜ}(ϕ) dt + µ(ϕ)µ(ϕ)⊤` (p.38). -/
noncomputable def matG (ρ : Measure X) (p q : X → ℝ) (ϕ : X → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (∫ t in (0 : ℝ)..1, pathCov ρ p q ϕ t i j) +
    pathMeanVec ρ p q ϕ i * pathMeanVec ρ p q ϕ j

/-- `d⃗ = E_P[ϕ] − E_Q[ϕ]` (p.38). -/
noncomputable def vecD (ρ : Measure X) (p q : X → ℝ) (ϕ : X → Fin m → ℝ) : Fin m → ℝ :=
  fun j => (∫ x, p x * ϕ x j ∂ρ) - ∫ x, q x * ϕ x j ∂ρ

/-- The batch matrix (122):
`Ĝ = (1/n)∑ᵢ [∆ᵢ∆ᵢ⊤/2 + (ϕ(Zᵢ)ϕ(Wᵢ)⊤ + ϕ(Wᵢ)ϕ(Zᵢ)⊤)/2]`, `∆ᵢ = ϕ(Xᵢ) − ϕ(X′ᵢ)`. -/
noncomputable def batchG {n : ℕ} (ϕ : X → Fin m → ℝ) (Xs Xs' Zs Ws : Fin n → X) :
    Matrix (Fin m) (Fin m) ℝ :=
  (n : ℝ)⁻¹ • ∑ i, ((1 / 2 : ℝ) • vecMulVec (ϕ (Xs i) - ϕ (Xs' i)) (ϕ (Xs i) - ϕ (Xs' i)) +
    (1 / 2 : ℝ) • (vecMulVec (ϕ (Zs i)) (ϕ (Ws i)) + vecMulVec (ϕ (Ws i)) (ϕ (Zs i))))

/-- `d̂ = (1/n)∑ᵢ[ϕ(Pᵢ) − ϕ(Qᵢ)]` (p.34). -/
noncomputable def batchD {n : ℕ} (ϕ : X → Fin m → ℝ) (Ps Qs : Fin n → X) : Fin m → ℝ :=
  (n : ℝ)⁻¹ • ∑ i, (ϕ (Ps i) - ϕ (Qs i))

/-- The empirical risk `L̂ₙ(θ) = θ⊤Ĝθ − 2θ⊤d̂` (p.34). -/
noncomputable def batchRisk (Ghat : Matrix (Fin m) (Fin m) ℝ) (dhat : Fin m → ℝ)
    (θ : Fin m → ℝ) : ℝ :=
  θ ⬝ᵥ (Ghat *ᵥ θ) - 2 * (θ ⬝ᵥ dhat)

/-- `Σ_ν = E_ν[ϕϕ⊤]` for `ν = (P + Q)/2` (Assumption B.5). -/
noncomputable def sigmaNu (ρ : Measure X) (p q : X → ℝ) (ϕ : X → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => ∫ x, (p x + q x) / 2 * (ϕ x i * ϕ x j) ∂ρ

/-- `R_log = E_ν[(θ̂⊤ϕ(X) − θ⋆⊤ϕ(X))²]` for `ν = (P + Q)/2` (eq. (127)). -/
noncomputable def riskLog (ρ : Measure X) (p q : X → ℝ) (ϕ : X → Fin m → ℝ)
    (θhat θstar : Fin m → ℝ) : ℝ :=
  ∫ x, (p x + q x) / 2 * (θhat ⬝ᵥ ϕ x - θstar ⬝ᵥ ϕ x) ^ 2 ∂ρ

end Supplement

end LRTempElim


