-- Prove2me | Definitions.Def_HigherOrderId_Certify_Release
-- name    : HigherOrderId_Certify_Release
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:14:55.632552+00:00
-- url     : https://prove2.me/theorems/98c0a454-f7e4-4b80-b73a-7bf17a5bfd95
-- title:
--   Designs, the centered simplex class 𝔇_{d,m}(α), the Gaussian value–gradient release (7) and requirement (9)
-- statement:
--   A **design** with $E$ environments consists of known means $x_1,\dots,x_E\in\mathbb R^d$ and allocations $n_1,\dots,n_E\in\mathbb N$. Under $(b,Q)$ its **Gaussian value–gradient release** (7)/(52) is the observation $(\hat v_e,\hat g_e)_{e\le E}\in(\mathbb R\times\mathbb R^d)^E$ whose $E(d+1)$ coordinates are independent with
--   $$\hat v_e\sim N\!\left(f(x_e),\tfrac{\sigma^2}{n_e}\right),\qquad (\hat g_e)_i\sim N\!\left((b+Qx_e)_i,\tfrac{\sigma^2}{n_e}\right).$$
--
--   Fix $0\le m\le d$, $k=d-m$, $E=k+1$, $\alpha>0$ and a budget $N$. The class $\mathfrak D_{d,m}(\alpha)$ consists of the designs with $\|x_e\|_2=\alpha$ for all $e$, $\sum_e x_e=0$, $E^{-1}\sum_e x_ex_e^\top=(\alpha^2/k)P_{\mathcal V}$ for some $k$-dimensional subspace $\mathcal V\subseteq\mathbb R^d$ with orthogonal projector $P_{\mathcal V}$, and equal allocations $n_e=N/E$ with $N/E$ a positive integer (the printed equivalent form of the centered regular-simplex designs).
--
--   An acceptance rule $\varphi$ (value $1$ certifies $V<\varepsilon$) satisfies **requirement (9)** at tolerance $\varepsilon$ when
--   $$\Pr_{b,Q}(C=1)\le\delta\ \text{ for every }(b,Q)\in\Theta_R\text{ with }V(b,Q)\ge\varepsilon,\qquad \Pr_{0,0}(C=1)\ge 1-\beta,$$
--   where $\Pr_{b,Q}(C=1)=\int\varphi\,d(\text{release law under }(b,Q))$.
--
--   **Formalization Note.** The release law is a finite product (`Measure.pi`, `Measure.prod`) of Mathlib's `gaussianReal` with variance `σ²/n_e`. $P_{\mathcal V}$ is written $WW^\top$ with $W$ a $d\times k$ matrix with $W^\top W=I_k$ (its columns are an orthonormal basis of $\mathcal V$). The sup in (9) is written as a bound for every alternative.
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 5, Eq. (7) and 'Environment designs'; p. 6, Eq. (9); p. 20, Eq. (52)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model

open MeasureTheory ProbabilityTheory Matrix

namespace HigherOrderId.Certify

/-!
# Environment designs, the class 𝔇_{d,m}(α), the Gaussian value–gradient release (7) and the
certification requirement (9)

Zhang, Yan, Qiao, Yu, *The Higher-Order Identifiability Paradox: Learning and Certifying
Hypergraph Order*, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 5, Eq. (7) and
"Environment designs"; p. 6, Eq. (9); p. 20, Eq. (52).

* A design is a list of `E` known environment means `x_e ∈ ℝ^d` and allocations `n_e ∈ ℕ`.
* The observation is `(v̂_e, ĝ_e)_{e}` in `(ℝ × ℝ^d)^E`; every coordinate is an independent
  Gaussian with variance `σ²/n_e`: `v̂_e ∼ N(f(x_e), σ²/n_e)`, `ĝ_e ∼ N(∇f(x_e), (σ²/n_e) I_d)`.
* `InDesignClass d m N α D` is the printed characterisation of 𝔇_{d,m}(α):
  `‖x_e‖₂ = α`, `Σ_e x_e = 0`, `E⁻¹ Σ_e x_e x_eᵀ = (α²/k) P_V` for a `k`-dimensional subspace
  `V` (written `P_V = W Wᵀ` with `W` a `d × k` matrix of orthonormal columns), with
  `k = d − m`, `E = k + 1`, and `n_e = N/E` with `N/E` a positive integer.
* `Certifies D σ R ε δ β φ` is (9) for a (possibly randomized) acceptance rule `φ`:
  `Pr(C = 1)` is the integral of `φ` against the release law.
-/

/-- A design: environment means `x_e` and allocations `n_e`, `e ∈ Fin E`. -/
structure Design (d E : ℕ) where
  /-- The known environment means. -/
  x : Fin E → Fin d → ℝ
  /-- The allocations. -/
  n : Fin E → ℕ

/-- The observation space `(ℝ × ℝ^d)^E` of the value–gradient release. -/
abbrev Obs (d E : ℕ) := Fin E → ℝ × (Fin d → ℝ)

/-- The noise variance `σ²/n` of one released coordinate. -/
noncomputable def noiseVar (σ : ℝ) (n : ℕ) : NNReal :=
  Real.toNNReal (σ ^ 2 / (n : ℝ))

/-- The law of the Gaussian value–gradient release (7)/(52) of design `D` under `(b, Q)`:
all `E(d + 1)` coordinates independent, `v̂_e ∼ N(f(x_e), σ²/n_e)`,
`(ĝ_e)_i ∼ N((b + Qx_e)_i, σ²/n_e)`. -/
noncomputable def releaseLaw {d E : ℕ} (D : Design d E) (σ : ℝ) (b : Fin d → ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) : Measure (Obs d E) :=
  Measure.pi fun e =>
    (gaussianReal (mechValue b Q (D.x e)) (noiseVar σ (D.n e))).prod
      (Measure.pi fun i => gaussianReal (mechGrad b Q (D.x e) i) (noiseVar σ (D.n e)))

/-- The centered regular-simplex design class `𝔇_{d,m}(α)` with budget `N`
(`k = d − m`, `E = k + 1`). -/
def InDesignClass (d m N : ℕ) (α : ℝ) (D : Design d (d - m + 1)) : Prop :=
  (∀ e, ∑ i, D.x e i ^ 2 = α ^ 2) ∧
  (∑ e, D.x e = 0) ∧
  (∃ W : Matrix (Fin d) (Fin (d - m)) ℝ, Wᵀ * W = 1 ∧
    ((d - m + 1 : ℕ) : ℝ)⁻¹ • ∑ e, vecMulVec (D.x e) (D.x e) =
      (α ^ 2 / ((d - m : ℕ) : ℝ)) • (W * Wᵀ)) ∧
  (d - m + 1) ∣ N ∧ 0 < N / (d - m + 1) ∧
  ∀ e, D.n e = N / (d - m + 1)

/-- Requirement (9) at tolerance `ε` for an acceptance rule `φ` (`φ = 1` certifies `V < ε`):
`Pr_{b,Q}(C = 1) ≤ δ` for every `(b, Q) ∈ Θ_R` with `V(b, Q) ≥ ε`, and
`Pr_{b=0,Q=0}(C = 1) ≥ 1 − β`. -/
def Certifies {d E : ℕ} (D : Design d E) (σ R ε δ β : ℝ) (φ : Obs d E → ℝ) : Prop :=
  (∀ (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ), InTheta R b Q → ε ≤ energy b Q →
      ∫ y, φ y ∂(releaseLaw D σ b Q) ≤ δ) ∧
  1 - β ≤ ∫ y, φ y ∂(releaseLaw D σ 0 0)

end HigherOrderId.Certify


