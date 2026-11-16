-- Prove2me | Definitions.Def_LRTempElim_Supplement_SampleablePath
-- name    : LRTempElim_Supplement_SampleablePath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:37:08.480864+00:00
-- url     : https://prove2.me/theorems/d22abc52-c8ee-4286-a570-6464956e442a
-- title:
--   Finite-interval readout on a sampleable path: statistics (12), constants (13), capped ratio and tail $\mathcal T_r(M)$
-- statement:
--   Let $W\sim\mu$ be a random input and $X_t=T_t(W)$ a sampling rule. A **configuration** consists of a feature map $\phi:\mathcal X\to\mathbb R^k$, nodes $0=t_0<\dots<t_K=1$ with widths $h_i=t_{i+1}-t_i$, and a ridge $\lambda>0$. For $i=0,\dots,K-1$,
--   $$
--   B_i(W)=\tfrac12\big[\phi(X_{t_i})\phi(X_{t_i})^\top+\phi(X_{t_{i+1}})\phi(X_{t_{i+1}})^\top\big],\qquad D_i(W)=\frac{\phi(X_{t_{i+1}})-\phi(X_{t_i})}{h_i},
--   $$
--   $$
--   \bar B_i=\mathbb EB_i(W),\quad d_i=\mathbb ED_i(W),\quad v_i=(\bar B_i+\lambda I)^{-1}d_i,\quad m=\sum_ih_iv_i .
--   $$
--   From independent replicas $W_1,\dots,W_N$ the averages $\hat B_i,\hat d_i$ give $\hat m=\sum_ih_i(\hat B_i+\lambda I)^{-1}\hat d_i$ and $\hat f=\phi^\top\hat m$. With $r=dP/dQ$ and $\ell^\star=\log r$,
--   $$
--   \Sigma_Q=\mathbb E_Q[\phi\phi^\top],\quad c_Q=\|\Sigma_Q^{1/2}\|_{\mathrm{op}},\quad \sigma_{B,i}^2=\mathbb E\|B_i(W)-\bar B_i\|_F^2,\quad \sigma_{D,i}^2=\mathbb E\|D_i(W)-d_i\|_2^2,
--   $$
--   $$
--   \mathcal V_{k,K,\lambda}=\frac{c_Q}{\lambda}\sum_ih_i\big(\sigma_{D,i}+\sigma_{B,i}\|v_i\|_2\big),\qquad \mathcal B_{k,K,\lambda}=\|\phi^\top m-\ell^\star\|_{L^1(Q)} .
--   $$
--   For $M>0$ the capped ratio is $\hat r_M=\min\{e^{\hat f},M\}$ and the tail is $\mathcal T_r(M)=\mathbb E_Q[(r-M)_+]$. The expected errors $\mathbb E\|\hat f-\ell^\star\|_{L^1(Q)}$ and $\mathbb E\|\hat r_M-r\|_{L^1(Q)}$ average over the $N$ replicas. A configuration is **regular** when its grid is as above, $\lambda>0$, $\phi$ is measurable, $\Sigma_Q$ is finite and $\sigma_{B,i},\sigma_{D,i}<\infty$ for every interval.
--
--   These are the objects of Theorem 3, the finite-sample guarantee for the analytic readout on any sampleable path.
--
--   **Formalization Note** The random input lives on a measurable space $\Omega$ with law $\mu$; the replicas are a point of $\Omega^N$ under $\mu^{\otimes N}$. "$\Sigma_Q$ finite" is: every coordinate of $\phi$ is in $L^2(Q)$; "$\sigma_{B,i},\sigma_{D,i}<\infty$" is: every entry of $B_i(W)$ and coordinate of $D_i(W)$ is in $L^2(\mu)$. $c_Q$ is computed as $\|\Sigma_Q\|_{\mathrm{op}}^{1/2}$, equal to $\|\Sigma_Q^{1/2}\|_{\mathrm{op}}$ for the positive semidefinite $\Sigma_Q$. The expected errors and the tail are lower Lebesgue integrals with values in $[0,\infty]$.
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §4.2 eqs. (12)–(13) and Theorem 3, p.8 (pdf p.10)

import Mathlib
import Definitions.Def_LRTempElim_Supplement_Norms

open MeasureTheory Matrix
open scoped ENNReal

namespace LRTempElim

namespace Supplement

/-!
# The finite-interval readout on a sampleable path: statistics (12) and constants (13)

W. Chen, Y. Wu, J. Yang, D. Zeng, *Likelihood-Ratio Learning under Weak Overlap via Analytic
Temporal Elimination*, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee65139…),
§4.2 eqs. (12)–(13) and Theorem 3, p.8 (pdf p.10); §A.3, p.21 (pdf p.23).

"Let W₁, …, W_N be independent copies of a random input W, and let X_t = T_t(W) have endpoint laws
Q and P. … All nodes of a replica may share randomness. Fix ϕ : X → ℝᵏ independently of these
replicas, nodes tᵢ, widths hᵢ = tᵢ₊₁ − tᵢ, and λ > 0. Define the per-replica statistics and their
means by Bᵢ(W) = ½(ϕ(X_{tᵢ})ϕ(X_{tᵢ})⊤ + ϕ(X_{tᵢ₊₁})ϕ(X_{tᵢ₊₁})⊤), Dᵢ(W) = (ϕ(X_{tᵢ₊₁}) − ϕ(X_{tᵢ}))/hᵢ,
B̄ᵢ = EBᵢ(W), dᵢ = EDᵢ(W), vᵢ = (B̄ᵢ + λI)⁻¹dᵢ, m = ∑ᵢ hᵢvᵢ. (12) Their empirical averages give
m̂ = ∑ᵢ hᵢ(B̂ᵢ + λI)⁻¹d̂ᵢ and f̂ = ϕ⊤m̂ … Put Σ_Q = E_Q[ϕϕ⊤], c_Q = ∥Σ_Q^{1/2}∥_op,
σ²_{B,i} = E∥Bᵢ(W) − B̄ᵢ∥²_F, σ²_{D,i} = E∥Dᵢ(W) − dᵢ∥²₂,
V_{k,K,λ} = (c_Q/λ) ∑ᵢ hᵢ(σ_{D,i} + σ_{B,i}∥vᵢ∥₂), B_{k,K,λ} = ∥ϕ⊤m − ℓ⋆∥_{L¹(Q)}. (13)"
"For any M > 0, let r̂_M = min{e^{f̂}, M} and T_r(M) = E_Q[(r − M)₊]" (Theorem 3).

**Formalization Note.**
* A `Config X` bundles what Theorem 3 lets vary along a sequence: the feature dimension `k`, the
  number of intervals `K`, the nodes `t₀, …, t_K` (`node : Fin (K+1) → ℝ`), the feature map
  `ϕ : X → ℝᵏ` and the ridge `λ`. Interval `i : Fin K` runs from `tᵢ` to `tᵢ₊₁`
  (`i.castSucc`, `i.succ`).
* The sampling rule is `T : ℝ → Ω → X`, `X_t = T t W`, with `W ∼ μ` on a measurable space `Ω`.
  The `N` replicas are a point `ws : Fin N → Ω` under the product law `μ^{⊗N}`.
* Expectations of matrix/vector statistics are entrywise Bochner integrals; Theorem 3 assumes the
  square-integrability (`σ_{B,i}, σ_{D,i} < ∞`) that makes them genuine.
* `cQ = ∥Σ_Q∥_op^{1/2}`, which equals `∥Σ_Q^{1/2}∥_op` because `Σ_Q` is positive semidefinite.
* `r = dP/dQ` is `P.rnDeriv Q` (in `ℝ≥0∞`); `ℓ⋆ = log r` uses its real value. `r̂_M` and the
  tail `T_r(M) = E_Q[(r − M)₊]` are as in Theorem 3; the tail is a lower Lebesgue integral in
  `ℝ≥0∞` (truncated subtraction is the positive part).
-/

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- The data of one finite-interval readout: features, grid and ridge (§4.2, p.8). -/
structure Config (X : Type*) where
  /-- feature dimension `k` -/
  k : ℕ
  /-- number of intervals `K` -/
  K : ℕ
  /-- the nodes `t₀ < ⋯ < t_K` -/
  node : Fin (K + 1) → ℝ
  /-- the feature map `ϕ : X → ℝᵏ` -/
  ϕ : X → Fin k → ℝ
  /-- the ridge `λ` -/
  ridge : ℝ

namespace Config

variable (c : Config X)

/-- The grid condition `0 = t₀ < ⋯ < t_K = 1`. -/
def IsGrid : Prop :=
  StrictMono c.node ∧ c.node 0 = 0 ∧ c.node (Fin.last c.K) = 1

/-- The width `hᵢ = tᵢ₊₁ − tᵢ` of interval `i`. -/
def width (i : Fin c.K) : ℝ := c.node i.succ - c.node i.castSucc

/-- The per-replica mass `Bᵢ(W) = ½(ϕ(X_{tᵢ})ϕ(X_{tᵢ})⊤ + ϕ(X_{tᵢ₊₁})ϕ(X_{tᵢ₊₁})⊤)` (12). -/
noncomputable def statB (T : ℝ → Ω → X) (i : Fin c.K) (w : Ω) : Matrix (Fin c.k) (Fin c.k) ℝ :=
  (1 / 2 : ℝ) • (vecMulVec (c.ϕ (T (c.node i.castSucc) w)) (c.ϕ (T (c.node i.castSucc) w)) +
    vecMulVec (c.ϕ (T (c.node i.succ) w)) (c.ϕ (T (c.node i.succ) w)))

/-- The per-replica difference `Dᵢ(W) = (ϕ(X_{tᵢ₊₁}) − ϕ(X_{tᵢ}))/hᵢ` (12). -/
noncomputable def statD (T : ℝ → Ω → X) (i : Fin c.K) (w : Ω) : Fin c.k → ℝ :=
  (c.width i)⁻¹ • (c.ϕ (T (c.node i.succ) w) - c.ϕ (T (c.node i.castSucc) w))

/-- `B̄ᵢ = E Bᵢ(W)` (12). -/
noncomputable def meanB (μ : Measure Ω) (T : ℝ → Ω → X) (i : Fin c.K) :
    Matrix (Fin c.k) (Fin c.k) ℝ :=
  fun a b => ∫ w, c.statB T i w a b ∂μ

/-- `dᵢ = E Dᵢ(W)` (12). -/
noncomputable def meanD (μ : Measure Ω) (T : ℝ → Ω → X) (i : Fin c.K) : Fin c.k → ℝ :=
  fun a => ∫ w, c.statD T i w a ∂μ

/-- `vᵢ = (B̄ᵢ + λI)⁻¹dᵢ` (12). -/
noncomputable def popV (μ : Measure Ω) (T : ℝ → Ω → X) (i : Fin c.K) : Fin c.k → ℝ :=
  (c.meanB μ T i + c.ridge • (1 : Matrix (Fin c.k) (Fin c.k) ℝ))⁻¹ *ᵥ c.meanD μ T i

/-- The population head `m = ∑ᵢ hᵢvᵢ` (12). -/
noncomputable def popM (μ : Measure Ω) (T : ℝ → Ω → X) : Fin c.k → ℝ :=
  ∑ i, c.width i • c.popV μ T i

/-- The empirical average `B̂ᵢ = N⁻¹ ∑ₙ Bᵢ(Wₙ)`. -/
noncomputable def empB {N : ℕ} (T : ℝ → Ω → X) (i : Fin c.K) (ws : Fin N → Ω) :
    Matrix (Fin c.k) (Fin c.k) ℝ :=
  (N : ℝ)⁻¹ • ∑ n, c.statB T i (ws n)

/-- The empirical average `d̂ᵢ = N⁻¹ ∑ₙ Dᵢ(Wₙ)`. -/
noncomputable def empD {N : ℕ} (T : ℝ → Ω → X) (i : Fin c.K) (ws : Fin N → Ω) : Fin c.k → ℝ :=
  (N : ℝ)⁻¹ • ∑ n, c.statD T i (ws n)

/-- The empirical readout `m̂ = ∑ᵢ hᵢ(B̂ᵢ + λI)⁻¹d̂ᵢ` (p.8, the readout in (9)). -/
noncomputable def empM {N : ℕ} (T : ℝ → Ω → X) (ws : Fin N → Ω) : Fin c.k → ℝ :=
  ∑ i, c.width i • ((c.empB T i ws + c.ridge • (1 : Matrix (Fin c.k) (Fin c.k) ℝ))⁻¹ *ᵥ
    c.empD T i ws)

/-- The fitted log-ratio `f̂(x) = ϕ(x)⊤m̂`. -/
noncomputable def fhat {N : ℕ} (T : ℝ → Ω → X) (ws : Fin N → Ω) (x : X) : ℝ :=
  c.ϕ x ⬝ᵥ c.empM T ws

/-- `Σ_Q = E_Q[ϕϕ⊤]` (13). -/
noncomputable def sigmaQ (Q : Measure X) : Matrix (Fin c.k) (Fin c.k) ℝ :=
  fun a b => ∫ x, c.ϕ x a * c.ϕ x b ∂Q

/-- `c_Q = ∥Σ_Q^{1/2}∥_op = ∥Σ_Q∥_op^{1/2}` (13). -/
noncomputable def cQ (Q : Measure X) : ℝ := Real.sqrt (opNorm (c.sigmaQ Q))

/-- `σ_{B,i} = (E∥Bᵢ(W) − B̄ᵢ∥²_F)^{1/2}` (13). -/
noncomputable def sigmaB (μ : Measure Ω) (T : ℝ → Ω → X) (i : Fin c.K) : ℝ :=
  Real.sqrt (∫ w, frobNorm (c.statB T i w - c.meanB μ T i) ^ 2 ∂μ)

/-- `σ_{D,i} = (E∥Dᵢ(W) − dᵢ∥²₂)^{1/2}` (13). -/
noncomputable def sigmaD (μ : Measure Ω) (T : ℝ → Ω → X) (i : Fin c.K) : ℝ :=
  Real.sqrt (∫ w, eNorm (c.statD T i w - c.meanD μ T i) ^ 2 ∂μ)

/-- The sampling constant `V_{k,K,λ} = (c_Q/λ) ∑ᵢ hᵢ(σ_{D,i} + σ_{B,i}∥vᵢ∥₂)` (13). -/
noncomputable def constV (Q : Measure X) (μ : Measure Ω) (T : ℝ → Ω → X) : ℝ :=
  c.cQ Q / c.ridge *
    ∑ i, c.width i * (c.sigmaD μ T i + c.sigmaB μ T i * eNorm (c.popV μ T i))

/-- The hypotheses Theorem 3 places on one configuration, for the sampling rule `T` and the
input law `μ`:
* the grid is `0 = t₀ < ⋯ < t_K = 1` and the ridge is `λ > 0` (§4.2);
* `ϕ` is measurable (a fixed feature map, chosen independently of the replicas);
* "`Σ_Q` is finite": every coordinate of `ϕ` is in `L²(Q)`;
* "`σ_{B,i}, σ_{D,i} < ∞` for every interval": every entry of `Bᵢ(W)` and every coordinate of
  `Dᵢ(W)` is in `L²(μ)` (so their means `B̄ᵢ`, `dᵢ` exist and the variances are finite). -/
def Regular (Q : Measure X) (μ : Measure Ω) (T : ℝ → Ω → X) : Prop :=
  c.IsGrid ∧ 0 < c.ridge ∧ Measurable c.ϕ ∧
    (∀ a, MemLp (fun x => c.ϕ x a) 2 Q) ∧
    (∀ i a b, MemLp (fun w => c.statB T i w a b) 2 μ) ∧
    (∀ i a, MemLp (fun w => c.statD T i w a) 2 μ)

end Config

/-- The density ratio `r = dP/dQ` as a real number (the paper's `r = p/q`). -/
noncomputable def ratio (P Q : Measure X) (x : X) : ℝ := (P.rnDeriv Q x).toReal

/-- The absolute log-ratio `ℓ⋆ = log r`. -/
noncomputable def logRatioRN (P Q : Measure X) (x : X) : ℝ := Real.log (ratio P Q x)

/-- The population bias `B_{k,K,λ} = ∥ϕ⊤m − ℓ⋆∥_{L¹(Q)}` (13). -/
noncomputable def Config.constB (c : Config X) (P Q : Measure X) (μ : Measure Ω)
    (T : ℝ → Ω → X) : ℝ :=
  ∫ x, |c.ϕ x ⬝ᵥ c.popM μ T - logRatioRN P Q x| ∂Q

/-- The ratio tail `T_r(M) = E_Q[(r − M)₊]` (Theorem 3), in `ℝ≥0∞`. -/
noncomputable def ratioTail (P Q : Measure X) (M : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (P.rnDeriv Q x - ENNReal.ofReal M) ∂Q

/-- The expected log-ratio error `E∥f̂ − ℓ⋆∥_{L¹(Q)}` over `N` i.i.d. replicas `W₁, …, W_N ∼ μ`. -/
noncomputable def Config.expLogErr (c : Config X) (P Q : Measure X) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : ℝ → Ω → X) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ ws, ∫⁻ x, ENNReal.ofReal |c.fhat T ws x - logRatioRN P Q x| ∂Q
    ∂(Measure.pi fun _ : Fin N => μ)

/-- The expected capped-ratio error `E∥r̂_M − r∥_{L¹(Q)}`, `r̂_M = min{e^{f̂}, M}`, over `N`
i.i.d. replicas. -/
noncomputable def Config.expRatioErr (c : Config X) (P Q : Measure X) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : ℝ → Ω → X) (N : ℕ) (M : ℝ) : ℝ≥0∞ :=
  ∫⁻ ws, ∫⁻ x, ENNReal.ofReal |min (Real.exp (c.fhat T ws x)) M - ratio P Q x| ∂Q
    ∂(Measure.pi fun _ : Fin N => μ)

end Supplement

end LRTempElim


