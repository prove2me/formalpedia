-- Prove2me | Definitions.Def_AccelMM_BTMap_Model
-- name    : AccelMM_BTMap_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:33:13.889995+00:00
-- url     : https://prove2.me/theorems/cc11874f-f182-4eb3-8074-ac3a3ef6ab93
-- title:
--   §2, pp. 5–6, §3.2, p. 8 and §4.2, p. 12 — Bradley–Terry log-likelihood, Gamma prior, log-posterior ρ, MM surrogate, rescaling Π, M, L_M, d(M), a(M)
-- statement:
--   The Bradley–Terry model of paired comparisons with a Gamma prior, for $n$ items. The data are the counts $d_{i,j}\in\mathbb N$ of observed comparisons in which item $i$ beat item $j$; the diagonal $d_{i,i}$ is ignored. The parameter is $w\in\mathbb R^n$, with strengths $\theta_i=e^{w_i}$.
--
--   1. **Co-occurrence matrix** $M$: $m_{i,j}=d_{i,j}+d_{j,i}$ for $i\ne j$ and $m_{i,i}=0$; its maximum row sum $d(M)=\|M\|_\infty=\max_i\sum_j m_{i,j}$ (the maximum number of comparisons of an item); the Laplacian $L_M=D_M-M$ with $D_M$ the diagonal matrix of row sums; the **algebraic connectivity** $a(M)=\lambda_2(L_M)$, the second smallest eigenvalue of $L_M$; and its largest eigenvalue $\lambda_n(L_M)$.
--   2. $W_\omega=\{w:\|w\|_\infty\le\omega\}=[-\omega,\omega]^n$, $c_\omega=1/(e^{-\omega}+e^{\omega})^2$, $\mathbf 1$ the all-ones vector, and $A_{W_\omega}=c_\omega L_M+e^{-\omega}\beta I$.
--   3. **Log-likelihood** (2.3), **prior log-likelihood** (2.5) for a $\mathrm{Gamma}(\alpha,\beta)$ prior on each $e^{w_i}$, and **log-a posteriori function** (2.4):
--   $$\ell(w)=\sum_{i=1}^n\sum_{j\ne i}d_{i,j}\bigl(w_i-\log(e^{w_i}+e^{w_j})\bigr),\qquad \ell_0(w)=\sum_{i=1}^n\bigl((\alpha-1)w_i-\beta e^{w_i}\bigr),\qquad \rho=\ell+\ell_0 .$$
--   4. **MM surrogate** (2.7) and $\rho(x;y)=\ell(x;y)+\ell_0(x)$, where
--   $$\ell(x;y)=\sum_{i=1}^n\sum_{j\ne i}d_{i,j}\Bigl(x_i-\frac{e^{x_i}+e^{x_j}}{e^{y_i}+e^{y_j}}-\log(e^{y_i}+e^{y_j})+1\Bigr).$$
--   5. **Rescaling** (4.4)–(4.5): $\Pi(x)=x+c(x)\mathbf 1$ with
--   $$c(x)=\log\Bigl(\frac{\alpha-1}{\beta}\,n\Bigr)-\log\Bigl(\sum_{i=1}^n e^{x_i}\Bigr).$$
--
--   These objects are shared by every statement of the mission: MAP estimation maximizes $\rho$, the MM algorithm maximizes $\rho(\cdot\,;w^{(t)})$, and the accelerated algorithm applies $\Pi$ after each step.
--
--   **Formalization Note** Items are indexed by `Fin n` (0-based). The paper uses $M$ without displaying its entries; $m_{i,j}=d_{i,j}+d_{j,i}$ is the reading consistent with (2.8)–(2.9). Eigenvalues come from Mathlib's `eigenvalues₀`, listed in decreasing order, so $\lambda_n$ is index $0$ and $\lambda_2$ is index $n-2$; by convention $a(M)=0$ for $n<2$ and $\lambda_n(L_M)=0$ for $n=0$. $d(M)=0$ for $n=0$. $\rho$ is exactly (2.4), with no additive constant. $c(x)$ uses `Real.log`, which is $0$ on non-positive arguments; every statement involving $\Pi$ assumes $\alpha>1$ and $\beta>0$. The symmetry of $L_M$ is proved in the file (needed to take eigenvalues).
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), pp. 5–6, 8, 12, (2.3)–(2.5), (2.7), (4.4)–(4.5), Lemmas 3.1, 3.4

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework

namespace AccelMM.BTMap

/-- `W_ω = {w ∈ ℝⁿ : ‖w‖_∞ ≤ ω}` (§3.2–§4.2), the same set as `[−ω, ω]ⁿ`. -/
def box {n : ℕ} (ω : ℝ) : Set (E n) := {w | ∀ i, |w i| ≤ ω}

/-- The all-ones vector `1`. -/
noncomputable def ones (n : ℕ) : E n := WithLp.toLp 2 (fun _ => 1)

/-- `c_ω = 1/(e^{−ω} + e^{ω})²` (Lemma 3.1, p. 8). -/
noncomputable def cOmega (ω : ℝ) : ℝ := 1 / (Real.exp (-ω) + Real.exp ω) ^ 2

/-- Entries of the co-occurrence matrix `M`: `m_{i,j} = d_{i,j} + d_{j,i}` for `i ≠ j`, and
`m_{i,i} = 0`. -/
noncomputable def mM {n : ℕ} (d : Fin n → Fin n → ℕ) (i j : Fin n) : ℝ :=
  if i = j then 0 else ((d i j : ℝ) + d j i)

/-- `d(M) = ‖M‖_∞ = maxᵢ Σⱼ m_{i,j}`, the maximum number of comparisons per item
(`0` when `n = 0`). -/
noncomputable def degM {n : ℕ} (d : Fin n → Fin n → ℕ) : ℝ :=
  ⨆ i, ∑ j, mM d i j

/-- The Laplacian `L_M = D_M − M`, with `D_M` the diagonal matrix of the row sums of `M`. -/
noncomputable def lapM {n : ℕ} (d : Fin n → Fin n → ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => ∑ j, mM d i j) - Matrix.of (mM d)

theorem lapM_isHermitian {n : ℕ} (d : Fin n → Fin n → ℕ) : (lapM d).IsHermitian := by
  ext i j
  by_cases h : i = j
  · subst h; simp [lapM]
  · simp [lapM, mM, Matrix.diagonal, h, Ne.symm h, add_comm]

/-- `a(M) = λ₂(L_M)`, the second smallest eigenvalue of `L_M` (`eigenvalues₀` is listed in
decreasing order); `0` by convention when `n < 2`. -/
noncomputable def algConn {n : ℕ} (d : Fin n → Fin n → ℕ) : ℝ :=
  if h : 2 ≤ Fintype.card (Fin n) then
    (lapM_isHermitian d).eigenvalues₀ ⟨Fintype.card (Fin n) - 2, by omega⟩
  else 0

/-- `λ_n(L_M)`, the largest eigenvalue of `L_M`; `0` by convention when `n = 0`. -/
noncomputable def lamMax {n : ℕ} (d : Fin n → Fin n → ℕ) : ℝ :=
  if h : 1 ≤ Fintype.card (Fin n) then
    (lapM_isHermitian d).eigenvalues₀ ⟨0, by omega⟩
  else 0

/-- `A_{W_ω} = c_ω L_M + e^{−ω} β I` (§4.2, p. 12). -/
noncomputable def AW {n : ℕ} (d : Fin n → Fin n → ℕ) (ω β : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  cOmega ω • lapM d + (Real.exp (-ω) * β) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- (2.3): the Bradley–Terry log-likelihood `ℓ(w) = Σᵢ Σ_{j≠i} d_{i,j}(wᵢ − log(e^{wᵢ} + e^{wⱼ}))`. -/
noncomputable def loglik {n : ℕ} (d : Fin n → Fin n → ℕ) (w : E n) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    (d i j : ℝ) * (w i - Real.log (Real.exp (w i) + Real.exp (w j)))

/-- (2.5): the prior log-likelihood `ℓ₀(w) = Σᵢ ((α − 1)wᵢ − β e^{wᵢ})`. -/
noncomputable def logPrior {n : ℕ} (α β : ℝ) (w : E n) : ℝ :=
  ∑ i, ((α - 1) * w i - β * Real.exp (w i))

/-- (2.4): the log-a posteriori probability function `ρ(w) = ℓ(w) + ℓ₀(w)`. -/
noncomputable def rho {n : ℕ} (α β : ℝ) (d : Fin n → Fin n → ℕ) (w : E n) : ℝ :=
  loglik d w + logPrior α β w

/-- (2.7): the minorant surrogate `ℓ(x; y) = Σᵢ Σ_{j≠i} ℓ_{ij}(x; y)` with
`ℓ_{ij}(x; y) = d_{i,j}(xᵢ − (e^{xᵢ} + e^{xⱼ})/(e^{yᵢ} + e^{yⱼ}) − log(e^{yᵢ} + e^{yⱼ}) + 1)`. -/
noncomputable def surr {n : ℕ} (d : Fin n → Fin n → ℕ) (x y : E n) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    (d i j : ℝ) * (x i - (Real.exp (x i) + Real.exp (x j)) / (Real.exp (y i) + Real.exp (y j))
      - Real.log (Real.exp (y i) + Real.exp (y j)) + 1)

/-- §2, p. 6: the minorant surrogate of `ρ`, `ρ(x; y) = ℓ(x; y) + ℓ₀(x)`. -/
noncomputable def rhoSurr {n : ℕ} (α β : ℝ) (d : Fin n → Fin n → ℕ) (x y : E n) : ℝ :=
  surr d x y + logPrior α β x

/-- (4.5): `c(x) = log(((α − 1)/β) n) − log(Σᵢ e^{xᵢ})`. -/
noncomputable def shift {n : ℕ} (α β : ℝ) (x : E n) : ℝ :=
  Real.log ((α - 1) / β * n) - Real.log (∑ i, Real.exp (x i))

/-- (4.4): the rescaling `Π(x) = x + c(x)1`. -/
noncomputable def Pi {n : ℕ} (α β : ℝ) (x : E n) : E n :=
  x + shift α β x • ones n

end AccelMM.BTMap


