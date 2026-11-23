-- Prove2me | Definitions.Def_CtxInvOpt_Offline_Supplement_ConeUpdateEta
-- name    : CtxInvOpt_Offline_Supplement_ConeUpdateEta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:05:31.264373+00:00
-- url     : https://prove2.me/theorems/84e7a827-2a18-4e81-a152-61394283ec36
-- title:
--   Algorithm 1, p. 19 — ConeUpdate with margin η, basis B and dimension p
-- statement:
--   This file formalizes **ConeUpdate** (Algorithm 1), the update that ProjectedCones applies to an ellipsoidal cone inside a $p$-dimensional subspace.
--
--   The inputs are a diagonal matrix $W=\mathrm{diag}(w)$ with $p-1$ positive entries, an orthonormal $p\times p$ matrix $U$, a projected effective difference $\delta\in\mathbb R^d$, a margin $\eta\ge 0$, and a basis $B$ of $p$ orthonormal rows in $\mathbb R^d$. Put $v=(U^{-1}B\delta)_{[2:p]}$ and $\bar\delta=v/\|v\|$.
--
--   1. If $p=2$: $\beta=-\eta\bar\delta$, $b=\sqrt W\,\bar\delta$, $a=\tfrac{1+\beta}{2}b$, $V_1=(1,a)'/\sqrt{1+a^2}$; $V$ is any orthonormal matrix with first column $V_1$; the outputs are $\widetilde U=UV$ and $\widetilde W=W/2+\eta$.
--   2. If $p\ge 3$:
--   $$\beta=-\frac{\eta}{\sqrt{\bar\delta'W\bar\delta}},\quad b=\frac{W\bar\delta}{\sqrt{\bar\delta'W\bar\delta}},\quad a=\frac{1+(p-1)\beta}{p}\,b,$$
--   $$N=\frac{(p-1)^2}{(p-1)^2-1}(1-\beta^2)\Big(W-\frac{2(1+(p-1)\beta)}{p(1+\beta)}bb'\Big),\qquad M=\begin{pmatrix}1&a'\\ a&aa'-N\end{pmatrix}.$$
--   With a spectral decomposition $M=V\Lambda V'$, the outputs are $\widetilde U=UV$ and $\widetilde W$, the diagonal matrix of the eigenvalues of $N$ in nondecreasing order ($\widetilde W_{i,i}=\lambda_{p-i}(N)$, eigenvalues listed in nonincreasing order).
--
--   The relation $\mathrm{IsConeUpdateEta}$ holds exactly when $(\mathrm{diag}\,w',U')$ is one of the outputs that these choices allow.
--
--   **Formalization Note** The printed $U^{-1}B\delta_{[2:p]}$ is read as $(U^{-1}B\delta)_{[2:p]}$, the tail of the rotated coordinates; $U^{-1}$ is written $U^{\mathsf T}$, which is the same matrix for the orthonormal $U$ of a run. For $p\ge3$ the page leaves the column order of $V$ open. The relation takes the first column to be the eigenvector of the positive eigenvalue of $M$, with positive first entry, and pairs the other columns with $\widetilde W$ exactly as the published `CtxInvOpt.Pointed.IsConeUpdate` does. These constraints only restrict which outputs count. The published relation fixes $\eta=0$, $B=I$, $p=d$ and is not this algorithm; only its bordered matrix $M$ (`borderedMatrix`) is reused.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 19, Algorithm 1 (ConeUpdate)

import Mathlib
import Definitions.Def_CtxInvOpt_Pointed_ConeUpdate

namespace CtxInvOpt.Offline.Supplement

open Matrix

/-- The Euclidean norm `‖v‖ = √(v′v)` of a coordinate vector `v ∈ ℝᵏ`. -/
noncomputable def coordNorm {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ v)

/-- **arXiv:2106.14015v3, Algorithm 1 (ConeUpdate), p. 19, with margin `η`, basis `B` and dimension
`p = m + 1`.** The relation "`(W̃, Ũ) = (diag w', U')` is an output of
`ConeUpdate(W, U, δ, η, B, p)` on `W = diag w`, `U`, the projected vector `δ ∈ ℝᵈ`, the margin `η` and
the basis `B` (`p` orthonormal rows in `ℝᵈ`)".

* `δ̄ = (U⁻¹Bδ)_{[2:p]} / ‖(U⁻¹Bδ)_{[2:p]}‖` (the printed `U⁻¹Bδ_{[2:p]}` with the subscript on the
  rotated vector); `U⁻¹ = Uᵀ` for the orthogonal `U` of a run.
* **`p = 2` (`m = 1`):** `β = −ηδ̄`, `b = √W δ̄`, `a = ((1 + β)/2) b`, `V₁ = (1, a)′/√(1 + a²)`,
  `V` any orthonormal matrix with first column `V₁`, `Ũ = UV`, `W̃ = W/2 + η`.
* **`p ≥ 3`:** `β = −η/√(δ̄′Wδ̄)`, `b = Wδ̄/√(δ̄′Wδ̄)`, `a = ((1 + (p−1)β)/p) b`,
  `N = ((p−1)²/((p−1)²−1)) (1 − β²) (W − (2(1 + (p−1)β)/(p(1 + β))) bb′)`, `M = (1 a′; a aa′ − N)`;
  `VΛV′` is a spectral decomposition of `M` (`MV = V diag μ`, `V` orthonormal) whose first column is
  the eigenvector of the positive eigenvalue `μ₀` with `V₀₀ > 0`, the other columns carrying the
  negative eigenvalues; `Ũ = UV`; `W̃` lists the eigenvalues of `N` (`N = P diag(w') Pᵀ`, `P`
  orthonormal) in nondecreasing order (`W̃_{i,i} = λ_{p−i}(N)` with `λ₁ ≥ ⋯ ≥ λ_{p−1}`), and a strictly
  larger `|μ_{i+1}|` never goes with a smaller `W̃_i` (the pairing of the published
  `CtxInvOpt.Pointed.IsConeUpdate`). -/
def IsConeUpdateEta {d m : ℕ} (η : ℝ) (B : Matrix (Fin (m + 1)) (Fin d) ℝ)
    (w : Fin m → ℝ) (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (δ : EuclideanSpace ℝ (Fin d)) (w' : Fin m → ℝ)
    (U' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : Prop :=
  let v : Fin m → ℝ := CtxInvOpt.Pointed.tailVec (Uᵀ *ᵥ (B *ᵥ WithLp.ofLp δ))
  let δbar : Fin m → ℝ := (coordNorm v)⁻¹ • v
  if m = 1 then
    let β : Fin m → ℝ := fun i => -(η * δbar i)
    let b : Fin m → ℝ := fun i => Real.sqrt (w i) * δbar i
    let a : Fin m → ℝ := fun i => ((1 + β i) / 2) * b i
    (∀ i, w' i = w i / 2 + η) ∧
      ∃ V ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ,
        (∀ i, V i 0 = (Fin.cons 1 a : Fin (m + 1) → ℝ) i / Real.sqrt (1 + a ⬝ᵥ a)) ∧
        U' = U * V
  else
    let q : ℝ := δbar ⬝ᵥ (Matrix.diagonal w *ᵥ δbar)
    let β : ℝ := -η / Real.sqrt q
    let b : Fin m → ℝ := (Real.sqrt q)⁻¹ • (Matrix.diagonal w *ᵥ δbar)
    let a : Fin m → ℝ := ((1 + (m : ℝ) * β) / ((m : ℝ) + 1)) • b
    let N : Matrix (Fin m) (Fin m) ℝ :=
      (((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) * (1 - β ^ 2)) •
        (Matrix.diagonal w -
          ((2 * (1 + (m : ℝ) * β)) / (((m : ℝ) + 1) * (1 + β))) • Matrix.vecMulVec b b)
    ∃ V ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ, ∃ μ : Fin (m + 1) → ℝ,
      CtxInvOpt.Pointed.borderedMatrix a N * V = V * Matrix.diagonal μ ∧
      0 < μ 0 ∧ (∀ i : Fin m, μ i.succ < 0) ∧ 0 < V 0 0 ∧
      (∃ P ∈ Matrix.orthogonalGroup (Fin m) ℝ, N = P * Matrix.diagonal w' * Pᵀ) ∧
      Monotone w' ∧
      (∀ i j : Fin m, |μ j.succ| < |μ i.succ| → w' j ≤ w' i) ∧
      U' = U * V

end CtxInvOpt.Offline.Supplement


