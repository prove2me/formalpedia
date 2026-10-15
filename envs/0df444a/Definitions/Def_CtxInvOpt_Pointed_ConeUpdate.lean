-- Prove2me | Definitions.Def_CtxInvOpt_Pointed_ConeUpdate
-- name    : CtxInvOpt_Pointed_ConeUpdate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:30.623322+00:00
-- url     : https://prove2.me/theorems/6c8294c3-4a06-4700-bd12-4edc081ab390
-- title:
--   Algorithm 1 (ConeUpdate), p. 19, with η = 0, B = I_d, p = d — as a relation between input and output cones
-- statement:
--   Algorithm ConeUpdate (p. 19) takes an ellipsoidal cone $E(W,U)$ in $\mathbb R^p$, $p=m+1$, and a vector $\delta$, and returns a new cone $E(\widetilde W,\widetilde U)$. With $\eta=0$ and $B=I$, let $\bar\delta=(U^{-1}\delta)_{[2:p]}/\|(U^{-1}\delta)_{[2:p]}\|$.
--
--   1. **If $p=2$:** $b=\sqrt W\bar\delta$, $a=b/2$, $V_1=(1,a)'/\sqrt{1+a^2}$, $V$ is any orthonormal basis with first element $V_1$, $\widetilde U=UV$ and $\widetilde W=W/2$.
--   2. **If $p\ge 3$:** with $b=W\bar\delta/\sqrt{\bar\delta'W\bar\delta}$ and $a=b/p$,
--   $$N=\frac{(p-1)^2}{(p-1)^2-1}\Big(W-\frac{2}{p}\,bb'\Big),\qquad M=\begin{pmatrix}1&a'\\ a&aa'-N\end{pmatrix};$$
--   $V\Lambda V'$ is a spectral decomposition of $M$, $\widetilde U=UV$, and the diagonal of $\widetilde W$ lists the eigenvalues of $N$.
--
--   $N$ and $a$ are exactly one step of the ellipsoid method in dimension $p-1$ for the ellipsoid with shape matrix $W$, centred at $0$, cut through its centre along $\bar\delta$.
--
--   **Formalization Note** The algorithm is encoded as a predicate `IsConeUpdate w U δ w' U'`, because its output is not unique. Three choices the page leaves open are fixed and disclosed. (i) The printed $U^{-1}B\delta_{[2:p]}$ multiplies a $p\times p$ matrix by a $(p-1)$-vector; it is read as $(U^{-1}\delta)_{[2:p]}$. (ii) The columns of $V$: the first is the eigenvector of the unique positive eigenvalue $\mu_0$ of $M$ (whose Schur complement $-N$ is negative definite), normalised so that $V_{00}>0$; the others carry the negative eigenvalues $\mu_{i+1}$. (iii) The pairing: whenever $|\mu_{j+1}|<|\mu_{i+1}|$, $\widetilde W_{jj}\le\widetilde W_{ii}$. Algorithm 1 ($\widetilde W_{ii}=\lambda_{p-i}(N)$) and Lemma B-1 ($\lambda_i(N)$, nonincreasing) disagree and neither fixes the order of $V$; this pairing is the one under which the inclusion of Lemma B-1 holds numerically, while the reverse pairing fails. $N$ and $a$ are the published `ellipsoidUpdateMatrix` and `ellipsoidUpdateCenter` (Bertsimas–Tsitsiklis, Theorem 8.1). The square root of the $1\times1$ matrix $W$ is $\sqrt{w_1}$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 19, Algorithm 1 (ConeUpdate); App-22, Lemma B-1

import Mathlib
import Definitions.Def_CtxInvOpt_Pointed_EllCone
import Definitions.Def_LinearOptimization_EllipsoidMethod

namespace CtxInvOpt.Pointed

open Matrix LinearOptimization

/-- **Algorithm 1, p. 19.** The bordered matrix `M = (1 a′; a aa′ − N)` of size `(m+1) × (m+1)`. -/
def borderedMatrix {m : ℕ} (a : Fin m → ℝ) (N : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of (Fin.cons (Fin.cons 1 a) (fun i => Fin.cons (a i) (fun j => a i * a j - N i j)))

/-- **Algorithm 1 (ConeUpdate), p. 19, with `η = 0`, `B = I_d`, `p = d = m + 1`.** The relation
"`(W̃, Ũ) = (diag w', U')` is an output of ConeUpdate on input `(diag w, U, δ)`".

* `δ̄ = (U⁻¹δ)_{[2:p]} / ‖(U⁻¹δ)_{[2:p]}‖` (Euclidean norm `√(v ⬝ᵥ v)`).
* **`p = 2` (`m = 1`):** `b = √W δ̄`, `a = b / 2`, `V₁ = (1, a)′/√(1 + a²)`, `V` any orthonormal matrix
  with first column `V₁`, `Ũ = UV`, `W̃ = W / 2`.
* **`p ≥ 3` (`m ≥ 2`):** `N = ((p−1)²/((p−1)²−1)) (W − (2/p) bb′)` with `b = Wδ̄/√(δ̄′Wδ̄)`, which is the
  ellipsoid-method matrix `ellipsoidUpdateMatrix W δ̄` in dimension `m`, and `a = b/p`, which is
  `ellipsoidUpdateCenter 0 W δ̄`; `M = (1 a′; a aa′ − N)`; `VΛV′` is a spectral decomposition of `M`
  (`MV = V diag μ`, `V` orthonormal) whose first column is the eigenvector of the positive eigenvalue
  `μ₀` with `V₀₀ > 0` and whose other columns carry the negative eigenvalues; `W̃` lists the
  eigenvalues of `N` (`N = P diag(w') Pᵀ`, `P` orthonormal), paired so that a strictly larger `|μ_{i+1}|`
  never goes with a smaller `W̃_i`; `Ũ = UV`. The page leaves the column order of `V` open; this
  pairing is the one under which Lemma B-1's inclusion holds. -/
def IsConeUpdate {m : ℕ} (w : Fin m → ℝ) (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (δ : EuclideanSpace ℝ (Fin (m + 1))) (w' : Fin m → ℝ)
    (U' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : Prop :=
  let v : Fin m → ℝ := tailVec (rotCoord U δ)
  let δbar : Fin m → ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v
  if m = 1 then
    let a : Fin m → ℝ := fun i => (1 / 2 : ℝ) * (Real.sqrt (w i) * δbar i)
    (∀ i, w' i = w i / 2) ∧
      ∃ V ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ,
        (∀ i, V i 0 = (Fin.cons 1 a : Fin (m + 1) → ℝ) i / Real.sqrt (1 + a ⬝ᵥ a)) ∧
        U' = U * V
  else
    let N := ellipsoidUpdateMatrix (Matrix.diagonal w) δbar
    let a := ellipsoidUpdateCenter 0 (Matrix.diagonal w) δbar
    ∃ V ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ, ∃ μ : Fin (m + 1) → ℝ,
      borderedMatrix a N * V = V * Matrix.diagonal μ ∧
      0 < μ 0 ∧ (∀ i : Fin m, μ i.succ < 0) ∧ 0 < V 0 0 ∧
      (∃ P ∈ Matrix.orthogonalGroup (Fin m) ℝ, N = P * Matrix.diagonal w' * Pᵀ) ∧
      (∀ i j : Fin m, |μ j.succ| < |μ i.succ| → w' j ≤ w' i) ∧
      U' = U * V

end CtxInvOpt.Pointed


