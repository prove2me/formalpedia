-- Prove2me | Definitions.Def_PrivGaussMS_Statistics
-- name    : PrivGaussMS_Statistics
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:49.858466+00:00
-- url     : https://prove2.me/theorems/e269535f-1f26-41c8-b6a5-7fa71ed911db
-- title:
--   Empirical mean $\bar x$, scatter $S$, augmented statistics $T_I$, $T$, $B$, block parameters $(\theta,C,b)$ and the nuclear norm
-- statement:
--   For a dataset $x=(x_1,\dots,x_n)$ of $\mathbb R^d$ write $\bar x=n^{-1}\sum_i x_i$, $S=\sum_i(x_i-\bar x)(x_i-\bar x)^T$ and $\tilde x_i=(x_i^T,1)^T$. For $I\subseteq[n]$,
--   $$T_I=\sum_{i\in I}\tilde x_i\tilde x_i^T,\qquad T=T_{[n]}=\begin{pmatrix}S+n\bar x\bar x^T& n\bar x\\ n\bar x^T& n\end{pmatrix},\qquad B=\sum_i\rho_i\tilde x_i\tilde x_i^T .$$
--   For a $(d+1)\times(d+1)$ matrix in the block form (14) the block parameters are the bottom-right entry $b$, the mean $\theta=b^{-1}B_{1:d,d+1}$ and the covariance $C=B_{1:d,1:d}-b\theta\theta^T$; for $B=T$ they are $(\bar x,S,n)$. The nuclear norm $\|M\|_*=\operatorname{tr}((M^TM)^{1/2})$ is the sum of singular values, and $B^{-1/2}B'B^{-1/2}-I_{d+1}$ is the relative change of two statistics. The affine map $x_i\mapsto Fx_i+v$ acts on augmented records by the matrix $\begin{pmatrix}F&v\\0&1\end{pmatrix}$.
--
--   **Formalization Note** Square roots are the symmetric positive semidefinite roots (`CFC.sqrt`); inverses are Lean's total inverse and are used only on positive definite matrices. Indices are 0-based and the augmented coordinate is the last one.
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), §B.2.1 eq. (12), p.34; §B.3.1 eq. (14), p.35; §B.3.2, p.37; notation p.23

import Mathlib
import Definitions.Def_PrivGaussMS_Basics

open MeasureTheory Matrix
open scoped MatrixOrder

namespace PrivGaussMS

/-!
# Raw and weighted empirical statistics in augmented form

Moayedi, Yassaee, Ebrahimi, *Optimal Private Gaussian Multi-sampling*, STOC 2027 submission
(manuscript sha256 1838c582…), §B.2.1, eq. (12), p.34; §B.3.1, eq. (14), p.35; §B.3.2, p.37;
notation p.23 (nuclear norm `∥·∥_∗`, symmetric square roots).

**Formalization Note.**
* A dataset is `x : Fin n → ℝ^d` (rows `x_i`, the paper's `[n]` read 0-based). The augmented record
  is `x̃_i = (x_iᵀ, 1)ᵀ ∈ ℝ^{d+1}`, the augmented coordinate being the last index `Fin.last d`.
* `statI x I = T_I = Σ_{i∈I} x̃_i x̃_iᵀ`, `Tstat x = T` (12), `Bweighted x ρ = Σ ρ_i x̃_i x̃_iᵀ` (14).
* For a `(d+1) × (d+1)` matrix `B` in the block form (14) the block parameters are
  `b = B_{d+1,d+1}`, `θ = B_{1:d,d+1}/b` and `C = B_{1:d,1:d} − b θθᵀ` ("using its block parameters
  θ and C", p.35). When `b = 0`, Lean's `x/0 = 0` gives `θ = 0`, as the paper prescribes; for
  `B = Bweighted x ρ` with `b = 0` every weight vanishes and `C = 0` as well.
* Square roots are `CFC.sqrt` for the Loewner order (`open scoped MatrixOrder`): the symmetric PSD
  square root on PSD matrices (p.23). Inverses are Mathlib's `⁻¹` (`0` on singular matrices); every
  statement that uses one assumes the matrix is positive definite.
* `nuclearNorm M = tr((MᵀM)^{1/2})` is the sum of the singular values (`∥·∥_∗`, p.23).
-/

variable {n d : ℕ}

/-- The empirical mean `x̄ = n⁻¹ Σ_i x_i` (p.34). -/
noncomputable def mean (x : Fin n → Vec d) : Vec d := (n : ℝ)⁻¹ • ∑ i, x i

/-- The unnormalized empirical covariance `S = Σ_i (x_i − x̄)(x_i − x̄)ᵀ` (p.34). -/
noncomputable def scatter (x : Fin n → Vec d) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ i, Matrix.vecMulVec (WithLp.ofLp (x i - mean x)) (WithLp.ofLp (x i - mean x))

/-- The augmented record `x̃_i = (x_iᵀ, 1)ᵀ` (p.34). -/
noncomputable def aug (x : Fin n → Vec d) (i : Fin n) : Fin (d + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp (x i)) 1

/-- `T_I = Σ_{i∈I} x̃_i x̃_iᵀ` (p.37). -/
noncomputable def statI (x : Fin n → Vec d) (I : Finset (Fin n)) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  ∑ i ∈ I, Matrix.vecMulVec (aug x i) (aug x i)

/-- The raw augmented statistic `T = Σ_i x̃_i x̃_iᵀ` (12). -/
noncomputable def Tstat (x : Fin n → Vec d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  statI x Finset.univ

/-- The weighted augmented statistic `B = Σ_i ρ_i x̃_i x̃_iᵀ` (14). -/
noncomputable def Bweighted (x : Fin n → Vec d) (ρ : Fin n → ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  ∑ i, ρ i • Matrix.vecMulVec (aug x i) (aug x i)

/-- The bottom-right entry `b` of an augmented statistic (14). -/
def bw (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : ℝ := B (Fin.last d) (Fin.last d)

/-- The block mean `θ = B_{1:d,d+1}/b` of an augmented statistic (14). -/
noncomputable def blockMean (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Fin d → ℝ :=
  fun j => B (Fin.castSucc j) (Fin.last d) / bw B

/-- The block covariance `C = B_{1:d,1:d} − b θθᵀ` of an augmented statistic (14). -/
noncomputable def blockCov (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => B (Fin.castSucc i) (Fin.castSucc j) - bw B * blockMean B i * blockMean B j

/-- The augmented matrix of block parameters `(θ, C, b)`: `[[C + bθθᵀ, bθ], [bθᵀ, b]]` (14). -/
def blockMatrix (θ : Fin d → ℝ) (C : Matrix (Fin d) (Fin d) ℝ) (b : ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => Fin.lastCases
    (Fin.lastCases b (fun l => b * θ l) j)
    (fun k => Fin.lastCases (b * θ k) (fun l => C k l + b * θ k * θ l) j) i

/-- The nuclear norm `∥M∥_∗ = tr((MᵀM)^{1/2})`, the sum of singular values (p.23). -/
noncomputable def nuclearNorm {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  (CFC.sqrt (Mᵀ * M)).trace

/-- The relative change `B^{−1/2} B′ B^{−1/2} − I_{d+1}` (Lemmas B.3, B.5). -/
noncomputable def relChange (B B' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  (CFC.sqrt B)⁻¹ * B' * (CFC.sqrt B)⁻¹ - 1

/-- The augmented affine map `x̃ ↦ [[F, v], [0, 1]] x̃` of `x ↦ F x + v` (Lemma B.3, p.38). -/
def augAffine (F : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => Fin.lastCases
    (Fin.lastCases 1 (fun _ => 0) j)
    (fun k => Fin.lastCases (v k) (fun l => F k l) j) i

/-- The dataset `x_i ↦ F x_i + v` (Lemma B.3, p.38; Algorithm 3 discussion, p.36). -/
noncomputable def affineData (F : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (x : Fin n → Vec d) : Fin n → Vec d :=
  fun i => WithLp.toLp 2 (F *ᵥ WithLp.ofLp (x i) + v)

end PrivGaussMS


