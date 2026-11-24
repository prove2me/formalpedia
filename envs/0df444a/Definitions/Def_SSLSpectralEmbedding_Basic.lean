-- Prove2me | Definitions.Def_SSLSpectralEmbedding_Basic
-- name    : SSLSpectralEmbedding_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T06:23:15.644136+00:00
-- url     : https://prove2.me/theorems/ae345183-38f6-457b-9899-3e0b423b6c57
-- title:
--   Relation matrices, graph Laplacians, VICReg and SimCLR losses, and linear-probe objects
-- statement:
--   Objects of Sections 2, 3, 4.1 and 6 and Appendix A.15 of Balestriero and LeCun (2022). A data set has $N$ samples; a representation is a matrix $Z\in\mathbb{R}^{N\times K}$ whose $i$-th row $Z_{i,.}$ is the embedding of sample $i$.
--
--   1. **Relation matrix and Laplacian.** A relation matrix $G\in\mathbb{R}^{N\times N}$ is symmetric, has nonnegative entries and zero diagonal. $D=\operatorname{diag}(G\mathbf 1)$ is its degree matrix and $L=D-G$ its graph Laplacian. $H=I-\frac1N\mathbf 1\mathbf 1^\top$ is the centring matrix, and $\operatorname{Cov}(Z)=\frac1N Z^\top HZ$.
--   2. **VICReg (eq. 2).** $\mathcal L_{\rm var}(Z)=\sum_k\max(0,1-\sqrt{\operatorname{Cov}(Z)_{k,k}})$, $\mathcal L_{\rm cov}(Z)=\sum_k\sum_{j\ne k}\operatorname{Cov}(Z)_{k,j}^2$, $\mathcal L_{\rm inv}(Z)=\frac{\gamma}{N}\sum_{i,j}G_{i,j}\|Z_{i,.}-Z_{j,.}\|_2^2$, and $\mathcal L_{\rm vic}=\alpha\mathcal L_{\rm var}+\beta\mathcal L_{\rm cov}+\mathcal L_{\rm inv}$. The squared variant (Section 3.1) replaces $\mathcal L_{\rm var}$ by $\sum_k(1-\operatorname{Cov}(Z)_{k,k})^2$.
--   3. **Spectral data of VICReg (eq. 8).** $M_{\alpha,\gamma}=H-\frac{\gamma}{\alpha}L=P\operatorname{diag}(\lambda)P^\top$ with $P$ orthogonal and $\lambda_1\ge\dots\ge\lambda_N$. The candidate optimum is $Z^*_{\alpha,\gamma}=(P(\operatorname{diag}(\lambda)N)^{1/2})_{:,1:K}$.
--   4. **Laplacian Eigenmaps (eq. 11).** $Z^*_{\rm LE}$ minimises $\operatorname{Tr}(Z^\top LZ)$ over $Z$ with $Z^\top DZ=I$ and columns of zero mean.
--   5. **Linear VICReg (eq. 12).** For data $X\in\mathbb{R}^{N\times D}$, $B=\operatorname{Cov}(X)-\frac{\gamma}{\alpha N}X^\top LX$.
--   6. **Graph estimation (eqs. 14-16, 3).** For a dissimilarity $d$ on embeddings, $(\mathbf D)_{i,j}=d(Z_{i,.},Z_{j,.})$. The objective is $\sum_{i,j}\mathbf D_{i,j}W_{i,j}+\mathcal R(W)$ with $\mathcal R_{\log}(W)=\sum_{i\ne j}\tau W_{i,j}(\log W_{i,j}-1)$ (and $0\log0=0$). $\mathcal G$ is the set of symmetric nonnegative matrices with zero diagonal, and $\mathcal G_{\rm rsto}$ its right-stochastic elements. The kernels are $e^{-\mathbf D_{i,j}/\tau}1_{\{i\ne j\}}$ and its row-normalised version. The cosine distance is $1-\operatorname{CosSim}$, and the SimCLR estimate is $\widehat G(Z)_{i,j}=e^{\operatorname{CosSim}(z_i,z_j)/\tau}/\sum_{k\ne i}e^{\operatorname{CosSim}(z_i,z_k)/\tau}$ for $i\ne j$, $0$ on the diagonal.
--   7. **Linear probe (Section 6.1).** $\mathcal L(W)=\frac12\|Y-ZW\|_F^2$ for a target $Y\in\mathbb{R}^{N\times C}$.
--   8. **LDA scatter matrices (Appendix A.15).** For labels $y\in\{1,\dots,C\}^N$ with class sizes $N_c$, $G_{i,j}=1/N_c$ if $y_i=y_j=c$ and $0$ otherwise. Then $\Sigma_w=X^\top(I-G)X$ and $\Sigma_b=X^\top GX$.
--
--   **Formalization Note** $\operatorname{Cov}$ is normalised by $N$, as in the proofs of Appendix A.7-A.9 and the code for eq. (12). The code for eq. (2) uses `torch.cov`, which normalises by $N-1$. The sum in $\mathcal L_{\rm cov}$ runs over all ordered off-diagonal pairs, as in the code for eq. (2). The indicator in eq. (3) is printed as $1_{\{i=j\}}$ and in eq. (16) as $1_{\{1\ne j\}}$; both are read as $1_{\{i\ne j\}}$. For zero vectors the cosine similarity takes Lean's value $0/0=0$.
-- source:
--   Balestriero and LeCun, Contrastive and Non-Contrastive Self-Supervised Learning Recover Global and Local Spectral Embedding Methods, arXiv:2205.11508v3 (NeurIPS 2022), Sections 2, 3.1-3.3, 4.1, 6.1 and Appendix A.15

import Mathlib

/-!
Balestriero and LeCun, *Contrastive and Non-Contrastive Self-Supervised Learning Recover Global
and Local Spectral Embedding Methods*, arXiv:2205.11508v3 (NeurIPS 2022): the relation matrix,
graph Laplacian and VICReg losses of Sections 2 and 3, the Laplacian-Eigenmaps problem of
Section 3.2, the graph estimates of SimCLR in Section 4.1, the linear-probe loss of Section 6.1
and the scatter matrices of the LDA argument in Appendix A.15.

A data set of `N` samples with `K`-dimensional embeddings is a matrix `Z : Matrix (Fin N) (Fin K) ℝ`
whose `i`-th row is the embedding of sample `i`.
-/

noncomputable section

namespace SSLSpectralEmbedding

open Matrix

variable {N K : ℕ}

/-- Section 2, p. 3 and Fig. 1: a relation matrix `G` is symmetric, has nonnegative entries and
zero diagonal; `G i j > 0` marks samples `i` and `j` as a positive pair. -/
def IsRelationMatrix (G : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  G.IsSymm ∧ (∀ i j, 0 ≤ G i j) ∧ ∀ i, G i i = 0

/-- Section 3.1, below eq. (7), p. 6: the diagonal degree matrix `D` of `G`, `D i i = ∑ j, G i j`. -/
def degMat (G : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i => ∑ j, G i j

/-- Section 3.1, below eq. (7), p. 6: the graph Laplacian `L = D - G`. -/
def laplacian (G : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  degMat G - G

/-- Eq. (8), p. 6 and Appendix A.7: the centring matrix `H = I - (1/N) 1 1ᵀ` (the Laplacian of the
complete graph, scaled by `1/N`). -/
def centering (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  1 - Matrix.of fun _ _ => (1 / (N : ℝ))

/-- Appendix A.7–A.9: the covariance matrix of the columns of `Z`, `Cov(Z) = (1/N) Zᵀ H Z`
(normalised by `N`). -/
def cov (Z : Matrix (Fin N) (Fin K) ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  (1 / (N : ℝ)) • (Zᵀ * centering N * Z)

/-- Eq. (2) and eq. (7): the pairwise sum `∑_{i,j} G i j ‖Z_{i,.} - Z_{j,.}‖²` of the invariance
term. -/
def pairSum (G : Matrix (Fin N) (Fin N) ℝ) (Z : Matrix (Fin N) (Fin K) ℝ) : ℝ :=
  ∑ i, ∑ j, G i j * ∑ k, (Z i k - Z j k) ^ 2

/-- Eq. (2): the invariance term `L_inv(Z) = (γ/N) ∑_{i,j} G i j ‖Z_{i,.} - Z_{j,.}‖²`. -/
def invTerm (γ : ℝ) (G : Matrix (Fin N) (Fin N) ℝ) (Z : Matrix (Fin N) (Fin K) ℝ) : ℝ :=
  γ / N * pairSum G Z

/-- Eq. (2): the variance (hinge) term `L_var(Z) = ∑_k max(0, 1 - √Cov(Z)_{k,k})`. -/
def varTerm (Z : Matrix (Fin N) (Fin K) ℝ) : ℝ :=
  ∑ k, max 0 (1 - Real.sqrt (cov Z k k))

/-- Eq. (2): the covariance term `L_cov(Z) = ∑_k ∑_{j ≠ k} Cov(Z)_{k,j}²`. -/
def covTerm (Z : Matrix (Fin N) (Fin K) ℝ) : ℝ :=
  ∑ k, ∑ j, if j = k then 0 else cov Z k j ^ 2

/-- Eq. (2), p. 4: the VICReg loss `α L_var + β L_cov + L_inv`. -/
def vicLoss (α β γ : ℝ) (G : Matrix (Fin N) (Fin N) ℝ) (Z : Matrix (Fin N) (Fin K) ℝ) : ℝ :=
  α * varTerm Z + β * covTerm Z + invTerm γ G Z

/-- Section 3.1, p. 5: the VICReg loss with the hinge variance term replaced by the squared loss
`∑_k (1 - Cov(Z)_{k,k})²`. -/
def vicLossSq (α β γ : ℝ) (G : Matrix (Fin N) (Fin N) ℝ) (Z : Matrix (Fin N) (Fin K) ℝ) : ℝ :=
  α * ∑ k, (1 - cov Z k k) ^ 2 + β * covTerm Z + invTerm γ G Z

/-- Eq. (8), p. 6: the matrix `I - (1/N) 1 1ᵀ - (γ/α)(D - G)` whose eigendecomposition gives the
optimal VICReg representation. -/
def vicMat (α γ : ℝ) (G : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  centering N - (γ / α) • laplacian G

/-- Eq. (8): `M = P diag(λ) Pᵀ` with `P` orthogonal and the eigenvalues `λ` in descending order. -/
def IsDescEigendecomp (M P : Matrix (Fin N) (Fin N) ℝ) (lam : Fin N → ℝ) : Prop :=
  Pᵀ * P = 1 ∧ M = P * Matrix.diagonal lam * Pᵀ ∧ Antitone lam

/-- Theorem 1, p. 7: `Z*_{α,γ} = (P (diag(λ) N)^{1/2})_{:,1:K}`, the first `K` columns of `P`
scaled by `√(N λ_k)`. -/
def vicOpt (P : Matrix (Fin N) (Fin N) ℝ) (lam : Fin N → ℝ) (hKN : K ≤ N) :
    Matrix (Fin N) (Fin K) ℝ :=
  fun i k => P i (Fin.castLE hKN k) * Real.sqrt (lam (Fin.castLE hKN k) * N)

/-- Eq. (11), p. 9 and Section 3.2: an optimal Laplacian-Eigenmaps representation `Z*_LE`: it
minimises `Tr(Zᵀ (D - G) Z)` subject to `Zᵀ D Z = I`, among representations whose columns have
zero mean (LE discards the eigenvector of the eigenvalue `0`). -/
def IsLESolution (G : Matrix (Fin N) (Fin N) ℝ) (Z : Matrix (Fin N) (Fin K) ℝ) : Prop :=
  (Zᵀ * degMat G * Z = 1 ∧ ∀ k, ∑ i, Z i k = 0) ∧
    ∀ Z' : Matrix (Fin N) (Fin K) ℝ, Z'ᵀ * degMat G * Z' = 1 → (∀ k, ∑ i, Z' i k = 0) →
      (Zᵀ * laplacian G * Z).trace ≤ (Z'ᵀ * laplacian G * Z').trace

/-- Eq. (12), p. 10: `B = Cov(X) - (γ/(α N)) Xᵀ L X`, whose square root gives the optimal weights of
linear VICReg. -/
def linB {D : ℕ} (α γ : ℝ) (G : Matrix (Fin N) (Fin N) ℝ) (X : Matrix (Fin N) (Fin D) ℝ) :
    Matrix (Fin D) (Fin D) ℝ :=
  cov X - (γ / (α * N)) • (Xᵀ * laplacian G * X)

/-- Section 4.1, p. 11: the matrix of pairwise distances `(D)_{i,j} = d(f(x_i), f(x_j))` of the
embeddings (rows of `Z`). -/
def distMat (d : (Fin K → ℝ) → (Fin K → ℝ) → ℝ) (Z : Matrix (Fin N) (Fin K) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => d (Z i) (Z j)

/-- Eq. (14), p. 11: the graph-estimation objective `∑_{i,j} (D)_{i,j} (G)_{i,j} + R(G)`. -/
def graphObjective (Dm : Matrix (Fin N) (Fin N) ℝ) (R : Matrix (Fin N) (Fin N) ℝ → ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, Dm i j * W i j + R W

/-- Eq. (15), p. 11: the entropic regulariser `R_log(G) = ∑_{i≠j} τ G_{i,j} (log G_{i,j} - 1)`
(with `0 log 0 = 0`). -/
def entropyReg (τ : ℝ) (W : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else τ * W i j * (Real.log (W i j) - 1)

/-- Section 4.1, p. 11: `𝒢`, the symmetric matrices with nonnegative entries and zero diagonal. -/
def graphSet (N : ℕ) : Set (Matrix (Fin N) (Fin N) ℝ) :=
  {W | W.IsSymm ∧ (∀ i j, 0 ≤ W i j) ∧ ∀ i, W i i = 0}

/-- Section 4.1, p. 11: `𝒢_rsto = {G ∈ 𝒢 : G 1 = 1}`, the right-stochastic elements of `𝒢`. -/
def rstoSet (N : ℕ) : Set (Matrix (Fin N) (Fin N) ℝ) :=
  {W | W ∈ graphSet N ∧ ∀ i, ∑ j, W i j = 1}

/-- Appendix A.10, p. 27: the set over which the proof of Theorem 4 solves the `𝒢_rsto` problem:
nonnegative, zero-diagonal, right-stochastic matrices (the proof does not impose symmetry). -/
def rowStochSet (N : ℕ) : Set (Matrix (Fin N) (Fin N) ℝ) :=
  {W | (∀ i j, 0 ≤ W i j) ∧ (∀ i, W i i = 0) ∧ ∀ i, ∑ j, W i j = 1}

/-- Eq. (16), first line: `(Ĝ)_{i,j} = exp(-(D)_{i,j}/τ) 1_{i≠j}`. -/
def expKernel (τ : ℝ) (Dm : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i = j then 0 else Real.exp (-Dm i j / τ)

/-- Eq. (16), second line: `(Ĝ)_{i,j} = exp(-(D)_{i,j}/τ) / ∑_{k≠i} exp(-(D)_{i,k}/τ) 1_{i≠j}`. -/
def softmaxKernel (τ : ℝ) (Dm : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i = j then 0 else
    Real.exp (-Dm i j / τ) / ∑ k, (if k = i then 0 else Real.exp (-Dm i k / τ))

/-- Section 2, p. 4: the cosine similarity `⟨u, v⟩ / (‖u‖₂ ‖v‖₂)`. -/
def cosSim (u v : Fin K → ℝ) : ℝ :=
  (∑ k, u k * v k) / (Real.sqrt (∑ k, u k ^ 2) * Real.sqrt (∑ k, v k ^ 2))

/-- Appendix A.10, p. 28: the cosine distance `1 - ⟨u, v⟩ / (‖u‖ ‖v‖)`. -/
def cosineDist (u v : Fin K → ℝ) : ℝ :=
  1 - cosSim u v

/-- Eq. (3), p. 4: the SimCLR similarity estimate
`(Ĝ(Z))_{i,j} = exp(CosSim(z_i,z_j)/τ) / ∑_{k≠i} exp(CosSim(z_i,z_k)/τ)` for `i ≠ j`, and `0` on the
diagonal. -/
def simclrSim (τ : ℝ) (Z : Matrix (Fin N) (Fin K) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i = j then 0 else
    Real.exp (cosSim (Z i) (Z j) / τ) / ∑ k, (if k = i then 0 else Real.exp (cosSim (Z i) (Z k) / τ))

/-- Squared Frobenius norm `‖A‖_F²`. -/
def frobSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- Section 6.1, p. 15: the linear-probe loss `L(W) = (1/2) ‖Y - Z W‖_F²`. -/
def lsLoss {C : ℕ} (Y : Matrix (Fin N) (Fin C) ℝ) (Z : Matrix (Fin N) (Fin K) ℝ)
    (W : Matrix (Fin K) (Fin C) ℝ) : ℝ :=
  (1 / 2) * frobSq (Y - Z * W)

/-- Appendix A.15, p. 30: the supervised relation matrix normalised to degree `I`:
`(G)_{i,j} = 1/N_c` if samples `i` and `j` both belong to class `c` (with `N_c` samples), else `0`. -/
def ldaRelation {C : ℕ} (y : Fin N → Fin C) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if y i = y j then 1 / ((Finset.univ.filter fun k => y k = y i).card : ℝ) else 0

/-- Appendix A.15, p. 30: the within-class scatter `Σ_w = Xᵀ (I - G) X`. -/
def withinScatter {D C : ℕ} (X : Matrix (Fin N) (Fin D) ℝ) (y : Fin N → Fin C) :
    Matrix (Fin D) (Fin D) ℝ :=
  Xᵀ * (1 - ldaRelation y) * X

/-- Appendix A.15, p. 30: the between-class scatter `Σ_b = Xᵀ G X`. -/
def betweenScatter {D C : ℕ} (X : Matrix (Fin N) (Fin D) ℝ) (y : Fin N → Fin C) :
    Matrix (Fin D) (Fin D) ℝ :=
  Xᵀ * ldaRelation y * X

end SSLSpectralEmbedding


