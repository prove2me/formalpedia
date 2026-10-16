-- Prove2me | Definitions.Def_RobustSpecClust_Round_Setting
-- name    : RobustSpecClust_Round_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:48.356832+00:00
-- url     : https://prove2.me/theorems/fde9aa9d-0c6a-4fd5-864f-1e30b8f50956
-- title:
--   §3, §4.2, App. G — cluster sizes, X⁰, U⁰, ℓ₁/Frobenius norms, top-r eigenvectors, membership matrices, (1+ε)-approximate k-means, misclassified sets (G.3)
-- statement:
--   This file fixes the objects of the rounding step of the robust spectral clustering algorithm of Srivastava, Sarkar and Hanasusanto (Algorithm 1, steps 3–4) and of its analysis in Appendix G, in the setting **without outliers**.
--
--   1. **Labels and cluster sizes.** There are $n$ points and $r$ clusters. A fixed label map $\varphi : [n] \to [r]$ defines the clusters $C_k = \{ i : \varphi(i) = k\}$ with sizes $n_k = |C_k|$, and $n_{\min} = \min_{k \in [r]} n_k$ (defined when $r \ge 1$).
--   2. **Matrix norms.** For a real matrix $A$, $\|A\|_1 = \sum_{i,j} |A_{ij}|$ is the entrywise $\ell_1$ norm and $\|A\|_F^2 = \sum_{i,j} A_{ij}^2$ the squared Frobenius norm. For a vector $x$, $\|x\| = (\sum_j x_j^2)^{1/2}$.
--   3. **True clustering matrix.** $X^0 \in \{0,1\}^{n \times n}$ has $X^0_{ij} = 1$ if and only if $\varphi(i) = \varphi(j)$.
--   4. **Scaled membership matrix.** $U^0 = Z^0 \,\mathrm{Diag}(1/\sqrt{n_1}, \dots, 1/\sqrt{n_r})$, i.e. $U^0_{ik} = 1/\sqrt{n_k}$ if $\varphi(i) = k$ and $0$ otherwise, where $Z^0$ is the membership matrix of $\varphi$.
--   5. **Top-$r$ eigenvectors.** For a square matrix $A$ and $U \in \mathbb R^{n \times r}$, "$U$ consists of orthonormal top-$r$ eigenvectors of $A$ with eigenvalues $\lambda_1, \dots, \lambda_r$" means
--   $$U^\top U = I_r,\qquad AU = U\,\mathrm{Diag}(\lambda_1,\dots,\lambda_r),\qquad v^\top A v \le \lambda_k\, v^\top v \ \text{ for all } k \text{ and all } v \text{ with } U^\top v = 0 .$$
--   The last clause says that every Rayleigh quotient on the orthogonal complement of the column space of $U$ is at most each selected eigenvalue, so the $\lambda_k$ are the $r$ largest eigenvalues (with multiplicity, ties broken arbitrarily). $U$ is a top-$r$ eigenvector matrix of $A$ if such $\lambda$ exist.
--   6. **Membership matrices.** $\mathbb M_{n,r}$ is the set of $\{0,1\}$-matrices in $\mathbb R^{n\times r}$ with exactly one $1$ in each row. Such a matrix is written $\Theta = \Theta(a)$ for an assignment $a : [n] \to [r]$, with $\Theta(a)_{ik} = 1$ iff $a(i) = k$; this is a bijection between assignments and $\mathbb M_{n,r}$.
--   7. **Approximate k-means.** The k-means cost of $(\Theta(a), B)$, $B \in \mathbb R^{r \times r}$, on the rows of $V \in \mathbb R^{n\times r}$ is $\|V - \Theta(a) B\|_F^2$, the objective of (G.1). The pair $(a, B)$ is a $(1+\epsilon)$-approximate solution, (G.2), if
--   $$\|V - \Theta(a)B\|_F^2 \le (1+\epsilon)\,\|V - \Theta(a')B'\|_F^2 \quad\text{for every assignment } a' \text{ and every } B' \in \mathbb R^{r\times r}.$$
--   8. **Misclassified sets.** For $V, \bar V \in \mathbb R^{n \times r}$ with rows $v_i, \bar v_i$ and thresholds $\delta_1,\dots,\delta_r$, the set (G.3) is
--   $$\mathcal S_k = \{ i \in C_k : \|\bar v_i - v_i\| \ge \delta_k / 2\}.$$
--
--   These objects are shared by every statement of the mission: Davis–Kahan, the eigenstructure of $X^0$, Lemma 5 of Lei and Rinaldo, and Theorem 2.
--
--   **Formalization Note** Points are `Fin n`, clusters `Fin r`; matrices are `Matrix ι κ ℝ`. $n_{\min}$ is `Finset.inf'` over the clusters and needs `[NeZero r]`. The norms are explicit sums, not Mathlib's matrix norm instances. "Exactly one 1 per row" is encoded by the assignment `a`, and "$\le (1+\epsilon)\min$" by "$\le (1+\epsilon)\cdot$ every cost" (the minimum over the finite set of assignments and the closed set of centres is attained). The labels $\varphi$ are fixed (the paper draws them from a multinomial, but its analysis conditions on them).
-- source:
--   arXiv:1912.07546v3, §2.1 (p. 6, ‖·‖₁), §2.2 (p. 7, X⁰), §3 Algorithm 1 steps 3–4 and p. 10 ((1+ε)-approximate k-means), §4.2 (pp. 16–17), Appendix G Lemma 5 (G.1)–(G.3) (pp. 45–46), proof of Theorem 2 (p. 46, U⁰ = Z⁰Diag(1/√n_k))

import Mathlib

namespace RobustSpecClust.Round

open Matrix

/-- Size `n_k` of the true cluster `C_k = {i | φ i = k}` for the fixed label map `φ`. -/
def clusterSize {n r : ℕ} (φ : Fin n → Fin r) (k : Fin r) : ℕ :=
  (Finset.univ.filter (fun i => φ i = k)).card

/-- The smallest cluster size `n_min = min_k n_k` (needs at least one cluster). -/
noncomputable def nmin {n r : ℕ} [NeZero r] (φ : Fin n → Fin r) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun k => (clusterSize φ k : ℝ))

/-- Entrywise ℓ₁ norm `‖A‖₁ = ∑_{i,j} |A_ij|` (§2.1, p. 6; not an operator norm). -/
def l1 {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

/-- Squared Frobenius norm `‖A‖_F² = ∑_{i,j} A_ij²`. -/
def frobSq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- Euclidean norm of a real vector, `‖x‖ = (∑_j x_j²)^{1/2}`. -/
noncomputable def vecNorm {κ : Type*} [Fintype κ] (x : κ → ℝ) : ℝ :=
  Real.sqrt (∑ j, x j ^ 2)

/-- The true clustering matrix `X⁰` without outliers: `X⁰_ij = 1` iff `i` and `j`
have the same label (p. 7). -/
def trueClust {n r : ℕ} (φ : Fin n → Fin r) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if φ i = φ j then 1 else 0

/-- The membership matrix of an assignment `a : Fin n → Fin r`: row `i` has its single
`1` in column `a i`. The map `a ↦ memb a` is a bijection onto `𝕄_{n,r}`, the set of
`{0,1}`-matrices with exactly one `1` in each row (Lemma 5, p. 45). -/
def memb {n r : ℕ} (a : Fin n → Fin r) : Matrix (Fin n) (Fin r) ℝ :=
  fun i k => if a i = k then 1 else 0

/-- `U⁰ = Z⁰ Diag(1/√n₁, …, 1/√n_r)` (Appendix G, p. 46). -/
noncomputable def U0 {n r : ℕ} (φ : Fin n → Fin r) : Matrix (Fin n) (Fin r) ℝ :=
  fun i k => if φ i = k then 1 / Real.sqrt (clusterSize φ k) else 0

/-- The columns of `U` are orthonormal eigenvectors of `A` with eigenvalues `λ k`, and
these are the `r` largest eigenvalues: every Rayleigh quotient of `A` on the orthogonal
complement of the column space of `U` is at most each `λ k`. -/
def IsTopEigvecsWith {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin n) (Fin r) ℝ)
    (lam : Fin r → ℝ) : Prop :=
  Uᵀ * U = 1 ∧ A * U = U * Matrix.diagonal lam ∧
    ∀ v : Fin n → ℝ, Uᵀ *ᵥ v = 0 → ∀ k, v ⬝ᵥ (A *ᵥ v) ≤ lam k * (v ⬝ᵥ v)

/-- `U` is a matrix of orthonormal top-`r` eigenvectors of `A` (ties broken arbitrarily). -/
def IsTopEigvecs {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin n) (Fin r) ℝ) :
    Prop :=
  ∃ lam : Fin r → ℝ, IsTopEigvecsWith A U lam

/-- The k-means cost `‖V − ΘB‖_F²` of the membership matrix `Θ = memb a` and centres `B`
(objective of (G.1)). -/
def kmeansCost {n r : ℕ} (V : Matrix (Fin n) (Fin r) ℝ) (a : Fin n → Fin r)
    (B : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  frobSq (V - memb a * B)

/-- `(memb a, B)` is a `(1+ε)`-approximate solution of the k-means problem (G.1) on the
rows of `V`, i.e. (G.2): its cost is at most `(1+ε)` times the cost of every
membership matrix and every centre matrix. -/
def IsApproxKMeans {n r : ℕ} (ε : ℝ) (V : Matrix (Fin n) (Fin r) ℝ) (a : Fin n → Fin r)
    (B : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  ∀ (a' : Fin n → Fin r) (B' : Matrix (Fin r) (Fin r) ℝ),
    kmeansCost V a B ≤ (1 + ε) * kmeansCost V a' B'

/-- The set (G.3): `S_k = {i ∈ G_k : ‖v̄_i − v_i‖ ≥ δ_k / 2}`, where `G_k = {i | φ i = k}`,
`v_i` and `v̄_i` are the rows of `V` and `Vbar`. -/
noncomputable def misSet {n r : ℕ} (V Vbar : Matrix (Fin n) (Fin r) ℝ) (φ : Fin n → Fin r)
    (δ : Fin r → ℝ) (k : Fin r) : Finset (Fin n) :=
  Finset.univ.filter (fun i => φ i = k ∧ δ k / 2 ≤ vecNorm (Vbar i - V i))

end RobustSpecClust.Round


