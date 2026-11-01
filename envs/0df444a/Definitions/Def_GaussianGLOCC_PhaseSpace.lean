-- Prove2me | Definitions.Def_GaussianGLOCC_PhaseSpace
-- name    : GaussianGLOCC_PhaseSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:22:50.617381+00:00
-- url     : https://prove2.me/theorems/2a3ae2a3-826d-4e42-a011-0dd13e5e7073
-- title:
--   Phase-space layout: $\sigma$, bipartite blocks, $c(r)$, $s(r)$ and the TMSS normal form
-- statement:
--   Phase space of $n$ bosonic modes is $\mathbb R^{2n}$ with interleaved coordinates $R=(X_1,P_1,\dots,X_n,P_n)$. The canonical commutation relations read $[R_j,R_k]=i\sigma_{jk}$ with the **symplectic matrix**
--
--   $$
--   \sigma=\bigoplus_{k=1}^{n}\sigma_1,\qquad \sigma_1=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
--   $$
--
--   A bipartite system of $n_A+n_B$ modes is split into system $A$ (the first $n_A$ modes) and system $B$ (the last $n_B$ modes), and a real $2(n_A+n_B)$-square matrix is written in blocks
--
--   $$
--   \gamma=\begin{pmatrix}A&C\\C^{T}&B\end{pmatrix}.
--   $$
--
--   A local symplectic transformation is $S_A\oplus S_B$. For a vector $r\in\mathbb R^n$ of squeezing parameters put, with $\Lambda=\operatorname{diag}(1,-1)$,
--
--   $$
--   c(r)=\bigoplus_k\cosh(r_k)\,\mathbb 1_2,\qquad s(r)=\bigoplus_k\sinh(r_k)\,\Lambda,\qquad \gamma_r=\begin{pmatrix}c(r)&s(r)\\s(r)&c(r)\end{pmatrix}.
--   $$
--
--   $\gamma_r$ is the covariance matrix of the product of $n$ two-mode squeezed states (TMSS), $A$-mode $k$ paired with $B$-mode $k$; for one pair it is the matrix $\gamma_r=\begin{pmatrix}A_r&C_r\\C_r&A_r\end{pmatrix}$, $A_r=\cosh(r)\mathbb 1$, $C_r=\sinh(r)\Lambda$, of eq. (3). These are the matrices every statement of the mission is written in.
--
--   **Formalization Note** The paper's $\sigma$ is the negative of the published `interleavedSymplecticForm`; both give the same symplectic group. The vacuum covariance matrix is $\mathbb 1$, so $\gamma_0=\mathbb 1$ (checked in the sanity file). $\Lambda$ on $n$ modes is the published `Claimed50.P37.reflection`.
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, §2, eqs. (3)–(4), p.3; eqs. (8), (17), p.4, 6; eq. (22), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P37
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex interleavedSymplecticForm)
open QAlgorithms.Papers.Independent.Claimed50.P37 (reflection)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, *Entanglement transformations of pure Gaussian states*,
arXiv:quant-ph/0301038v1, eq. (4), p.3: the symplectic matrix `σ = ⊕ σ₁`,
`σ₁ = [[0, −1], [1, 0]]`, with `[R_j, R_k] = i σ_{j,k}`.

**Formalization Note.** Coordinates are interleaved `(X₁, P₁, …)` (`QuadratureIndex n = Fin n × Fin 2`,
`0 = X`, `1 = P`), as `R := (X1, P1, . . . , X2n, P2n)` on p.3. The published
`interleavedSymplecticForm n` is `⊕ [[0, 1], [−1, 0]]`, the negative of the paper's `σ`; this
definition is its negative, so `σ` here is literally the paper's. Both signs define the same
symplectic group (`isSymplectic` of the published module). -/
def sigma (n : ℕ) : Cov n := -interleavedSymplecticForm n

/-- arXiv:quant-ph/0301038v1, p.3–4: the A/B layout of an `(nA + nB)`-mode phase space.
System A is the first `nA` modes (`Fin.castAdd`), system B the last `nB` modes (`Fin.natAdd`);
within each mode the order is `(X, P)`.

**Formalization Note.** This equivalence sends `Sum.inl (k, q)` to mode `k` of A and
`Sum.inr (k, q)` to mode `nA + k` (mode `k` of B), quadrature `q`. -/
def abSplit (nA nB : ℕ) :
    QuadratureIndex nA ⊕ QuadratureIndex nB ≃ QuadratureIndex (nA + nB) :=
  (Equiv.sumProdDistrib (Fin nA) (Fin nB) (Fin 2)).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl (Fin 2)))

/-- arXiv:quant-ph/0301038v1, eq. (17), p.6 (and (40), p.10): the bipartite matrix
`γ = [[A, C], [Cᵀ, B]]`, with A's block first, written in the A/B layout of `abSplit`. -/
def blockCov {nA nB : ℕ} (A : Cov nA) (C : Matrix (QuadratureIndex nA) (QuadratureIndex nB) ℝ)
    (B : Cov nB) : Cov (nA + nB) :=
  Matrix.reindex (abSplit nA nB) (abSplit nA nB) (Matrix.fromBlocks A C C.transpose B)

/-- arXiv:quant-ph/0301038v1, eq. (17), p.6: the A–A block `A` of a bipartite matrix `γ`. -/
def blockA {nA nB : ℕ} (γ : Cov (nA + nB)) : Cov nA :=
  γ.submatrix (fun x => abSplit nA nB (Sum.inl x)) (fun x => abSplit nA nB (Sum.inl x))

/-- arXiv:quant-ph/0301038v1, eq. (17), p.6: the A–B block `C` of a bipartite matrix `γ`
(rows A, columns B). For a symmetric `γ` the B–A block is `Cᵀ`. -/
def blockC {nA nB : ℕ} (γ : Cov (nA + nB)) :
    Matrix (QuadratureIndex nA) (QuadratureIndex nB) ℝ :=
  γ.submatrix (fun x => abSplit nA nB (Sum.inl x)) (fun x => abSplit nA nB (Sum.inr x))

/-- arXiv:quant-ph/0301038v1, eq. (17), p.6: the B–B block `B` of a bipartite matrix `γ`. -/
def blockB {nA nB : ℕ} (γ : Cov (nA + nB)) : Cov nB :=
  γ.submatrix (fun x => abSplit nA nB (Sum.inr x)) (fun x => abSplit nA nB (Sum.inr x))

/-- arXiv:quant-ph/0301038v1, p.3, eq. (5): the symplectic matrix `S_A ⊕ S_B` of a local
Gaussian unitary `U_A ⊗ U_B`, in the A/B layout of `abSplit`. -/
def localSymplectic {nA nB : ℕ} (SA : Cov nA) (SB : Cov nB) : Cov (nA + nB) :=
  blockCov SA 0 SB

/-- arXiv:quant-ph/0301038v1, eq. (22), p.7: `c(r) := ⊕_k cosh(r_k) 𝟙₂`. -/
noncomputable def cvec {n : ℕ} (r : Fin n → ℝ) : Cov n :=
  Matrix.diagonal (fun i => Real.cosh (r i.1))

/-- arXiv:quant-ph/0301038v1, eq. (22), p.7: `s(r) := ⊕_k sinh(r_k) Λ`, `Λ = diag(1, −1)`.

**Formalization Note.** The entry is `sinh(r_k)` on the X quadrature and `−sinh(r_k)` on the
P quadrature of mode `k`, i.e. `s(r) = c'(r) · Λ` with `Λ` the published `reflection`
(`diag(1, −1, …, 1, −1)`, eq. (8), p.4). -/
noncomputable def svec {n : ℕ} (r : Fin n → ℝ) : Cov n :=
  Matrix.diagonal (fun i => Real.sinh (r i.1) * reflection n i i)

/-- arXiv:quant-ph/0301038v1, eqs. (3) and (22), pp.3, 7: the covariance matrix of the
product `⊗_k ρ_{r_k}` of `n` two-mode squeezed states (TMSS), A-mode `k` paired with B-mode
`k`: `γ = [[c(r), s(r)], [s(r), c(r)]]`, i.e. `A_r = cosh(r)𝟙`, `C_r = sinh(r)Λ` per pair.

**Formalization Note.** The vacuum covariance matrix is `𝟙` (eq. (2), p.3, with the factor
`1/4`); A is the first `n` modes and B the last `n` (`abSplit`). `normalForm 0 = 1` (the
vacuum) is checked in `Solutions/verification/GaussianGLOCC_sanity.lean`. -/
noncomputable def normalForm {n : ℕ} (r : Fin n → ℝ) : Cov (n + n) :=
  blockCov (cvec r) (svec r) (cvec r)

end GaussianGLOCC


