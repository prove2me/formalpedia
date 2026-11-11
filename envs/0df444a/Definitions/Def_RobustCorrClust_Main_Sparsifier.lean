-- Prove2me | Definitions.Def_RobustCorrClust_Main_Sparsifier
-- name    : RobustCorrClust_Main_Sparsifier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:39:43.100866+00:00
-- url     : https://prove2.me/theorems/c7573b1b-b445-446a-b0bb-20b013f5fffc
-- title:
--   Frobenius inner product, weighted graphs, Laplacians, (1 ± ε)-spectral sparsifiers, the rescaling H̃ and the sparsified loss Ψ_H̃ (Definitions 2–3)
-- statement:
--   For real $n\times n$ matrices, $\langle X,Y\rangle=\sum_{u,v}X_{uv}Y_{uv}$ and $\|X\|_F^2=\langle X,X\rangle$.
--
--   A **weighted graph** on $V$ is given by its weighted adjacency matrix $W$: symmetric, with nonnegative entries and zero diagonal. Its **Laplacian** is $L_W=\mathrm{Diag}(W\mathbf 1)-W$ and its **total weight** is $W_{\mathrm{tot}}=\tfrac12\mathbf 1^\top W\mathbf 1$.
--
--   **Definition 2.** For $\varepsilon\in\mathbb R$, a weighted graph $H$ is a **$(1\pm\varepsilon)$-spectral sparsifier** of the weighted graph $W$ if $H$ is a weighted subgraph of $W$ (every pair of weight $0$ in $W$ has weight $0$ in $H$) and
--   $$(1-\varepsilon)\,x^\top L_W x\le x^\top L_H x\le(1+\varepsilon)\,x^\top L_W x\qquad\text{for all }x\in\mathbb R^n.$$
--
--   The **rescaled sparsifier** $\tilde H$ has weights $w_H/(1-\varepsilon)$.
--
--   **Definition 3.** For a signed graph $G$ with $m=|E^+|$ and a weighted graph $\tilde H$,
--   $$\Psi_{\tilde H}(Y)=\langle L_{\tilde H},Y\rangle+\tfrac12\|Y\|_F^2-\tfrac n2-m .$$
--
--   **Formalization Note.** A weighted graph is its adjacency matrix `Matrix (Fin n) (Fin n) ℝ`; the positive graph $G^+$ of a signed graph is the 0/1 matrix `adjMat G`. All norms and inner products are explicit entrywise sums (Mathlib's default matrix norm is the sup norm).
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), pp. 14-15, Definition 2; p. 19, Definition 3

import Mathlib
import Definitions.Def_RobustCorrClust_Main_SignedGraph

namespace RobustCorrClust.Main

open Finset Matrix

/-! Weighted graphs, Laplacians and spectral sparsifiers (§3, pp. 14–15, Definition 2) and the
sparsified square loss `Ψ_H̃` (§4.2, p. 19, Definition 3). A weighted graph on `Fin n` is given
by its weighted adjacency matrix. -/

/-- The trace (Frobenius) inner product `⟨X, Y⟩ = ∑_{u,v} X_uv Y_uv`. -/
def frobInner {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ u, ∑ v, X u v * Y u v

/-- The squared Frobenius norm `‖X‖²_F = ∑_{u,v} X_uv²`. -/
def frobSq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  frobInner X X

/-- `W` is the weighted adjacency matrix of a weighted graph on `Fin n`: symmetric, nonnegative
weights, zero diagonal (no loops). -/
def IsWeightedGraph {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  W.IsSymm ∧ (∀ u v, 0 ≤ W u v) ∧ ∀ u, W u u = 0

/-- The graph Laplacian `L = Diag(A 1) − A` of a weighted adjacency matrix `A` (p. 14). -/
def lap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun u => ∑ v, A u v) - A

/-- The quadratic form `xᵀ L x`. -/
def quadForm {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  x ⬝ᵥ (L *ᵥ x)

/-- The total weight `W_G = ½ 1ᵀ A 1`. -/
noncomputable def totalWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ u, ∑ v, A u v

/-- Definition 2 (p. 15): the weighted graph `H` is a `(1 ± ε)`-spectral sparsifier of the
weighted graph `A`: `H` is a weighted subgraph of `A` (every pair of weight `0` in `A` has
weight `0` in `H`) and `(1 − ε) xᵀL_A x ≤ xᵀL_H x ≤ (1 + ε) xᵀL_A x` for every `x ∈ ℝⁿ`. -/
def IsSpectralSparsifier {n : ℕ} (ε : ℝ) (A H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsWeightedGraph H ∧ (∀ u v, A u v = 0 → H u v = 0) ∧
    ∀ x : Fin n → ℝ, (1 - ε) * quadForm (lap A) x ≤ quadForm (lap H) x ∧
      quadForm (lap H) x ≤ (1 + ε) * quadForm (lap A) x

/-- The rescaled sparsifier `H̃` (p. 19): same edges, weights `w_H / (1 − ε)`. -/
noncomputable def rescale {n : ℕ} (ε : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 - ε)⁻¹ • H

/-- Definition 3 (p. 19): `Ψ_H̃(Y) := ⟨L_H̃, Y⟩ + ½‖Y‖²_F − n/2 − m`, where `Ht` is the weighted
adjacency matrix of `H̃` and `m = |E⁺|` is the number of positive pairs of the input graph `G`. -/
noncomputable def PsiTilde {n : ℕ} (G : SimpleGraph (Fin n)) (Ht Y : Matrix (Fin n) (Fin n) ℝ) :
    ℝ :=
  frobInner (lap Ht) Y + frobSq Y / 2 - (n : ℝ) / 2 - (numPos G : ℝ)

end RobustCorrClust.Main


