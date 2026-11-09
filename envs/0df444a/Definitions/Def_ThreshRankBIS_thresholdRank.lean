-- Prove2me | Definitions.Def_ThreshRankBIS_thresholdRank
-- name    : ThreshRankBIS_thresholdRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:00:21.600832+00:00
-- url     : https://prove2.me/theorems/c3c2c1ec-a602-4c9f-aaa6-cc3e262ef7ea
-- title:
--   Threshold rank $k_\rho(G)$, Laplacian $L_G$, spectral subspace $U$
-- statement:
--   Let $A_G$ be the $2n\times 2n$ adjacency matrix of the $d$-regular bipartite graph $G$, with eigenvalues $\lambda_1(A_G)\ge\dots\ge\lambda_{2n}(A_G)$ counted with multiplicity, and $L_G=dI-A_G$ the unnormalized Laplacian. For $0<\rho<1$ the **threshold rank** is
--
--   $$
--   k=k_\rho(G)=\#\{i:\lambda_i(A_G)\ge(1-\rho)d\}=\#\{i:\mu_i(L_G)\le\rho d\}.
--   $$
--
--   Let $U\subseteq\mathbb R^{V}$ be the $k$-dimensional spectral subspace of $L_G$ for its eigenvalues at most $\rho d$ (the span of the corresponding eigenvectors). The module also defines the indicator vector $\mathbf 1_S$ of a vertex set and the squared Euclidean distance $\mathrm{dist}(\mathbf 1_S,U)^2$.
--
--   Small threshold rank means that only a few normalized adjacency eigenvalues are close to $1$; the running time of the main theorem is exponential only in $k$.
--
--   **Formalization Note** The eigenvalues are Mathlib's indexed family for a Hermitian matrix, so $k$ counts with multiplicity. $U$ is the sum of the eigenspaces of $L_G$ for the eigenvalues $\mu\le\rho d$.
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), §1.1, p.3; §2.2, p.8

import Mathlib
import Definitions.Def_ThreshRankBIS_IsRegular
set_option autoImplicit false

namespace ThreshRankBIS

open Finset

/-- The adjacency matrix `A_G` of `HiddenPartition.bip E`, a real `2n × 2n` 0/1 matrix indexed by
`V n = X ⊕ Y` (§1.1, p.3; §2.2, p.8). -/
noncomputable def adjMat {n : ℕ} (E : Fin n → Fin n → Bool) : Matrix (V n) (V n) ℝ := by
  classical
  exact fun u v => if (HiddenPartition.bip E).Adj u v then 1 else 0

/-- `A_G` is symmetric, hence Hermitian over `ℝ`. -/
theorem adjMat_isHermitian {n : ℕ} (E : Fin n → Fin n → Bool) : (adjMat E).IsHermitian := by
  classical
  refine Matrix.IsHermitian.ext fun u v => ?_
  simp only [adjMat, star_trivial]
  by_cases h : (HiddenPartition.bip E).Adj u v
  · simp [h, (HiddenPartition.bip E).adj_symm h]
  · have h' : ¬ (HiddenPartition.bip E).Adj v u := fun h'' => h ((HiddenPartition.bip E).adj_symm h'')
    simp [h, h']

/-- The unnormalized Laplacian `L_G = dI − A_G` (§2.2, p.8). -/
noncomputable def lapMat {n : ℕ} (E : Fin n → Fin n → Bool) (d : ℕ) : Matrix (V n) (V n) ℝ :=
  (d : ℝ) • (1 : Matrix (V n) (V n) ℝ) - adjMat E

/-- **The threshold rank** `k = k_ρ(G) = #{i : λ_i(A_G) ≥ (1 − ρ)d}` (§1.1, p.3; §2.2, p.8): the
number of eigenvalues of the adjacency matrix `A_G`, **counted with multiplicity**, that are at
least `(1 − ρ)d`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), §1.1, p.3 and §2.2,
p.8.

The module also defines the Laplacian `L_G = dI − A_G`, the spectral subspace `U` of `L_G` for
the eigenvalues at most `ρd` (§2.2, p.8), the indicator vector `1_S` in Euclidean space and the
squared Euclidean distance `dist(1_S, U)²`.

**Formalization Note.** `Matrix.IsHermitian.eigenvalues` is an indexed family of `2n` real
numbers listing the spectrum with multiplicity, so `thresholdRank` counts indices, not distinct
values. `specSub` is the sum of the eigenspaces of `L_G` for the eigenvalues `µ ≤ ρd`; since
`L_G = dI − A_G` is symmetric, its dimension is `#{i : µ_i(L_G) ≤ ρd} = k`. -/
noncomputable def thresholdRank {n : ℕ} (ρ : ℝ) (E : Fin n → Fin n → Bool) (d : ℕ) : ℕ :=
  Fintype.card {i : V n // (1 - ρ) * (d : ℝ) ≤ (adjMat_isHermitian E).eigenvalues i}

/-- The spectral subspace `U ⊆ ℝ^{V(G)}` of `L_G` for the eigenvalues at most `ρd` (§2.2, p.8). -/
noncomputable def specSub {n : ℕ} (ρ : ℝ) (E : Fin n → Fin n → Bool) (d : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (V n)) :=
  ⨆ (μ : ℝ) (_ : μ ≤ ρ * (d : ℝ)),
    Module.End.eigenspace (Matrix.toEuclideanLin (lapMat E d)) μ

/-- The indicator vector `1_S` of a finite set `S` in the Euclidean space `ℝ^ι` (§2.1, p.7). -/
noncomputable def indE {ι : Type} [Fintype ι] (S : Finset ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => by classical exact if i ∈ S then (1 : ℝ) else 0)

/-- The squared Euclidean distance `dist(1_S, U)²` from the indicator of `S ⊆ V(G)` to the
spectral subspace `U` (§2.2, p.8; Lemma 5, p.9). -/
noncomputable def distU2 {n : ℕ} (ρ : ℝ) (E : Fin n → Fin n → Bool) (d : ℕ)
    (S : Finset (V n)) : ℝ :=
  Metric.infDist (indE S) (specSub ρ E d : Set (EuclideanSpace ℝ (V n))) ^ 2

end ThreshRankBIS


