-- Prove2me | Definitions.Def_MaxCutMatrix2027_Upper_MatrixModel
-- name    : MaxCutMatrix2027_Upper_MatrixModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T12:47:27.36412+00:00
-- url     : https://prove2.me/theorems/4009255c-0c8a-45a1-b2c9-b964f0b15836
-- title:
--   Graph sampling, spectral truncation, matrix norms and moment sets
-- statement:
--   Let $G$ be a finite undirected simple graph on $[n]$. All assignments to two sides, including constant ones, are permitted. The induced MAX-CUT value uses the published unordered-edge cut count and a finite maximum. Independent vertex-set sampling uses the published finite expectation
--   $$\mathbb E_p F(Q)=\sum_{Q\subseteq[n]}p^{|Q|}(1-p)^{n-|Q|}F(Q).$$
--   The sampled cut value is zero for an empty or singleton set. Vertices use $\operatorname{Fin}(n)$.
--
--   Write $A$ for the real adjacency matrix and $(\theta_j,u_j)$ for its actual Mathlib orthonormal spectral decomposition. With $0<\tau\le1$, define
--   $$L=\sum_{|\theta_j|>\tau n}\theta_j u_ju_j^T,\qquad R=A-L.$$
--   The cube is the full continuous set $[-1,1]^n$. Quadratic minima and absolute suprema are taken over this cube, which is nonempty and compact; the objectives are continuous. For a real matrix $B$, the definitions also give its diagonal part, its restriction $PBP$ by the same sampled set on both axes, and
--   $$\|B\|_{\infty\to1}=\sup_{x,y\in[-1,1]^n}|y^TBx|,\qquad
--   \|B\|_{\mathrm{Col}}=\sum_j\sqrt{\sum_i B_{ij}^2}.$$
--   These extrema are finite. Neither $L$ nor $R$ is required to have zero diagonal.
--
--   The spectral vectors are $y_i=(\lambda_j\sqrt n\,u_j(i))_j$, where $\lambda_j=\theta_j/n$ on retained indices. Discarded coordinates are zero-padded into Euclidean $\mathbb R^n$; $f(w)$ sums $w_j^2/\lambda_j$ over retained coordinates. For arbitrary deterministic vectors $y_i$ in Euclidean $\mathbb R^d$, the same layer defines
--   $$K=\left\{\frac1n\sum_i x_i y_i:x\in[-1,1]^n\right\},\quad
--   K_Q=\left\{\frac1s\sum_{i\in Q}x_i y_i:x\in[-1,1]^n\right\},\quad
--   \Delta=d_H(K_Q,K),\quad t_y=\frac1n\sum_i\|y_i\|_2^2.$$
--   The sets are actual images of the cube, not input sets supplied with moment or compactness promises. Zero retained rank gives the singleton zero. This shared layer fixes all normalizations used by the analytic milestones.
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), §3 and §4, pp.13–14,16,18–22, p.18 (PDF p.18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Mathlib
import Definitions.Def_IIDMatchHard_Cut

set_option autoImplicit false
open scoped BigOperators

namespace MaxCutMatrix2027.Upper

/-- §3, pp.13–14: Boolean sides encode both signs, including constant cuts.
The published cutSize/maxCut counts unordered edges once. -/
noncomputable def inducedMaxCut {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Finset (Fin n)) : ℝ :=
  IIDMatchHard.maxCut (G.induce (↑Q : Set (Fin n)))

/-- Independent selectors, including real expected sample sizes. -/
noncomputable def sampleAverage {n : ℕ} (p : ℝ) (F : Finset (Fin n) → ℝ) : ℝ :=
  IIDMatchHard.randSubsetExp p F

/-- The full continuous cube; zero is always a member, even in dimension zero. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, -1 ≤ x i ∧ x i ≤ 1}

def quadratic {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * B i j * x j

noncomputable def cubeMin {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf (quadratic B '' cube n)

noncomputable def cubeAbsSup {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun x => |quadratic B x|) '' cube n)

noncomputable def cutNorm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {r | ∃ x ∈ cube n, ∃ y ∈ cube n, r = |∑ i, ∑ j, y i * B i j * x j|}

noncomputable def columnNorm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ j, Real.sqrt (∑ i, B i j ^ 2)

noncomputable def diagonalPart {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => B i i)

/-- The same selector is used on both axes. -/
noncomputable def restrictMatrix {n : ℕ} (Q : Finset (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i ∈ Q ∧ j ∈ Q then B i j else 0

/-- An ordinary, symmetric, zero-diagonal 0/1 adjacency matrix. -/
noncomputable def adjacency {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact G.adjMatrix ℝ

/-- Only structural symmetry, not an analytic bound, is proved in this definition layer. -/
theorem adjacency_hermitian {n : ℕ} (G : SimpleGraph (Fin n)) : (adjacency G).IsHermitian := by
  classical
  ext i j
  simp [adjacency, SimpleGraph.adj_comm]

/-- Mathlib's actual spectral decomposition, so no spectral estimates are supplied as input. -/
noncomputable def eigenvalue {n : ℕ} (G : SimpleGraph (Fin n)) : Fin n → ℝ :=
  (adjacency_hermitian G).eigenvalues

noncomputable def eigenvector {n : ℕ} (G : SimpleGraph (Fin n)) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (adjacency_hermitian G).eigenvectorBasis

noncomputable def retainedMatrix {n : ℕ} (G : SimpleGraph (Fin n)) (τ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i k => ∑ j, if τ * n < |eigenvalue G j| then
    eigenvalue G j * eigenvector G j i * eigenvector G j k else 0

noncomputable def residualMatrix {n : ℕ} (G : SimpleGraph (Fin n)) (τ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := adjacency G - retainedMatrix G τ

/-- The retained-coordinate vectors of p.21, embedded isometrically into ℝⁿ by
zero padding discarded coordinates. Both signs of eigenvalues use the strict cutoff. -/
noncomputable def spectralVectors {n : ℕ} (G : SimpleGraph (Fin n)) (τ : ℝ)
    (i : Fin n) : EuclideanSpace ℝ (Fin n) := by
  classical
  exact WithLp.toLp 2 (fun j => if τ * n < |eigenvalue G j| then
    (eigenvalue G j / n) * Real.sqrt n * eigenvector G j i else 0)

/-- f(w)=wᵀDw; discarded coordinates are identically zero on the moment sets. -/
noncomputable def spectralObjective {n : ℕ} (G : SimpleGraph (Fin n)) (τ : ℝ)
    (w : EuclideanSpace ℝ (Fin n)) : ℝ := by
  classical
  exact ∑ j, if τ * n < |eigenvalue G j| then w j ^ 2 / (eigenvalue G j / n) else 0

/-- §4.2, p.21. Arbitrary finite-dimensional Euclidean vectors specialize to the retained
spectral vectors; there is no condition on their lengths. -/
def populationSet {n d : ℕ} (y : Fin n → EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {w | ∃ x ∈ cube n, w = (n : ℝ)⁻¹ • ∑ i, x i • y i}

noncomputable def sampledSet {n d : ℕ} (y : Fin n → EuclideanSpace ℝ (Fin d))
    (s : ℝ) (Q : Finset (Fin n)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {w | ∃ x ∈ cube n, w = s⁻¹ • ∑ i ∈ Q, x i • y i}

noncomputable def sampleDistance {n d : ℕ} (y : Fin n → EuclideanSpace ℝ (Fin d))
    (s : ℝ) (Q : Finset (Fin n)) : ℝ :=
  Metric.hausdorffDist (sampledSet y s Q) (populationSet y)

noncomputable def averageEnergy {n d : ℕ} (y : Fin n → EuclideanSpace ℝ (Fin d)) : ℝ :=
  (∑ i, ‖y i‖ ^ 2) / n

end MaxCutMatrix2027.Upper


