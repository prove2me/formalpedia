-- Prove2me | Definitions.Def_MildHamilton_Main_Spectral
-- name    : MildHamilton_Main_Spectral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:45:57.630521+00:00
-- url     : https://prove2.me/theorems/697e827d-e01d-445d-b1df-c3df04265dad
-- title:
--   Adjacency eigenvalues, cut density, second singular value and uniform sampling
-- statement:
--   A graph $G$ is **$p$-cut-dense** if
--
--   $$e_G(S, V(G)\setminus S) \ge p\,|S|\,|V(G)\setminus S| \quad\text{for every } S\subseteq V(G).$$
--
--   The module also fixes the remaining vocabulary of the paper: the eigenvalues of the adjacency matrix, listed with multiplicity in nonincreasing order, so that the second entry is $\lambda_2(G)$; $d_G(v,X)$, the number of neighbours of $v$ in $X$; $\Delta(G[R])$, the maximum degree of the induced subgraph; the internal vertices of a walk; the Euclidean operator norm $\|F\|$ of a real matrix; the second singular value $s_2(F)$, the square root of the second largest eigenvalue of $F^{\mathsf T}F$; and the biadjacency matrix $A[U,W]$.
--
--   Together with the published notion of an $(n,d,\lambda)$-graph, these objects carry every spectral and expansion hypothesis of the mission.
--
--   **Formalization Note** Uniform probabilities are stated by counting in multiplied form, $\#\text{event}\le x\cdot\#\text{sample}$ or $x\cdot\#\text{sample}\le\#\text{event}$, so an empty sample space gives $0\le0$ rather than a quotient $0/0$. The value of $s_2$ at a matrix with fewer than two columns is $0$, and no statement uses that case.
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), p. 3 (λ_2, p-cut-dense, ‖·‖), p. 4 (s_2, F[I,J])

import Mathlib

open scoped Matrix.Norms.L2Operator

namespace MildHamilton.Main

/-- The eigenvalues of the adjacency matrix of `G`, listed with multiplicity in nonincreasing
order: index `0` is the largest and index `1` is `λ_2(G)`. Muyesser, STOC 2027 submission #233, Lemma 2.1,
p. 3. -/
noncomputable def adjEigenvalues {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fin (Fintype.card V) → ℝ :=
  (show (G.adjMatrix ℝ).IsHermitian from G.isSymm_adjMatrix).eigenvalues₀

open Classical in
/-- `p`-cut-density (Muyesser, STOC 2027 submission #233, p. 3):
`e_G(S, V(G) \ S) ≥ p |S| |V(G) \ S|` for every `S ⊆ V(G)`. `p` carries no sign condition. A graph on
a vertex subset `R` is passed as `G.induce R`, or as a graph on the subtype of `R`. -/
def IsCutDense {V : Type*} [Fintype V] (G : SimpleGraph V) (p : ℝ) : Prop :=
  ∀ S : Finset V, p * (S.card : ℝ) * (Sᶜ.card : ℝ) ≤ ((G.interedges S Sᶜ).card : ℝ)

open Classical in
/-- `d_G(v, X)`: the number of neighbours of `v` in the finite set `X`. -/
noncomputable def nbrCount {V : Type*} (G : SimpleGraph V) (v : V) (X : Finset V) : ℕ :=
  (X.filter fun x => G.Adj v x).card

open Classical in
/-- `Δ(G[R])`, the maximum degree of the subgraph of `G` induced on `R`. -/
noncomputable def inducedMaxDegree {V : Type*} (G : SimpleGraph V) (R : Finset V) : ℕ :=
  (G.induce (R : Set V)).maxDegree

open Classical in
/-- The internal vertices of a walk from `u` to `v`: those of its support other than `u` and `v`. On a
path these are exactly the vertices strictly between the ends, and a path of length at most 1 has none. -/
noncomputable def internalVerts {V : Type*} {G : SimpleGraph V} {u v : V} (P : G.Walk u v) : Finset V :=
  (P.support.toFinset.erase u).erase v

/-- `‖F‖`, the operator norm of a real matrix with respect to the Euclidean norms
(Muyesser, STOC 2027 submission #233, p. 3). -/
noncomputable def opNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (F : Matrix m n ℝ) : ℝ := ‖F‖

/-- `s_2(F)`, the second singular value of a real matrix (Muyesser, STOC 2027 submission #233, p. 4):
the square root of the second entry of the nonincreasing list of eigenvalues of `FᵀF` (written `Fᴴ * F`,
which is the same matrix over `ℝ`). The value at
a matrix with fewer than two columns is `0`; every use has at least two columns. -/
noncomputable def secondSingularValue {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (F : Matrix m n ℝ) : ℝ :=
  if h : 1 < Fintype.card n then
    Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self F).eigenvalues₀ ⟨1, h⟩)
  else 0

/-- The biadjacency matrix `A[U, W]` of `G[U, W]`: rows indexed by `U`, columns by `W`. -/
noncomputable def biadjacency {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) : Matrix U W ℝ :=
  (G.adjMatrix ℝ).submatrix (fun u : U => (u : V)) (fun w : W => (w : V))

open Classical in
/-- Under the uniform choice from the finite set `sample`, the event has probability at most `x`,
in multiplied form: `#event ≤ x · #sample`. On an empty sample space the claim is `0 ≤ 0`. -/
def UniformProbLE {Ω : Type*} (sample : Finset Ω) (event : Ω → Prop) (x : ℝ) : Prop :=
  ((sample.filter event).card : ℝ) ≤ x * (sample.card : ℝ)

open Classical in
/-- Under the uniform choice from the finite set `sample`, the event has probability at least `x`,
in multiplied form: `x · #sample ≤ #event`. On an empty sample space the claim is `0 ≤ 0`. -/
def UniformProbGE {Ω : Type*} (sample : Finset Ω) (event : Ω → Prop) (x : ℝ) : Prop :=
  x * (sample.card : ℝ) ≤ ((sample.filter event).card : ℝ)

end MildHamilton.Main


