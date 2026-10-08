-- Prove2me | Definitions.Def_EffResSparsify_Sampling_Defs
-- name    : EffResSparsify_Sampling_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:33:46.291991+00:00
-- url     : https://prove2.me/theorems/6ce53598-f0e5-4e23-8d13-bd71c17108ff
-- title:
--   Weighted graphs, incidence matrix, Laplacian, pseudoinverse, effective resistance, the matrix Π and the sampling procedure Sparsify (§1.1, §2, §3)
-- statement:
--   This file fixes the objects of Spielman and Srivastava's sparsification theorem.
--
--   A **weighted graph** $G=(V,E,w)$ has a finite vertex set $V$ with $n=|V|$, a finite edge set $E$ with $m=|E|$, and edge weights $w_e>0$. Every edge is oriented arbitrarily: it has a **head** and a **tail**, which are distinct vertices (no loops). Parallel edges are allowed. $G$ is **connected** when the simple graph on $V$ in which $a\sim b$ whenever some edge joins $a$ and $b$ is connected; this includes $V\neq\emptyset$.
--
--   1. The **signed edge-vertex incidence matrix** $B\in\mathbb R^{m\times n}$ has $B(e,v)=1$ if $v$ is the head of $e$, $B(e,v)=-1$ if $v$ is the tail of $e$, and $B(e,v)=0$ otherwise. Its rows are $b_e=\chi_{\mathrm{head}(e)}-\chi_{\mathrm{tail}(e)}$.
--   2. $W\in\mathbb R^{m\times m}$ is the diagonal matrix with $W(e,e)=w_e$, and $W^{1/2}$ the diagonal matrix with entries $\sqrt{w_e}$.
--   3. The **Laplacian** is $L=B^{\mathsf T}WB$, so that $x^{\mathsf T}Lx=\sum_{e}w_e\,(x(\mathrm{head}\,e)-x(\mathrm{tail}\,e))^2$.
--   4. $L^{+}$ is the **Moore–Penrose pseudoinverse** of $L$. Since $L$ is symmetric, $L^{+}=\sum_{\lambda_i\neq0}\lambda_i^{-1}u_iu_i^{\mathsf T}$, where $\lambda_i$ are the nonzero eigenvalues of $L$ and $u_i$ corresponding orthonormal eigenvectors.
--   5. The **effective resistance** of an edge $e$ is $R_e=b_eL^{+}b_e^{\mathsf T}=(BL^{+}B^{\mathsf T})(e,e)$.
--   6. The $m\times m$ matrix
--   $$\Pi=W^{1/2}BL^{+}B^{\mathsf T}W^{1/2}.$$
--   7. **Sparsify$(G,q)$**: draw $q$ edges independently with replacement, edge $e$ with probability
--   $$p_e=\frac{w_eR_e}{\sum_{f\in E}w_fR_f},$$
--   and give $e$ the weight $w_e/(qp_e)$ for each time it is drawn. An outcome is a sequence $s=(s_1,\dots,s_q)\in E^q$, of probability $\prod_{i=1}^q p_{s_i}$. On the outcome $s$ the diagonal matrix $S$ has $S(e,e)=\#\{i: s_i=e\}/(qp_e)$, the sparsifier $H$ has weights $\tilde w_e=S(e,e)\,w_e$ (zero for an edge never drawn), and its Laplacian is $\tilde L=B^{\mathsf T}\tilde WB=B^{\mathsf T}W^{1/2}SW^{1/2}B$.
--   8. The probability that $H=\mathrm{Sparsify}(G,q)$ has a property $P$ is $\sum_{s\in E^q}\big(\prod_i p_{s_i}\big)\,\mathbf 1[P(s)]$.
--
--   These are the objects of Theorem 1 and of Lemmas 3 and 4; every statement of the mission is phrased in them.
--
--   **Formalization Note** $L^{+}$ is the matrix of the published pseudoinverse `HarmonicGames.Decomposition.pinv` of the linear map $x\mapsto Lx$ on Euclidean $\mathbb R^V$; for symmetric $L$ this is the spectral formula of §2.2 and is the gauge-fixed inverse (its range is $\mathbf 1^\perp$). The probabilities $p_e$ are defined literally as "proportional to $w_eR_e$"; that the normaliser equals $n-1$ is a consequence (p. 8), not part of the definition. Expectations and probabilities over Sparsify are finite sums over $E^q$.
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, p. 2 (§1.1, Sparsify), pp. 4–6 (§2.1–2.3), p. 6 (§3, the matrix Π), p. 7 (eq. (3))

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv

namespace EffResSparsify.Sampling

open Matrix

/-- A weighted undirected graph `G = (V, E, w)` whose edges carry an arbitrary orientation
(§2.1, p. 4): every edge `e` has a head `head e` and a tail `tail e`, distinct (no loops), and a
weight `w e > 0`. Parallel edges are allowed. -/
structure WGraph (V E : Type*) where
  /-- the head of the oriented edge `e` -/
  head : E → V
  /-- the tail of the oriented edge `e` -/
  tail : E → V
  /-- the edge weight `w_e` -/
  w : E → ℝ
  head_ne_tail : ∀ e, head e ≠ tail e
  w_pos : ∀ e, 0 < w e

namespace WGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The underlying simple graph on `V`: `a ~ b` iff some edge joins `a` and `b`. -/
def toSimpleGraph (G : WGraph V E) : SimpleGraph V :=
  SimpleGraph.fromRel (fun a b => ∃ e, G.head e = a ∧ G.tail e = b)

/-- `G` is connected (the standing assumption of §2.1, p. 4). Mathlib's `Connected` includes
nonemptiness of `V`. -/
def IsConnected (G : WGraph V E) : Prop := G.toSimpleGraph.Connected

/-- The signed edge-vertex incidence matrix `B` (§2.1, p. 4), an `m × n` matrix:
`B(e,v) = 1` if `v` is the head of `e`, `-1` if `v` is the tail of `e`, and `0` otherwise.
Its row `b_e` is `χ_head − χ_tail`. -/
def incidence (G : WGraph V E) : Matrix E V ℝ :=
  fun e v => if v = G.head e then 1 else if v = G.tail e then -1 else 0

/-- The diagonal weight matrix `W` with `W(e,e) = w_e` (§2.1, p. 4). -/
def weightMatrix (G : WGraph V E) : Matrix E E ℝ := Matrix.diagonal G.w

/-- The diagonal matrix `W^{1/2}` with `W^{1/2}(e,e) = √w_e`. -/
noncomputable def sqrtWeightMatrix (G : WGraph V E) : Matrix E E ℝ :=
  Matrix.diagonal (fun e => Real.sqrt (G.w e))

/-- The Laplacian `L = Bᵀ W B` (§2.1, p. 4). -/
def laplacian (G : WGraph V E) : Matrix V V ℝ :=
  G.incidenceᵀ * G.weightMatrix * G.incidence

/-- The Moore–Penrose pseudoinverse `L⁺` of the Laplacian (§2.2, p. 5), as a matrix: the
published pseudoinverse `HarmonicGames.Decomposition.pinv` of the linear map `x ↦ L x` on the
Euclidean space `ℝ^V`, converted back to a matrix. For the symmetric matrix `L` this is
`∑_{λ_i ≠ 0} λ_i⁻¹ u_i u_iᵀ`. -/
noncomputable def lapPinv (G : WGraph V E) : Matrix V V ℝ :=
  Matrix.toEuclideanLin.symm
    (HarmonicGames.Decomposition.pinv (Matrix.toEuclideanLin G.laplacian))

/-- The effective resistance of the edge `e` (§2.3, p. 6): `R_e = b_e L⁺ b_eᵀ`, the diagonal
entry `(B L⁺ Bᵀ)(e,e)`. -/
noncomputable def effRes (G : WGraph V E) (e : E) : ℝ :=
  (G.incidence * G.lapPinv * G.incidenceᵀ) e e

/-- The `m × m` matrix `Π = W^{1/2} B L⁺ Bᵀ W^{1/2}` (§3, p. 6). -/
noncomputable def projPi (G : WGraph V E) : Matrix E E ℝ :=
  G.sqrtWeightMatrix * G.incidence * G.lapPinv * G.incidenceᵀ * G.sqrtWeightMatrix

/-- The sampling probability of `Sparsify` (p. 2): `p_e` proportional to `w_e R_e`,
`p_e = w_e R_e / ∑_f w_f R_f`. -/
noncomputable def sampleProb (G : WGraph V E) (e : E) : ℝ :=
  G.w e * G.effRes e / ∑ f, G.w f * G.effRes f

/-- An outcome of `Sparsify(G, q)` is the sequence `s : Fin q → E` of the `q` edges drawn
independently with replacement; its probability is `∏_i p_{s i}`. -/
noncomputable def outcomeProb (G : WGraph V E) (q : ℕ) (s : Fin q → E) : ℝ :=
  ∏ i, G.sampleProb (s i)

/-- The number of times the edge `e` is sampled in the outcome `s`. -/
def sampleCount {q : ℕ} (s : Fin q → E) (e : E) : ℕ :=
  (Finset.univ.filter (fun i => s i = e)).card

/-- The random diagonal entry `S(e,e) = (# of times e is sampled)/(q p_e)` of eq. (3), p. 7. -/
noncomputable def sparsifyS (G : WGraph V E) (q : ℕ) (s : Fin q → E) (e : E) :
    ℝ :=
  (sampleCount s e : ℝ) / ((q : ℝ) * G.sampleProb e)

/-- The edge weights of `H = Sparsify(G, q)` on the outcome `s` (p. 2): each draw of `e` adds
weight `w_e/(q p_e)`, summed over repeated draws, i.e. `w̃_e = S(e,e) w_e` (eq. (3), p. 7). An
edge never drawn has weight `0`. -/
noncomputable def sparsifiedWeight (G : WGraph V E) (q : ℕ) (s : Fin q → E)
    (e : E) : ℝ :=
  G.sparsifyS q s e * G.w e

/-- The Laplacian `L̃ = Bᵀ W̃ B` of `H = Sparsify(G, q)` on the outcome `s` (p. 7). -/
noncomputable def sparsifiedLaplacian (G : WGraph V E) (q : ℕ) (s : Fin q → E) :
    Matrix V V ℝ :=
  G.incidenceᵀ * Matrix.diagonal (G.sparsifiedWeight q s) * G.incidence

open Classical in
/-- The probability that the outcome of `Sparsify(G, q)` satisfies the event `P`:
`∑_{s : Fin q → E} (∏_i p_{s i}) · 1[P s]`. -/
noncomputable def sparsifyProb (G : WGraph V E) (q : ℕ) (P : (Fin q → E) → Prop) : ℝ :=
  ∑ s : Fin q → E, if P s then G.outcomeProb q s else 0

end WGraph

end EffResSparsify.Sampling


