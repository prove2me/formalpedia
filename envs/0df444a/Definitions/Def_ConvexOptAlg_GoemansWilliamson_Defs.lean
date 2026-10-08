-- Prove2me | Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs
-- name    : ConvexOptAlg_GoemansWilliamson_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:59:57.41603+00:00
-- url     : https://prove2.me/theorems/881719c4-a257-40d6-a54a-f9e3e1553a30
-- title:
--   §6.6, pp. 344–345 — graph Laplacian, hypercube maximum, the MAXCUT SDP relaxation and the {−1,1}-valued sign
-- statement:
--   Throughout, $n\in\mathbb N$ and matrices are real $n\times n$ matrices indexed by $[n]=\{1,\dots,n\}$.
--
--   1. **Graph Laplacian.** For a matrix $A$ of weights, $L = D - A$, where $D$ is the diagonal matrix with entries $\bigl(\sum_{j=1}^n A_{i,j}\bigr)_{i\in[n]}$.
--   2. **Frobenius inner product.** $\langle M, X\rangle = \operatorname{Tr}(M^\top X) = \sum_{i,j} M_{i,j}X_{i,j}$.
--   3. **Hypercube.** $x\in\mathbb R^n$ lies in $\{-1,1\}^n$ if every coordinate is $1$ or $-1$.
--   4. **Hypercube maximum.** For a matrix $M$,
--   $$\max_{x\in\{-1,1\}^n} x^\top M x,$$
--   a maximum over a finite nonempty set. With $M = L$ this is the value (6.7) of MAXCUT; with $M = B$ it is the value of (6.9).
--   5. **SDP relaxation.** $X$ is *feasible* if $X\in\mathbb S^n_+$ (symmetric positive semidefinite) and $X_{i,i}=1$ for every $i\in[n]$. A matrix $\Sigma$ is a *solution* of the relaxation $\max\{\langle M,X\rangle : X\in\mathbb S^n_+,\ X_{i,i}=1\}$ if $\Sigma$ is feasible and $\langle M,X\rangle\le\langle M,\Sigma\rangle$ for every feasible $X$.
--   6. **Sign.** $\operatorname{sign}(r) = 1$ if $r\ge 0$ and $-1$ if $r<0$; for $\xi\in\mathbb R^n$, $\zeta=\operatorname{sign}(\xi)\in\{-1,1\}^n$ coordinatewise.
--
--   These are the objects of the Goemans–Williamson rounding scheme of §6.6: the MAXCUT objective written with the Laplacian, its convex (SDP) relaxation, and the sign rounding of a Gaussian vector.
--
--   **Formalization Note** The hypercube maximum is a `Finset.sup'` over the $2^n$ Boolean vectors $b$, each read as the $\pm1$ vector $b_i\mapsto 1$ (true) or $-1$ (false); this is a genuine maximum for every $n$, including $n=0$. "The solution" of the relaxation is not assumed unique: any maximizer is a solution. Mathlib's `Real.sign` has $\operatorname{sign}(0)=0$; the book's $\zeta$ lies in $\{-1,1\}^n$, so the sign here is fixed to $1$ at $0$ (the event $\xi_i=0$ has probability $0$ when $\Sigma_{i,i}=1$, so the choice does not affect any expectation). Positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, which includes symmetry.
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, arXiv:1405.4980v2, §6.6, p. 344 (MAXCUT, (6.6), (6.7), Laplacian), p. 345 (SDP relaxation), p. 346 (6.9); §1.5, p. 240 (⟨A,B⟩ = Tr(A⊤B))

import Mathlib

namespace ConvexOptAlg.GoemansWilliamson

open Matrix

/-- The graph Laplacian (Bubeck, arXiv:1405.4980v2, §6.6, p. 344): `L = D − A`, where `D` is the
diagonal matrix with entries `(∑ⱼ A i j)_{i ∈ [n]}`. -/
noncomputable def laplacian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => ∑ j, A i j) - A

/-- The Frobenius inner product `⟨M, X⟩ = Tr(M⊤X)` (Bubeck, §1.5, p. 240). -/
def frobInner {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (Mᵀ * X)

/-- A vector of the hypercube `{−1, 1}ⁿ`: every coordinate is `1` or `−1`. -/
def IsSignVector {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i, x i = 1 ∨ x i = -1

/-- The encoding of a point of the hypercube by a Boolean vector: `true ↦ 1`, `false ↦ −1`.
It is a bijection from `Fin n → Bool` onto `{−1, 1}ⁿ`. -/
def signOfBool (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The value `max_{x ∈ {−1, 1}ⁿ} x⊤Mx` of the quadratic form of `M` over the hypercube
((6.7), p. 344, with `M = L`; (6.9), p. 346, with `M = B`). It is a maximum over the finite,
nonempty set of the `2ⁿ` Boolean vectors (each read as a `±1` vector by `signOfBool`). -/
def hypercubeMax {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun b : Fin n → Bool => (fun i => signOfBool (b i)) ⬝ᵥ M *ᵥ (fun i => signOfBool (b i)))

/-- A feasible point of the SDP relaxation (p. 345): `X ∈ S₊ⁿ` (symmetric positive
semidefinite) with `X i i = 1` for every `i ∈ [n]`. -/
def IsSDPFeasible {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.PosSemidef ∧ ∀ i, X i i = 1

/-- `Σ` is a solution of the SDP relaxation `max_{X ∈ S₊ⁿ, X i i = 1} ⟨M, X⟩` (p. 345 with
`M = L`; p. 346 with `M = B`): `Σ` is feasible and `⟨M, X⟩ ≤ ⟨M, Σ⟩` for every feasible `X`.
Any maximizer qualifies ("the solution" of the book need not be unique). -/
def IsSDPRelaxationOptimum {n : ℕ} (M Sig : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsSDPFeasible Sig ∧ ∀ X, IsSDPFeasible X → frobInner M X ≤ frobInner M Sig

/-- The sign function used for the rounding, with values in `{−1, 1}`: `sign(r) = 1` if `r ≥ 0`
and `−1` if `r < 0`. (Mathlib's `Real.sign` has `sign 0 = 0`; the book's `ζ = sign(ξ)` lies in
`{−1, 1}ⁿ`, so the value at `0` is fixed to `1`. The event `ξ i = 0` has probability `0` when
`Σ i i = 1`.) -/
noncomputable def sgn (r : ℝ) : ℝ :=
  if 0 ≤ r then 1 else -1

/-- The rounded vector `ζ = sign(ξ) ∈ {−1, 1}ⁿ`, coordinatewise. -/
noncomputable def sgnVec {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ :=
  fun i => sgn (ξ i)

end ConvexOptAlg.GoemansWilliamson


