-- Prove2me | Definitions.Def_QMCTriFree_Circuit_Lasserre
-- name    : QMCTriFree_Circuit_Lasserre
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:59.916891+00:00
-- url     : https://prove2.me/theorems/b8e6bef1-d3b6-4a4c-9a31-66298cc83504
-- title:
--   Quantum Max-Cut Hamiltonian, $\|H\|$, and the level-2 Lasserre relaxation with edge values $x_{ij}$ (pp. 2–3, 6–7, Definition 5, eq. (4))
-- statement:
--   Let $V=\{0,\dots,n-1\}$ be the vertex set, one qubit per vertex, and let $w_{ij}\ge 0$ be symmetric edge weights; the **neighbours** of $i$ are the vertices $k\ne i$ with $w_{ik}\ne 0$, and the graph is **triangle-free** if no three distinct vertices are pairwise joined. The weights are **normalised** when $\sum_{i<j} w_{ij}=1$.
--
--   The **Quantum Max-Cut** term on the pair $(i,j)$ is
--   $$h_{ij}=\tfrac12\bigl(1-X_iX_j-Y_iY_j-Z_iZ_j\bigr)=2\,|\psi^-\rangle\langle\psi^-|_{ij},$$
--   and the Hamiltonian is $H=\sum_{i<j} w_{ij}h_{ij}$. Its maximum eigenvalue is
--   $$\|H\|=\sup_{\langle\psi|\psi\rangle=1}\ \operatorname{Re}\langle\psi|H|\psi\rangle .$$
--
--   Let $\mathcal P^{(2)}_n$ be the Pauli strings of weight at most $2$ (the identity $1$, the single-site $X_i,Y_i,Z_i$, and products of two single-site Paulis on distinct sites). A real matrix $M$ indexed by $\mathcal P^{(2)}_n\times\mathcal P^{(2)}_n$ is **feasible** for $\mathrm{Lasserre}_2(H)$ if
--   1. $M\succeq 0$;
--   2. $M(A,B)=M(A',B')$ whenever $A^\dagger B=A'^\dagger B'$;
--   3. $M(A,B)=-M(A',B')$ whenever $A^\dagger B=-A'^\dagger B'$;
--   4. $M(A,B)=0$ whenever $A^\dagger B$ is not Hermitian;
--   5. $M(A,A)=1$ for every $A$.
--
--   Its objective is $\tfrac12\sum_{i<j}w_{ij}\bigl(1-M(X_i,X_j)-M(Y_i,Y_j)-M(Z_i,Z_j)\bigr)$, and $M$ **solves** $\mathrm{Lasserre}_2(H)$ if it is feasible and no feasible matrix has larger objective. For an edge $(i,j)$ the **edge value** is
--   $$x_{ij}=-\tfrac12\bigl(1+M(1,X_iX_j)+M(1,Y_iY_j)+M(1,Z_iZ_j)\bigr),\qquad\text{i.e.}\quad 1+x_{ij}=\tfrac12\bigl(1-M(1,X_iX_j)-M(1,Y_iY_j)-M(1,Z_iZ_j)\bigr).$$
--
--   These objects carry every statement of the mission: the goal compares the output of Algorithm 17 with $\|H\|$, and the edge values $x_{ij}$ are what the algorithm reads from the relaxation.
--
--   **Formalization Note** Pauli strings are `Fin n → Fin 4` (0 = identity, 1, 2, 3 = X, Y, Z) with the published operators `pauliOp` (tensor products of `QAlgorithms.pauliX/Y/Z`); the index set is the subtype of strings of weight at most 2, and `entry M s t` reads $M(s,t)$ at two strings (returning 0 off that index set, which no statement uses). Each unordered edge is counted once ($i<j$), both in $H$ and in the objective. The value $\|H\|$ is a supremum over unit amplitude vectors, a nonempty bounded set. The edge value is used only for $i\ne j$.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, pp. 2–3 (Section 2, Problem 1), pp. 6–7 (Definition 5, eq. (2), eq. (4)), p. 16 (Algorithm 17, steps 1 and 3)

import Mathlib
import Definitions.Def_QMCProduct_HalfApprox_Basic

set_option autoImplicit false

namespace QMCTriFree.Circuit

open QMCProduct.HalfApprox Matrix

/-! King, arXiv:2209.02589v3, Section 2 (pp. 2–3) and Section 4 (pp. 6–7). The Pauli-string
layer (`Op`, `PauliString`, `pauli1`, `pauliOp`, `pauliDegree`; index `0` = identity, `1, 2, 3`
= `X, Y, Z`) is the published `QMCProduct_HalfApprox_Basic`. -/

/-- The identity Pauli string `1`. -/
def idStr (n : ℕ) : PauliString n := fun _ => 0

/-- The weight-one string `σ_i`, `σ = 1, 2, 3` for `X, Y, Z`. -/
def siteStr {n : ℕ} (a : Fin 4) (i : Fin n) : PauliString n :=
  fun t => if t = i then a else 0

/-- The string `σ_i σ_j` (weight two for `i ≠ j`). -/
def pairStr {n : ℕ} (a : Fin 4) (i j : Fin n) : PauliString n :=
  fun t => if t = i ∨ t = j then a else 0

/-- The weighted graph `(V, {w_ij})` with `V = Fin n`: weights symmetric and nonnegative, p. 2. -/
def IsWeightedGraph {n : ℕ} (w : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, w i j = w j i) ∧ ∀ i j, 0 ≤ w i j

/-- The normalisation `∑_ij w_ij = 1` of p. 3, summed over unordered pairs `i < j`. -/
def IsNormalized {n : ℕ} (w : Fin n → Fin n → ℝ) : Prop :=
  ∑ i : Fin n, ∑ j : Fin n, (if i < j then w i j else 0) = 1

/-- The neighbours `k ∼ i` of `i`: vertices `k ≠ i` with `w_ik ≠ 0`. -/
noncomputable def nbrs {n : ℕ} (w : Fin n → Fin n → ℝ) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun k => k ≠ i ∧ w i k ≠ 0)

/-- No three pairwise distinct vertices are pairwise joined by edges. -/
def IsTriangleFree {n : ℕ} (w : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k → ¬ (w i j ≠ 0 ∧ w j k ≠ 0 ∧ w i k ≠ 0)

/-- The QMC edge term `h_ij = ½(1 − X_iX_j − Y_iY_j − Z_iZ_j) = 2|ψ⁻⟩⟨ψ⁻|`, p. 3. -/
noncomputable def hEdge {n : ℕ} (i j : Fin n) : Op n :=
  (1 / 2 : ℂ) • (1 - pauliOp (pairStr 1 i j) - pauliOp (pairStr 2 i j) - pauliOp (pairStr 3 i j))

/-- `H = ∑_ij w_ij h_ij`, each edge counted once (`i < j`), p. 3. -/
noncomputable def qmcH {n : ℕ} (w : Fin n → Fin n → ℝ) : Op n :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then (w i j : ℂ) • hEdge i j else 0

/-- `⟨ψ|A|ψ⟩` for a vector `ψ` of amplitudes. -/
noncomputable def expect {n : ℕ} (A : Op n) (ψ : QAlgorithms.Qubits n → ℂ) : ℂ :=
  star ψ ⬝ᵥ (A *ᵥ ψ)

/-- Unit vectors of the `n`-qubit space. -/
abbrev UnitVec (n : ℕ) := {ψ : QAlgorithms.Qubits n → ℂ // star ψ ⬝ᵥ ψ = 1}

/-- Problem 1, p. 3: `‖H‖`, the maximum eigenvalue of `H`, as the maximum of `⟨ψ|H|ψ⟩` over unit
vectors (the set is nonempty and bounded). -/
noncomputable def qmcValue {n : ℕ} (w : Fin n → Fin n → ℝ) : ℝ :=
  ⨆ ψ : UnitVec n, (expect (qmcH w) ψ.1).re

/-- `P_n^(2)`: Pauli strings of weight at most `2`, p. 6. -/
abbrev P2 (n : ℕ) := {s : PauliString n // pauliDegree s ≤ 2}

/-- The entry `M(A, B)` of a matrix indexed by `P_n^(2)`, read at two strings (`0` off `P_n^(2)`,
never used there). -/
noncomputable def entry {n : ℕ} (M : Matrix (P2 n) (P2 n) ℝ) (s t : PauliString n) : ℝ :=
  if hs : pauliDegree s ≤ 2 then
    if ht : pauliDegree t ≤ 2 then M ⟨s, hs⟩ ⟨t, ht⟩ else 0
  else 0

/-- The constraints of Definition 5, p. 7, at level `d = 2`. -/
def IsFeasible {n : ℕ} (M : Matrix (P2 n) (P2 n) ℝ) : Prop :=
  M.PosSemidef ∧
  (∀ A B A' B' : P2 n, (pauliOp A.1)ᴴ * pauliOp B.1 = (pauliOp A'.1)ᴴ * pauliOp B'.1 →
      M A B = M A' B') ∧
  (∀ A B A' B' : P2 n, (pauliOp A.1)ᴴ * pauliOp B.1 = -((pauliOp A'.1)ᴴ * pauliOp B'.1) →
      M A B = -M A' B') ∧
  (∀ A B : P2 n, ¬ ((pauliOp A.1)ᴴ * pauliOp B.1).IsHermitian → M A B = 0) ∧
  (∀ A : P2 n, M A A = 1)

/-- The objective (2) of `Lasserre_2(H)`, p. 6: `½ ∑_ij w_ij (1 − M(X_i,X_j) − M(Y_i,Y_j) −
M(Z_i,Z_j))`, each edge once. -/
noncomputable def lasserreObj {n : ℕ} (w : Fin n → Fin n → ℝ) (M : Matrix (P2 n) (P2 n) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j then
      (1 / 2 : ℝ) * w i j * (1 - entry M (siteStr 1 i) (siteStr 1 j) -
        entry M (siteStr 2 i) (siteStr 2 j) - entry M (siteStr 3 i) (siteStr 3 j))
    else 0

/-- `M` solves `Lasserre_2(H)`: feasible and of maximal objective (Algorithm 17, step 1). -/
def IsOptimal {n : ℕ} (w : Fin n → Fin n → ℝ) (M : Matrix (P2 n) (P2 n) ℝ) : Prop :=
  IsFeasible M ∧ ∀ M' : Matrix (P2 n) (P2 n) ℝ, IsFeasible M' → lasserreObj w M' ≤ lasserreObj w M

/-- The edge value (4), p. 7 (Algorithm 17, step 3):
`x_ij = −½(1 + M(1, X_iX_j) + M(1, Y_iY_j) + M(1, Z_iZ_j))`. Meaningful for `i ≠ j` only. -/
noncomputable def xval {n : ℕ} (M : Matrix (P2 n) (P2 n) ℝ) (i j : Fin n) : ℝ :=
  -(1 / 2 : ℝ) * (1 + entry M (idStr n) (pairStr 1 i j) + entry M (idStr n) (pairStr 2 i j) +
    entry M (idStr n) (pairStr 3 i j))

end QMCTriFree.Circuit


