-- Prove2me | Definitions.Def_QAlgorithms_Defs_Walk
-- name    : QAlgorithms_Defs_Walk
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:34:55.305857+00:00
-- url     : https://prove2.me/theorems/a6ec2002-5222-40a5-b00a-5c1d2bf7c82c
-- title:
--   Quantum walks and graph access (shared definition layer)
-- statement:
--   Quantum walks and graph access (shared definition layer)
--
--   ### QAlgorithms.IsColumnStochastic
--
--   This is a definition of a property of a real square matrix $P$ whose rows and columns are indexed by a finite type $\iota$. It holds exactly when both of the following are true:
--
--   1. Every entry is nonnegative: $P_{j,k} \ge 0$ for all $j, k \in \iota$.
--   2. Every column sums to one: for every $j \in \iota$,
--   $$
--   \sum_{k\in\iota} P_{k,j} = 1.
--   $$
--
--   Here the sum runs over the row index $k$ with the column index $j$ fixed. If $\iota$ is empty, both conditions hold vacuously.
--
--   ### QAlgorithms.unmarkedSubmatrix
--
--   This is a definition. It takes a real square matrix $P$ indexed by an arbitrary type $\iota$, together with a finite set $M \subseteq \iota$ of "marked" indices.
--
--   It returns the square submatrix $P'$ obtained by keeping only the rows and columns indexed by unmarked elements. Its index set is $\iota \setminus M$, and
--   $$
--   P'_{u,v} = P_{u,v} \qquad \text{for } u, v \notin M.
--   $$
--   No condition is placed on $P$; for example, stochasticity is not required. If $M$ contains every index, the result is the empty matrix.
--
--   ### QAlgorithms.szegedyState
--
--   This is a definition. It takes a real square matrix $P$ indexed by a type $\iota$ with decidable equality, and an index $j \in \iota$. It returns a vector $|\psi_j\rangle$ in the complex Euclidean space with basis indexed by pairs $(a, b) \in \iota \times \iota$.
--
--   Its coordinates are
--   $$
--   \psi_j(a,b) = \begin{cases} \sqrt{P_{b,j}} & \text{if } a = j, \\ 0 & \text{otherwise.} \end{cases}
--   $$
--   Here $\sqrt{\cdot}$ is the real square root, taken to be $0$ on negative numbers. Informally, $|\psi_j\rangle = |j\rangle \otimes \sum_{b} \sqrt{P_{b,j}}\,|b\rangle$, built from column $j$ of $P$.
--
--   No assumption on $P$ is made. In particular, $|\psi_j\rangle$ has norm $1$ only when column $j$ of $P$ is nonnegative and sums to $1$.
--
--   ### QAlgorithms.szegedyProj
--
--   This is a definition. It takes a real square matrix $P$ indexed by a finite type $\iota$ with decidable equality, and returns a complex matrix $\Pi$ indexed by $\iota \times \iota$.
--
--   Its entries are
--   $$
--   \Pi_{a,b} = \sum_{j\in\iota} \psi_j(a)\,\overline{\psi_j(b)},
--   $$
--   where $\psi_j$ is the vector from the previous definition. That vector has coordinate $\sqrt{P_{b',j}}$ at pairs $(j, b')$ and $0$ elsewhere, with the real square root returning $0$ on negative inputs. Equivalently,
--   $$
--   \Pi = \sum_j |\psi_j\rangle\langle\psi_j|.
--   $$
--   No hypothesis on $P$ is imposed, so $\Pi$ is not asserted to be a projection. It is one when the $\psi_j$ are unit vectors, as happens for column-stochastic $P$.
--
--   ### QAlgorithms.swapOp
--
--   This is a definition. For a type $\iota$ with decidable equality, it is the $0/1$ complex matrix $S$ indexed by $\iota\times\iota$ with entries
--   $$
--   S_{a,b} = \begin{cases} 1 & \text{if } a = (b_2, b_1), \\ 0 & \text{otherwise,} \end{cases}
--   $$
--   where $b = (b_1, b_2)$. Acting on column vectors, it sends the basis vector $|(b_1,b_2)\rangle$ to $|(b_2,b_1)\rangle$. In other words, it swaps the two tensor factors.
--
--   ### QAlgorithms.szegedyWalk
--
--   This is a definition. It takes a real square matrix $P$ indexed by a finite type $\iota$ with decidable equality, and returns the complex matrix indexed by $\iota\times\iota$
--   $$
--   W_P = S\,(2\Pi - I).
--   $$
--   The pieces are:
--
--   - $S$ is the swap matrix: entry $(a,b)$ is $1$ exactly when $a = (b_2, b_1)$, and $0$ otherwise.
--   - $I$ is the identity matrix.
--   - $\Pi$ is the matrix $\Pi_{a,b} = \sum_j \psi_j(a)\overline{\psi_j(b)}$.
--   - $\psi_j$ is the vector with coordinate $\sqrt{P_{b',j}}$ at $(j, b')$ and $0$ elsewhere. The square root is the real one, returning $0$ on negative inputs.
--
--   No assumption on $P$, such as stochasticity, is made. So $2\Pi - I$ is a reflection, and $W_P$ is unitary, only under further conditions on $P$.
--
--   ### QAlgorithms.discriminant
--
--   This is a definition. It takes a real square matrix $P$ indexed by an arbitrary type $\iota$ and returns the real matrix $D$ of the same shape with entries
--   $$
--   D_{j,k} = \sqrt{P_{j,k}\,P_{k,j}}.
--   $$
--   Here $\sqrt{\cdot}$ is the real square root, which returns $0$ when its argument is negative, i.e. when $P_{j,k}$ and $P_{k,j}$ have opposite strict signs. $D$ is symmetric by construction. No condition on $P$ is assumed.
--
--   ### QAlgorithms.IsBipartition
--
--   This is a definition of a property of a simple graph $G$ on the vertex set $\{0, 1, \dots, N-1\}$ together with a labelling $\mathrm{side} : \{0,\dots,N-1\} \to \{\text{true}, \text{false}\}$.
--
--   It holds exactly when every edge joins vertices with different labels: for all vertices $u, v$, if $u$ and $v$ are adjacent in $G$, then $\mathrm{side}(u) \ne \mathrm{side}(v)$.
--
--   Neither side is required to be nonempty. If $G$ has no edges, every labelling qualifies, including constant ones.
--
--   ### QAlgorithms.IsNeighbourList
--
--   This is a definition of a property of a simple graph $G$ on the vertex set $\{0,\dots,N-1\}$ together with an assignment $\mathrm{nbr}$ that gives each vertex $v$ a finite list $\mathrm{nbr}(v)$ of vertices. It holds exactly when, for every vertex $v$:
--
--   1. The list $\mathrm{nbr}(v)$ contains no repeated entries.
--   2. For every vertex $w$, $w$ appears in $\mathrm{nbr}(v)$ if and only if $v$ and $w$ are adjacent in $G$.
--
--   So each list enumerates the neighbours of $v$ exactly once each, in an arbitrary order.
--
--   ### QAlgorithms.IsProperEdgeColouring
--
--   This is a definition of a property of a simple graph $G$ on the vertex set $\{0,\dots,N-1\}$ together with a function $\mathrm{col}$ that assigns to every ordered pair of vertices $(u,v)$ a colour $\mathrm{col}(u,v)$ in an arbitrary type $\alpha$ of colours. It holds exactly when both of the following are true:
--
--   1. **Symmetry on edges.** For all $u, v$ with $u$ adjacent to $v$, $\mathrm{col}(u,v) = \mathrm{col}(v,u)$.
--   2. **Properness.** For all vertices $u, v, w$ with $u$ adjacent to $v$, $u$ adjacent to $w$, and $v \ne w$, we have $\mathrm{col}(u,v) \ne \mathrm{col}(u,w)$. That is, two distinct edges sharing the endpoint $u$ receive different colours.
--
--   The values of $\mathrm{col}$ on non-adjacent pairs are unconstrained. No bound is placed on the number of colours, since $\alpha$ is arbitrary.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Walk.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
/-!
# Quantum walks and graph access (shared definition layer)

Childs's stochastic matrices are column-stochastic: `P_{kj}` is the probability of a transition
to `k` from `j` (p.90). Mathlib's `Matrix` stochasticity conventions are not used.
-/

namespace QAlgorithms

open scoped ComplexConjugate

/-- Childs p.90 (§18.2): `P` is stochastic in the source's sense: nonnegative entries and every
column sums to `1` (`P_{kj}` is the probability of a transition to `k` from `j`). -/
def IsColumnStochastic {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) : Prop :=
  (∀ j k, 0 ≤ P j k) ∧ ∀ j, ∑ k, P k j = 1

/-- Childs p.92 ((18.36)): `P_M`, the restriction of `P` to the unmarked vertices `V \ M`. -/
def unmarkedSubmatrix {ι : Type*} (P : Matrix ι ι ℝ) (M : Finset ι) :
    Matrix {v // v ∉ M} {v // v ∉ M} ℝ :=
  P.submatrix Subtype.val Subtype.val

/-- Childs p.90 ((18.5)–(18.6)): `|ψ_j⟩ = |j⟩ ⊗ Σ_k √(P_{kj}) |k⟩ = Σ_k √(P_{kj}) |j, k⟩` (the
square roots are of nonnegative entries for a stochastic `P`). -/
noncomputable def szegedyState {ι : Type*} [DecidableEq ι] (P : Matrix ι ι ℝ) (j : ι) :
    EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 fun p => if p.1 = j then (Real.sqrt (P p.2 j) : ℂ) else 0

/-- Childs p.90 ((18.7)): `Π = Σ_j |ψ_j⟩⟨ψ_j|`. -/
noncomputable def szegedyProj {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.of fun a b => ∑ j, szegedyState P j a * conj (szegedyState P j b)

/-- Childs p.90 ((18.8)): the swap `S = Σ_{j,k} |j, k⟩⟨k, j|`. -/
def swapOp {ι : Type*} [DecidableEq ι] : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.of fun a b => if a = (b.2, b.1) then 1 else 0

/-- Childs p.90 (§18.2): one step `U = S(2Π − 1)` of the quantum walk of `P`. -/
noncomputable def szegedyWalk {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  swapOp * (2 • szegedyProj P - 1)

/-- Childs p.91 (Theorem 18.1): the discriminant matrix `D_{jk} = √(P_{jk} P_{kj})`. -/
noncomputable def discriminant {ι : Type*} (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun j k => Real.sqrt (P j k * P k j)

/-- Childs p.143 (Lemma 27.1): `side` is a bipartition of `G` (every edge joins the two sides). -/
def IsBipartition {N : ℕ} (G : SimpleGraph (Fin N)) (side : Fin N → Bool) : Prop :=
  ∀ u v, G.Adj u v → side u ≠ side v

/-- Childs p.143 (§27.4, "we can efficiently compute the neighbors of any given vertex"):
`nbr v` lists the neighbours of `v` in `G`, each exactly once; `idx(α, β)` is the position of
`β` in `nbr α` (`List.idxOf`). -/
def IsNeighbourList {N : ℕ} (G : SimpleGraph (Fin N)) (nbr : Fin N → List (Fin N)) : Prop :=
  ∀ v, (nbr v).Nodup ∧ ∀ w, w ∈ nbr v ↔ G.Adj v w

/-- Childs p.143 (Lemma 27.1): `col` is a proper edge colouring of `G`: the colour of an edge does
not depend on its orientation, and two distinct edges at a common vertex get different colours. -/
def IsProperEdgeColouring {N : ℕ} {α : Type*} (G : SimpleGraph (Fin N)) (col : Fin N → Fin N → α) :
    Prop :=
  (∀ u v, G.Adj u v → col u v = col v u) ∧
    ∀ u v w, G.Adj u v → G.Adj u w → v ≠ w → col u v ≠ col u w

/-! ### Sanity tests -/

/-- The identity matrix (stay put) is column-stochastic. -/
example : IsColumnStochastic (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine ⟨fun j k => ?_, fun j => ?_⟩
  · by_cases h : j = k <;> simp [Matrix.one_apply, h]
  · simp [Matrix.one_apply]

/-- `S` swaps the registers: `S|k, j⟩ = |j, k⟩`. -/
example (j k : Fin 2) : (swapOp : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (j, k) (k, j) = 1 := by
  simp [swapOp]

/-- For the identity walk, the discriminant is the identity. -/
example : discriminant (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext j k
  by_cases h : j = k <;> simp [discriminant, Matrix.one_apply, h]

end QAlgorithms


