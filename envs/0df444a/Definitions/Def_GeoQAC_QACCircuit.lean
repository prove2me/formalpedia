-- Prove2me | Definitions.Def_GeoQAC_QACCircuit
-- name    : GeoQAC_QACCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:57.854022+00:00
-- url     : https://prove2.me/theorems/54c4f3ca-0179-49fd-9dcc-3d4f6689ef87
-- title:
--   QAC circuits $C=L_dM_d\cdots L_1M_1L_0$
-- statement:
--   Fix a finite set $V$ of qubits. A **generalized controlled-Z gate** on a set $S\subseteq V$ is
--   $$
--   CZ_S = I - 2\,|1_S\rangle\langle 1_S|,
--   $$
--   with the identity understood on the remaining qubits: it multiplies a computational-basis state by $-1$ exactly when all qubits of $S$ are $1$.
--
--   A **depth-$d$ QAC circuit** has the form
--   $$
--   C = L_d M_d \cdots L_1 M_1 L_0,
--   $$
--   where each $L_j$ is a tensor product of one-qubit unitaries and each $M_j$ is a product of generalized controlled-Z gates with pairwise disjoint supports, of any arity. The depth counts the multi-qubit layers $M_j$ only. Circuits are nonuniform: the one-qubit unitaries are arbitrary.
--
--   This is the circuit model of the paper. Generalized Toffoli gates are Hadamard-conjugated CZ gates and need no separate constructor.
--
--   **Formalization Note** A basis configuration is a map $V\to\{0,1\}$ and operators are matrices indexed by configurations. A multi-qubit layer is a finite set of pairwise disjoint *nonempty* supports ($CZ_\emptyset=-I$ is only a global phase and is excluded); its matrix is the diagonal matrix of the products of the commuting CZ factors. A layer may be empty, so "depth $d$" includes every depth $\le d$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §2.3 and Definition 2.1, p.10

import Mathlib

namespace GeoQAC

/-!
# QAC circuits

Dong, Ou, Yao, *On the Computational Power of Geometrically Local QAC circuits*, arXiv:2604.07178
(version of 2026-11-03), §2.3 and Definition 2.1, p.10.

A depth-`d` QAC circuit is `C = L_d M_d ⋯ L_1 M_1 L_0`, where each `L_j` is a tensor product of
one-qubit unitaries and each `M_j` is a product of generalized controlled-Z gates
`CZ_S = I − 2|1_S⟩⟨1_S|` with pairwise disjoint supports, of any arity.

**Formalization Note.**
* The qubits are a finite type `V`; a computational-basis configuration is `V → Bool` (`false` is
  `|0⟩`). Operators are matrices indexed by configurations, vectors are functions
  `(V → Bool) → ℂ`.
* The depth `d` counts the multi-qubit layers `M_j` only; there are `d + 1` one-qubit layers
  (Definition 2.1; Figure 1, p.4). A layer may be empty, so depth `d` includes depth `≤ d`.
* A layer is a finite set of pairwise disjoint **nonempty** supports. (`CZ_∅ = −I` would only be a
  global phase; it is excluded.) A singleton support `CZ_{v} = Z_v` is allowed.
* The CZ gates of a layer are diagonal and commute; the layer's matrix is the diagonal matrix whose
  entry at `x` is `∏_S (−1)^{[x_v = 1 ∀ v ∈ S]}`, which equals `∏_S CZ_S`.
* Generalized Toffoli gates are H-conjugated CZs (p.10) and need no separate constructor.
* Circuits are nonuniform with arbitrary one-qubit unitaries (p.10).
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The computational-basis vector `|x⟩` of a configuration `x : V → Bool`. -/
noncomputable def basisVec (x : V → Bool) : (V → Bool) → ℂ :=
  fun y => if y = x then 1 else 0

/-- The tensor product `⊗_v u_v` of one-qubit unitaries (one per qubit), as a matrix on
configurations: its `(x, y)` entry is `∏_v (u_v)_{x_v, y_v}`. -/
noncomputable def tensorLayer (u : V → Matrix.unitaryGroup Bool ℂ) :
    Matrix (V → Bool) (V → Bool) ℂ :=
  Matrix.of fun x y => ∏ v, (u v : Matrix Bool Bool ℂ) (x v) (y v)

/-- The generalized controlled-Z gate `CZ_S = I − 2|1_S⟩⟨1_S|` (p.10): the diagonal matrix with
entry `−1` at the configurations that are `1` on all of `S`, and `1` elsewhere. -/
noncomputable def cz (S : Finset V) : Matrix (V → Bool) (V → Bool) ℂ :=
  Matrix.diagonal fun x => if ∀ v ∈ S, x v = true then -1 else 1

/-- A multi-qubit layer `M_j` (Definition 2.1): a finite set of pairwise disjoint nonempty supports,
each carrying a generalized controlled-Z gate. -/
structure QACLayer (V : Type) [Fintype V] [DecidableEq V] where
  /-- The supports of the CZ gates of the layer. -/
  supp : Finset (Finset V)
  /-- Every support is nonempty. -/
  nonempty : ∀ S ∈ supp, S.Nonempty
  /-- The supports are pairwise disjoint. -/
  disjoint : (supp : Set (Finset V)).PairwiseDisjoint id

/-- The matrix `∏_{S} CZ_S` of a layer; the factors are commuting diagonal matrices, so the product
is the diagonal matrix of the products of their diagonal entries. -/
noncomputable def QACLayer.matrix (L : QACLayer V) : Matrix (V → Bool) (V → Bool) ℂ :=
  Matrix.diagonal fun x => ∏ S ∈ L.supp, (if ∀ v ∈ S, x v = true then (-1 : ℂ) else 1)

/-- A depth-`d` QAC circuit `C = L_d M_d ⋯ L_1 M_1 L_0` on the qubits `V` (Definition 2.1, p.10):
`d + 1` one-qubit layers `L_0, …, L_d` and `d` multi-qubit layers `M_1, …, M_d`. -/
structure QACCircuit (V : Type) [Fintype V] [DecidableEq V] (d : ℕ) where
  /-- `oneQ j v` is the one-qubit unitary of `L_j` on qubit `v`. -/
  oneQ : Fin (d + 1) → V → Matrix.unitaryGroup Bool ℂ
  /-- `multi j` is the multi-qubit layer `M_{j+1}`. -/
  multi : Fin d → QACLayer V

/-- The unitary `L_d M_d ⋯ L_1 M_1 L_0` of a circuit; `L_0` acts first. -/
noncomputable def QACCircuit.matrix {d : ℕ} (C : QACCircuit V d) :
    Matrix (V → Bool) (V → Bool) ℂ :=
  ((List.ofFn fun j : Fin d => tensorLayer (C.oneQ j.succ) * (C.multi j).matrix).reverse.prod) *
    tensorLayer (C.oneQ 0)

end GeoQAC


