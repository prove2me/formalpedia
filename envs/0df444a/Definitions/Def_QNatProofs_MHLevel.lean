-- Prove2me | Definitions.Def_QNatProofs_MHLevel
-- name    : QNatProofs_MHLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:01:39.475993+00:00
-- url     : https://prove2.me/theorems/69e24615-02f0-40c8-94c4-17c4f58c654a
-- title:
--   Clifford gates, QNC$^0$ depth and the levels $A_kCQ$ of the magic hierarchy
-- statement:
--   All circuits of the mission use the gate set of **one- and two-qubit unitary gates**.
--
--   A **Clifford gate** is such a gate $U$ that maps every Pauli string $P$ on its wires to a scalar multiple of a Pauli string under conjugation, $UPU^\dagger = c\,P'$. A **Clifford segment** is a circuit all of whose gates are Clifford gates, of any length. A **layer** is a list of gates on pairwise disjoint wires, and a circuit has **depth at most $D$** if it is the concatenation of at most $D$ layers.
--
--   For $k,D\in\mathbb N$, the level $\mathrm{MHLevel}(k,D)$ consists of the circuits
--   $$
--   C_0\,Q_1\,C_1\,Q_2\cdots Q_k\,C_k \qquad(\text{applied left to right}),
--   $$
--   where every $C_i$ is a Clifford segment and every $Q_i$ is a circuit of one- and two-qubit gates of depth at most $D$. Segments may be empty. This is the level $A_kCQ$ of the magic hierarchy with constant QNC$^0$ depth $D$: circuits that "alternate between arbitrary Clifford circuits and constant-depth circuits of one- and two-qubit gates", whose "levels bound the number of alternations" (p.3).
--
--   The level is the paper's resource measure for state preparation: the main theorem places the PRAL family at level $8d_F+20$.
--
--   **Formalization Note** The paper cites [Par25] for $\mathrm{MH}_k$ and $A_kCQ$ and does not define them. The form above is the one its level counts use: $A_1CQ$ is "an arbitrary-size Clifford circuit followed by a QNC$^0$ circuit" (p.40), and $[\mathrm{Cliff}][A_4CQ][\mathrm{Cliff}][A_4CQ][\mathrm{Cliff}]$ lies in $A_8CQ$ (p.25), so a trailing Clifford segment is free. The Clifford group is taken whole, not as a generating set, so the adjoint of a level-$k$ circuit is again at level $k$. "Constant depth" in a statement means one $D$ fixed before every size parameter.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), p.3, p.18, p.22, p.25, p.40 (the level counts); [Par25] cited, not read

import Mathlib
import Definitions.Def_QNatProofs_reducedOutput

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms
open scoped Matrix

/-- The one- and two-qubit unitary gates: every gate of arity `1` or `2` whose matrix is unitary.
This is the gate set of every circuit in this mission (Li, Parham, *Natural proofs for quantum
state preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.3: "circuits
[that] alternate between arbitrary Clifford circuits and constant-depth circuits of one- and
two-qubit gates"). -/
def allGates : Set Gate :=
  {g | (g.arity = 1 ∨ g.arity = 2) ∧ g.IsUnitary}

/-- The single-qubit Paulis `I, X, Y, Z`, indexed by `0, 1, 2, 3`. -/
def pauli1 : Fin 4 → Matrix Bool Bool ℂ :=
  ![1, pauliX, pauliY, pauliZ]

/-- The Pauli string `σ_{p 0} ⊗ ⋯ ⊗ σ_{p (k-1)}` on `k` qubits: its `(y, z)` entry is
`∏ᵢ σ_{p i} (y i) (z i)`. -/
def pauliString {k : ℕ} (p : Fin k → Fin 4) : Matrix (Qubits k) (Qubits k) ℂ :=
  Matrix.of fun y z => ∏ i : Fin k, pauli1 (p i) (y i) (z i)

/-- A **Clifford gate**: a one- or two-qubit unitary gate `U` that maps every Pauli string on its
wires, under conjugation `P ↦ U P U†`, to a scalar multiple of a Pauli string.

**Formalization Note** The Clifford group is taken whole (not a generating set such as
`{H, S, CNOT}`), so every Clifford unitary on one or two qubits costs one gate, and the adjoint of
a Clifford gate is a Clifford gate. -/
def IsCliffordGate (g : Gate) : Prop :=
  g ∈ allGates ∧ ∀ p : Fin g.arity → Fin 4, ∃ (c : ℂ) (p' : Fin g.arity → Fin 4),
    g.mat * pauliString p * g.matᴴ = c • pauliString p'

/-- A **Clifford segment**: a circuit all of whose gates are Clifford gates (any length). -/
def IsCliffordSeg {m : ℕ} (c : Circuit allGates m) : Prop :=
  ∀ g ∈ c, IsCliffordGate g.gate

/-- A **layer**: a list of gates acting on pairwise disjoint sets of wires. -/
def IsLayer {m : ℕ} (l : Circuit allGates m) : Prop :=
  l.Pairwise fun g h => Disjoint (Set.range g.wires) (Set.range h.wires)

/-- A circuit has **depth at most `D`**: it is the concatenation of at most `D` layers. -/
def DepthLE {m : ℕ} (D : ℕ) (c : Circuit allGates m) : Prop :=
  ∃ L : List (Circuit allGates m), L.length ≤ D ∧ (∀ l ∈ L, IsLayer l) ∧ c = L.flatten

/-- **Level `k` of the magic hierarchy with QNC⁰ depth `D`** (Li, Parham, arXiv:2610.06826 (held
copy sha256 b604fa11…), p.3, p.18, p.40; the paper cites [Par25] for `MH_k` and `A_kCQ`): the
circuits on `m` wires of the form
`C₀ Q₁ C₁ Q₂ ⋯ Q_k C_k` (applied left to right), where every `Cᵢ` is a Clifford segment of any
length and every `Qᵢ` is a circuit of one- and two-qubit unitary gates of depth at most `D`.
Segments may be empty.

**Formalization Note** The paper does not define the levels; this is the form its level counts
use (p.3: "circuits [that] alternate between arbitrary Clifford circuits and constant-depth
circuits of one- and two-qubit gates. Its levels bound the number of alternations"; p.40: "the
first level `A₁CQ` …, consisting of an arbitrary-size Clifford circuit followed by a QNC⁰
circuit"; p.25: `[Cliff][A₄CQ][Cliff][A₄CQ][Cliff]` lies in `A₈CQ`, so a trailing Clifford block
is free). The constant depth is the explicit parameter `D`; "constant-depth" in a statement means
one `D` fixed before every size parameter. -/
def MHLevel : ℕ → ℕ → (m : ℕ) → Set (Circuit allGates m)
  | 0, _, _ => {c | IsCliffordSeg c}
  | k + 1, D, m => {c | ∃ a q b : Circuit allGates m, a ∈ MHLevel k D m ∧ DepthLE D q ∧
      IsCliffordSeg b ∧ c = a ++ q ++ b}

end QNatProofs


