-- Prove2me | Definitions.Def_ConstDepthUnitary_OGate
-- name    : ConstDepthUnitary_OGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:44:48.601916+00:00
-- url     : https://prove2.me/theorems/e25346c7-7182-46b6-835b-ea95d7aaef8e
-- title:
--   Oracle circuits
-- statement:
--   An **oracle circuit** with a $t$-qubit oracle is a circuit whose gates are ordinary gates or **queries**. A query on an injective tuple $w$ of $t$ wires applies the oracle matrix $O$ on those wires, and the identity elsewhere. Layers again have pairwise disjoint supports. The circuit itself is a fixed query algorithm: only $O$ varies. Its matrix $A^O$, depth, size (queries included) and number of queries are defined as for circuits.
--
--   This is the oracle model of Lemma 3.1 and footnote 9 of the source: $A(U)=A^{O_U}$ for a single algorithm $A$ and a $U$-dependent oracle $O_U$.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.1 and footnote 9, p.15

import Mathlib
import Definitions.Def_ConstDepthUnitary_Gate

namespace ConstDepthUnitary

/-- A gate of an oracle circuit: an ordinary gate, or a query to a `t`-qubit oracle on the wires `w`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.1 and footnote 9, p.15: "In the oracle model, the circuit is a fixed query algorithm and
only the oracle depends on U." -/
inductive OGate (W : Type) (t : ℕ) where
  /-- An ordinary gate. -/
  | gate (g : Gate W)
  /-- One query to the oracle, on the wires `w` (in this order). -/
  | query (w : Fin t ↪ W)

namespace OGate

variable {W : Type} [DecidableEq W] {t : ℕ}

/-- The wires an oracle-circuit gate acts on. -/
def support : OGate W t → Finset W
  | gate g => g.support
  | query w => Finset.univ.map w

/-- The matrix of an oracle-circuit gate, given the oracle `O`. A query applies `O` on the wires `w` and
the identity elsewhere. -/
noncomputable def matrix [Fintype W] (O : Matrix (Fin t → Bool) (Fin t → Bool) ℂ) :
    OGate W t → Matrix (W → Bool) (W → Bool) ℂ
  | gate g => g.matrix
  | query w => Matrix.of fun x y =>
      if ∀ v, (∀ i, w i ≠ v) → x v = y v then O (x ∘ w) (y ∘ w) else 0

/-- `1` for a query, `0` otherwise. -/
def queryCount : OGate W t → ℕ
  | gate _ => 0
  | query _ => 1

/-- Every ordinary gate is one- or two-qubit (queries are not restricted). -/
def IsStandard : OGate W t → Prop
  | gate g => g.IsStandard
  | query _ => True

end OGate

/-- A layer of an oracle circuit: gates with pairwise disjoint supports. -/
structure OLayer (W : Type) [DecidableEq W] (t : ℕ) where
  /-- The gates of the layer. -/
  gates : List (OGate W t)
  /-- The gates act on pairwise disjoint sets of wires. -/
  disjoint : gates.Pairwise fun g h => Disjoint g.support h.support

/-- An oracle circuit (a fixed query algorithm): a list of layers, the head layer applied first. -/
abbrev OCircuit (W : Type) [DecidableEq W] (t : ℕ) := List (OLayer W t)

namespace OCircuit

variable {W : Type} [DecidableEq W] {t : ℕ}

/-- The matrix of the algorithm run with the oracle `O`; the head layer is the rightmost factor. -/
noncomputable def matrix [Fintype W] (O : Matrix (Fin t → Bool) (Fin t → Bool) ℂ) :
    OCircuit W t → Matrix (W → Bool) (W → Bool) ℂ
  | [] => 1
  | l :: ls => matrix O ls * (l.gates.map (OGate.matrix O)).prod

/-- The depth: the number of layers. -/
def depth (C : OCircuit W t) : ℕ := C.length

/-- The size: the total number of gates, queries included. -/
def size (C : OCircuit W t) : ℕ := (C.map fun l => l.gates.length).sum

/-- The number of oracle queries. -/
def queries (C : OCircuit W t) : ℕ := (C.map fun l => (l.gates.map OGate.queryCount).sum).sum

/-- Every ordinary gate of the algorithm is one- or two-qubit. -/
def IsStandard (C : OCircuit W t) : Prop := ∀ l ∈ C, ∀ g ∈ l.gates, g.IsStandard

end OCircuit

end ConstDepthUnitary


