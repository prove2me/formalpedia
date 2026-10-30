-- Prove2me | Definitions.Def_AKNMixed_FQP_Op
-- name    : AKNMixed_FQP_Op
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:43.257285+00:00
-- url     : https://prove2.me/theorems/a87b7801-c865-4abb-9951-360899135c82
-- title:
--   Node label: a gate of $\mathcal G$ or a subroutine of $\mathcal S$
-- statement:
--   A node of a circuit is labeled either by a gate $g\in\mathcal G$ of order $(k,l)$ or, in a circuit that uses subroutines, by a probabilistic function $f\in\mathcal S$ from $m$ to $p$ bits. `Op G S` is the disjoint union of the two kinds of label, with
--
--   1. order $(k,l)$ and map $g$ for a gate;
--   2. order $(m+p,m+p)$ and map the subroutine gate $g_f$ for a subroutine, with its input register on the first $m$ wires and its output register on the last $p$ wires.
--
--   **Formalization Note** `Op.inOrd`, `Op.outOrd` and `Op.superop` give the order and the super-operator of a label.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Definition 2, p. 7; §4.2, unnumbered, pp. 9–10 ("a node of fan-in=fan-out=m + p may be associated instead of a quantum gate, a probabilistic function")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_AKNMixed_FQP_QGate
import Definitions.Def_AKNMixed_FQP_ProbFun
import Definitions.Def_AKNMixed_FQP_subroutineGate

namespace AKNMixed.FQP

open QAlgorithms

/-- **The label of a circuit node: a gate of `G` or a subroutine of `S`.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Definition 2, p. 7 ("Each node v in the graph is labeled by a gate g_v ∈ G of order
(k_v, l_v)") and §4.2, unnumbered, pp. 9–10 ("A quantum circuit that uses subroutines is a
circuit in which a node of fan-in=fan-out=m + p may be associated instead of a quantum gate, a
probabilistic function f : {0,1}^m ⟼ R^{{0,1}^p}").

`Op G S` is the disjoint union of the members of the gate set `G` and of the subroutine set `S`.
A gate label has the gate's order; a subroutine label has order `(m + p, m + p)`. -/
abbrev Op {m p : ℕ} (G : Set QGate) (S : Set (ProbFun m p)) : Type :=
  {g // g ∈ G} ⊕ {s // s ∈ S}

/-- Definition 2, p. 7, and §4.2, p. 9: the number of input wires of a node label (`k_v` for a
gate, `m + p` for a subroutine). -/
def Op.inOrd {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} : Op G S → ℕ
  | .inl g => g.1.inOrd
  | .inr _ => m + p

/-- Definition 2, p. 7, and §4.2, p. 9: the number of output wires of a node label (`l_v` for a
gate, `m + p` for a subroutine). -/
def Op.outOrd {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} : Op G S → ℕ
  | .inl g => g.1.outOrd
  | .inr _ => m + p

/-- Definition 1, p. 7, and Definition 5, p. 10: the super-operator of a node label: the gate's
map, or the subroutine gate `g_f` with its input register on the first `m` wires and its output
register on the last `p` wires (`Fin.append`). -/
noncomputable def Op.superop {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} :
    (o : Op G S) → Superop (Qubits o.inOrd) (Qubits o.outOrd)
  | .inl g => g.1.map
  | .inr s => fun X => Matrix.of fun y z =>
      subroutineGate s.1
        (Matrix.of fun q q' => X (Fin.append q.1 q.2) (Fin.append q'.1 q'.2))
        ((fun i => y (Fin.castAdd p i)), (fun j => y (Fin.natAdd m j)))
        ((fun i => z (Fin.castAdd p i)), (fun j => z (Fin.natAdd m j)))

end AKNMixed.FQP


