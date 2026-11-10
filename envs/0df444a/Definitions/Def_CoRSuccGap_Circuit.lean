-- Prove2me | Definitions.Def_CoRSuccGap_Circuit
-- name    : CoRSuccGap_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:47:37.799544+00:00
-- url     : https://prove2.me/theorems/28912018-362a-4f76-879e-2ad72ae92a82
-- title:
--   Relational (CoR) circuits, their value $[\![C]\!]^{\mathcal M}$ and composition-gate count $g_{;}(C)$
-- statement:
--   A **relational circuit** (CoR circuit) over a signature $\sigma$ is a finite directed acyclic graph with a designated output gate. Each gate is labelled by an input symbol $R\in\sigma$, one of the constants $\mathbf 0,\mathbf 1,\mathbf{id}$, or one of the CoR operations $\cup,\cap,\overline{\,\cdot\,},\cdot^{\smile},;$; operation gates have ordered input ports fed by earlier gates. A gate may feed any number of later gates, including both ports of one composition. On a structure $\mathcal M$ the value $[\![g]\!]^{\mathcal M}\subseteq D^2$ of each gate is computed once from its predecessors with the operations of the calculus of relations, and $[\![C]\!]^{\mathcal M}$ is the value of the output gate.
--
--   The **composition-gate count** $g_{;}(C)$ is the number of distinct gates of $C$ labelled by composition: a shared gate counts once, whatever its fan-out. No other primitive is available: no order, no named vertices, no extra vertex predicates.
--
--   For example, the circuit $g_0=R$, $g_1=g_0;g_0$, $g_2=g_1;g_1$ computes the same relation as the term $(R;R);(R;R)$ but has only two composition gates, against three composition occurrences in the term.
--
--   These circuits are the model in which Theorem 1.1 proves its lower bound despite arbitrary sharing.
--
--   **Formalization Note** A circuit is a straight-line program: gates are numbered $0,\dots,\mathrm{size}-1$ and gate $i$ is a `Gate σ (Fin i)`, whose operands are indices of earlier gates; this numbering is a topological order of the DAG. `Circuit.gateVal M i` is $[\![g_i]\!]^{\mathcal M}$, `Circuit.eval M` is $[\![C]\!]^{\mathcal M}$, and `Circuit.numCompGates` counts the composition gates of the whole program.
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), §2.2, pp.15–16 (PDF 17–18), Figure 6; g;(C): §2.3, p.16 (PDF 18); allowed primitives: §2.3, p.17 (PDF 19)

import Mathlib

set_option autoImplicit false

namespace CoRSuccGap

/-!
# Relational (CoR) circuits

Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the
Calculus of Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), §2.2, pp.15–16 (PDF 17–18): "A relational circuit (or CoR circuit) is a finite directed
acyclic graph (DAG) with a designated output gate. Each gate is labeled by an input relation
symbol R ∈ σ, a constant, or a CoR operation; operation gates have ordered input ports fed by their
predecessors. A gate may feed multiple later gates, including both ports of one composition. Its
value ⟦g⟧^M is computed once from its predecessors; ⟦C⟧^M is the value of the output gate." §2.3,
p.16 (PDF 18): "g;(C) counts distinct composition gates … A shared gate counts once, irrespective
of its fan-out."

**Formalization Note.**
* A circuit is a straight-line program: gates are numbered `0, …, size − 1`, and gate `i` is a
  `Gate σ (Fin i)`, whose operands are indices of earlier gates. This is a topological order of
  the DAG, so the graph is acyclic; any gate may be read by any number of later gates, and the two
  ports of one composition may read the same gate (Figure 6, p.16). The ports are ordered.
* Exactly the paper's nine labels: input symbol, 0, 1, id, ∪, ∩, complement, converse,
  composition (p.17: "A relational circuit has only the input symbols and the three constants
  0, 1, id").
* `numCompGates` is g;(C): the number of gates (of the whole program, reachable from the output or
  not) labelled by composition; each gate counts once whatever its fan-out.
-/

/-- A gate label of a relational circuit whose operands are references of type `ι` (to earlier
gates): an input symbol, a constant, or a CoR operation with ordered ports. -/
inductive Gate (σ : Type*) (ι : Type*) where
  /-- An input gate labelled by `R ∈ σ`. -/
  | rel (R : σ) : Gate σ ι
  /-- The constant gate 0. -/
  | zero : Gate σ ι
  /-- The constant gate 1. -/
  | one : Gate σ ι
  /-- The constant gate id. -/
  | id : Gate σ ι
  /-- A union gate with ports `a`, `b`. -/
  | union (a b : ι) : Gate σ ι
  /-- An intersection gate with ports `a`, `b`. -/
  | inter (a b : ι) : Gate σ ι
  /-- A complement gate. -/
  | compl (a : ι) : Gate σ ι
  /-- A converse gate. -/
  | conv (a : ι) : Gate σ ι
  /-- A composition gate computing `a; b` (ordered ports). -/
  | comp (a b : ι) : Gate σ ι

namespace Gate

variable {σ : Type*} {ι : Type*}

/-- The value of a gate on the structure `M`, given the values `val` of the gates it reads. -/
def evalWith {D : Type*} (M : σ → D → D → Prop) (val : ι → D → D → Prop) :
    Gate σ ι → D → D → Prop
  | rel R => M R
  | zero => fun _ _ => False
  | one => fun _ _ => True
  | id => fun a b => a = b
  | union x y => fun a b => val x a b ∨ val y a b
  | inter x y => fun a b => val x a b ∧ val y a b
  | compl x => fun a b => ¬ val x a b
  | conv x => fun a b => val x b a
  | comp x y => fun a b => ∃ c, val x a c ∧ val y c b

/-- Whether a gate is a composition gate. -/
def isComp : Gate σ ι → Bool
  | comp _ _ => true
  | _ => false

end Gate

/-- A relational circuit over `σ` (§2.2, p.15): `size` gates in topological order, gate `i`
reading only gates `j < i`, and a designated output gate. -/
structure Circuit (σ : Type*) where
  /-- The number of gates. -/
  size : ℕ
  /-- The label of gate `i`, whose operands are earlier gates. -/
  gate : (i : Fin size) → Gate σ (Fin i)
  /-- The designated output gate. -/
  output : Fin size

namespace Circuit

variable {σ : Type*}

/-- ⟦g⟧^M: the value of each gate on the structure `M`, computed once from its predecessors. -/
def gateVal (C : Circuit σ) {D : Type*} (M : σ → D → D → Prop) : Fin C.size → D → D → Prop
  | ⟨i, hi⟩ => (C.gate ⟨i, hi⟩).evalWith M
      (fun j => C.gateVal M ⟨j.val, lt_trans j.isLt hi⟩)
termination_by i => i.val
decreasing_by exact j.isLt

/-- ⟦C⟧^M: the value of the output gate. -/
def eval (C : Circuit σ) {D : Type*} (M : σ → D → D → Prop) : D → D → Prop :=
  C.gateVal M C.output

/-- g;(C): the number of distinct composition gates of `C` (§2.3, p.16). -/
def numCompGates (C : Circuit σ) : ℕ :=
  (Finset.univ.filter (fun i : Fin C.size => (C.gate i).isComp = true)).card

end Circuit

end CoRSuccGap


