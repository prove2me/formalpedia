-- Prove2me | Definitions.Def_QiOPoQ_Supplement_Placement
-- name    : QiOPoQ_Supplement_Placement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:01:31.673546+00:00
-- url     : https://prove2.me/theorems/3b80589b-1cd9-4ddc-be65-036640511b34
-- title:
--   Ancilla-free $n$-qubit circuits, concatenation and adjoints
-- statement:
--   Section 6 works with ancilla-free $n$-qubit circuits. A legal placement is a gate of the gate set on an ordered tuple of distinct wires; an ancilla-free $n$-qubit circuit is a list of placements on $n$ wires, with all $n$ wires as output in order. Concatenation $A\|B$, with $(A\|B)(\cdot)=B(A(\cdot))$, is list append; $C^\dagger$ is the reversed list of adjoint gates. `decAC` decodes a description as such a circuit.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, p.14; Notation 6.1, p.30

import Mathlib
import Definitions.Def_QiOPoQ_Circ
import Definitions.Def_QiOPoQ_encCirc

set_option autoImplicit false

namespace QiOPoQ.Supplement

/-- A legal gate placement on `n` qubits: a gate of `G` on an ordered tuple of distinct wires
(Gheorghiu, Gupte, Havlíček, Liu, arXiv:2609.40289, sha256 fe2f9210…, Notation 6.1, p.30: "the
legal gate placements on n qubits"). -/
abbrev Placement (G : GateSet) (n : ℕ) := Σ i : Fin G.k, Fin (G.arity i) ↪ Fin (n + 0)

variable {G : GateSet}

/-- **An ancilla-free `n`-qubit circuit (§6).** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable
Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256
fe2f9210…), §3.1, p.14: "A circuit is ancilla-free if n_anc = 0"; Notation 6.1, p.30 (n-qubit
circuits, concatenation `A∥B`, `C_{n,N}`). The circuit with gate list `gs` (applied first to last)
on `n` input wires, no ancillas, and output register all `n` wires in order. Concatenation `A∥B`
(`(A∥B)(·) = B(A(·))`) is list append. -/
def afCirc (n : ℕ) (gs : List (Placement G n)) : Circ G :=
  { nin := n, nanc := 0, gates := gs, out := List.finRange (n + 0),
    out_nodup := List.nodup_finRange _ }

/-- The adjoint of a placed gate: the adjoint gate of `G` on the same wires. -/
def placeDagger {n : ℕ} (p : Placement G n) : Placement G n :=
  ⟨G.adj p.1, (finCongr (G.arity_adj p.1)).toEmbedding.trans p.2⟩

/-- `C†` (Notation 6.1, p.30: the gate set is "inverse-closed"; Assumption 6.2, p.31: `R†`): the
gates of `C` in reverse order, each replaced by its adjoint gate, so that `C†` implements the
adjoint unitary. -/
def afDagger {n : ℕ} (gs : List (Placement G n)) : List (Placement G n) :=
  (gs.map placeDagger).reverse

open Classical in
/-- Decoding a description as an ancilla-free `n`-qubit circuit (`none` if it describes none). -/
noncomputable def decAC (n : ℕ) (s : List Bool) : Option (List (Placement G n)) :=
  if h : ∃ gs : List (Placement G n), encCirc (afCirc n gs) = s then some h.choose else none

end QiOPoQ.Supplement


