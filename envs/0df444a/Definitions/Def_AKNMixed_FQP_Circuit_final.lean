-- Prove2me | Definitions.Def_AKNMixed_FQP_Circuit_final
-- name    : AKNMixed_FQP_Circuit_final
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:20:26.462125+00:00
-- url     : https://prove2.me/theorems/1263e898-3693-4e78-bb88-081f2c9b8df9
-- title:
--   Final density matrix $Q\circ\rho=g_t\circ\dots\circ g_1\circ\rho$ (Definition 3)
-- statement:
--   Let $Q$ be a circuit whose nodes are listed in the topological order $g_1,\dots,g_t$. The **final density matrix** for an initial matrix $\rho$ on all wires is
--
--   $$Q\circ\rho=g_t\circ\cdots\circ g_2\circ g_1\circ\rho ,$$
--
--   each node acting through its step on the whole system, the head $g_1$ first.
--
--   **Formalization Note** The topological sort is the order of the node list; Lemma 2 shows the result does not depend on it.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Definition 3, p. 8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_AKNMixed_FQP_Circuit

namespace AKNMixed.FQP

open QAlgorithms

/-- **The final density matrix `Q ∘ ρ = g_t ∘ … ∘ g_2 ∘ g_1 ∘ ρ`.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Definition 3, p. 8: "Let Q be a quantum circuit. Choose a topological sort for Q: g_t...g_1. Where
g_j are the gates used in the circuit. The final density matrix for an initial density matrix ρ
is Q ∘ ρ = g_t ∘ ... ∘ g_2 ∘ g_1 ∘ ρ."

`Q.final ρ` applies the steps of the nodes of `Q` to the `N`-wire matrix `ρ` in list order, the
head node (`g_1`) first.

**Formalization Note.** The topological sort is the order of `Q.nodes`; independence of the
choice is Lemma 2 (`AKNMixed.FQP.final_eq_of_perm`). -/
noncomputable def Circuit.final {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} {nIn r : ℕ}
    (Q : Circuit G S nIn r) (ρ : Matrix (Qubits Q.N) (Qubits Q.N) ℂ) :
    Matrix (Qubits Q.N) (Qubits Q.N) ℂ :=
  Q.nodes.foldl (fun X v => v.step X) ρ

end AKNMixed.FQP


