-- Prove2me | Definitions.Def_GOSNIZK_CircuitSound_Circuit
-- name    : GOSNIZK_CircuitSound_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:26.608193+00:00
-- url     : https://prove2.me/theorems/a87ff00e-e406-4ae6-be40-cfed1bafac83
-- title:
--   NAND circuits and satisfaction C(w) = 1 (§6, p. 13)
-- statement:
--   A **NAND circuit** on $n$ wires is a list of gates and a designated output wire $\mathrm{out}$. A gate is a triple $(i,j,k)$ of wires: $i$ and $j$ are its inputs and $k$ its output. An assignment $w=(w_1,\dots,w_n)$ of truth values to the wires **satisfies** the circuit $C$, written $C(w)=1$, when it respects every gate and the output wire is true:
--   $$C(w)=1 \iff \Big(\forall (i,j,k)\in C:\ w_k=\neg(w_i\wedge w_j)\Big)\ \wedge\ w_{\mathrm{out}}=1.$$
--   Circuit SAT, the language proved in Figure 3, consists of the circuits that have a satisfying assignment.
--
--   **Formalization Note** Wires are `Fin n` and the gates are a `List (Fin n × Fin n × Fin n)`. No acyclicity or topological order is required, so the definition covers every system of NAND constraints, a superset of the paper's circuits; the satisfaction relation is the paper's "the wires respect the circuit and the output wire is true" verbatim. Since `out : Fin n`, a circuit has at least one wire.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 13, Section 6 (first paragraph)

import Mathlib

namespace GOSNIZK.CircuitSound

/-- A circuit of NAND gates on `n` wires (Groth, Ostrovsky, Sahai, *New Techniques for
Noninteractive Zero-Knowledge*, J. ACM 59(3) (2012), authors' version of March 7, 2011, §6, p. 13):
each gate `(i, j, k)` has input wires `i`, `j` and output wire `k`, and `out` is the output wire. -/
structure Circuit (n : ℕ) where
  gates : List (Fin n × Fin n × Fin n)
  out : Fin n

/-- `C(w) = 1` (p. 13): the wire values `w` respect every NAND gate, `w_k = ¬(w_i ∧ w_j)` for each
gate `(i, j, k)`, and the output wire is true, `w_out = 1`. -/
def Circuit.Sat {n : ℕ} (Γ : Circuit n) (w : Fin n → Bool) : Prop :=
  (∀ g ∈ Γ.gates, w g.2.2 = !(w g.1 && w g.2.1)) ∧ w Γ.out = true

end GOSNIZK.CircuitSound


