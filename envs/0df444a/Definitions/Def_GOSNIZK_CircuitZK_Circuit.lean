-- Prove2me | Definitions.Def_GOSNIZK_CircuitZK_Circuit
-- name    : GOSNIZK_CircuitZK_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:23:31.146034+00:00
-- url     : https://prove2.me/theorems/0310e652-1e26-4179-b117-9034bfeece32
-- title:
--   NAND circuits and satisfying wire assignments $C(w) = 1$ (§6, p. 13)
-- statement:
--   A **NAND circuit** on $n$ wires is a list of gates $(i, j, k)$, each with input wires $i, j$ and output wire $k$, together with a designated output wire $\mathrm{out}$. A wire assignment $w = (w_1, \dots, w_n) \in \{0,1\}^n$ satisfies the circuit, written $C(w) = 1$, if it respects every gate and makes the output true:
--   $$w_k = \neg(w_i \wedge w_j)\ \text{ for every gate } (i, j, k), \qquad w_{\mathrm{out}} = 1.$$
--   A truth value $b$ is read as the element $0$ or $1$ of the message space $\mathbb Z/N$.
--
--   Circuit satisfiability is the NP-complete language whose zero-knowledge proof is the subject of the mission.
--
--   **Formalization Note** No acyclicity is required: the definition covers every system of NAND constraints with an output wire, which contains the paper's circuits.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 13, Section 6

import Mathlib

namespace GOSNIZK.CircuitZK

/-- A circuit of NAND gates on `n` wires (Groth, Ostrovsky, Sahai, J. ACM 59(3) (2012), authors' version of
March 7, 2011, §6, p. 13): a list of gates `(i, j, k)`, each with input wires `i, j` and output wire `k`, and a
designated output wire `out`. -/
structure Circuit (n : ℕ) where
  gates : List (Fin n × Fin n × Fin n)
  out : Fin n

/-- `C(w) = 1` (p. 13): the wire values `w` respect every NAND gate, `w_k = ¬(w_i ∧ w_j)`, and the output wire is
true. -/
def Circuit.Sat {n : ℕ} (C : Circuit n) (w : Fin n → Bool) : Prop :=
  (∀ g ∈ C.gates, w g.2.2 = !(w g.1 && w g.2.1)) ∧ w C.out = true

instance {n : ℕ} (C : Circuit n) (w : Fin n → Bool) : Decidable (C.Sat w) := by
  unfold Circuit.Sat; infer_instance

/-- A truth value read as an element `0` or `1` of the message space. -/
def bit {N : ℕ} (b : Bool) : ZMod N := if b then 1 else 0

end GOSNIZK.CircuitZK


