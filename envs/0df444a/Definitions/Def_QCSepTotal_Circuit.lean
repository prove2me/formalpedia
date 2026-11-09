-- Prove2me | Definitions.Def_QCSepTotal_Circuit
-- name    : QCSepTotal_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:29.912439+00:00
-- url     : https://prove2.me/theorems/a5d96054-1d5e-4250-8be9-1b75c12a23f2
-- title:
--   Boolean circuits with fan-in-two AND/OR gates and NOT gates, and their size
-- statement:
--   A **Boolean circuit** on input variables indexed by $\iota$ is a sequence of gates, each a fan-in-two AND gate, a fan-in-two OR gate or a NOT gate, whose inputs are input variables or earlier gates, together with a designated output wire. Its **size** is the number of gates. Input variables are not counted, and there are no constant gates.
--
--   Theorem 1.4 assumes a circuit of size at most $s$ for the domain indicator $D_F$, and Proposition 2.4 turns a size-$S$ circuit into a certificate predicate.
--
--   **Formalization Note** Each gate reads only inputs and earlier gates, so ill-formed references cannot occur. The output may be any wire; gates after the output can be deleted, so "there is a circuit of size at most $s$" means the same as when the last gate is the output.
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), §2, p.5 (Boolean circuits: fan-in-two AND and OR gates, NOT gates)

import Mathlib

namespace QCSepTotal

/-- A gate of a Boolean circuit whose wires are the inputs `ι` and the `k` earlier gates: a
fan-in-two AND or OR gate, or a NOT gate (F. Le Gall, *Improved Separations between Quantum and
Classical Communication Complexity of Total Functions*, arXiv:2609.16726, held version sha256
970e1476…, §2, p.5: "Boolean circuits use fan-in-two AND and OR gates, and NOT gates"). -/
inductive Gate (ι : Type) (k : ℕ) where
  /-- `a ∧ b` -/
  | and (a b : ι ⊕ Fin k)
  /-- `a ∨ b` -/
  | or (a b : ι ⊕ Fin k)
  /-- `¬ a` -/
  | not (a : ι ⊕ Fin k)

/-- The value of a gate, given the values of all wires it may read. -/
def Gate.eval {ι : Type} {k : ℕ} : Gate ι k → (ι ⊕ Fin k → Bool) → Bool
  | .and a b, w => w a && w b
  | .or a b, w => w a || w b
  | .not a, w => !w a

/-- A list of `k` gates, each reading only inputs and strictly earlier gates (so that no
reference is ill-formed). -/
inductive Gates (ι : Type) : ℕ → Type where
  /-- no gates -/
  | nil : Gates ι 0
  /-- append a gate reading the inputs and the `k` gates before it -/
  | snoc {k : ℕ} (C : Gates ι k) (g : Gate ι k) : Gates ι (k + 1)

/-- The values of all gates on the input `x`. -/
def Gates.vals {ι : Type} : {k : ℕ} → Gates ι k → (ι → Bool) → Fin k → Bool
  | _, .nil, _ => Fin.elim0
  | _, .snoc C g, x =>
      Fin.lastCases (motive := fun _ => Bool) (g.eval (Sum.elim x (C.vals x))) (C.vals x)

/-- A **Boolean circuit** on inputs `ι`: `size` gates (fan-in-two AND/OR, NOT) and a designated
output wire. Its **size** is the number of gates; inputs are not counted, and there are no
constant gates.

**Formalization Note.** The output may be any wire. Every function with a circuit of size `k`
in which the last gate is the output also has one of this form, and conversely the gates after
the output wire can be deleted, so "has a circuit of size at most `s`" is the paper's notion. -/
structure Circuit (ι : Type) where
  /-- the number of gates -/
  size : ℕ
  /-- the gates -/
  gates : Gates ι size
  /-- the output wire -/
  out : ι ⊕ Fin size

/-- The function computed by a circuit. -/
def Circuit.eval {ι : Type} (C : Circuit ι) (x : ι → Bool) : Bool :=
  Sum.elim x (C.gates.vals x) C.out

end QCSepTotal


