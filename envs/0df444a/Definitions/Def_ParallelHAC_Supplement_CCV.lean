-- Prove2me | Definitions.Def_ParallelHAC_Supplement_CCV
-- name    : ParallelHAC_Supplement_CCV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:31:34.173428+00:00
-- url     : https://prove2.me/theorems/4816e946-4500-467d-93e9-a022f602ce7a
-- title:
--   Comparator circuits and the Comparator Circuit Value language CCV
-- statement:
--   A **comparator circuit** on $m$ wires is a sequence of gates $(i,j)$ with $i\ne j<m$. Wires carry bits; the gate $(i,j)$ replaces the values $(v_i,v_j)$ by $(v_i\wedge v_j,\ v_i\vee v_j)$ and leaves the other wires unchanged. An instance of **Comparator Circuit Value** consists of a circuit, one input bit per wire, and a designated wire; it is a YES-instance when the designated wire carries $1$ after all gates have been applied in order.
--
--   Instances are bit strings. A natural number is written in a self-delimiting binary code (each binary digit $b$, least significant first, as the pair $1b$, followed by a terminating $0$), and an instance is the concatenation of the codes of $m$, the number of gates, the gate endpoints, the input bits and the designated wire. **CCV** is the set of strings that encode a well-formed YES-instance; every other string is a NO-instance.
--
--   CCV is the complete problem of the class CC of Cook, Filmus and Lê (2014), which the paper uses in Definition 7 without defining it.
--
--   **Formalization Note** Any standard encoding is logspace-equivalent to this one.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §2.5, p.12 (PDF p.15), citing [CFL14] (Cook, Filmus, Lê, ACM TOCT 6(4), 2014)

import Mathlib

namespace ParallelHAC.Supplement

/-!
# The Comparator Circuit Value problem (standard; cited as [CFL14] on p.12)

Source: arXiv:2507.20047 (sha256 a21061c8…), §2.5, p.12 (PDF p.15), which uses the class CC of
S. Cook, Y. Filmus, D. T. M. Lê, *The complexity of the comparator circuit value problem*,
ACM TOCT 6(4), 2014 ([CFL14]) without defining it.

**Formalization Note.** Inputs are bit strings `List Bool`. A natural number is written in a
self-delimiting binary code (`encodeNat`); an instance is the concatenation of the codes of the
numbers listing it. Strings that encode no well-formed instance are NO-instances.
-/

/-- Self-delimiting binary code of `n : ℕ`: each binary digit `b` of `n` (least significant
first, `Nat.bits`) is written as the pair `true, b`, and the code ends with `false`. -/
def encodeNat (n : ℕ) : List Bool :=
  (Nat.bits n).flatMap (fun b => [true, b]) ++ [false]

/-- Concatenated self-delimiting codes of a list of natural numbers. -/
def encodeNats (l : List ℕ) : List Bool :=
  l.flatMap encodeNat

/-- A **comparator circuit** on `wires` wires: a list of comparator gates `(i, j)`. -/
structure ComparatorCircuit where
  /-- Number of wires. -/
  wires : ℕ
  /-- The gates, applied in list order. -/
  gates : List (ℕ × ℕ)

/-- Every gate `(i, j)` joins two distinct wires `i ≠ j`, both `< wires`. -/
def ComparatorCircuit.WellFormed (C : ComparatorCircuit) : Prop :=
  ∀ g ∈ C.gates, g.1 < C.wires ∧ g.2 < C.wires ∧ g.1 ≠ g.2

/-- One comparator gate `(i, j)`: wire `i` receives `v i ∧ v j` and wire `j` receives
`v i ∨ v j`; the other wires are unchanged. -/
def applyComparator (v : ℕ → Bool) (g : ℕ × ℕ) : ℕ → Bool :=
  fun w => if w = g.1 then (v g.1 && v g.2) else if w = g.2 then (v g.1 || v g.2) else v w

/-- The wire values after all gates, starting from the input bits (wire `w` starts with
`input[w]`). -/
def ComparatorCircuit.eval (C : ComparatorCircuit) (input : List Bool) : ℕ → Bool :=
  C.gates.foldl applyComparator (fun w => input.getD w false)

/-- An instance of Comparator Circuit Value: a circuit, its input bits, a designated wire. -/
structure CCVInstance where
  /-- The circuit. -/
  circuit : ComparatorCircuit
  /-- One input bit per wire. -/
  input : List Bool
  /-- The designated output wire. -/
  output : ℕ

/-- Well-formed: well-formed gates, one input bit per wire, designated wire `< wires`. -/
def CCVInstance.WellFormed (I : CCVInstance) : Prop :=
  I.circuit.WellFormed ∧ I.input.length = I.circuit.wires ∧ I.output < I.circuit.wires

/-- The encoding: the codes of `wires`, the number of gates, the gate endpoints
`i₁, j₁, …, i_g, j_g`, the input bits (as `0`/`1`) and the designated wire. -/
def CCVInstance.encode (I : CCVInstance) : List Bool :=
  encodeNats ([I.circuit.wires, I.circuit.gates.length] ++
    I.circuit.gates.flatMap (fun g => [g.1, g.2]) ++
    I.input.map (fun b => if b then 1 else 0) ++ [I.output])

/-- **CCV** (Comparator Circuit Value), the language of encodings of well-formed instances whose
designated wire carries `1` after the circuit is evaluated. -/
def CCV : Set (List Bool) :=
  {x | ∃ I : CCVInstance, I.WellFormed ∧ I.encode = x ∧ I.circuit.eval I.input I.output = true}

end ParallelHAC.Supplement


