-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Circuit
-- name    : QAdvFew_PoQOracle_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:53.012611+00:00
-- url     : https://prove2.me/theorems/285d9c5f-8b12-4213-bb9e-3de2108871f3
-- title:
--   Boolean oracle circuits
-- statement:
--   A **Boolean oracle circuit** with inputs indexed by a type $\iota$ is a straight-line list of gates: inputs, constants, fan-in-one NOT gates, unbounded fan-in AND, OR and parity gates, and oracle gates, each reading earlier gates, together with a list of output gates. An oracle gate evaluates the oracle on the bits supplied to it.
--
--   The **size** is the length in bits of the explicit binary description of the circuit (p. 12: "there are at most $2^\ell$ circuits of size $\ell$"). The **depth** is the largest number of AND, OR, parity and oracle gates on an input-to-output path.
--
--   **Formalization Note** NOT gates are not counted in the depth, the usual $\mathsf{AC}^0$ convention. Definition 3.9 read literally counts them, but then Lemma 4.7 is false at $d=1$: the parity of two free oracle bits is computed by a machine in $S^{\mathsf{NP}}_{t'}$, and no circuit of depth $2$ with counted NOT gates computes it. An input is named in the description by a binary number or by the string itself (`IndexCode`), so writing down an input named by a string $s$ costs about $2|s|$ bits. Mathlib's `Encodable (List Bool)` is not used, because its code of a string of length $L$ has about $2^L$ bits.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.1, p. 12 (PDF p. 14); Definition 3.9, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Oracle

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The bit-string name of a circuit input with index type `ι`, used in a circuit's description
(Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1,
§3.2.1, p. 12 (PDF p. 14): "We measure the size of a circuit by its description length in bits"):
binary for `Fin n`, the string itself for an input named by a bit string, a tag bit for a sum, and a
self-delimited first component for a product.

**Formalization Note** Mathlib's `Encodable (List Bool)` is not used: its code of a string of length
`L` has about `2^L` bits, which would charge one input gate exponentially much. -/
class IndexCode (ι : Type) where
  /-- the name of an input -/
  enc : ι → Str

instance (n : ℕ) : IndexCode (Fin n) := ⟨fun i => Nat.bits i⟩

instance : IndexCode (List Bool) := ⟨id⟩

instance {α β : Type} [IndexCode α] [IndexCode β] : IndexCode (α ⊕ β) :=
  ⟨Sum.elim (fun a => false :: IndexCode.enc a) (fun b => true :: IndexCode.enc b)⟩

instance {α β : Type} [IndexCode α] [IndexCode β] : IndexCode (α × β) :=
  ⟨fun p => (IndexCode.enc p.1).flatMap (fun b => [true, b]) ++ false :: IndexCode.enc p.2⟩

/-- A gate of a Boolean oracle circuit with inputs indexed by `ι` (Goldin, Lombardi, Morimae,
*Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Definition 3.9, p. 13
(PDF p. 15)): an input, a constant, a fan-in-one NOT, unbounded fan-in AND, OR and parity, and an
oracle gate ("An oracle gate evaluates the indicated oracle on the bits supplied to that gate").
Arguments are indices of earlier gates. -/
inductive Gate (ι : Type) where
  | inp (i : ι)
  | const (b : Bool)
  | not (k : ℕ)
  | and (ks : List ℕ)
  | or (ks : List ℕ)
  | xor (ks : List ℕ)
  | orc (ks : List ℕ)

/-- A Boolean (oracle) circuit: a straight-line list of gates, each reading earlier gates, and a list
of output gates (Definition 3.9; §3.2.1, p. 12). -/
structure Circuit (ι : Type) where
  gates : List (Gate ι)
  outs : List ℕ

namespace Circuit

variable {ι : Type}

/-- The value of one gate, given the values of the earlier gates (a reference to a gate that is not
earlier reads `0`). -/
def gateVal (O : Oracle) (x : ι → Bool) (vals : List Bool) : Gate ι → Bool
  | .inp i => x i
  | .const b => b
  | .not k => !(vals.getD k false)
  | .and ks => ks.all (fun k => vals.getD k false)
  | .or ks => ks.any (fun k => vals.getD k false)
  | .xor ks => ks.foldl (fun acc k => xor acc (vals.getD k false)) false
  | .orc ks => O (ks.map (fun k => vals.getD k false))

/-- The values of all gates on input `x` with oracle `O`. -/
def values (O : Oracle) (C : Circuit ι) (x : ι → Bool) : List Bool :=
  C.gates.foldl (fun vals g => vals ++ [gateVal O x vals g]) []

/-- The outputs of `C^O(x)`. -/
def eval (O : Oracle) (C : Circuit ι) (x : ι → Bool) : List Bool :=
  C.outs.map (fun k => (C.values O x).getD k false)

/-- The single output of `C^O(x)` (the first output, `0` if there is none). -/
def eval1 (O : Oracle) (C : Circuit ι) (x : ι → Bool) : Bool := (C.eval O x).headD false

/-- The depth of one gate given the depths of the earlier gates: inputs and constants `0`, a NOT gate
the depth of its argument, every other gate one more than its deepest argument. -/
def gateDepth (ds : List ℕ) : Gate ι → ℕ
  | .inp _ => 0
  | .const _ => 0
  | .not k => ds.getD k 0
  | .and ks => (ks.map (fun k => ds.getD k 0)).foldl max 0 + 1
  | .or ks => (ks.map (fun k => ds.getD k 0)).foldl max 0 + 1
  | .xor ks => (ks.map (fun k => ds.getD k 0)).foldl max 0 + 1
  | .orc ks => (ks.map (fun k => ds.getD k 0)).foldl max 0 + 1

/-- The depth: "the largest number of gates on an input-to-output path" (Definition 3.9), where the
gates counted are AND, OR, parity and oracle gates.

**Formalization Note** NOT gates are not counted, the usual `AC0` convention. Counting them makes
Lemma 4.7 false at `d = 1`: the parity of two free oracle bits is computed by a machine in `S^NP_{t'}`,
and no circuit of depth `2` with counted NOT gates computes it. By De Morgan, a circuit of this depth
`d` is a circuit of depth `d` with NOT gates only at the inputs. -/
def depth (C : Circuit ι) : ℕ :=
  let ds := C.gates.foldl (fun ds g => ds ++ [gateDepth ds g]) []
  (C.outs.map (fun k => ds.getD k 0)).foldl max 0

/-- A bit string in self-delimiting form: each bit `b` as `1b`, then `0`. -/
def encBits (s : Str) : Str := s.flatMap (fun b => [true, b]) ++ [false]

/-- A natural number in self-delimiting binary. -/
def encNum (k : ℕ) : Str := encBits (Nat.bits k)

/-- A list of numbers: its length in unary, then the numbers in binary. -/
def encNums (ks : List ℕ) : Str := encNat ks.length ++ (ks.map encNum).flatten

/-- The code of a gate: a unary tag, then its arguments (an input by its `IndexCode`). -/
def encGate [IndexCode ι] : Gate ι → Str
  | .const b => encNat 0 ++ [b]
  | .inp i => encNat 1 ++ encBits (IndexCode.enc i)
  | .not k => encNat 2 ++ encNum k
  | .and ks => encNat 3 ++ encNums ks
  | .or ks => encNat 4 ++ encNums ks
  | .xor ks => encNat 5 ++ encNums ks
  | .orc ks => encNat 6 ++ encNums ks

/-- The description of a circuit: the number of gates in unary, the gate codes, the output list. -/
def code [IndexCode ι] (C : Circuit ι) : Str :=
  encNat C.gates.length ++ (C.gates.map encGate).flatten ++ encNums C.outs

/-- The size of a circuit: the length of its description in bits (§3.2.1, p. 12: "We measure the
size of a circuit by its description length in bits. Under our convention, there are at most `2^ℓ`
circuits of size `ℓ`"). The description is injective, so the count holds.

**Formalization Note** An input indexed by a string `s` costs about `2|s|` bits and an input `i` of
`Fin n` about `2 log₂ n` bits (`IndexCode`), the length of writing the index down. -/
def size [IndexCode ι] (C : Circuit ι) : ℕ := C.code.length

/-- `C` has no parity gates. -/
def NoXor (C : Circuit ι) : Prop := ∀ g ∈ C.gates, ∀ ks, g ≠ .xor ks

/-- `C` has no oracle gates. -/
def NoOracle (C : Circuit ι) : Prop := ∀ g ∈ C.gates, ∀ ks, g ≠ .orc ks

end Circuit

end QAdvFew.PoQOracle


