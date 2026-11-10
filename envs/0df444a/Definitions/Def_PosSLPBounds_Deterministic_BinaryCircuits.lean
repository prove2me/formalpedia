-- Prove2me | Definitions.Def_PosSLPBounds_Deterministic_BinaryCircuits
-- name    : PosSLPBounds_Deterministic_BinaryCircuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T20:43:33.830817+00:00
-- url     : https://prove2.me/theorems/660dbdcc-2b5b-4979-8814-f9bc9034541e
-- title:
--   Binary encodings and integer and polynomial semantics for division-free circuits
-- statement:
--   A division-free integer straight-line program is a finite topologically ordered circuit with binary addition, subtraction and multiplication, integer literals and indexed variable inputs. The published circuit syntax and its ring evaluation are reused. For one output in $r$ variables, evaluation in the polynomial ring gives a polynomial $f\in\mathbb Z[X_1,\ldots,X_r]$; integer evaluation uses no variable inputs.
--
--   The fixed bit code writes a natural number as its binary bit length in unary, a zero separator, and its canonical little-endian binary digits. Zero has an empty digit string. Signed integers use the bijection $z=n\mapsto2n$ and $z=-(n+1)\mapsto2n+1$. Wire tags distinguish variables, integer literals and earlier gates; gate tags distinguish addition, subtraction and multiplication. A circuit contains its gate-list length, gate records, output-list length and output records. Parsers reject truncated or noncanonical fields, unknown tags and trailing data. No polynomial coefficient or semantic degree is computed during parsing.
--
--   The positivity language is
--   $$
--   \mathrm{PosSLP}=\{x:\ x\text{ encodes a valid circuit with no variables, one output, literals }0,1,\text{ and integer output }>0\}.
--   $$
--   Every other string is a negative instance. The coefficient-query code concatenates $r$, the circuit, $D$, the $r$ exponent coordinates, and $m$ in this binary format. Its separate parser returns syntactic data; degree promises remain hypotheses of the coefficient theorem.
--
--   This interface fixes the input representation used by both targets. Sharing, constants, negative coefficients, zero polynomials and the case $r=0$ are retained. Default zero values of the reused evaluator never admit invalid circuits: source-validity is required separately.
--
--   **Formalization Note** For a valid PosSLP circuit with $s$ operation gates, this code has between $s+1$ and $32(s+1)^2$ bits; the latter is a deliberately loose bound obtained from the field lengths, not a time bound or a numerical claim from the paper. Gate indices are binary. Only the PosSLP language restricts literals to 0 and 1. The polynomial semantic function uses Mathlib's multivariate polynomials on Fin r over the integers. This module asserts no efficient integer-output evaluator.
-- source:
--   Alex Meiburg, Eric Allender, Markus Bläser, STOC 2027 submission #1162 (October 2026), §1 p.1, §3 p.3 and Lemma 1 p.5; binary serialization is an explicit local encoding convention; PDF SHA-256 726079fb6c4a7099c90cde697accb5947be487e2e7ba8162a0bcf56a44a57e98

import Mathlib
import Definitions.Def_AlmostLinearModComp_Composition_Circuits
set_option autoImplicit false

namespace PosSLPBounds.Deterministic

open AlmostLinearModComp.Composition

/-- Self-delimiting binary natural: the bit length in unary (ones followed by zero),
then the little-endian canonical `Nat.bits` payload. Zero has empty payload. -/
def encodeNat (n : ℕ) : List Bool :=
  List.replicate (Nat.bits n).length true ++ [false] ++ Nat.bits n

/-- Value of a little-endian bit string. -/
def bitsValue (bs : List Bool) : ℕ :=
  bs.foldr (fun b n => 2 * n + if b then 1 else 0) 0

/-- A syntactic parser: reject truncated fields and noncanonical binary payloads. -/
def parseNat (bs : List Bool) : Option (ℕ × List Bool) := do
  let len := (bs.takeWhile id).length
  if bs[len]? != some false then none else do
    let rest := bs.drop (len + 1)
    let payload := rest.take len
    if payload.length = len ∧ Nat.bits (bitsValue payload) = payload then
      some (bitsValue payload, rest.drop len)
    else none

/-- Zigzag integer code; negative zero has no second encoding. -/
def integerCode : ℤ → ℕ
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def integerOfCode (n : ℕ) : ℤ :=
  if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

/-- Tags 0,1,2 mean input, integer literal, previous gate respectively. -/
def encodeWire : Wire → List Bool
  | .input i => encodeNat 0 ++ encodeNat i
  | .integer z => encodeNat 1 ++ encodeNat (integerCode z)
  | .gate i => encodeNat 2 ++ encodeNat i

def parseWire (bs : List Bool) : Option (Wire × List Bool) := do
  let (tag, rest) ← parseNat bs
  let (n, tail) ← parseNat rest
  match tag with
  | 0 => some (.input n, tail)
  | 1 => some (.integer (integerOfCode n), tail)
  | 2 => some (.gate n, tail)
  | _ => none

/-- Tags 0,1,2 mean addition, subtraction, multiplication respectively. -/
def encodeGate : RingGate → List Bool
  | .add a b => encodeNat 0 ++ encodeWire a ++ encodeWire b
  | .sub a b => encodeNat 1 ++ encodeWire a ++ encodeWire b
  | .mul a b => encodeNat 2 ++ encodeWire a ++ encodeWire b

def parseGate (bs : List Bool) : Option (RingGate × List Bool) := do
  let (tag, rest) ← parseNat bs
  let (a, rest) ← parseWire rest
  let (b, tail) ← parseWire rest
  match tag with
  | 0 => some (.add a b, tail)
  | 1 => some (.sub a b, tail)
  | 2 => some (.mul a b, tail)
  | _ => none

/-- Parse exactly n objects, stopping immediately if any object is malformed. -/
def parseMany {α : Type} (p : List Bool → Option (α × List Bool)) :
    ℕ → List Bool → Option (List α × List Bool)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (a, rest) ← p bs
    let (as, tail) ← parseMany p n rest
    some (a :: as, tail)

/-- Gate count, gate list, output count, output list, all in the fixed binary code. -/
def encodeCircuit (c : Circuit) : List Bool :=
  encodeNat c.gates.length ++ c.gates.flatMap encodeGate ++
    encodeNat c.outputs.length ++ c.outputs.flatMap encodeWire

def parseCircuit (bs : List Bool) : Option (Circuit × List Bool) := do
  let (ng, rest) ← parseNat bs
  let (gs, rest) ← parseMany parseGate ng rest
  let (no, rest) ← parseNat rest
  let (outs, tail) ← parseMany parseWire no rest
  some (⟨gs, outs⟩, tail)

/-- A standalone circuit has no trailing fields. Topological validity is separate. -/
def decodeCircuit (bs : List Bool) : Option Circuit := do
  let (c, rest) ← parseCircuit bs
  if rest = [] then some c else none

def wireLiteral01 : Wire → Prop
  | .integer z => z = 0 ∨ z = 1
  | _ => True

def gateLiteral01 : RingGate → Prop
  | .add a b | .sub a b | .mul a b => wireLiteral01 a ∧ wireLiteral01 b

/-- Only PosSLP, not general integer SLPs, restricts literals to 0 and 1. -/
def literals01 (c : Circuit) : Prop :=
  (∀ g ∈ c.gates, gateLiteral01 g) ∧ ∀ w ∈ c.outputs, wireLiteral01 w

/-- Exact integer evaluation; the singleton-output and validity conditions belong to the language. -/
def integerValue (c : Circuit) : ℤ := (c.eval ([] : List ℤ)).headD 0

/-- Reject malformed encodings, variables, forward references, nonsingleton outputs,
non-0/1 literals, and nonpositive outputs. No bound on the output magnitude is imposed. -/
def posSLP (bs : List Bool) : Prop :=
  ∃ c : Circuit, decodeCircuit bs = some c ∧ c.valid 0 1 ∧ literals01 c ∧
    0 < integerValue c

/-- Polynomial semantics in any finite number r of indeterminates. -/
noncomputable def polynomialValue (r : ℕ) (c : Circuit) : MvPolynomial (Fin r) ℤ :=
  (c.eval (List.ofFn fun i : Fin r => MvPolynomial.X i)).headD 0

/-- Binary tuple: r, circuit, D, the r exponent coordinates in order, m.
This is independent of the degree or coefficient of the polynomial computed. -/
def encodeCoefficientQuery (r : ℕ) (c : Circuit) (D : ℕ) (k : Fin r → ℕ)
    (m : ℕ) : List Bool :=
  encodeNat r ++ encodeCircuit c ++ encodeNat D ++
    (List.ofFn k).flatMap encodeNat ++ encodeNat m

/-- Parsed syntactic data. The list k is checked for length, not against semantic degrees. -/
structure CoefficientQuery where
  variableCount : ℕ
  circuit : Circuit
  degreeBound : ℕ
  exponents : List ℕ
  modulus : ℕ

def decodeCoefficientQuery (bs : List Bool) : Option CoefficientQuery := do
  let (r, rest) ← parseNat bs
  let (c, rest) ← parseCircuit rest
  let (D, rest) ← parseNat rest
  let (k, rest) ← parseMany parseNat r rest
  let (m, tail) ← parseNat rest
  if tail = [] then some ⟨r, c, D, k, m⟩ else none

end PosSLPBounds.Deterministic


