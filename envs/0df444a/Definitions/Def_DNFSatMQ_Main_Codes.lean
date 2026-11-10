-- Prove2me | Definitions.Def_DNFSatMQ_Main_Codes
-- name    : DNFSatMQ_Main_Codes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:32:17.400999+00:00
-- url     : https://prove2.me/theorems/9cfbd0cb-7646-4b39-800f-fcd9ee382cc0
-- title:
--   Bit codes: polynomial expressions (PTFs) and their size, bounded-fan-in circuits, lists of conjunctions, sparse coefficient vectors
-- statement:
--   How the objects a program writes on its output tape are read back.
--
--   **Numbers.** A natural number is written in a self-delimiting code (each bit $b$ as $1b$, then a terminating $0$, bits little-endian); a rational $\pm a/b$ as a sign bit followed by $a$ and $b$.
--
--   **Polynomial expressions** (p. 2, after Theorem 1.2). `PolyExpr n` is the type of expression trees over the variables $x_0,\dots,x_{n-1}$ built from variables, rational constants, $+$, $-$ and $\times$ ("stored in factored form"). Its value at $x\in\{0,1\}^n$ is computed with $x_i \in \{0,1\}$. Its **size** is the number of nodes plus the bit lengths of every variable index and of the numerator and denominator of every constant; this is "the length of a polynomial expression", not the number of monomials. A PTF is $h(x) = \mathbf 1\{p(x) \ge 0\}$; `ptfSet p` $= h^{-1}(1)$. `decodePolyExpr n y` reads the expression written at the start of the word $y$ (3-bit node tags, then the operands).
--
--   **Circuits** (§4, p. 10). A bounded-fan-in evaluation circuit is a list of gates (input, constant, NOT, AND, OR), each reading earlier gates; its value is the last gate's, and $\mathrm{size}(h)$ is the number of gates. `decodeCircuit` rejects circuits whose gates read later gates.
--
--   **Densifier output.** `decodeConjList n y` reads a number $m$ and then $m$ conjunctions on $2n$ bits each.
--
--   **Sparse vectors** (Theorem 9.1). `decodeSparse d y` reads a list of entries $(A, v)$ ($A \subseteq [d]$ as $d$ indicator bits, $v$ rational); `sparseVec` is the vector it represents (first entry for $A$, else $0$), and `l0Norm` is $\|v\|_0$, the number of nonzero entries.
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Theorem 1.2 and the definition of PTF size, p. 2 (PDF 3); §4 p. 10 (PDF 11) for circuits

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Basic

namespace DNFSatMQ.Main

/-! Bit codes for the objects a program writes on its output tape. Every decoder reads a prefix
of a bit string and returns the object together with the unread rest. -/

/-- The value of a little-endian list of bits. -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsVal bs

/-- Self-delimiting natural-number code: each bit `b` is written as `true, b`, and `false` ends the
number. Returns the bits read and the rest. -/
def decodeNatBits : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => (decodeNatBits rest).map fun p => (b :: p.1, p.2)
  | _ => none

/-- Decode a natural number (self-delimiting code, little-endian bits). -/
def decodeNat (y : List Bool) : Option (ℕ × List Bool) :=
  (decodeNatBits y).map fun p => (bitsVal p.1, p.2)

/-- Decode a rational number `± a / b`: a sign bit (`true` = negative), then `a`, then `b`
(`b = 0` gives the value `0`). -/
def decodeRat : List Bool → Option (ℚ × List Bool)
  | [] => none
  | sgn :: rest => do
      let (a, r1) ← decodeNat rest
      let (b, r2) ← decodeNat r1
      some ((if sgn then -1 else 1) * ((a : ℚ) / (b : ℚ)), r2)

/-! ## Polynomial expressions and PTFs (p. 2, after Theorem 1.2) -/

/-- A **polynomial expression** over the variables `x_0, …, x_{n-1}`: variables, rational
constants, sums, differences and products, stored as a tree (factored form, not expanded into
monomials). -/
inductive PolyExpr (n : ℕ) : Type
  | var (i : Fin n)
  | const (q : ℚ)
  | add (a b : PolyExpr n)
  | sub (a b : PolyExpr n)
  | mul (a b : PolyExpr n)

/-- The real value of a polynomial expression at `x ∈ {0,1}ⁿ` (`true ↦ 1`, `false ↦ 0`). -/
def PolyExpr.eval {n : ℕ} : PolyExpr n → Pt n → ℝ
  | .var i, x => bval (x i)
  | .const q, _ => (q : ℝ)
  | .add a b, x => a.eval x + b.eval x
  | .sub a b, x => a.eval x - b.eval x
  | .mul a b, x => a.eval x * b.eval x

/-- The **size** (length) of a polynomial expression: one per node, plus the bit length of every
variable index and of the numerator and denominator of every constant. -/
def PolyExpr.size {n : ℕ} : PolyExpr n → ℕ
  | .var i => 1 + (i : ℕ).size
  | .const q => 1 + q.num.natAbs.size + q.den.size
  | .add a b => 1 + a.size + b.size
  | .sub a b => 1 + a.size + b.size
  | .mul a b => 1 + a.size + b.size

/-- Prefix decoder of polynomial expressions (with a fuel bound on the recursion depth). Tags:
`000` variable (then its index), `001` constant (then a rational), `010` sum, `011` difference,
`100` product (then the two operands). -/
def decodeExprAux (n : ℕ) : ℕ → List Bool → Option (PolyExpr n × List Bool)
  | 0, _ => none
  | _ + 1, false :: false :: false :: r => do
      let (i, r') ← decodeNat r
      if h : i < n then some (.var ⟨i, h⟩, r') else none
  | _ + 1, false :: false :: true :: r => do
      let (q, r') ← decodeRat r
      some (.const q, r')
  | k + 1, false :: true :: false :: r => do
      let (a, r1) ← decodeExprAux n k r
      let (b, r2) ← decodeExprAux n k r1
      some (.add a b, r2)
  | k + 1, false :: true :: true :: r => do
      let (a, r1) ← decodeExprAux n k r
      let (b, r2) ← decodeExprAux n k r1
      some (.sub a b, r2)
  | k + 1, true :: false :: false :: r => do
      let (a, r1) ← decodeExprAux n k r
      let (b, r2) ← decodeExprAux n k r1
      some (.mul a b, r2)
  | _ + 1, _ => none

/-- The polynomial expression written at the start of the word `y` (the rest of `y` is free for
other data), if any. Every node uses at least three bits, so the fuel `y.length` never runs out
on a well-formed code. -/
def decodePolyExpr (n : ℕ) (y : List Bool) : Option (PolyExpr n) :=
  (decodeExprAux n y.length y).map Prod.fst

/-- The satisfying set `H = h⁻¹(1)` of the PTF `h(x) = 1{p(x) ≥ 0}` of a polynomial expression. -/
noncomputable def ptfSet {n : ℕ} (p : PolyExpr n) : Finset (Pt n) :=
  Finset.univ.filter fun x => 0 ≤ p.eval x

/-! ## Bounded-fan-in evaluation circuits (§4, p. 10) -/

/-- A gate of a bounded-fan-in Boolean circuit on `n` inputs: an input gate, a constant, or a
NOT / AND / OR gate whose arguments are earlier gates (by position). -/
inductive Gate (n : ℕ) : Type
  | input (i : Fin n)
  | const (b : Bool)
  | not (j : ℕ)
  | and (j k : ℕ)
  | or (j k : ℕ)

/-- A circuit is its list of gates in topological order; its output is the last gate. -/
abbrev Circuit (n : ℕ) : Type := List (Gate n)

/-- Every argument of the gate refers to a gate before position `p`. -/
def Gate.refsBelow {n : ℕ} (p : ℕ) : Gate n → Bool
  | .input _ => true
  | .const _ => true
  | .not j => decide (j < p)
  | .and j k => decide (j < p) && decide (k < p)
  | .or j k => decide (j < p) && decide (k < p)

/-- The circuit is well formed: each gate reads only earlier gates. -/
def Circuit.wf {n : ℕ} (C : Circuit n) : Bool :=
  (List.range C.length).all fun p => match C[p]? with
    | some g => g.refsBelow p
    | none => true

/-- The value of one gate given the values of the earlier gates. -/
def Gate.value {n : ℕ} (vals : List Bool) (x : Pt n) : Gate n → Bool
  | .input i => x i
  | .const b => b
  | .not j => !(vals.getD j false)
  | .and j k => vals.getD j false && vals.getD k false
  | .or j k => vals.getD j false || vals.getD k false

/-- The values of all gates on input `x`. -/
def Circuit.values {n : ℕ} (C : Circuit n) (x : Pt n) : List Bool :=
  C.foldl (fun vals g => vals ++ [g.value vals x]) []

/-- The Boolean function computed by the circuit (the last gate; `false` for the empty circuit). -/
def Circuit.eval {n : ℕ} (C : Circuit n) (x : Pt n) : Bool :=
  ((C.values x).getLast?).getD false

/-- `size(h)`: the number of input and Boolean gates. -/
def Circuit.size {n : ℕ} (C : Circuit n) : ℕ := C.length

/-- Decode one gate. Tags: `000` input (index), `001` constant (one bit), `010` NOT, `011` AND,
`100` OR (gate positions as natural numbers). -/
def decodeGate (n : ℕ) : List Bool → Option (Gate n × List Bool)
  | false :: false :: false :: r => do
      let (i, r') ← decodeNat r
      if h : i < n then some (.input ⟨i, h⟩, r') else none
  | false :: false :: true :: b :: r => some (.const b, r)
  | false :: true :: false :: r => do
      let (j, r') ← decodeNat r
      some (.not j, r')
  | false :: true :: true :: r => do
      let (j, r1) ← decodeNat r
      let (k, r2) ← decodeNat r1
      some (.and j k, r2)
  | true :: false :: false :: r => do
      let (j, r1) ← decodeNat r
      let (k, r2) ← decodeNat r1
      some (.or j k, r2)
  | _ => none

/-- Decode `k` gates in a row. -/
def decodeGates (n : ℕ) : ℕ → List Bool → Option (List (Gate n) × List Bool)
  | 0, r => some ([], r)
  | k + 1, r => do
      let (g, r1) ← decodeGate n r
      let (gs, r2) ← decodeGates n k r1
      some (g :: gs, r2)

/-- The circuit written at the start of the word `y`: its number of gates, then the gates. A
circuit that is not well formed is rejected. -/
def decodeCircuit (n : ℕ) (y : List Bool) : Option (Circuit n) := do
  let (k, r) ← decodeNat y
  let (gs, _) ← decodeGates n k r
  if Circuit.wf gs then some gs else none

/-- The satisfying set `H = h⁻¹(1)` of a circuit. -/
def circuitSet {n : ℕ} (C : Circuit n) : Finset (Pt n) :=
  Finset.univ.filter fun x => C.eval x = true

/-! ## Lists of conjunctions (densifier output) -/

/-- Decode one conjunction on `n` variables from `2n` bits: for coordinate `i`, the pair
`(false, _)` means free and `(true, b)` means the literal `x_i = b`. -/
def decodeConj (n : ℕ) (y : List Bool) : Option (Conj n × List Bool) :=
  if 2 * n ≤ y.length then
    some ((fun i => if y.getD (2 * i) false then some (y.getD (2 * i + 1) false) else none),
      y.drop (2 * n))
  else none

/-- Decode `m` conjunctions in a row. -/
def decodeConjs (n : ℕ) : ℕ → List Bool → Option (List (Conj n) × List Bool)
  | 0, r => some ([], r)
  | m + 1, r => do
      let (c, r1) ← decodeConj n r
      let (cs, r2) ← decodeConjs n m r1
      some (c :: cs, r2)

/-- The list of conjunctions written at the start of `y`: its length `m`, then `m` conjunctions. -/
def decodeConjList (n : ℕ) (y : List Bool) : Option (List (Conj n)) := do
  let (m, r) ← decodeNat y
  let (cs, _) ← decodeConjs n m r
  some cs

/-! ## Sparse coefficient vectors (KM output) -/

/-- Decode one entry `(A, v)` of a vector indexed by the subsets of `[d]`: the indicator of `A`
on `d` bits, then the rational value `v`. -/
def decodeEntry (d : ℕ) (y : List Bool) : Option ((Finset (Fin d) × ℚ) × List Bool) :=
  if d ≤ y.length then
    (decodeRat (y.drop d)).map fun p =>
      ((Finset.univ.filter fun i : Fin d => y.getD i false = true, p.1), p.2)
  else none

/-- Decode `k` entries in a row. -/
def decodeEntries (d : ℕ) : ℕ → List Bool → Option (List (Finset (Fin d) × ℚ) × List Bool)
  | 0, r => some ([], r)
  | k + 1, r => do
      let (e, r1) ← decodeEntry d r
      let (es, r2) ← decodeEntries d k r1
      some (e :: es, r2)

/-- A vector `ṽ` indexed by the subsets of `[d]`, "represented by its nonzero entries", written at
the start of `y`: the number of entries, then the entries. -/
def decodeSparse (d : ℕ) (y : List Bool) : Option (List (Finset (Fin d) × ℚ)) := do
  let (k, r) ← decodeNat y
  let (es, _) ← decodeEntries d k r
  some es

/-- The vector given by a list of entries: `ṽ(A)` is the value of the first entry for `A`, and `0`
if there is none. -/
def sparseVec {d : ℕ} (es : List (Finset (Fin d) × ℚ)) (A : Finset (Fin d)) : ℝ :=
  match es.find? (fun e => decide (e.1 = A)) with
  | some e => (e.2 : ℝ)
  | none => 0

/-- `‖v‖₀`, the number of nonzero entries of a vector indexed by the subsets of `[d]`. -/
noncomputable def l0Norm {d : ℕ} (v : Finset (Fin d) → ℝ) : ℕ :=
  (Finset.univ.filter fun A => v A ≠ 0).card

end DNFSatMQ.Main


