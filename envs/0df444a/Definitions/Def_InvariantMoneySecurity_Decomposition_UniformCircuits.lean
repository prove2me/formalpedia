-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_UniformCircuits
-- name    : InvariantMoneySecurity_Decomposition_UniformCircuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:47.36264+00:00
-- url     : https://prove2.me/theorems/eed31b48-77ef-41a7-afab-9cc55f549a0f
-- title:
--   Uniform quantum algorithms with quantum inputs and discarded workspace
-- statement:
--   A circuit is a finite chronological list of unitary gates, each acting on at most three named qubits. It specifies its full wire count, injective input and retained-output wire maps, and each local matrix. Other wires start at zero and are discarded on output. Arbitrary mixed inputs and entangled retained outputs are supported. The resulting channel is
--   $$\rho\longmapsto\operatorname{Tr}_{\mathrm{garbage}}\bigl(U V\rho V^*U^*\bigr),$$
--   where $V$ inserts clean ancillas and $U$ is the ordered product of the placed gates.
--
--   A uniform quantum polynomial-time family has a polynomial bound on its wire and gate counts. A polynomial-time multi-stack Turing machine generates a structural description which the supplied terminating parser decodes to the family's complete circuit shape. Another polynomial-time machine supplies every real and imaginary local matrix entry as a signed binary dyadic approximation of error at most $2^{-t}$ on the unary request $(1^n,1^t)$. Neither arbitrary global unitaries nor numerical advice are free instructions.
--
--   Classical randomness, measurements, and classical control are represented by coherent records and final partial trace. Uniform preparation of a pure target $v_n$ allows negligible infidelity, rather than demanding exact finite-gate preparation:
--   $$1-\langle v_n|\rho_n|v_n\rangle\le\mu(n),\qquad \mu=\operatorname{negl}.$$
--   For pure targets this is equivalent to negligible trace-distance error. The effective local-gate convention and deferred measurements give the usual QPT model up to negligible approximation, including all subsequent quantum computation after a measured input. The module is reusable independently of invariant money.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), pp. 6–7, §2 and Definition 2.1(i); pp. 13–14, Definition 3.10

import Definitions.Def_InvariantMoneySecurity_Decomposition_QuantumModel
import Definitions.Def_QAlgorithms_ClassicalStringComputability
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition

/-- Length-delimited binary strings. Every field, including an empty one, has its own length. -/
def codeBits (b : List Bool) : List Bool := List.replicate b.length true ++ [false] ++ b

/-- Unary structural fields are polynomial in the width and gate count. -/
def codeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Signed binary integers: numerical precision is charged in bits, not unary magnitude. -/
def codeInt (z : ℤ) : List Bool :=
  [decide (z < 0)] ++ codeBits ((Nat.digits 2 z.natAbs).map fun d => d == 1)

/-- A local, at most three-qubit gate. The matrix is tied to effectively computed entries below. -/
structure LocalGate (w : ℕ) where
  arity : ℕ
  arity_le : arity ≤ 3
  wires : Fin arity ↪ Fin w
  matrix : Matrix (Bits arity) (Bits arity) ℂ
  unitary : matrix.conjTranspose * matrix = 1

/-- Embed a local gate, keeping every wire outside its support unchanged. -/
def LocalGate.operator {w : ℕ} (g : LocalGate w) : Matrix (Bits w) (Bits w) ℂ :=
  fun a b => if (∀ j, j ∉ Set.range g.wires → a j = b j)
    then g.matrix (a ∘ g.wires) (b ∘ g.wires) else 0

/-- All wire positions are included in the structural serialization. -/
def LocalGate.code {w : ℕ} (g : LocalGate w) : List Bool :=
  codeNat g.arity ++ (List.ofFn fun j => codeNat (g.wires j).val).flatten

/-- Numerical data in one fixed enumeration of the at most 8 × 8 basis pairs, real part then
imaginary part of each matrix entry. -/
def LocalGate.entries {w : ℕ} (g : LocalGate w) : List ℝ :=
  (Finset.univ.toList.flatMap fun a => Finset.univ.toList.flatMap fun b =>
    [(g.matrix a b).re, (g.matrix a b).im])

/-- A serial circuit with named input and retained output wires. Other output wires are discarded. -/
structure Circuit (i o : ℕ) where
  width : ℕ
  inputWire : Fin i ↪ Fin width
  outputWire : Fin o ↪ Fin width
  gates : List (LocalGate width)

/-- Gates are in chronological order; a later gate multiplies on the left. -/
def Circuit.operator {i o : ℕ} (C : Circuit i o) : Matrix (Bits C.width) (Bits C.width) ℂ :=
  C.gates.foldl (fun U g => g.operator * U) 1

/-- Clean ancilla initialization is an actual basis embedding. -/
def Circuit.initializer {i o : ℕ} (C : Circuit i o) : Matrix (Bits C.width) (Bits i) ℂ :=
  fun a b => if (a ∘ C.inputWire = b ∧
    ∀ j, j ∉ Set.range C.inputWire → a j = false) then 1 else 0

/-- Density execution followed by partial trace. Entanglement across retained wires is preserved. -/
def Circuit.run {i o : ℕ} (C : Circuit i o)
    (ρ : Matrix (Bits i) (Bits i) ℂ) : Matrix (Bits o) (Bits o) ℂ :=
  let U := C.operator
  let V := C.initializer
  let σ := U * (V * ρ * V.conjTranspose) * U.conjTranspose
  fun x y => ∑ a, ∑ b,
    if (a ∘ C.outputWire = x ∧ b ∘ C.outputWire = y ∧
      ∀ j, j ∉ Set.range C.outputWire → a j = b j) then σ a b else 0

/-- Full structural code; length-delimited gate codes prevent concatenation collisions. -/
def Circuit.code {i o : ℕ} (C : Circuit i o) : List Bool :=
  codeNat i ++ codeNat o ++ codeNat C.width ++
  (List.ofFn fun j => codeNat (C.inputWire j).val).flatten ++
  (List.ofFn fun j => codeNat (C.outputWire j).val).flatten ++
  codeNat C.gates.length ++ (C.gates.map fun g => codeBits g.code).flatten

/-- A terminating parser for a unary-delimited natural number. -/
def readNat : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: bs => some (0, bs)
  | true :: bs => do
      let (n, tail) ← readNat bs
      return (n + 1, tail)

/-- Read exactly k unary-delimited naturals. -/
def readNats : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, bs => some ([], bs)
  | k + 1, bs => do
      let (n, tail) ← readNat bs
      let (ns, rest) ← readNats k tail
      return (n :: ns, rest)

/-- A length-delimited binary field, rejecting truncation. -/
def readBits (bs : List Bool) : Option (List Bool × List Bool) := do
  let (k, tail) ← readNat bs
  if k ≤ tail.length then return (tail.take k, tail.drop k) else none

/-- Each gate code states its arity and every wire; trailing junk rejects. -/
def readGates : ℕ → List Bool → Option (List (ℕ × List ℕ) × List Bool)
  | 0, bs => some ([], bs)
  | k + 1, bs => do
      let (field, tail) ← readBits bs
      let (a, wires) ← readNat field
      let (js, rest) ← readNats a wires
      if rest ≠ [] then none else do
        let (gs, final) ← readGates k tail
        return ((a, js) :: gs, final)

/-- Complete finite circuit structure, before numerical matrix entries. -/
abbrev CircuitShape := ℕ × ℕ × ℕ × List ℕ × List ℕ × List (ℕ × List ℕ)

/-- Recoverable metadata: no gate, wire or allocated register is omitted. -/
def Circuit.shape {i o : ℕ} (C : Circuit i o) : CircuitShape :=
  (i, o, C.width, List.ofFn (fun j => (C.inputWire j).val),
    List.ofFn (fun j => (C.outputWire j).val),
    C.gates.map fun g => (g.arity, List.ofFn fun j => (g.wires j).val))

/-- Actual finite parser, rejecting malformed codes and trailing data. -/
def readCircuit (bs : List Bool) : Option CircuitShape := do
  let (i, s1) ← readNat bs
  let (o, s2) ← readNat s1
  let (w, s3) ← readNat s2
  let (iw, s4) ← readNats i s3
  let (ow, s5) ← readNats o s4
  let (k, s6) ← readNat s5
  let (gs, s7) ← readGates k s6
  if s7 = [] then return (i, o, w, iw, ow, gs) else none

/-- Only local matrices are described numerically; no dense global unitary is a free gate. -/
def Circuit.entries {i o : ℕ} (C : Circuit i o) : List ℝ :=
  C.gates.flatMap LocalGate.entries

/-- Uniform QPT as concrete circuits plus genuine polynomial-time Turing generators.
The precision request is unary, and each dyadic numerator has a binary code.
Measurements, classical randomness and adaptation use coherent records, discarded on output.
No reduction, composition principle or success probability is a structure field. -/
structure QPT (i o : ℕ → ℕ) where
  circuit : ∀ n, Circuit (i n) (o n)
  bound : ∃ q : Polynomial ℕ, ∀ n,
    (circuit n).width ≤ q.eval n ∧ (circuit n).gates.length ≤ q.eval n
  uniform : ∃ f : List Bool → List Bool,
    QAlgorithms.Complexity.PolyTimeComputable f ∧
    ∀ n, readCircuit (f (codeNat n)) = some (circuit n).shape
  effective : ∃ (z : ℕ → ℕ → List ℤ) (f : List Bool → List Bool),
    QAlgorithms.Complexity.PolyTimeComputable f ∧
    (∀ n t, f (codeNat n ++ codeNat t) = (z n t |>.map codeInt).flatten) ∧
    ∀ n t, List.Forall₂
      (fun a r => |(a : ℝ) / (2 : ℝ) ^ t - r| ≤ (2 : ℝ)⁻¹ ^ t)
      (z n t) (circuit n).entries

/-- Execute the actual uniform circuit, retaining all designated quantum outputs. -/
def QPT.run {i o : ℕ → ℕ} (A : QPT i o) (n : ℕ) := (A.circuit n).run

/-- Little-endian concatenation of qubit registers. -/
def appendBits {a b : ℕ} (x : Bits a) (y : Bits b) : Bits (a + b) :=
  Fin.addCases x y

/-- Density input with a public classical prefix and an arbitrary quantum suffix. -/
def classicalQuantumInput {a b : ℕ} (p : Bits a) (ρ : Matrix (Bits b) (Bits b) ℂ) :
    Matrix (Bits (a + b)) (Bits (a + b)) ℂ :=
  fun x y => if ((fun j => x (Fin.castAdd b j)) = p ∧
    (fun j => y (Fin.castAdd b j)) = p)
    then ρ (fun j => x (Fin.natAdd a j)) (fun j => y (Fin.natAdd a j)) else 0

/-- A pure target is efficiently prepared up to negligible infidelity.
For pure targets this is equivalent to negligible trace distance; square roots of
nonnegative negligible errors remain negligible. No exact finite-gate preparation is required. -/
def Prepares (o : ℕ → ℕ) (v : ∀ n, Bits (o n) → ℂ) : Prop :=
  ∃ A : QPT (fun _ => 0) o, ∃ μ : ℕ → ℝ, Negligible μ ∧ (∀ n, 0 ≤ μ n) ∧
    ∀ n, 1 - born (ketbra (v n)) (A.run n (1 : Matrix (Bits 0) (Bits 0) ℂ)) ≤ μ n

end InvariantMoneySecurity.Decomposition


