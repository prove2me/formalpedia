-- Prove2me | Definitions.Def_QAlgorithms_Defs_LearningSeparation
-- name    : QAlgorithms_Defs_LearningSeparation
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:52:16.658996+00:00
-- url     : https://prove2.me/theorems/7690ba7f-9507-4103-80ba-878eebcbd56b
-- title:
--   Efficient classical and quantum PAC and exact learnability, Blum-integer factoring hardness
-- statement:
--   # Efficient classical and quantum PAC and exact learnability, Blum-integer factoring hardness
--   (shared definition layer)
--
--   R. A. Servedio, S. J. Gortler, *Quantum versus classical learnability* (arXiv:quant-ph/0007036v1),
--   cited "SG p.N" (PDF pages), §§2–5.
--
--   Conventions. A concept on `n` bits is `c : Qubits n → Bool`; a concept class is a family
--   `C : (n : ℕ) → Set (Qubits n → Bool)`. Accuracy and confidence `ε, δ ∈ (0, 1)` enter as
--   `ε = 1/a`, `δ = 1/b` with integers `a, b ≥ 2` (every `ε, δ ∈ (0, 1)` lies above some such value, and
--   "polynomial in `1/ε, 1/δ`" is "polynomial in `a, b`"). Classical machines are the frozen
--   `Complexity.PolyTimeComputable` (Turing `FinTM2`) and `Stabilizer.RandPolyTimeSampler`; quantum
--   networks are frozen circuits over the standard basis `{H, T, CNOT}` (`htcxGateSet`). A learner's
--   hypothesis is a Boolean circuit (frozen `BoolCircuit`), output as a bit string.
--   -/
--
--   namespace QAlgorithms.Learning
--
--   open QAlgorithms.Complexity
--
--   /-- SG §5 (p.11): the Blum integers `N = pq` with `p ≠ q` `ℓ`-bit primes (`2^{ℓ−1} ≤ p < 2^ℓ`),
--   both congruent to `3` modulo `4`.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\LearningSeparation.lean

import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
/-!
# Efficient classical and quantum PAC and exact learnability, Blum-integer factoring hardness
(shared definition layer)

R. A. Servedio, S. J. Gortler, *Quantum versus classical learnability* (arXiv:quant-ph/0007036v1),
cited "SG p.N" (PDF pages), §§2–5.

Conventions. A concept on `n` bits is `c : Qubits n → Bool`; a concept class is a family
`C : (n : ℕ) → Set (Qubits n → Bool)`. Accuracy and confidence `ε, δ ∈ (0, 1)` enter as
`ε = 1/a`, `δ = 1/b` with integers `a, b ≥ 2` (every `ε, δ ∈ (0, 1)` lies above some such value, and
"polynomial in `1/ε, 1/δ`" is "polynomial in `a, b`"). Classical machines are the frozen
`Complexity.PolyTimeComputable` (Turing `FinTM2`) and `Stabilizer.RandPolyTimeSampler`; quantum
networks are frozen circuits over the standard basis `{H, T, CNOT}` (`htcxGateSet`). A learner's
hypothesis is a Boolean circuit (frozen `BoolCircuit`), output as a bit string.
-/

namespace QAlgorithms.Learning

open QAlgorithms.Complexity

/-- SG §5 (p.11): the Blum integers `N = pq` with `p ≠ q` `ℓ`-bit primes (`2^{ℓ−1} ≤ p < 2^ℓ`),
both congruent to `3` modulo `4`. -/
def blumIntegers (ℓ : ℕ) : Finset ℕ :=
  (((Finset.range (2 ^ ℓ)) ×ˢ (Finset.range (2 ^ ℓ))).filter fun pq =>
    pq.1 ≠ pq.2 ∧ pq.1.Prime ∧ pq.2.Prime ∧ 2 ^ (ℓ - 1) ≤ pq.1 ∧ 2 ^ (ℓ - 1) ≤ pq.2 ∧
      pq.1 % 4 = 3 ∧ pq.2 % 4 = 3).image fun pq => pq.1 * pq.2

/-- SG §5 (p.11): the probability that the randomized polynomial-time algorithm `A`, run on the
binary encoding of a uniformly random Blum integer `N` with `ℓ`-bit factors, outputs the encoding of
a nontrivial divisor of `N` (for a Blum integer: `p` or `q`). `0` when there is no such integer. -/
noncomputable def factorBlumSuccess (A : Stabilizer.RandPolyTimeSampler) (ℓ : ℕ) : ℝ :=
  ((blumIntegers ℓ).card : ℝ)⁻¹ * ∑ N ∈ blumIntegers ℓ,
    ((A.outDist (LocalHamiltonian.encBin N)).toOuterMeasure
      {s | ∃ d, 1 < d ∧ d < N ∧ d ∣ N ∧ s = LocalHamiltonian.encBin d}).toReal

/-- SG §5 (p.11) and Observations 17–18 (p.12): no polynomial-time classical (randomized) algorithm
factors a randomly selected Blum integer with non-negligible success probability: for every such
algorithm `A` and every polynomial `q`, the success probability is eventually below
`1 / (q(ℓ) + 1)`. -/
def FactoringBlumHard : Prop :=
  ∀ (A : Stabilizer.RandPolyTimeSampler) (q : Polynomial ℕ), ∃ ℓ0 : ℕ, ∀ ℓ ≥ ℓ0,
    factorBlumSuccess A ℓ < 1 / (((q.eval ℓ : ℕ) : ℝ) + 1)

/-- The opcode of a Boolean gate (`and`, `or`, `not` = 0, 1, 2). -/
def boolOpCode : BoolOp → ℕ
  | .and => 0
  | .or => 1
  | .not => 2

/-- The representation of a Boolean circuit `h` as a bit string (SG §2.1, p.3; §2.2, p.4): the
number of gates, each gate's opcode and argument wires, and the output wire, all in the frozen
self-delimiting unary code `encNat`. -/
def encBoolCircuit {n : ℕ} (C : BoolCircuit n 1) : Str :=
  encNat C.gates.length ++
    (C.gates.map fun g => encNat (boolOpCode g.op) ++ encNat g.a ++ encNat g.b).flatten ++
    encNat (C.outputs 0)

/-- The output string `s` begins with the representation of a well-formed Boolean circuit whose
function satisfies `P` (SG §2.1, p.3; §4.1, p.10). An undecodable output satisfies no `P`. -/
def OutputsCircuitWith {n : ℕ} (s : Str) (P : (Qubits n → Bool) → Prop) : Prop :=
  ∃ C : BoolCircuit n 1, C.WellFormed ∧ encBoolCircuit C <+: s ∧ P fun x => C.eval x 0

/-- The quantum membership query `QMQ_c : |x, b⟩ ↦ |x, b ⊕ c(x)⟩` (SG §3.1, p.5) on `n + 1` qubits,
the label qubit last: the frozen `xorOracle c` on a qubit register. -/
def qmqOracle {n : ℕ} (c : Qubits n → Bool) : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ :=
  Matrix.of fun y z =>
    if Fin.init y = Fin.init z ∧ y (Fin.last n) = xor (z (Fin.last n)) (c (Fin.init z)) then 1
    else 0

/-- The input of a QEX network (SG §4.1, p.10): `T` copies of the example state `ψ` (block `t` is
wires `t(n+1), …, t(n+1) + n`, the label last), i.e. the `T` QEX gates at the bottom of the
circuit, followed by `w` ancillas in `|0⟩`. -/
noncomputable def qexInputState {n : ℕ} (T w : ℕ) (ψ : EuclideanSpace ℂ (Qubits n × Bool)) :
    EuclideanSpace ℂ (Qubits (T * (n + 1) + w)) :=
  WithLp.toLp 2 fun z =>
    if ∀ k : Fin w, z (Fin.natAdd (T * (n + 1)) k) = false then
      ∏ t : Fin T, ψ (fun j => z (Fin.castAdd w (finProdFinEquiv (t, Fin.castSucc j))),
        z (Fin.castAdd w (finProdFinEquiv (t, Fin.last n))))
    else 0

/-- The input of a classical PAC learner (SG §2.2, p.4): `n`, `a = 1/ε`, `b = 1/δ` in unary,
followed by the labelled examples. -/
def pacSampleEnc (n a b : ℕ) (xs : List (Qubits n × Bool)) : Str :=
  encNat n ++ encNat a ++ encNat b ++ (xs.map fun e => List.ofFn e.1 ++ [e.2]).flatten

/-- SG §4.1 (p.10) and §2.3 (p.4): `C` is efficiently quantum PAC learnable: there is a polynomial
`p` such that for all `n ≥ 1` and `ε = 1/a`, `δ = 1/b` there is a QEX network over `{H, T, CNOT}`
with `T` QEX gates and at most `p(n + a + b)` gates in all, which, for every `c ∈ C_n` and every
distribution `D`, outputs with probability `≥ 1 − δ` a circuit `h` with `error_D(h, c) ≤ ε`. The
network depends on `(n, a, b)` only. -/
def EffQuantumPACLearnable (C : (n : ℕ) → Set (Qubits n → Bool)) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n ≥ 1, ∀ a ≥ 2, ∀ b ≥ 2,
    ∃ (T w k : ℕ) (circ : Circuit htcxGateSet (T * (n + 1) + w))
      (outW : Fin k → Fin (T * (n + 1) + w)),
      T + circ.size ≤ p.eval (n + a + b) ∧
      -- the output is read from the network's own register: one wire per output bit, and a
      -- polynomial workspace, so the hypothesis' length is bounded by the network's size (SG p.10)
      w ≤ p.eval (n + a + b) ∧ Function.Injective outW ∧
      ∀ c ∈ C n, ∀ D : Qubits n → ℝ, IsDistribution D →
        (open Classical in
          probEvent (act circ.unitary (qexInputState T w (exampleState c D)))
            (fun z => OutputsCircuitWith (List.ofFn fun i => z (outW i))
              fun h => pacError D c h ≤ 1 / (a : ℝ))) ≥ 1 - 1 / (b : ℝ)

/-- SG §2.2 (p.4): `C` is efficiently (classically) PAC learnable: one randomized polynomial-time
algorithm `A` which, given `n, 1/ε, 1/δ` and `p(n + 1/ε + 1/δ)` i.i.d. examples of `c ∈ C_n` under
any distribution `D`, outputs with probability `≥ 1 − δ` a circuit `h` with `error_D(h, c) ≤ ε`. -/
def EffClassicalPACLearnable (C : (n : ℕ) → Set (Qubits n → Bool)) : Prop :=
  ∃ (p : Polynomial ℕ) (A : Stabilizer.RandPolyTimeSampler), ∀ n ≥ 1, ∀ a ≥ 2, ∀ b ≥ 2,
    ∀ c ∈ C n, ∀ D : Qubits n → ℝ, IsDistribution D →
      ∑ xs : Fin (p.eval (n + a + b)) → Qubits n, (∏ i, D (xs i)) *
        ((A.outDist (pacSampleEnc n a b (List.ofFn fun i => (xs i, c (xs i))))).toOuterMeasure
          {s | OutputsCircuitWith s fun h => pacError D c h ≤ 1 / (a : ℝ)}).toReal ≥ 1 - 1 / (b : ℝ)

/-- SG §3.1 (p.5): `C` is efficiently quantum exact learnable from membership queries: networks of
a fixed architecture independent of `c`, of size (gates plus QMQ calls) at most `p(n)`, over
`{H, T, CNOT}`, started in `|0…0⟩`, which output a circuit for `c` with probability `≥ 2/3`. -/
def EffQuantumExactLearnable (C : (n : ℕ) → Set (Qubits n → Bool)) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n ≥ 1,
    ∃ (N k : ℕ) (circ : OracleCircuit htcxGateSet (fun _ : Fin 1 => n + 1) N) (outW : Fin k → Fin N),
      circ.length ≤ p.eval n ∧
      -- one wire per output bit and polynomially many wires (SG p.5: a network of poly(n) size)
      N ≤ p.eval n ∧ Function.Injective outW ∧
      ∀ c ∈ C n,
        (open Classical in
          probEvent (act (circ.unitary fun _ => qmqOracle c) (zeroKet N))
            (fun z => OutputsCircuitWith (List.ofFn fun i => z (outW i)) fun h => h = c)) ≥ 2 / 3

/-- A classical membership-query learner run against `MQ_c` (SG §2.1, p.3): the next-step function
`g` sees `n`, the random bits `r` and the query history; it either asks the query `x` (output
`true` followed by the bits of `x`) or halts with an output (`false` followed by the output). At
most `k` rounds; running out of rounds is failure (`none`). -/
def mqRun (g : Str → Str) (n : ℕ) (r : List Bool) (c : Qubits n → Bool) :
    ℕ → List (Qubits n × Bool) → Option Str
  | 0, _ => none
  | k + 1, hist =>
      match g (encNat n ++ Stabilizer.encBits r ++
          Stabilizer.encBits (hist.flatMap fun e => List.ofFn e.1 ++ [e.2])) with
      | true :: rest =>
          mqRun g n r c k (hist ++ [((fun i : Fin n => rest.getD (i : ℕ) false),
            c (fun i : Fin n => rest.getD (i : ℕ) false))])
      | false :: rest => some rest
      | [] => none

/-- SG §2.1 (p.3): `C` is efficiently (classically) exact learnable from membership queries: a
probabilistic polynomial-time learner (next-step function `g` polynomial-time, at most `p(n)`
rounds, `rb(n)` random bits) which, for every `c ∈ C_n`, outputs a circuit for `c` with
probability `≥ 2/3` over its random bits. -/
def EffClassicalExactLearnable (C : (n : ℕ) → Set (Qubits n → Bool)) : Prop :=
  ∃ (p rb : Polynomial ℕ) (g : Str → Str), PolyTimeComputable g ∧ ∀ n ≥ 1, ∀ c ∈ C n,
    (open Classical in
      ((2 : ℝ) ^ rb.eval n)⁻¹ * ((Finset.univ.filter fun r : Fin (rb.eval n) → Bool =>
        ∃ s, mqRun g n (List.ofFn r) c (p.eval n) [] = some s ∧
          OutputsCircuitWith s fun h => h = c).card : ℝ)) ≥ 2 / 3

/-! ### Sanity tests -/

example : blumIntegers 0 = ∅ := by decide

example {n : ℕ} (c : Qubits n → Bool) (x : Qubits n) (b : Bool) :
    qmqOracle c (Fin.snoc x (xor b (c x))) (Fin.snoc x b) = 1 := by
  simp [qmqOracle, Fin.init_snoc]

example {n : ℕ} (x : Qubits n) (b : Bool) :
    qmqOracle (fun _ : Qubits n => false) (Fin.snoc x b) (Fin.snoc x b) = 1 := by
  simp [qmqOracle, Fin.init_snoc]

example (g : Str → Str) (n : ℕ) (r : List Bool) (c : Qubits n → Bool) :
    mqRun g n r c 0 [] = none := rfl

example (n : ℕ) (r : List Bool) (c : Qubits n → Bool) :
    mqRun (fun _ => [false, true]) n r c 1 [] = some [true] := rfl

example (A : Stabilizer.RandPolyTimeSampler) : factorBlumSuccess A 0 = 0 := by
  simp [factorBlumSuccess, show blumIntegers 0 = ∅ by decide]

end QAlgorithms.Learning


