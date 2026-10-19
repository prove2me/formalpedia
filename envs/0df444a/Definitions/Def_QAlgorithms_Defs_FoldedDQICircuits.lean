-- Prove2me | Definitions.Def_QAlgorithms_Defs_FoldedDQICircuits
-- name    : QAlgorithms_Defs_FoldedDQICircuits
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:37:10.151106+00:00
-- url     : https://prove2.me/theorems/e009faf1-19e0-4764-b4c8-ecd594a29700
-- title:
--   FoldedDQICircuits
-- statement:
--   FoldedDQICircuits
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\FoldedDQICircuits.lean

import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_QAlgorithms_Defs_FoldedDQILayers
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix

namespace QAlgorithms.FoldedDQI

/-- Explicit ideal algorithm register: mask, error labels, syndrome, answer;
2610.02145 pp.39–40. -/
abbrev AlgorithmRegister (F : Type*) (M h K : ℕ) :=
  (Qubits M × (Fin M → Fin h → F)) × ((Fin K → F) × Bool)

/-- Public mask amplitudes prepared by the remaining-ones rotations;
2610.02145 p.39 (A.45)–(A.46). No oracle enters this preparation. -/
def maskAmplitude (M ell : ℕ) (hM : 0 < M) (mask : Qubits M) : ℝ :=
  windowWeights M ell hM (hammingWeight mask)/(Real.sqrt (Nat.choose M (hammingWeight mask)))

/-- The exact per-position remaining-ones rotation, identity off reachable counters;
2610.02145 p.39. -/
def remainingOnesRotation (positions ones : ℕ) : Matrix Bool Bool ℂ :=
  if 0 < positions ∧ ones ≤ positions then
    rotY (2*Real.arccos (Real.sqrt (((positions : ℝ)-ones)/positions)))
  else 1

/-- Known trace-Fourier transform of one error-label register;
2610.02145 p.39 (A.47). -/
def labelFourier {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F] {M h K : ℕ} (i : Fin M) :
    Matrix (AlgorithmRegister F M h K) (AlgorithmRegister F M h K) ℂ :=
  Matrix.of fun p q => if p.1.1 = q.1.1 ∧ p.2 = q.2 ∧
      (∀ j, j ≠ i → p.1.2 j = q.1.2 j)
    then traceFourier h (p.1.2 i) (q.1.2 i) else 0

/-- Answer preparation H CNOT(mask,answer); 2610.02145 p.39, Lemma 7. -/
def predicateAnswerPreparation {F : Type*} [Field F] {M h K : ℕ} (i : Fin M) :
    Matrix (AlgorithmRegister F M h K) (AlgorithmRegister F M h K) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 then
    hadamard p.2.2 (xor q.2.2 (q.1.1 i)) else 0

/-- One ordinary fixed-block XOR query on the full register;
2610.02145 p.13 (2.25), p.39, Lemma 7. -/
def blockQuery {F : Type*} [Field F] [Fintype F] {M h K : ℕ}
    (A : FoldedOPI.BalancedInstance M (Fin h → F)) (i : Fin M) :
    Matrix (AlgorithmRegister F M h K) (AlgorithmRegister F M h K) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 then
    pauliX p.2.2 (xor q.2.2 (decide (q.1.2 i ∈ A.sets i)))
    else 0

/-- Reversible mask erasure by nonzero-label indicator; 2610.02145 p.39. -/
def maskErase {F : Type*} [Field F] {M h K : ℕ} (i : Fin M) :
    Matrix (AlgorithmRegister F M h K) (AlgorithmRegister F M h K) ℂ :=
  Matrix.of fun p q => if p =
    ((Function.update q.1.1 i (xor (q.1.1 i) (decide (q.1.2 i ≠ 0))),q.1.2),q.2)
    then 1 else 0

/-- Source local step: trace QFT, answer preparation, ONE XOR call and answer flip,
unpreparation, inverse trace QFT, mask erasure; 2610.02145 p.39 (A.47).
blockQuery combines the query with the subsequent X on the answer. -/
def localBlockStep {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F] {M h K : ℕ}
    (A : FoldedOPI.BalancedInstance M (Fin h → F)) (i : Fin M) :
    Matrix (AlgorithmRegister F M h K) (AlgorithmRegister F M h K) ℂ :=
  maskErase i * star (labelFourier i) * star (predicateAnswerPreparation i) *
    blockQuery A i * predicateAnswerPreparation i * labelFourier i

/-- Public syndrome computation and compute/copy/uncompute decoder erasure;
2610.02145 p.40 (A.49). Both operations have total reversible behavior. -/
def syndromeAndErase {F : Type*} [Field F] {M h K : ℕ}
    (gamma : F) (decode : (Fin K → F) → (Fin M → Fin h → F)) :
    Matrix (AlgorithmRegister F M h K) (AlgorithmRegister F M h K) ℂ :=
  let H := (OPI.vandermondeEncoder (fun t : Fin (M*h) => gamma^t.val) K).transpose
  let compute := fun q : AlgorithmRegister F M h K =>
    (q.1,(q.2.1+H.mulVec ((FoldedOPI.foldEquiv F M h).symm q.1.2),q.2.2))
  let erase := fun q : AlgorithmRegister F M h K =>
    ((q.1.1,q.1.2-decode q.2.1),q.2)
  Matrix.of fun p q => if p = erase (compute q) then 1 else 0

/-- The actual public scalar-GRS decoder regrouped into blocks;
2610.02145 pp.33–34, Lemma 5. The scalar radius is h*ell. Gaussian elimination,
rescaling and unique-decoder failure behavior come from the shared construction. -/
def publicSyndromeDecoder {F : Type*} [Field F] [Fintype F] {M h K : ℕ}
    (gamma : F) (distinct : Function.Injective (fun t : Fin (M*h) => gamma^t.val))
    (dimensions : K ≤ M*h) (ell : ℕ) (s : Fin K → F) : Fin M → Fin h → F :=
  FoldedOPI.foldEquiv F M h
    (ReedSolomon.uniqueSyndromeDecoder (fun t : Fin (M*h) => gamma^t.val) distinct dimensions (h*ell) s)

/-- Executed ideal construction, retaining all workspace and the answer;
2610.02145 pp.39–40. It is defined from the explicit source steps, not from
the claimed final layer-state identity or an arbitrary output distribution. -/
def idealConstructedState {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F] {M h K : ℕ} (hM : 0 < M)
    (ell : ℕ) (hell : ell ≤ M) (gamma : F)
    (distinct : Function.Injective (fun t : Fin (M*h) => gamma^t.val))
    (dimensions : K ≤ M*h)
    (A : FoldedOPI.BalancedInstance M (Fin h → F)) :
    EuclideanSpace ℂ (AlgorithmRegister F M h K) :=
  let prepared : EuclideanSpace ℂ (AlgorithmRegister F M h K) :=
    WithLp.toLp 2 fun q => if q.1.2 = 0 ∧ q.2 = (0,false)
      then (maskAmplitude M ell hM q.1.1 : ℂ) else 0
  let finalQFT : Matrix (AlgorithmRegister F M h K) (AlgorithmRegister F M h K) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 ∧ p.2.2 = q.2.2
      then star (traceFourier K) p.2.1 q.2.1 else 0
  act (finalQFT * syndromeAndErase gamma (publicSyndromeDecoder gamma distinct dimensions ell) *
    orderedProd (fun i : Fin M => localBlockStep A i)) prepared

/-- A uniform physical fixed-block family with a charged bit constructor;
2610.02145 pp.16,39–40. Queries have static labels and no primitive controls.
Polynomial bounds precede both M and hidden sets, at the fixed rate. -/
structure UniformFixedBlockFamily (R : ℚ) where
  rate_domain : 0 < R ∧ R < 1
  constructor : OPI.BitOracleProgram
  publicOnly : OPI.IsPublicPreprocessor constructor
  qubits : FoldedOPI.PublicDomain → ℕ
  circuit : (P : FoldedOPI.PublicDomain) →
    OracleCircuit htcxGateSet (fun _ : Fin P.M => (P.M+2)*(2*P.u)+1) (qubits P)
  output : (P : FoldedOPI.PublicDomain) →
    Fin (FoldedOPI.publicParameters P 3 * (2*P.u)) ↪ Fin (qubits P)
  serialize : (P : FoldedOPI.PublicDomain) → Complexity.Str
  serialization : ∀ P, serialize P = OPI.serializeWords
    [P.M,P.u,qubits P,(circuit P).length] ++
      ((circuit P).map fun step => match step with
        | .gate g => OPI.serializeWords ([0,
            if g.gate = Gate.ofMatrix1 hadamard then 0
            else if g.gate = Gate.ofMatrix1 gateT then 1 else 2] ++
            List.ofFn fun j => (g.wires j).val)
        | .query i adj control wires _ =>
            OPI.serializeWords ([1,i.val,if adj then 1 else 0,
              (control.map Fin.val).getD (qubits P)] ++ List.ofFn fun j => (wires j).val)).flatten ++
      OPI.serializeWords (List.ofFn fun j => (output P j).val)
  no_control : ∀ P, ∀ step ∈ circuit P, match step with
    | .gate _ => True
    | .query _ _ control _ _ => control = none
  bound : Polynomial ℕ
  generated : ∀ P, P.rate = R →
    ∃ fuel, fuel ≤ bound.eval P.M ∧
      let result := OPI.bitProgramExecution constructor
        (OPI.serializeWords [P.M,P.u] ++ LocalHamiltonian.encRat R)
        (fun _ => false) (fun _ => false) fuel
      result.status = some true ∧ result.output = serialize P ∧
        result.time ≤ bound.eval P.M ∧ result.visited.card ≤ bound.eval P.M
  resources : ∀ P, P.rate = R → qubits P+(circuit P).gateCount ≤ bound.eval P.M

/-- Born output law on the serialized public coefficient wires, discarding all
other registers; 2610.02145 pp.16,39–40. The coefficient decoder uses the same
public field basis as the oracle embedding. Accuracy and query bounds are not
built into this law. -/
def UniformFixedBlockFamily.outputLaw {R : ℚ} (F : UniformFixedBlockFamily R)
    (P : FoldedOPI.PublicDomain) (E : FoldedOPI.PublicFieldData P)
    (_width : E.encoding.e*Nat.clog 2 E.encoding.p = 2*P.u)
    (O : Fin P.M → Matrix (Qubits ((P.M+2)*(2*P.u)+1))
      (Qubits ((P.M+2)*(2*P.u)+1)) ℂ)
    (_hO : ∀ i, O i ∈ Matrix.unitaryGroup _ ℂ)
    (event : (Fin (FoldedOPI.publicParameters P 3) → FoldedOPI.publicField P) → Prop) : ℝ :=
  probEvent (act ((F.circuit P).unitary O) (zeroKet (F.qubits P)))
    (fun z => event (OPI.coefficientOutput E.encoding (FoldedOPI.publicParameters P 3)
      (List.ofFn fun i => z (F.output P i))))

/-- Canonical register bit string: mask, block labels, syndrome, answer;
2610.02145 pp.39–40. Every field element uses the same public polynomial basis. -/
def algorithmBits {F : Type} [Field F] [Fintype F] {M h K : ℕ}
    (E : OPI.publicFieldEncoding F) (q : AlgorithmRegister F M h K) : Complexity.Str :=
  List.ofFn q.1.1 ++
  ((List.ofFn fun i => (List.ofFn fun j => OPI.fieldBits E (q.1.2 i j)).flatten).flatten) ++
  (List.ofFn fun j => OPI.fieldBits E (q.2.1 j)).flatten ++ [q.2.2]

/-- Compilation tied to the full explicit ideal construction and public encoding;
2610.02145 pp.39–40. Query bounds and correctness of the constructed decoder
are not assumed. Approximate amplitudes on invalid encodings count in the norm. -/
def ConstructedCircuit {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F] {M h K N : ℕ} (hM : 0 < M)
    (ell : ℕ) (hell : ell ≤ M) (gamma : F)
    (distinct : Function.Injective (fun t : Fin (M*h) => gamma^t.val))
    (dimensions : K ≤ M*h)
    (embedding : AlgorithmRegister F M h K ↪ Qubits N)
    (E : OPI.publicFieldEncoding F) (_charTwo : E.p = 2)
    (_fits : M+(M*h+K)*(E.e*Nat.clog 2 E.p)+1 ≤ N)
    (_encoding : ∀ q, List.ofFn (embedding q) = algorithmBits E q ++
      List.replicate (N-(M+(M*h+K)*(E.e*Nat.clog 2 E.p)+1)) false)
    (circuit : OracleCircuit htcxGateSet (fun _ : Fin M => h*(E.e*Nat.clog 2 E.p)+1) N) : Prop :=
  let oracles := fun A : FoldedOPI.BalancedInstance M (Fin h → F) =>
    fun i => extendEncodedUnitary (FoldedOPI.blockOracleEmbedding E h)
      (FoldedOPI.fixedBlockOracles A.sets i)
  ∀ A, let ideal := idealConstructedState hM ell hell gamma distinct dimensions A
    let encoded : EuclideanSpace ℂ (Qubits N) :=
      WithLp.toLp 2 fun z => ∑ i : AlgorithmRegister F M h K, if embedding i = z then ideal i else 0
    ‖act (circuit.unitary (oracles A)) (zeroKet N)-encoded‖ ≤ (M : ℝ)⁻¹^2

example {R : ℚ} (F : UniformFixedBlockFamily R)
    (P : FoldedOPI.PublicDomain) (E : FoldedOPI.PublicFieldData P)
    (width : E.encoding.e*Nat.clog 2 E.encoding.p = 2*P.u)
    (O : Fin P.M → Matrix (Qubits ((P.M+2)*(2*P.u)+1))
      (Qubits ((P.M+2)*(2*P.u)+1)) ℂ)
    (hO : ∀ i, O i ∈ Matrix.unitaryGroup _ ℂ) :
    F.outputLaw P E width O hO (fun _ => False) = 0 := by
  simp [UniformFixedBlockFamily.outputLaw, probEvent]

example : remainingOnesRotation 0 0 = 1 := by simp [remainingOnesRotation]

end QAlgorithms.FoldedDQI


