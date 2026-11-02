-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P77
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:07:49.027277+00:00
-- url     : https://prove2.me/theorems/b9ba1066-2f14-43f8-8b57-68b7a635bf4c
-- title:
--   Definitions for Matchgates and classical simulation of quantum circuits
-- statement:
--   The objects the formalized statements of *Matchgates and classical simulation of quantum circuits* (arXiv:0804.4050) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `tupleCode`: PDF p.3 numerical convention: unambiguous tuple code; a unary field length precedes each field, including a possibly empty last field.
--   - `binaryNat`: PDF p.3: binary, most significant digit first, with arbitrary leading zeroes.
--   - `dyadic`: PDF p.3: signed dyadic output. The first bit is a sign, remaining bits are the numerator, and m specifies the denominator. Empty output decodes to zero.
--   - `EffectiveCode`: PDF p.3: exact finite metadata must be produced by a genuine polynomial-time multi-stack Turing computation, with its polynomial uniform over all inputs.
--   - `EffectiveNumbers`: PDF pp.3,9--10: finite continuous data are supplied to requested precision by one bit-machine. Both real and imaginary parts are charged; the item index and precision are unary and the instance description is a length-delimited field. No running-time claim is made for arbitrary uncomputable complex numbers.
--   - `StrongSimulation`: PDF p.3: a single classical simulator computes either one-wire probability to m binary digits. Its machine and time polynomial are selected before the instance, precision, existing output wire and outcome bit.
--   - `SelectedStrongSimulation`: PDF pp.3,10,13: strong simulation of the selected one-wire measurement. Only that observable needs a bounded-degree representation. The output wire is included in the family's effective metadata, before the precision request.
--   - `entries`: PDF pp.2,9: finite list of entries of a one-qubit matrix, row order 0,1.
--   - `parityGate`: PDF p.2 Eq.(1): even block is ordered 00,11 and odd block 01,10.
--   - `ParityApp`: PDF p.2: a placed parity-preserving unitary; determinant equality is a separate predicate so that the dropped-constraint result uses the same object.
--   - `ParityApp.Allowable`: PDF p.2: the defining determinant condition on an allowable matchgate.
--   - `ParityApp.toGateApp`: PDF pp.2,4: actual placed gate in the accepted circuit model.
--   - `parityCircuit`: PDF pp.2,4: list order is time order; the first matrix is rightmost.
--   - `RangeBound`: PDF pp.2,4,6: a fixed ordered path, with each gate spanning at most r edges.
--   - `ParityFamily`: PDF pp.2--3: a circuit family parameterized by finite classical instance descriptions. Polynomial-time metadata bounds both wire count and gate count.
--   - `ParityFamily.code`: PDF p.3: complete finite structural description, using unary wire indices.
--   - `ParityFamily.data`: PDF pp.2--3: all local gate entries, with no uncharged numerical oracle.
--   - `ParityFamily.Effective`: PDF p.3 uniformity and numerical-description convention.
--   - `ProductInputs`: PDF pp.2,9--10: normalized single-qubit factors; no parity constraint.
--   - `ProductInputs.data`: PDF pp.3,10: all input amplitudes are part of the charged description.
--   - `singleWireProbability`: PDF p.2: Born probability for one final computational-basis measurement.
--   - `productOperator`: PDF p.10: tensor product of one-qubit operators with wire 0 leftmost.
--   - `zOperator`: PDF pp.2,10: Pauli Z on an existing wire.
--   - `outputExpectation`: PDF pp.2,9: the exact expectation in a circuit's final state.
--   - `quadraticHamiltonian`: PDF p.8 Eq.(7): real skew coefficients; both ordered off-diagonal terms are summed, with no factor 1/2 and no additive scalar Hamiltonian.
--   - `gaussianOperation`: PDF p.9: Gaussian operation with the paper's positive exponent sign.
--   - `Skew`: PDF pp.8--9: antisymmetry is stated entrywise over the reals.
--   - `IsMajoranaRotation`: PDF p.9: SO(2n) with both orthogonality and determinant one.
--   - `majoranaWord`: PDF p.8 Eq.(6): ordered Majorana products, including the empty word.
--   - `CARPolynomial`: PDF pp.8,10: a canonical square-free polynomial given by its nonzero or explicitly zero coefficients. Each word is strictly ordered and occurs once.
--   - `CARPolynomial.eval`: PDF p.8: evaluation of the supplied canonical polynomial.
--   - `CARPolynomial.DegreeLE`: PDF p.10: degree at most d, allowing a constant/empty monomial.
--   - `gaussianCircuit`: PDF pp.9--10: circuit and its induced Heisenberg rotation.
--   - `circuitRotation`: PDF pp.9--10: the Heisenberg rotations are composed in reverse list order.
--   - `expandedWord`: PDF p.10 Eq.(9), general form: expansion indices may repeat; CAR reduction is performed after expansion, rather than deleting repeated tuples.
--   - `GaussianFamily`: PDF pp.9--10: Gaussian circuit data for an effectively given product-operator representation. The factors of every generator are supplied, not inferred from an arbitrary matrix description. Only the selected measured Z is represented; other wires need not have bounded-degree or efficient polynomial descriptions.
--   - `GaussianFamily.code`: PDF pp.3,8--10: all polynomial words and gate counts form finite metadata.
--   - `GaussianFamily.data`: PDF pp.3,9--10: generator factors, Gaussian coefficients, and observable coefficients are all charged. Structural size is charged by the metadata.
--   - `GaussianFamily.Effective`: PDF p.3: effective uniform Gaussian family with the full description cost.
--   - `jordanWigner`: PDF p.10 Eq.(10): zero-based Majorana index 2k is ZX and 2k+1 is ZY. Initial Z's occupy exactly the wires strictly preceding k.
--   - `JWFamily`: PDF pp.10--11: global Jordan--Wigner Gaussian gates, each specified by all quadratic coefficients rather than a dense exponential-size operator.
--   - `JWFamily.code`: PDF pp.3,10: structural cost of a Jordan--Wigner Gaussian family.
--   - `JWFamily.data`: PDF pp.3,10: all real Gaussian coefficients are supplied effectively.
--   - `JWFamily.Effective`: PDF p.3 uniformity including Gaussian numerical descriptions.
--   - `SupportedOnPair`: PDF p.11: only the four Majoranas on a specified existing adjacent pair may occur in its local quadratic Hamiltonian.
--   - `pairMajor`: PDF p.12 Eq.(11) on a specified adjacent pair; a=0,1 indexes that pair.
--   - `modifiedSwap`: PDF p.12 Eq.(11), copied as an exponential, including its scalar phase.
--   - `SourceStep`: PDF pp.4--5: nearest-neighbour CZ and arbitrary one-qubit normal form; constant gate overhead is relative to this presentation.
--   - `SourceStep.toGateApp`: PDF pp.4--5: exact denotation of the source presentation.
--   - `sourceCircuit`: PDF p.4: source circuit matrix, with input-independent gates.
--   - `SourceFamily`: PDF pp.4--5: a uniformly described normal-form family.
--   - `SourceFamily.code`: PDF p.4: all source arities, tags and wire positions are charged.
--   - `SourceFamily.data`: PDF pp.4--5: numerical source data are the one-qubit matrices.
--   - `SourceFamily.Effective`: PDF pp.3--5: uniformity includes gate-parameter description costs.
--   - `encodeFourBits`: PDF p.5: |0> maps to |0000> and |1> maps to |1001> in each block.
--   - `encodeTwoBits`: PDF p.6: alternative pair encoding |0> maps to |00>, |1> to |11>.
--   - `encodeState`: PDF pp.5--6: linear extension to every logical input, including entangled inputs. This is the actual constructed encoding, not an arbitrary isometry.
--   - `conjugatedGenerators`: PDF pp.12--13: c'_mu=T† c_mu T, computed from the actual Clifford operation.
--   - `IntertwinedFamily`: PDF pp.12--13: a Clifford-conjugated Gaussian family with available product factor and observable descriptions. Factors and polynomial identities describe source data; neither simulation nor Gaussian conjugation is assumed. Only the selected output observable is supplied or required to have bounded degree.
--   - `IntertwinedFamily.code`: PDF pp.3,13: structural data for the bounded-degree transformed observable.
--   - `IntertwinedFamily.data`: PDF pp.3,13: the effective description includes the actual transformed product factors, quadratic coefficients, and observable coefficients. Scalar phases of T need no description, since they cancel from every conjugation.
--   - `IntertwinedFamily.Effective`: PDF pp.3,13: all information needed from T is effectively supplied by its conjugated product generators and polynomial observable; no dense T oracle.
--   - `permutationOperator`: PDF p.14 Example 1: the actual operator permuting the fixed wire order.
--   - `EffectivePermutations`: PDF p.14: one global relabeling, with an effective finite permutation list.
--   - `basisInput`: PDF pp.3,16: computational-basis input followed by zero workspace. The decision-family type below requires enough wires to contain the input.
--   - `BasisDecisionFamily`: PDF pp.3,16: one input-independent circuit and existing output wire for each input length, with the classical input followed by zero ancillas.
--   - `BasisDecisionFamily.Effective`: PDF pp.3,16: the output wire description is charged along with all gates.
--   - `BasisDecisionFamily.Allowed`: PDF pp.3,16: locality and determinant equality on every actual circuit.
--   - `BasisDecisionFamily.acceptance`: PDF pp.3,16: output 1 denotes acceptance, for every classical input.
--   - `InP`: PDF p.3: P as a characteristic function computed by the accepted polynomial-time finite Turing machine predicate (Cook/PvsNP provenance). This definition does not substitute an arbitrary language predicate for P.
--   - `InBoundedMatchgate`: PDF p.3: the specified bounded-error matchgate language class, with worst-case success >=2/3 on every computational-basis input.
--   - `InPQPMatchgate`: PDF p.16: V_r under the symmetric PQP majority-gap conditions. Polynomial padding is explicit: one polynomial exponent is chosen before all inputs, and is >=2 even at length zero. This avoids the impossible literal n=0 gap.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, https://arxiv.org/abs/0804.4050v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

/-!
Jozsa--Miyake, arXiv:0804.4050v2. Page numbers below are PDF pages.
The accepted CARSystem is reused solely as a representation interface, and the
accepted generic Op is specialized to the qubit basis; no parity
restriction on states, Gaussian-channel theorem, or covariance predicate is used.
Paper-local numerical descriptions are polynomial-time binary transducers, not
exact-real primitives. Binary precision is equivalent to decimal digits with a
constant rescaling. Source corrections are recorded in HARD.md.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms
open QAlgorithms.Complexity (Str)
open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3 numerical convention: unambiguous tuple code; a unary field length
precedes each field, including a possibly empty last field. -/
def tupleCode (xs : List Str) : Str :=
  xs.flatMap fun x => QAlgorithms.Complexity.encNat x.length ++ x

/-- PDF p.3: binary, most significant digit first, with arbitrary leading zeroes. -/
def binaryNat (w : Str) : ℕ :=
  w.foldl (fun a b => 2 * a + if b then 1 else 0) 0

/-- PDF p.3: signed dyadic output. The first bit is a sign, remaining bits are
the numerator, and m specifies the denominator. Empty output decodes to zero. -/
def dyadic (w : Str) (m : ℕ) : ℝ :=
  (if w.headD false then -(binaryNat w.tail : ℝ) else (binaryNat w.tail : ℝ)) /
    (2 : ℝ) ^ m

/-- PDF p.3: exact finite metadata must be produced by a genuine polynomial-time
multi-stack Turing computation, with its polynomial uniform over all inputs. -/
def EffectiveCode (code : Str → Str) : Prop :=
  QAlgorithms.Complexity.PolyTimeComputable code

/-- PDF pp.3,9--10: finite continuous data are supplied to requested precision
by one bit-machine. Both real and imaginary parts are charged; the item index
and precision are unary and the instance description is a length-delimited field.
No running-time claim is made for arbitrary uncomputable complex numbers. -/
def EffectiveNumbers (data : Str → List ℂ) : Prop :=
  ∃ f : Str → Str, QAlgorithms.Complexity.PolyTimeComputable f ∧
    ∀ s (j : Fin (data s).length) m b,
      |dyadic (f (tupleCode [s, QAlgorithms.Complexity.unary j.val,
          QAlgorithms.Complexity.unary m, [b]])) m -
        (if b then ((data s).get j).im else ((data s).get j).re)| ≤ (2 : ℝ)⁻¹ ^ m

/-- PDF p.3: a single classical simulator computes either one-wire probability
to m binary digits. Its machine and time polynomial are selected before the
instance, precision, existing output wire and outcome bit. -/
def StrongSimulation (width : Str → ℕ)
    (p : (s : Str) → Fin (width s) → Bool → ℝ) : Prop :=
  ∃ f : Str → Str, QAlgorithms.Complexity.PolyTimeComputable f ∧
    ∀ s m (k : Fin (width s)) b,
      |dyadic (f (tupleCode [s, QAlgorithms.Complexity.unary m,
          QAlgorithms.Complexity.unary k.val, [b]])) m - p s k b| ≤ (2 : ℝ)⁻¹ ^ m

/-- PDF pp.3,10,13: strong simulation of the selected one-wire measurement.
Only that observable needs a bounded-degree representation. The output wire is
included in the family's effective metadata, before the precision request. -/
def SelectedStrongSimulation (p : Str → Bool → ℝ) : Prop :=
  ∃ f : Str → Str, QAlgorithms.Complexity.PolyTimeComputable f ∧
    ∀ s m b,
      |dyadic (f (tupleCode [s, QAlgorithms.Complexity.unary m, [b]])) m -
        p s b| ≤ (2 : ℝ)⁻¹ ^ m

/-- PDF pp.2,9: finite list of entries of a one-qubit matrix, row order 0,1. -/
def entries (A : Matrix Bool Bool ℂ) : List ℂ :=
  [A false false, A false true, A true false, A true true]

/-- PDF p.2 Eq.(1): even block is ordered 00,11 and odd block 01,10. -/
def parityGate (A B : Matrix Bool Bool ℂ) : Matrix (Qubits 2) (Qubits 2) ℂ :=
  fun x y =>
    if xor (x 0) (x 1) = xor (y 0) (y 1) then
      if xor (x 0) (x 1) then B (x 0) (y 0) else A (x 0) (y 0)
    else 0

/-- PDF p.2: a placed parity-preserving unitary; determinant equality is a
separate predicate so that the dropped-constraint result uses the same object. -/
structure ParityApp (n : ℕ) where
  A : Matrix.unitaryGroup Bool ℂ
  B : Matrix.unitaryGroup Bool ℂ
  wires : Fin 2 ↪ Fin n

/-- PDF p.2: the defining determinant condition on an allowable matchgate. -/
def ParityApp.Allowable {n : ℕ} (g : ParityApp n) : Prop :=
  Matrix.det (g.A : Matrix Bool Bool ℂ) = Matrix.det (g.B : Matrix Bool Bool ℂ)

/-- PDF pp.2,4: actual placed gate in the accepted circuit model. -/
def ParityApp.toGateApp {n : ℕ} (g : ParityApp n) : GateApp Set.univ n :=
  ⟨⟨2, parityGate g.A g.B⟩, Set.mem_univ _, g.wires⟩

/-- PDF pp.2,4: list order is time order; the first matrix is rightmost. -/
def parityCircuit {n : ℕ} (c : List (ParityApp n)) : Circuit Set.univ n :=
  c.map ParityApp.toGateApp

/-- PDF pp.2,4,6: a fixed ordered path, with each gate spanning at most r edges. -/
def RangeBound {n : ℕ} (r : ℕ) (c : List (ParityApp n)) : Prop :=
  ∀ g ∈ c, Nat.dist (g.wires 0).val (g.wires 1).val ≤ r

/-- PDF pp.2--3: a circuit family parameterized by finite classical instance
descriptions. Polynomial-time metadata bounds both wire count and gate count. -/
structure ParityFamily where
  width : Str → ℕ
  gates : (s : Str) → List (ParityApp (width s))

/-- PDF p.3: complete finite structural description, using unary wire indices. -/
def ParityFamily.code (F : ParityFamily) (s : Str) : Str :=
  tupleCode ([QAlgorithms.Complexity.unary (F.width s),
    QAlgorithms.Complexity.unary (F.gates s).length] ++
    (F.gates s).map fun g => tupleCode
      [QAlgorithms.Complexity.unary (g.wires 0).val,
       QAlgorithms.Complexity.unary (g.wires 1).val])

/-- PDF pp.2--3: all local gate entries, with no uncharged numerical oracle. -/
def ParityFamily.data (F : ParityFamily) (s : Str) : List ℂ :=
  (F.gates s).flatMap fun g => entries g.A ++ entries g.B

/-- PDF p.3 uniformity and numerical-description convention. -/
def ParityFamily.Effective (F : ParityFamily) : Prop :=
  EffectiveCode F.code ∧ EffectiveNumbers F.data

/-- PDF pp.2,9--10: normalized single-qubit factors; no parity constraint. -/
structure ProductInputs (width : Str → ℕ) where
  factor : (s : Str) → Fin (width s) → EuclideanSpace ℂ Bool
  normalized : ∀ s i, IsState (factor s i)

/-- PDF pp.3,10: all input amplitudes are part of the charged description. -/
def ProductInputs.data {width : Str → ℕ} (I : ProductInputs width) (s : Str) : List ℂ :=
  (List.ofFn fun i : Fin (width s) => [I.factor s i false, I.factor s i true]).flatten

/-- PDF p.2: Born probability for one final computational-basis measurement. -/
def singleWireProbability {n : ℕ} (U : Op (Qubits n)) (psi : EuclideanSpace ℂ (Qubits n))
    (k : Fin n) (b : Bool) : ℝ :=
  probEvent (act U psi) (fun x => x k = b)

/-- PDF p.10: tensor product of one-qubit operators with wire 0 leftmost. -/
def productOperator {n : ℕ} (P : Fin n → Matrix Bool Bool ℂ) : Op (Qubits n) :=
  fun x y => ∏ i, P i (x i) (y i)

/-- PDF pp.2,10: Pauli Z on an existing wire. -/
def zOperator {n : ℕ} (k : Fin n) : Op (Qubits n) :=
  productOperator fun i => if i = k then pauliZ else 1

/-- PDF pp.2,9: the exact expectation in a circuit's final state. -/
def outputExpectation {n : ℕ} (U : Op (Qubits n)) (psi : EuclideanSpace ℂ (Qubits n))
    (A : Op (Qubits n)) : ℂ :=
  inner ℂ (act U psi) (act A (act U psi))

/-- PDF p.8 Eq.(7): real skew coefficients; both ordered off-diagonal terms
are summed, with no factor 1/2 and no additive scalar Hamiltonian. -/
def quadraticHamiltonian {n : ℕ} (c : Major n → Op (Qubits n))
    (h : Matrix (Major n) (Major n) ℝ) : Op (Qubits n) :=
  Complex.I • ∑ i, ∑ j, if i = j then 0 else (h i j : ℂ) • (c i * c j)

/-- PDF p.9: Gaussian operation with the paper's positive exponent sign. -/
def gaussianOperation {n : ℕ} (c : Major n → Op (Qubits n))
    (h : Matrix (Major n) (Major n) ℝ) : Op (Qubits n) :=
  NormedSpace.exp (Complex.I • quadraticHamiltonian c h)

/-- PDF pp.8--9: antisymmetry is stated entrywise over the reals. -/
def Skew {n : ℕ} (h : Matrix (Major n) (Major n) ℝ) : Prop :=
  ∀ i j, h i j = -h j i

/-- PDF p.9: SO(2n) with both orthogonality and determinant one. -/
def IsMajoranaRotation {n : ℕ} (R : Matrix (Major n) (Major n) ℝ) : Prop :=
  R.transpose * R = 1 ∧ Matrix.det R = 1

/-- PDF p.8 Eq.(6): ordered Majorana products, including the empty word. -/
def majoranaWord {n : ℕ} (c : Major n → Op (Qubits n)) (l : List (Major n)) : Op (Qubits n) :=
  (l.map c).prod

/-- PDF pp.8,10: a canonical square-free polynomial given by its nonzero or
explicitly zero coefficients. Each word is strictly ordered and occurs once. -/
structure CARPolynomial (n : ℕ) where
  terms : List (List (Major n) × ℂ)
  ordered : ∀ t ∈ terms, t.1.Pairwise (fun i j => i.val < j.val)
  unique : (terms.map Prod.fst).Nodup

/-- PDF p.8: evaluation of the supplied canonical polynomial. -/
def CARPolynomial.eval {n : ℕ} (P : CARPolynomial n) (c : Major n → Op (Qubits n)) : Op (Qubits n) :=
  (P.terms.map fun t => t.2 • majoranaWord c t.1).sum

/-- PDF p.10: degree at most d, allowing a constant/empty monomial. -/
def CARPolynomial.DegreeLE {n : ℕ} (P : CARPolynomial n) (d : ℕ) : Prop :=
  ∀ t ∈ P.terms, t.1.length ≤ d

/-- PDF pp.9--10: circuit and its induced Heisenberg rotation. -/
def gaussianCircuit {n : ℕ} (c : Major n → Op (Qubits n))
    (hs : List (Matrix (Major n) (Major n) ℝ)) : Op (Qubits n) :=
  (hs.map (gaussianOperation c)).reverse.prod

/-- PDF pp.9--10: the Heisenberg rotations are composed in reverse list order. -/
def circuitRotation {n : ℕ} (hs : List (Matrix (Major n) (Major n) ℝ)) :
    Matrix (Major n) (Major n) ℝ :=
  (hs.map fun h => NormedSpace.exp ((-4 : ℝ) • h)).reverse.prod

/-- PDF p.10 Eq.(9), general form: expansion indices may repeat; CAR reduction
is performed after expansion, rather than deleting repeated tuples. -/
def expandedWord {n : ℕ} (c : Major n → Op (Qubits n))
    (R : Matrix (Major n) (Major n) ℝ) (l : List (Major n)) : Op (Qubits n) :=
  ∑ j : Fin l.length → Major n,
    ((∏ i : Fin l.length, R (l.get i) (j i) : ℝ) : ℂ) •
      majoranaWord c (List.ofFn j)

/-- PDF pp.9--10: Gaussian circuit data for an effectively given product-operator
representation. The factors of every generator are supplied, not inferred from
an arbitrary matrix description. Only the selected measured Z is represented;
other wires need not have bounded-degree or efficient polynomial descriptions. -/
structure GaussianFamily where
  width : Str → ℕ
  system : (s : Str) → CARSystem (width s)
  factors : (s : Str) → Major (width s) → Fin (width s) → Matrix Bool Bool ℂ
  factorization : ∀ s i, (system s).majorana i = productOperator (factors s i)
  gates : (s : Str) → List (Matrix (Major (width s)) (Major (width s)) ℝ)
  skew : ∀ s h, h ∈ gates s → Skew h
  measured : (s : Str) → Fin (width s)
  observable : (s : Str) → CARPolynomial (width s)
  representsZ : ∀ s, (observable s).eval (system s).majorana = zOperator (measured s)

/-- PDF pp.3,8--10: all polynomial words and gate counts form finite metadata. -/
def GaussianFamily.code (F : GaussianFamily) (s : Str) : Str :=
  tupleCode [QAlgorithms.Complexity.unary (F.width s),
    QAlgorithms.Complexity.unary (F.gates s).length,
    QAlgorithms.Complexity.unary (F.measured s).val,
    tupleCode ((F.observable s).terms.map fun t =>
      tupleCode (t.1.map fun i => QAlgorithms.Complexity.unary i.val))]

/-- PDF pp.3,9--10: generator factors, Gaussian coefficients, and observable
coefficients are all charged. Structural size is charged by the metadata. -/
def GaussianFamily.data (F : GaussianFamily) (s : Str) : List ℂ :=
  (List.ofFn fun i : Major (F.width s) =>
    (List.ofFn fun k : Fin (F.width s) => entries (F.factors s i k)).flatten).flatten ++
  (F.gates s).flatMap (fun h =>
    (List.ofFn fun i : Major (F.width s) =>
      List.ofFn fun j : Major (F.width s) => (h i j : ℂ)).flatten) ++
  (F.observable s).terms.map Prod.snd

/-- PDF p.3: effective uniform Gaussian family with the full description cost. -/
def GaussianFamily.Effective (F : GaussianFamily) : Prop :=
  EffectiveCode F.code ∧ EffectiveNumbers F.data

/-- PDF p.10 Eq.(10): zero-based Majorana index 2k is ZX and 2k+1 is ZY.
Initial Z's occupy exactly the wires strictly preceding k. -/
def jordanWigner (n : ℕ) (i : Major n) : Op (Qubits n) :=
  productOperator fun k =>
    if k.val < i.val / 2 then pauliZ
    else if k.val = i.val / 2 then (if i.val % 2 = 0 then pauliX else pauliY)
    else 1

/-- PDF pp.10--11: global Jordan--Wigner Gaussian gates, each specified by all
quadratic coefficients rather than a dense exponential-size operator. -/
structure JWFamily where
  width : Str → ℕ
  gates : (s : Str) → List (Matrix (Major (width s)) (Major (width s)) ℝ)
  skew : ∀ s h, h ∈ gates s → Skew h

/-- PDF pp.3,10: structural cost of a Jordan--Wigner Gaussian family. -/
def JWFamily.code (F : JWFamily) (s : Str) : Str :=
  tupleCode [QAlgorithms.Complexity.unary (F.width s),
    QAlgorithms.Complexity.unary (F.gates s).length]

/-- PDF pp.3,10: all real Gaussian coefficients are supplied effectively. -/
def JWFamily.data (F : JWFamily) (s : Str) : List ℂ :=
  (F.gates s).flatMap fun h =>
    (List.ofFn fun i : Major (F.width s) =>
      List.ofFn fun j : Major (F.width s) => (h i j : ℂ)).flatten

/-- PDF p.3 uniformity including Gaussian numerical descriptions. -/
def JWFamily.Effective (F : JWFamily) : Prop :=
  EffectiveCode F.code ∧ EffectiveNumbers F.data

/-- PDF p.11: only the four Majoranas on a specified existing adjacent pair
may occur in its local quadratic Hamiltonian. -/
def SupportedOnPair {n : ℕ} (w : Fin 2 ↪ Fin n)
    (h : Matrix (Major n) (Major n) ℝ) : Prop :=
  ∀ i j, (i.val / 2 ∉ Set.range (fun a => (w a).val) ∨
    j.val / 2 ∉ Set.range (fun a => (w a).val)) → h i j = 0

/-- PDF p.12 Eq.(11) on a specified adjacent pair; a=0,1 indexes that pair. -/
def pairMajor {n : ℕ} (w : Fin 2 ↪ Fin n) (a : Fin 2) (b : Bool) : Major n :=
  ⟨2 * (w a).val + if b then 1 else 0, by have := (w a).isLt; split_ifs <;> omega⟩

/-- PDF p.12 Eq.(11), copied as an exponential, including its scalar phase. -/
def modifiedSwap {n : ℕ} (c : Major n → Op (Qubits n)) (w : Fin 2 ↪ Fin n) : Op (Qubits n) :=
  NormedSpace.exp (((-Real.pi / 4 : ℝ) : ℂ) •
    (-c (pairMajor w 0 false) * c (pairMajor w 1 true) +
      c (pairMajor w 0 true) * c (pairMajor w 1 false) +
      c (pairMajor w 0 false) * c (pairMajor w 0 true) +
      c (pairMajor w 1 false) * c (pairMajor w 1 true)))

/-- PDF pp.4--5: nearest-neighbour CZ and arbitrary one-qubit normal form;
constant gate overhead is relative to this presentation. -/
inductive SourceStep (n : ℕ) where
  | one (A : Matrix.unitaryGroup Bool ℂ) (k : Fin n)
  | cz (w : Fin 2 ↪ Fin n) (adjacent : (w 0).val + 1 = (w 1).val)

/-- PDF pp.4--5: exact denotation of the source presentation. -/
def SourceStep.toGateApp {n : ℕ} : SourceStep n → GateApp Set.univ n
  | .one A k =>
      ⟨Gate.ofMatrix1 A, Set.mem_univ _,
        ⟨fun _ => k, by
          change Function.Injective (fun _ : Fin 1 => k)
          intro a b _
          exact Subsingleton.elim a b⟩⟩
  | .cz w _ => ⟨Gate.ofMatrix2 (controlled pauliZ), Set.mem_univ _, w⟩

/-- PDF p.4: source circuit matrix, with input-independent gates. -/
def sourceCircuit {n : ℕ} (c : List (SourceStep n)) : Circuit Set.univ n :=
  c.map SourceStep.toGateApp

/-- PDF pp.4--5: a uniformly described normal-form family. -/
structure SourceFamily where
  width : Str → ℕ
  gates : (s : Str) → List (SourceStep (width s))

/-- PDF p.4: all source arities, tags and wire positions are charged. -/
def SourceFamily.code (F : SourceFamily) (s : Str) : Str :=
  tupleCode ([QAlgorithms.Complexity.unary (F.width s),
    QAlgorithms.Complexity.unary (F.gates s).length] ++
    (F.gates s).map fun g => match g with
      | .one _ k => tupleCode [[false], QAlgorithms.Complexity.unary k.val]
      | .cz w _ => tupleCode [[true], QAlgorithms.Complexity.unary (w 0).val,
          QAlgorithms.Complexity.unary (w 1).val])

/-- PDF pp.4--5: numerical source data are the one-qubit matrices. -/
def SourceFamily.data (F : SourceFamily) (s : Str) : List ℂ :=
  (F.gates s).flatMap fun g => match g with
    | .one A _ => entries A
    | .cz _ _ => []

/-- PDF pp.3--5: uniformity includes gate-parameter description costs. -/
def SourceFamily.Effective (F : SourceFamily) : Prop :=
  EffectiveCode F.code ∧ EffectiveNumbers F.data

/-- PDF p.5: |0> maps to |0000> and |1> maps to |1001> in each block. -/
def encodeFourBits {n : ℕ} (x : Qubits n) : Qubits (4 * n) :=
  fun i => if i.val % 4 = 0 ∨ i.val % 4 = 3 then
    x ⟨i.val / 4, by have := i.isLt; omega⟩ else false

/-- PDF p.6: alternative pair encoding |0> maps to |00>, |1> to |11>. -/
def encodeTwoBits {n : ℕ} (x : Qubits n) : Qubits (2 * n) :=
  fun i => x ⟨i.val / 2, by have := i.isLt; omega⟩

/-- PDF pp.5--6: linear extension to every logical input, including entangled
inputs. This is the actual constructed encoding, not an arbitrary isometry. -/
def encodeState {n m : ℕ} (e : Qubits n → Qubits m)
    (psi : EuclideanSpace ℂ (Qubits n)) : EuclideanSpace ℂ (Qubits m) :=
  ∑ x : Qubits n, psi x • ket (e x)

/-- PDF pp.12--13: c'_mu=T† c_mu T, computed from the actual Clifford operation. -/
def conjugatedGenerators {n : ℕ} (T : Matrix.unitaryGroup (Qubits n) ℂ)
    (c : Major n → Op (Qubits n)) (i : Major n) : Op (Qubits n) :=
  star (T : Op (Qubits n)) * c i * (T : Op (Qubits n))

/-- PDF pp.12--13: a Clifford-conjugated Gaussian family with available product
factor and observable descriptions. Factors and polynomial identities describe
source data; neither simulation nor Gaussian conjugation is assumed. Only the
selected output observable is supplied or required to have bounded degree. -/
structure IntertwinedFamily where
  base : JWFamily
  T : (s : Str) → Matrix.unitaryGroup (Qubits (base.width s)) ℂ
  clifford : ∀ s, T s ∈ QAlgorithms.Clifford.normalizer (base.width s)
  factors : (s : Str) → Major (base.width s) → Fin (base.width s) → Matrix Bool Bool ℂ
  factorization : ∀ s i, conjugatedGenerators (T s) (jordanWigner (base.width s)) i =
    productOperator (factors s i)
  measured : (s : Str) → Fin (base.width s)
  observable : (s : Str) → CARPolynomial (base.width s)
  representsZ : ∀ s,
    (observable s).eval (conjugatedGenerators (T s) (jordanWigner (base.width s))) =
      zOperator (measured s)

/-- PDF pp.3,13: structural data for the bounded-degree transformed observable. -/
def IntertwinedFamily.code (F : IntertwinedFamily) (s : Str) : Str :=
  tupleCode [F.base.code s, QAlgorithms.Complexity.unary (F.measured s).val,
    tupleCode ((F.observable s).terms.map fun t =>
      tupleCode (t.1.map fun i => QAlgorithms.Complexity.unary i.val))]

/-- PDF pp.3,13: the effective description includes the actual transformed
product factors, quadratic coefficients, and observable coefficients. Scalar
phases of T need no description, since they cancel from every conjugation. -/
def IntertwinedFamily.data (F : IntertwinedFamily) (s : Str) : List ℂ :=
  F.base.data s ++
  (List.ofFn fun i : Major (F.base.width s) =>
    (List.ofFn fun k : Fin (F.base.width s) => entries (F.factors s i k)).flatten).flatten ++
  (F.observable s).terms.map Prod.snd

/-- PDF pp.3,13: all information needed from T is effectively supplied by its
conjugated product generators and polynomial observable; no dense T oracle. -/
def IntertwinedFamily.Effective (F : IntertwinedFamily) : Prop :=
  EffectiveCode F.code ∧ EffectiveNumbers F.data

/-- PDF p.14 Example 1: the actual operator permuting the fixed wire order. -/
def permutationOperator {n : ℕ} (p : Equiv.Perm (Fin n)) : Op (Qubits n) :=
  fun x y => if x = y ∘ p then 1 else 0

/-- PDF p.14: one global relabeling, with an effective finite permutation list. -/
def EffectivePermutations (width : Str → ℕ)
    (p : (s : Str) → Equiv.Perm (Fin (width s))) : Prop :=
  EffectiveCode (fun s => tupleCode (List.ofFn fun i : Fin (width s) =>
    QAlgorithms.Complexity.unary (p s i).val))

example : encodeFourBits (![true] : Qubits 1) = ![true, false, false, true] := by
  ext i; fin_cases i <;> rfl

example : encodeTwoBits (![true] : Qubits 1) = ![true, true] := by
  ext i; fin_cases i <;> rfl

example {n : ℕ} (c : Major n → Op (Qubits n)) :
    conjugatedGenerators (1 : Matrix.unitaryGroup (Qubits n) ℂ) c = c := by
  funext i; simp [conjugatedGenerators]

/-- PDF pp.3,16: computational-basis input followed by zero workspace.
The decision-family type below requires enough wires to contain the input. -/
def basisInput (n : ℕ) (x : Str) : EuclideanSpace ℂ (Qubits n) :=
  ket (fun i => (x[i.val]?).getD false)

/-- PDF pp.3,16: one input-independent circuit and existing output wire for
each input length, with the classical input followed by zero ancillas. -/
structure BasisDecisionFamily where
  family : ParityFamily
  output : (n : ℕ) → Fin (family.width (QAlgorithms.Complexity.unary n))
  enoughWires : ∀ n, n ≤ family.width (QAlgorithms.Complexity.unary n)

/-- PDF pp.3,16: the output wire description is charged along with all gates. -/
def BasisDecisionFamily.Effective (F : BasisDecisionFamily) : Prop :=
  F.family.Effective ∧ EffectiveCode
    (fun x => QAlgorithms.Complexity.unary (F.output x.length).val)

/-- PDF pp.3,16: locality and determinant equality on every actual circuit. -/
def BasisDecisionFamily.Allowed (F : BasisDecisionFamily) (r : ℕ) : Prop :=
  ∀ n, RangeBound r (F.family.gates (QAlgorithms.Complexity.unary n)) ∧
    ∀ g ∈ F.family.gates (QAlgorithms.Complexity.unary n), g.Allowable

/-- PDF pp.3,16: output 1 denotes acceptance, for every classical input. -/
def BasisDecisionFamily.acceptance (F : BasisDecisionFamily) (x : Str) : ℝ :=
  singleWireProbability
    (parityCircuit (F.family.gates (QAlgorithms.Complexity.unary x.length))).unitary
    (basisInput (F.family.width (QAlgorithms.Complexity.unary x.length)) x)
    (F.output x.length) true

/-- PDF p.3: P as a characteristic function computed by the accepted
polynomial-time finite Turing machine predicate (Cook/PvsNP provenance).
This definition does not substitute an arbitrary language predicate for P. -/
def InP (L : Set Str) : Prop :=
  ∃ f : Str → Str, QAlgorithms.Complexity.PolyTimeComputable f ∧
    ∀ x, f x = if x ∈ L then [true] else [false]

/-- PDF p.3: the specified bounded-error matchgate language class, with
worst-case success >=2/3 on every computational-basis input. -/
def InBoundedMatchgate (r : ℕ) (L : Set Str) : Prop :=
  ∃ F : BasisDecisionFamily, F.Effective ∧ F.Allowed r ∧
    ∀ x, (x ∈ L → (2 / 3 : ℝ) ≤ F.acceptance x) ∧
      (x ∉ L → F.acceptance x ≤ (1 / 3 : ℝ))

/-- PDF p.16: V_r under the symmetric PQP majority-gap conditions. Polynomial
padding is explicit: one polynomial exponent is chosen before all inputs, and
is >=2 even at length zero. This avoids the impossible literal n=0 gap. -/
def InPQPMatchgate (r : ℕ) (L : Set Str) : Prop :=
  ∃ F : BasisDecisionFamily, F.Effective ∧ F.Allowed r ∧
    ∃ p : Polynomial ℕ, (∀ n, 2 ≤ p.eval n) ∧
      ∀ x, (x ∈ L → (1 / 2 : ℝ) + (2 : ℝ)⁻¹ ^ p.eval x.length ≤ F.acceptance x) ∧
        (x ∉ L → F.acceptance x ≤ (1 / 2 : ℝ) - (2 : ℝ)⁻¹ ^ p.eval x.length)

example : basisInput 1 [true] = ket (![true] : Qubits 1) := by
  unfold basisInput
  apply congrArg (fun x : Qubits 1 => ket x)
  ext i
  fin_cases i
  rfl

example : basisInput 2 [true] = ket (![true, false] : Qubits 2) := by
  unfold basisInput
  apply congrArg (fun x : Qubits 2 => ket x)
  ext i
  fin_cases i <;> rfl

/-! Small definition sanity examples; no source theorem is proved here. -/

example : tupleCode [[]] = [false] := rfl

example : binaryNat [true, false, true] = 5 := rfl

example : dyadic [true, true] 1 = -(1 / 2 : ℝ) := by norm_num [dyadic, binaryNat]

example (A B : Matrix Bool Bool ℂ) :
    parityGate A B ![false, false] ![true, true] = A false true := rfl

example (A B : Matrix Bool Bool ℂ) :
    parityGate A B ![false, true] ![true, false] = B false true := rfl

example : parityGate (1 : Matrix Bool Bool ℂ) 1 = 1 := by
  ext x y
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  have hy : y = ![y 0, y 1] := by ext i; fin_cases i <;> rfl
  rw [hx, hy]
  cases x 0 <;> cases x 1 <;> cases y 0 <;> cases y 1 <;>
    simp [parityGate, Matrix.one_apply]

example {n : ℕ} (c : Major n → Op (Qubits n)) : majoranaWord c [] = 1 := rfl

example {n : ℕ} (c : Major n → Op (Qubits n)) : gaussianCircuit c [] = 1 := rfl

example {n : ℕ} (c : Major n → Op (Qubits n)) : gaussianOperation c 0 = 1 := by
  simp [gaussianOperation, quadraticHamiltonian, NormedSpace.exp_zero]

example (A : Matrix Bool Bool ℂ) : (entries A).length = 4 := rfl

example {n : ℕ} (w : Fin 2 ↪ Fin n) : (ParityApp.mk 1 1 w).Allowable := rfl

example (n r : ℕ) : RangeBound r ([] : List (ParityApp n)) := by
  simp [RangeBound]

example (n : ℕ) : Skew (0 : Matrix (Major n) (Major n) ℝ) := by
  simp [Skew]

example (n : ℕ) : IsMajoranaRotation (1 : Matrix (Major n) (Major n) ℝ) := by
  simp [IsMajoranaRotation]

example (x y : Qubits 1) : jordanWigner 1 ⟨0, by decide⟩ x y = pauliX (x 0) (y 0) := by
  simp [jordanWigner, productOperator, Fin.prod_univ_one]

example (x y : Qubits 1) : jordanWigner 1 ⟨1, by decide⟩ x y = pauliY (x 0) (y 0) := by
  simp [jordanWigner, productOperator, Fin.prod_univ_one]

end QAlgorithms.Papers.Independent.Intakethird100.P77


