-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P04
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P04
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T03:47:44.423155+00:00
-- url     : https://prove2.me/theorems/16bc32a7-9156-4db0-80f2-8371bf0f9db3
-- title:
--   Definitions for Secure quantum key distribution with an uncharacterized source
-- statement:
--   The objects the formalized statements of *Secure quantum key distribution with an uncharacterized source* (arXiv:quant-ph/0208155) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `emittedMarginal`: PDF p.2: coefficients of the partial trace over the auxiliary factor, in a product Hilbert basis. Used on actual trace-class operators only.
--   - `AuxiliaryMeasurement`: PDF pp.1–2: a normalized two-outcome measurement on the auxiliary factor alone. The coefficient condition is precisely I_A tensor M_g; no restriction on the dimensions, the outcome probabilities, or the measurement basis is made.
--   - `preparationBranch`: PDF p.2: the actual subnormalized joint branch from the local measurement. Its reduced emitted branch depends only on the POVM effect, so the square-root instrument loses no generality after discarding the measured auxiliary system.
--   - `weightedEmittedBranch`: PDF pp.1–2, Eq.(1): p[a,g] rho[a,g], including the probability 1/2 of choosing the basis. Zero-probability outcomes require no division or chosen state.
--   - `preparationWeight`: PDF pp.1–2: the actual joint probability p[a,g], with a uniform basis.
--   - `xBasisVector`: PDF p.3: the X basis is exactly H tensor n applied to the Z basis.
--   - `zProjector`: PDF pp.3–4: the computational-basis rank-one projector.
--   - `xProjector`: PDF pp.3–4: the complete X-basis measurement effect.
--   - `uniformKeyFidelity`: PDF p.4: squared classical fidelity with the uniform r-bit distribution.
--   - `QubitFactor`: PDF pp.3–4: a qubit tensor factor in an arbitrary complete Hilbert space. A unital star algebra representation of the full finite matrix algebra is unitarily equivalent to A maps to A tensor I_E, with arbitrary multiplicity E.
--   - `qubitMarginal`: PDF pp.3–4: the constructed reduced density matrix. The reversed matrix unit in the trace is essential: Tr(|j><i| rho) = rho[i,j].
--   - `keyLaw`: PDF p.4: the actual X-measurement law of the qubit factor.
--   - `EveMeasurement`: PDF p.4(a): arbitrary finite measurements on Eve, rather than on the key. Commutation with the full key matrix algebra is exactly locality on E. Public transcript/permutation registers are part of this unrestricted E.
--   - `measuredKeyLaw`: PDF p.4(a): the joint classical law after Eve's actual measurement.
--   - `accessibleKeyInfo`: PDF p.4(a): accessible information in bits, optimized over all finite POVMs on E. For a finite key this supremum also includes arbitrary-outcome measurements by finite coarse-graining; no maximum or finite E is assumed. The set is nonempty (one outcome), and bounded above by r for normalized states.
--   - `squaredHilbertFidelity`: PDF p.3, Eq.(5): squared Uhlmann fidelity on actual positive trace-class arguments. Unlike frozen rootFidelity, this includes the final square.
--   - `CorrectableEncoder`: PDF p.2, Eq.(2): the injective linear encoder, the actual decoder and its correctable error set. No worst-case Hamming-ball correction is assumed.
--   - `transposeEncoder`: PDF p.2: G transpose, constructed from G, so its kernel is the dual code.
--   - `circuitU1`: PDF p.3, Eq.(7): the actual U1, as a Z-basis permutation matrix.
--   - `circuitU2`: PDF p.3, Eq.(8): the actual U2, using the actual, possibly nonlinear f.
--   - `virtualCircuit`: PDF p.3: U = U2 U1, with U1 applied first.
--   - `virtualIsometry`: PDF pp.3–4: the actual isometry appending |0>_X and applying U.
--   - `virtualKeyEffect`: PDF pp.3–4: Heisenberg key effect of the constructed virtual circuit. An equality of these effects retains the joint law with every Eve measurement.
--   - `directKeyEffect`: PDF pp.2–3, Protocol 3(8): X measurement followed by the G-transpose key map.
--   - `correctableProjector`: PDF p.3: the projector onto the actual correctable Z error support.
--   - `virtualOutput`: PDF p.4: the actual output state of ancilla Q for a given S marginal.
--   - `projectedJointState`: PDF p.3, Eq.(4): normalized projected joint state, used only for q > 0.
--   - `maskedJointLaw`: PDF p.4, Eq.(13): joint law for K=W+Y and (W,Z), where Eve can choose her measurement after reading the independently sampled public uniform W.
--   - `maskedAccessibleInfo`: PDF p.4: accessible information including the public mask register W.
--   - `maskedKeyLaw`: PDF p.4: marginal law of the final, publicly shifted key; W is not secret.
--   - `singleQubitBB84Vector`: PDF p.4: the accepted BB84 encoding specialized to one qubit, reindexed from one-bit strings to Bool. Basis false is Z and true is X; bit false is the +1 eigenstate. The wrapper changes only the register index type.
--   - `identicalCopyState`: PDF p.4: the full emitted two-copy state, retaining the copy available to Eve.
--   - `copiedBasisAverage`: PDF pp.1,4, Eq.(1): basis averages with actual unbiased joint weights p[a,g]=1/4, not conditional weights 1/2.
--   - `occasionalCopyState`: PDF p.4: an occasional identical-copy emission, with the one- and two-copy sectors distinguished in the full emitted system. The probability t is independent of basis and bit, and the theorem guards 0 < t <= 1.
--   - `occasionalCopyAverage`: PDF pp.1,4: full weighted average, retaining the nonzero two-copy sector.
-- source:
--   Secure quantum key distribution with an uncharacterized source, arXiv:quant-ph/0208155v2, https://arxiv.org/abs/quant-ph/0208155v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P31

/-!
Koashi–Preskill, arXiv:quant-ph/0208155v2, PDF pp.1–4.
Pinned accepted Dependency50.P13 supplies the operator substrate; Advance50.P18
and Claimed50.P31 supply entropy and BB84 definitions, respectively, under the
independent-paper workflow override. No earlier paper theorem is reused.
States are actual positive trace-class operators, without a dimension restriction.
The finite matrix algebra representation below specifies a qubit tensor factor;
its commutant contains Eve, including every public classical register.
The operational protocol results and the printed sampling exponent are deferred.
Compilation is pending the explicitly requested batch handoff.
-/

noncomputable section

universe u v w

namespace QAlgorithms.Papers.Independent.Intakenext100.P04

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P13
  (State IsTraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Advance50.P18 (keyEntropy)

open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ### Constructed remote preparations -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.2: coefficients of the partial trace over the auxiliary factor, in a
product Hilbert basis. Used on actual trace-class operators only. -/
def emittedMarginal {I : Type v} {J : Type w} (b : HilbertBasis (I × J) ℂ H)
    (T : H →L[ℂ] H) : Matrix I I ℂ :=
  fun i k => ∑' j, inner ℂ (b (i, j)) (T (b (k, j)))

/-- PDF pp.1–2: a normalized two-outcome measurement on the auxiliary factor
alone. The coefficient condition is precisely I_A tensor M_g; no restriction
on the dimensions, the outcome probabilities, or the measurement basis is made. -/
structure AuxiliaryMeasurement {I : Type v} {J : Type w}
    (b : HilbertBasis (I × J) ℂ H) where
  effect : Bool → H →L[ℂ] H
  positive : ∀ g, (effect g).IsPositive
  complete : ∑ g, effect g = 1
  auxiliaryOnly : ∃ m : Bool → J → J → ℂ, ∀ g i j k l,
    inner ℂ (b (i, j)) (effect g (b (k, l))) = if i = k then m g j l else 0

/-- PDF p.2: the actual subnormalized joint branch from the local measurement.
Its reduced emitted branch depends only on the POVM effect, so the square-root
instrument loses no generality after discarding the measured auxiliary system. -/
def preparationBranch {I : Type v} {J : Type w} {b : HilbertBasis (I × J) ℂ H}
    (rho : State b) (M : AuxiliaryMeasurement b) (g : Bool) : H →L[ℂ] H :=
  (cfc Real.sqrt (M.effect g)).comp
    (rho.val.val.comp (cfc Real.sqrt (M.effect g)))

/-- PDF pp.1–2, Eq.(1): p[a,g] rho[a,g], including the probability 1/2 of
choosing the basis. Zero-probability outcomes require no division or chosen state. -/
def weightedEmittedBranch {I : Type v} {J : Type w}
    {b : HilbertBasis (I × J) ℂ H} (rho : State b)
    (M : AuxiliaryMeasurement b) (g : Bool) : Matrix I I ℂ :=
  (1 / 2 : ℂ) • emittedMarginal b (preparationBranch rho M g)

/-- PDF pp.1–2: the actual joint probability p[a,g], with a uniform basis. -/
def preparationWeight {I : Type v} {J : Type w}
    {b : HilbertBasis (I × J) ℂ H} (rho : State b)
    (M : AuxiliaryMeasurement b) (g : Bool) : ℝ :=
  (operatorTrace b (preparationBranch rho M g)).re / 2

example {I : Type v} {J : Type w} (b : HilbertBasis (I × J) ℂ H) :
    emittedMarginal b (0 : H →L[ℂ] H) = 0 := by
  funext i k
  simp [emittedMarginal]

/-- PDF p.3: the X basis is exactly H tensor n applied to the Z basis. -/
def xBasisVector (n : ℕ) (x : Qubits n) : EuclideanSpace ℂ (Qubits n) :=
  act (hadamardN n) (ket x)

/-- PDF pp.3–4: the computational-basis rank-one projector. -/
def zProjector (n : ℕ) (x : Qubits n) : Matrix (Qubits n) (Qubits n) ℂ :=
  pureDensity (ket x)

/-- PDF pp.3–4: the complete X-basis measurement effect. -/
def xProjector (n : ℕ) (x : Qubits n) : Matrix (Qubits n) (Qubits n) ℂ :=
  pureDensity (xBasisVector n x)

/-- PDF p.4: squared classical fidelity with the uniform r-bit distribution. -/
def uniformKeyFidelity {r : ℕ} (p : Qubits r → ℝ) : ℝ :=
  ((2 : ℝ) ^ r)⁻¹ * (∑ y, Real.sqrt (p y)) ^ 2

/-- PDF pp.3–4: a qubit tensor factor in an arbitrary complete Hilbert space.
A unital star algebra representation of the full finite matrix algebra is
unitarily equivalent to A maps to A tensor I_E, with arbitrary multiplicity E. -/
abbrev QubitFactor (n : ℕ) (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :=
  Matrix (Qubits n) (Qubits n) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H)

/-- PDF pp.3–4: the constructed reduced density matrix. The reversed matrix
unit in the trace is essential: Tr(|j><i| rho) = rho[i,j]. -/
def qubitMarginal {I : Type v} (b : HilbertBasis I ℂ H) (rho : State b)
    {n : ℕ} (A : QubitFactor n H) : Matrix (Qubits n) (Qubits n) ℂ :=
  fun i j => operatorTrace b ((A (fun k l => if k = j ∧ l = i then 1 else 0)).comp
    rho.val.val)

/-- PDF p.4: the actual X-measurement law of the qubit factor. -/
def keyLaw {I : Type v} (b : HilbertBasis I ℂ H) (rho : State b)
    {r : ℕ} (A : QubitFactor r H) (y : Qubits r) : ℝ :=
  (operatorTrace b ((A (xProjector r y)).comp rho.val.val)).re

/-- PDF p.4(a): arbitrary finite measurements on Eve, rather than on the key.
Commutation with the full key matrix algebra is exactly locality on E.
Public transcript/permutation registers are part of this unrestricted E. -/
structure EveMeasurement {r : ℕ} (A : QubitFactor r H) (n : ℕ) where
  effect : Fin n → H →L[ℂ] H
  positive : ∀ z, (effect z).IsPositive
  complete : ∑ z, effect z = 1
  eveOnly : ∀ z (B : Matrix (Qubits r) (Qubits r) ℂ),
    (effect z).comp (A B) = (A B).comp (effect z)

/-- PDF p.4(a): the joint classical law after Eve's actual measurement. -/
def measuredKeyLaw {I : Type v} (b : HilbertBasis I ℂ H) (rho : State b)
    {r n : ℕ} (A : QubitFactor r H) (M : EveMeasurement A n)
    (yz : Qubits r × Fin n) : ℝ :=
  (operatorTrace b ((A (xProjector r yz.1)).comp
    ((M.effect yz.2).comp rho.val.val))).re

/-- PDF p.4(a): accessible information in bits, optimized over all finite
POVMs on E. For a finite key this supremum also includes arbitrary-outcome
measurements by finite coarse-graining; no maximum or finite E is assumed.
The set is nonempty (one outcome), and bounded above by r for normalized states. -/
def accessibleKeyInfo {I : Type v} (b : HilbertBasis I ℂ H) (rho : State b)
    {r : ℕ} (A : QubitFactor r H) : ℝ :=
  sSup {t | ∃ n : ℕ, ∃ M : EveMeasurement A n,
    t = mutualInfoBits (measuredKeyLaw b rho A M)}

/-- PDF p.3, Eq.(5): squared Uhlmann fidelity on actual positive trace-class
arguments. Unlike frozen rootFidelity, this includes the final square. -/
def squaredHilbertFidelity {I : Type v} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) : ℝ :=
  ((operatorTrace b (cfc Real.sqrt
    ((cfc Real.sqrt rho).comp (sigma.comp (cfc Real.sqrt rho))))).re) ^ 2

example {r : ℕ} (A : QubitFactor r H) : Nonempty (EveMeasurement A 1) := by
  refine ⟨⟨fun _ => 1, fun _ => ContinuousLinearMap.isPositive_one, ?_, ?_⟩⟩
  · simp
  · intro z B
    ext x
    rfl

example {r : ℕ} : keyEntropy (fun _ : Qubits r => (0 : ℝ)) = 0 := by
  simp [QAlgorithms.Papers.Independent.Advance50.P18.keyEntropy]

/-! ### The constructed virtual circuit -/

/-- PDF p.2, Eq.(2): the injective linear encoder, the actual decoder and
its correctable error set. No worst-case Hamming-ball correction is assumed. -/
structure CorrectableEncoder (N r : ℕ) where
  encoder : (Qubits r) →ₗ[Bool] (Qubits N)
  injective : Function.Injective encoder
  decoder : Qubits N → Qubits r
  errors : Set (Qubits N)
  correct : ∀ y x, x ∈ errors → decoder (encoder y + x) = y

/-- PDF p.2: G transpose, constructed from G, so its kernel is the dual code. -/
def transposeEncoder {N r : ℕ} (C : CorrectableEncoder N r) (x : Qubits N) : Qubits r :=
  fun i => dotBits x (C.encoder (fun j => decide (j = i)))

/-- PDF p.3, Eq.(7): the actual U1, as a Z-basis permutation matrix. -/
def circuitU1 {N r : ℕ} (C : CorrectableEncoder N r) :
    Matrix (Qubits N × Qubits r) (Qubits N × Qubits r) ℂ :=
  fun p q => if p = (q.1 + C.encoder q.2, q.2) then 1 else 0

/-- PDF p.3, Eq.(8): the actual U2, using the actual, possibly nonlinear f. -/
def circuitU2 {N r : ℕ} (C : CorrectableEncoder N r) :
    Matrix (Qubits N × Qubits r) (Qubits N × Qubits r) ℂ :=
  fun p q => if p = (q.1, q.2 + C.decoder q.1) then 1 else 0

/-- PDF p.3: U = U2 U1, with U1 applied first. -/
def virtualCircuit {N r : ℕ} (C : CorrectableEncoder N r) :
    Matrix (Qubits N × Qubits r) (Qubits N × Qubits r) ℂ :=
  circuitU2 C * circuitU1 C

/-- PDF pp.3–4: the actual isometry appending |0>_X and applying U. -/
def virtualIsometry {N r : ℕ} (C : CorrectableEncoder N r) :
    Matrix (Qubits N × Qubits r) (Qubits N) ℂ :=
  fun p x => ∑ y, virtualCircuit C p (x, y) * xBasisVector r 0 y

/-- PDF pp.3–4: Heisenberg key effect of the constructed virtual circuit.
An equality of these effects retains the joint law with every Eve measurement. -/
def virtualKeyEffect {N r : ℕ} (C : CorrectableEncoder N r) (y : Qubits r) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  (virtualIsometry C).conjTranspose *
    Matrix.kronecker (1 : Matrix (Qubits N) (Qubits N) ℂ) (xProjector r y) *
    virtualIsometry C

/-- PDF pp.2–3, Protocol 3(8): X measurement followed by the G-transpose key map. -/
def directKeyEffect {N r : ℕ} (C : CorrectableEncoder N r) (y : Qubits r) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  ∑ x, if transposeEncoder C x = y then xProjector N x else 0

/-- PDF p.3: the projector onto the actual correctable Z error support. -/
def correctableProjector {N r : ℕ} (C : CorrectableEncoder N r) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  Matrix.diagonal (fun x => if x ∈ C.errors then 1 else 0)

/-- PDF p.4: the actual output state of ancilla Q for a given S marginal. -/
def virtualOutput {N r : ℕ} (C : CorrectableEncoder N r)
    (rho : Matrix (Qubits N) (Qubits N) ℂ) : Matrix (Qubits r) (Qubits r) ℂ :=
  traceLeft (virtualCircuit C * Matrix.kronecker rho (xProjector r 0) *
    (virtualCircuit C).conjTranspose)

/-- PDF p.3, Eq.(4): normalized projected joint state, used only for q > 0. -/
def projectedJointState {I : Type v} (b : HilbertBasis I ℂ H)
    (rho : State b) (P : H →L[ℂ] H) : H →L[ℂ] H :=
  (((operatorTrace b (P.comp rho.val.val)).re)⁻¹ : ℂ) •
    P.comp (rho.val.val.comp P)

example {N r : ℕ} (C : CorrectableEncoder N r) (x : Qubits N) (y : Qubits r) :
    circuitU1 C (x + C.encoder y, y) (x, y) = 1 := by
  simp [circuitU1]

example {N r : ℕ} (C : CorrectableEncoder N r) (x : Qubits N) (y : Qubits r) :
    circuitU2 C (x, y + C.decoder x) (x, y) = 1 := by
  simp [circuitU2]

/-- PDF p.4, Eq.(13): joint law for K=W+Y and (W,Z), where Eve can choose
her measurement after reading the independently sampled public uniform W. -/
def maskedJointLaw {I : Type v} (b : HilbertBasis I ℂ H) (rho : State b)
    {r n : ℕ} (A : QubitFactor r H) (M : Qubits r → EveMeasurement A n)
    (kwz : Qubits r × (Qubits r × Fin n)) : ℝ :=
  ((2 : ℝ) ^ r)⁻¹ *
    measuredKeyLaw b rho A (M kwz.2.1) (kwz.1 + kwz.2.1, kwz.2.2)

/-- PDF p.4: accessible information including the public mask register W. -/
def maskedAccessibleInfo {I : Type v} (b : HilbertBasis I ℂ H) (rho : State b)
    {r : ℕ} (A : QubitFactor r H) : ℝ :=
  sSup {t | ∃ n : ℕ, ∃ M : Qubits r → EveMeasurement A n,
    t = mutualInfoBits (maskedJointLaw b rho A M)}

/-- PDF p.4: marginal law of the final, publicly shifted key; W is not secret. -/
def maskedKeyLaw {r : ℕ} (p : Qubits r → ℝ) (k : Qubits r) : ℝ :=
  ∑ w, ((2 : ℝ) ^ r)⁻¹ * p (k + w)

example {I : Type v} (b : HilbertBasis I ℂ H) (rho : State b)
    {r n : ℕ} (A : QubitFactor r H) (M : Qubits r → EveMeasurement A n)
    (k w : Qubits r) (z : Fin n) :
    maskedJointLaw b rho A M (k, w, z) =
      ((2 : ℝ) ^ r)⁻¹ * measuredKeyLaw b rho A (M w) (k + w, z) := by
  rfl

/-- PDF p.4: the accepted BB84 encoding specialized to one qubit, reindexed
from one-bit strings to Bool. Basis false is Z and true is X; bit false is
the +1 eigenstate. The wrapper changes only the register index type. -/
def singleQubitBB84Vector (a g : Bool) : EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 fun z =>
    QAlgorithms.Papers.Independent.Claimed50.P31.bb84Vector
      (fun _ : Fin 1 => g) (fun _ => a) (fun _ => z)

/-- PDF p.4: the full emitted two-copy state, retaining the copy available to Eve. -/
def identicalCopyState (a g : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  pureDensity (tensorVec (singleQubitBB84Vector a g) (singleQubitBB84Vector a g))

/-- PDF pp.1,4, Eq.(1): basis averages with actual unbiased joint weights
p[a,g]=1/4, not conditional weights 1/2. -/
def copiedBasisAverage (a : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  ∑ g : Bool, (1 / 4 : ℂ) • identicalCopyState a g

example (g : Bool) : singleQubitBB84Vector false g = ket g := by
  ext z
  simp [singleQubitBB84Vector,
    QAlgorithms.Papers.Independent.Claimed50.P31.bb84Vector, ket, eq_comm]

example (a g : Bool) : identicalCopyState a g =
    pureDensity (tensorVec (singleQubitBB84Vector a g) (singleQubitBB84Vector a g)) := by
  rfl

/-- PDF p.4: an occasional identical-copy emission, with the one- and two-copy
sectors distinguished in the full emitted system. The probability t is independent
of basis and bit, and the theorem guards 0 < t <= 1. -/
def occasionalCopyState (t : ℝ) (a g : Bool) :
    Matrix (Bool ⊕ (Bool × Bool)) (Bool ⊕ (Bool × Bool)) ℂ :=
  fun p q => match p, q with
    | Sum.inl i, Sum.inl j => ((1 - t : ℝ) : ℂ) * pureDensity (singleQubitBB84Vector a g) i j
    | Sum.inr i, Sum.inr j => (t : ℂ) * identicalCopyState a g i j
    | _, _ => 0

/-- PDF pp.1,4: full weighted average, retaining the nonzero two-copy sector. -/
def occasionalCopyAverage (t : ℝ) (a : Bool) :
    Matrix (Bool ⊕ (Bool × Bool)) (Bool ⊕ (Bool × Bool)) ℂ :=
  ∑ g : Bool, (1 / 4 : ℂ) • occasionalCopyState t a g

example (a g : Bool) (i j : Bool × Bool) :
    occasionalCopyState 0 a g (Sum.inr i) (Sum.inr j) = 0 := by
  simp [occasionalCopyState]

end QAlgorithms.Papers.Independent.Intakenext100.P04


