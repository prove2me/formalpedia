-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P40
-- name    : QAlgorithms_Papers_Independent_Next46_P40
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:47:38.481985+00:00
-- url     : https://prove2.me/theorems/3ec35704-0194-4691-86eb-7c766398c8bd
-- title:
--   Definitions for Entanglement-Assisted Capacity of Quantum Multiple-Access Channels
-- statement:
--   The objects the formalized statements of *Entanglement-Assisted Capacity of Quantum Multiple-Access Channels* (arXiv:quant-ph/0511228) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `leftTensor`: PDF p.2: identity on the right reference, channel on the left factor. Every off-diagonal reference block is retained.
--   - `IsProjector`: PDF pp.3--4: orthogonal projector in basis coordinates.
--   - `coherentMeasurement`: PDF p.3, Lemma 1 proof: the square-root measurement isometry, with the outcome register last. Its positive square roots fix relative phases.
--   - `appendLabel`: PDF p.3: append the classical basis label to a pure state.
--   - `measuredPurification`: PDF p.3: coherent measurement acts only on the measured part of a purification.
--   - `marginalBC`: PDF p.3: the BC marginal of a state ordered (A B) C.
--   - `cmiACB`: PDF p.3: conditional mutual information I(A;C|B), for the order (A B) C.
--   - `cmiBCA`: PDF p.3: conditional mutual information I(B;C|A), for the order (A B) C.
--   - `productPurification`: PDF p.6, (42): two independent pure sender-reference resources, regrouped with the references first and the inputs last.
--   - `qmacTheta`: PDF p.6, (42): the entropic state is constructed by the channel.
--   - `qmacBlockChannel`: PDF p.6: n memoryless uses; senders may be entangled within their own block. The two input blocks are regrouped into a sequence of input pairs.
--   - `EAMACCode`: PDF p.6: an actual finite EA QMAC code, chosen before both messages. The two pure shared resources are independent; arbitrary local CPTP encoders act on the sender halves, followed by one receiver POVM. No communication other than n uses of M is present. Ancilla dimensions may depend on n.
--   - `macReceiverState`: PDF p.6, (41): the receiver state, including both retained resource halves.
--   - `macCorrect`: PDF p.6, (41): maximum joint message-pair error, not average error.
--   - `eaAchievable`: PDF p.6: all sufficiently large positive blocklengths, with an arbitrary positive rate slack and error tolerance. Integer message counts avoid 2^(nR) being implicitly required to be an integer.
--   - `eaMacCapacityRegion`: PDF p.6: operational capacity is the closure of the achievable pairs.
--   - `entropicRegion`: PDF p.6, (42)--(43): one-letter union over independent input states, represented by their normalized purifications. References have the same finite basis size as the corresponding inputs, sufficient for all densities.
--   - `regularizedEAMacRegion`: PDF pp.6--7, (44): regularized union and closure, with no added convex hull.
--   - `collectivePhaseUnitary`: PDF p.9, (59), with the plus-sign phase convention of (14), p.3.
--   - `collectivePhaseFlip`: PDF p.9, (59): the same random phase acts on both senders' inputs.
--   - `shannonBits`: PDF p.9: Shannon entropy in bits, with the zero terms equal to zero.
--   - `dephasingIsometry`: PDF p.12: the generalized dephasing Stinespring isometry in coordinates. The environmental vectors need not be orthogonal.
--   - `generalizedDephasing`: PDF p.12: generalized dephasing is the above dilation with E traced out.
--   - `diagonalPart`: PDF p.12: complete dephasing in the fixed basis.
--   - `diagonalPurification`: PDF p.12: canonical purification of the diagonal of a density matrix.
--   - `pairTensorPower`: PDF pp.4--5: n copies of the fixed pure shared resource, regrouped into sender and receiver blocks. The value at n=0 is the scalar unit state.
--   - `fullChannelVector`: PDF p.5, (38): the full pure output retains the inaccessible E block. Order is E^n (B^n R^n), where R is Bob's share of the initial resource. The unitary V acts on Alice's block before the memoryless channel dilation.
--   - `instrumentSum`: PDF p.4: discard only the classical output of an instrument. All quantum outputs, including the reference to the channel environment, remain available to the restoration criterion.
--   - `SingleEACode`: PDF p.4: the finite code consists of a message-independent family of unitary encoders and a receiver instrument, not merely a success number.
--   - `singleEACorrect`: PDF p.4, conditions (i), (ii), (iii), all for every message. The restoration channel is the NONSELECTIVE instrument tensored with id_E.
--   - `CoherentEACode`: PDF p.5, (37)--(39): finite coherent EA implementation. The transferred receiver unitaries describe (38); inverse controlled transfer implements W. All quantum registers are A'^n, R^n, B^n, E^n and J=Fin m; the optional coherently controlled sender label K=Fin m and any external reference F=Fin s are retained below.
--   - `explicitCoherentDecoder`: PDF p.5: D''=(W tensor id_B)D', with D' the positive-square-root measurement isometry. This is a computed map, not an unconstrained decoder.
--   - `coherentDecodedVector`: PDF p.5, (39): the complete pure decoded state, with E unmeasured.
--   - `packingError`: PDF p.5: error parameter supplied by packing. tau is the internal typicality tolerance, eta its internal rate slack; neither is the final accuracy.
--   - `coherentEACorrect`: PDF p.5, (38)--(39), including the real-positive overlaps from Lemma 1. The transfer identity is exact on the initial vector, so no message-dependent phase is hidden by a density-matrix equality.
--   - `coherentlyControlledOutput`: PDF pp.5--6: coherify while retaining the sender's label K, with J the receiver's coherent output. An arbitrary external reference F=Fin s is also retained, with the code fixed independently of its size.
--   - `coherentlyControlledTarget`: PDF p.5, (39): ideal coherent output has message-independent quantum state, including the inaccessible environment. Sender label K and external reference F=Fin s are retained.
-- source:
--   Entanglement-Assisted Capacity of Quantum Multiple-Access Channels, arXiv:quant-ph/0511228v2, https://arxiv.org/abs/quant-ph/0511228v2

import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInstruments
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

/-!
Statements from Hsieh--Devetak--Winter, arXiv:quant-ph/0511228v2.
All new objects are local to this paper. Finite basis coordinates represent nonzero
quantum registers. Distances are the full trace norm; entropies are in bits.
Compilation is pending the mechanical batch handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P40

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation marginalRB associate)

variable {A B C E R S : Type*}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype R] [Fintype S]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]
variable [DecidableEq R] [DecidableEq S]

/-!
Repair provenance: the accepted P19 mutualInformation is exactly the base-two
bipartite entropy formula used here. Its marginalRB after associate computes the
AC marginal of our (A B) C ordering, without a second partial-trace definition.
The frozen namesakes eaCapacity (Dependency50.P23) and regularizedRegion
(Claimed50.P20) are respectively a scalar single-sender capacity and a signed
three-resource region, not this two-sender maximum-error region. The QMAC names
below retain its independently defined operational and entropic regions.
qmacBlockChannel only regroups the two sender blocks around frozen piSuperop;
frozen Dependency50.P41.blockChannel instead uses flat Fin(a^n) coordinates.
Classical equality is local to this namespace and supplies equality on the full
coherent output index, including the finite function registers.
-/

/-- PDF p.2: identity on the right reference, channel on the left factor.
Every off-diagonal reference block is retained. -/
def leftTensor (N : Superop A B) : Superop (A × R) (B × R) :=
  fun X => Matrix.of fun p q =>
    N (Matrix.of fun a a2 => X (a, p.2) (a2, q.2)) p.1 q.1

/-- PDF pp.3--4: orthogonal projector in basis coordinates. -/
def IsProjector (P : Matrix A A ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- PDF p.3, Lemma 1 proof: the square-root measurement isometry,
with the outcome register last. Its positive square roots fix relative phases. -/
def coherentMeasurement {K : ℕ} (L : Fin K → Matrix A A ℂ) :
    Matrix (A × Fin K) A ℂ :=
  Matrix.of fun p a => cfc Real.sqrt (L p.2) p.1 a

/-- PDF p.3: append the classical basis label to a pure state. -/
def appendLabel {K : ℕ} (v : EuclideanSpace ℂ A) (k : Fin K) :
    EuclideanSpace ℂ (A × Fin K) :=
  WithLp.toLp 2 fun p => if p.2 = k then v p.1 else 0

/-- PDF p.3: coherent measurement acts only on the measured part of a purification. -/
def measuredPurification {K : ℕ} (D : Matrix (A × Fin K) A ℂ)
    (v : EuclideanSpace ℂ (R × A)) : EuclideanSpace ℂ ((R × A) × Fin K) :=
  WithLp.toLp 2 fun p => ∑ a, D (p.1.2, p.2) a * v (p.1.1, a)

/-- PDF p.3: the BC marginal of a state ordered (A B) C. -/
def marginalBC (X : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    Matrix (B × C) (B × C) ℂ :=
  Matrix.of fun p q => ∑ a, X ((a, p.1), p.2) ((a, q.1), q.2)

/-- PDF p.3: conditional mutual information I(A;C|B), for the order (A B) C. -/
def cmiACB (X : Matrix ((A × B) × C) ((A × B) × C) ℂ) : ℝ :=
  vnEntropy (traceRight X) + vnEntropy (marginalBC X) - vnEntropy X -
    vnEntropy (traceLeft (traceRight X))

/-- PDF p.3: conditional mutual information I(B;C|A), for the order (A B) C. -/
def cmiBCA (X : Matrix ((A × B) × C) ((A × B) × C) ℂ) : ℝ :=
  vnEntropy (traceRight X) + vnEntropy (marginalRB (associate X)) - vnEntropy X -
    vnEntropy (traceRight (traceRight X))

/-- PDF p.6, (42): two independent pure sender-reference resources, regrouped
with the references first and the inputs last. -/
def productPurification (v : EuclideanSpace ℂ (A × A))
    (w : EuclideanSpace ℂ (B × B)) :
    Matrix ((A × B) × (A × B)) ((A × B) × (A × B)) ℂ :=
  Matrix.of fun p q =>
    pureDensity v (p.1.1, p.2.1) (q.1.1, q.2.1) *
    pureDensity w (p.1.2, p.2.2) (q.1.2, q.2.2)

/-- PDF p.6, (42): the entropic state is constructed by the channel. -/
def qmacTheta (M : Superop (A × B) C)
    (v : EuclideanSpace ℂ (A × A)) (w : EuclideanSpace ℂ (B × B)) :
    Matrix ((A × B) × C) ((A × B) × C) ℂ :=
  idTensorSuperop M (productPurification v w)

/-- PDF p.6: n memoryless uses; senders may be entangled within their own block.
The two input blocks are regrouped into a sequence of input pairs. -/
def qmacBlockChannel (M : Superop (A × B) C) (n : ℕ) :
    Superop ((Fin n → A) × (Fin n → B)) (Fin n → C) :=
  fun X => piSuperop (fun _ : Fin n => M)
    (Matrix.of fun x y => X (fun i => (x i).1, fun i => (x i).2)
      (fun i => (y i).1, fun i => (y i).2))

/-- PDF p.6: an actual finite EA QMAC code, chosen before both messages.
The two pure shared resources are independent; arbitrary local CPTP encoders
act on the sender halves, followed by one receiver POVM. No communication
other than n uses of M is present. Ancilla dimensions may depend on n. -/
structure EAMACCode (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] (n m1 m2 : ℕ) where
  a1 : ℕ
  c1 : ℕ
  a2 : ℕ
  c2 : ℕ
  a1_pos : 0 < a1
  c1_pos : 0 < c1
  a2_pos : 0 < a2
  c2_pos : 0 < c2
  gamma1 : EuclideanSpace ℂ (Fin a1 × Fin c1)
  gamma2 : EuclideanSpace ℂ (Fin a2 × Fin c2)
  gamma1_unit : ‖gamma1‖ = 1
  gamma2_unit : ‖gamma2‖ = 1
  enc1 : Fin m1 → Superop (Fin a1) (Fin n → A)
  enc2 : Fin m2 → Superop (Fin a2) (Fin n → B)
  enc1_channel : ∀ k, IsChannel (enc1 k)
  enc2_channel : ∀ l, IsChannel (enc2 l)
  measurement : (Fin m1 × Fin m2) →
    Matrix ((Fin c1 × Fin c2) × (Fin n → C)) ((Fin c1 × Fin c2) × (Fin n → C)) ℂ
  measurement_complete : IsPOVM measurement

/-- PDF p.6, (41): the receiver state, including both retained resource halves. -/
def macReceiverState {n m1 m2 : ℕ} (M : Superop (A × B) C)
    (code : EAMACCode A B C n m1 m2) (k : Fin m1) (l : Fin m2) :
    Matrix ((Fin code.c1 × Fin code.c2) × (Fin n → C))
      ((Fin code.c1 × Fin code.c2) × (Fin n → C)) ℂ :=
  let X1 := leftTensor (R := Fin code.c1) (code.enc1 k) (pureDensity code.gamma1)
  let X2 := leftTensor (R := Fin code.c2) (code.enc2 l) (pureDensity code.gamma2)
  idTensorSuperop (qmacBlockChannel M n) (Matrix.of fun p q =>
    X1 (p.2.1, p.1.1) (q.2.1, q.1.1) * X2 (p.2.2, p.1.2) (q.2.2, q.1.2))

/-- PDF p.6, (41): maximum joint message-pair error, not average error. -/
def macCorrect {n m1 m2 : ℕ} (M : Superop (A × B) C)
    (code : EAMACCode A B C n m1 m2) (eps : ℝ) : Prop :=
  ∀ k l, 1 - eps ≤ effectProb (code.measurement (k, l)) (macReceiverState M code k l)

/-- PDF p.6: all sufficiently large positive blocklengths, with an arbitrary
positive rate slack and error tolerance. Integer message counts avoid 2^(nR)
being implicitly required to be an integer. -/
def eaAchievable (M : Superop (A × B) C) (rate : ℝ × ℝ) : Prop :=
  0 ≤ rate.1 ∧ 0 ≤ rate.2 ∧
  ∀ eps : ℝ, 0 < eps → ∀ delta : ℝ, 0 < delta →
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∃ m1 m2 : ℕ, 0 < m1 ∧ 0 < m2 ∧
      ∃ code : EAMACCode A B C n m1 m2,
        (n : ℝ) * (rate.1 - delta) ≤ Real.logb 2 (m1 : ℝ) ∧
        (n : ℝ) * (rate.2 - delta) ≤ Real.logb 2 (m2 : ℝ) ∧ macCorrect M code eps

/-- PDF p.6: operational capacity is the closure of the achievable pairs. -/
def eaMacCapacityRegion (M : Superop (A × B) C) : Set (ℝ × ℝ) :=
  closure {r | eaAchievable M r}

/-- PDF p.6, (42)--(43): one-letter union over independent input states,
represented by their normalized purifications. References have the same
finite basis size as the corresponding inputs, sufficient for all densities. -/
def entropicRegion (M : Superop (A × B) C) : Set (ℝ × ℝ) :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (v : EuclideanSpace ℂ (A × A)) (w : EuclideanSpace ℂ (B × B)),
      ‖v‖ = 1 ∧ ‖w‖ = 1 ∧
      r.1 ≤ cmiACB (qmacTheta M v w) ∧ r.2 ≤ cmiBCA (qmacTheta M v w) ∧
      r.1 + r.2 ≤ mutualInformation (qmacTheta M v w)}

/-- PDF pp.6--7, (44): regularized union and closure, with no added convex hull. -/
def regularizedEAMacRegion (M : Superop (A × B) C) : Set (ℝ × ℝ) :=
  closure {r | ∃ n : ℕ, 0 < n ∧
    ((n : ℝ) * r.1, (n : ℝ) * r.2) ∈ entropicRegion (qmacBlockChannel M n)}

/-- PDF p.9, (59), with the plus-sign phase convention of (14), p.3. -/
def collectivePhaseUnitary {d : ℕ} (k : Fin d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.diagonal fun p => Complex.exp
    ((2 * Real.pi * ((p.1.val : ℝ) + (p.2.val : ℝ)) * (k.val : ℝ) / (d : ℝ) : ℝ) * Complex.I)

/-- PDF p.9, (59): the same random phase acts on both senders' inputs. -/
def collectivePhaseFlip {d : ℕ} (p : Fin d → ℝ) :
    Superop (Fin d × Fin d) (Fin d × Fin d) :=
  fun X => ∑ k, (p k : ℂ) • conjSuperop (collectivePhaseUnitary k) X

/-- PDF p.9: Shannon entropy in bits, with the zero terms equal to zero. -/
def shannonBits {d : ℕ} (p : Fin d → ℝ) : ℝ :=
  -∑ k, p k * Real.logb 2 (p k)

/-- PDF p.12: the generalized dephasing Stinespring isometry in coordinates.
The environmental vectors need not be orthogonal. -/
def dephasingIsometry (env : A → EuclideanSpace ℂ E) : Matrix (A × E) A ℂ :=
  Matrix.of fun p a => if p.1 = a then env a p.2 else 0

/-- PDF p.12: generalized dephasing is the above dilation with E traced out. -/
def generalizedDephasing (env : A → EuclideanSpace ℂ E) : Superop A A :=
  fun X => traceRight (conjSuperop (dephasingIsometry env) X)

/-- PDF p.12: complete dephasing in the fixed basis. -/
def diagonalPart (X : Matrix A A ℂ) : Matrix A A ℂ :=
  Matrix.diagonal fun a => X a a

/-- PDF p.12: canonical purification of the diagonal of a density matrix. -/
def diagonalPurification (X : Matrix A A ℂ) : EuclideanSpace ℂ (A × A) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then (Real.sqrt (X p.1 p.1).re : ℂ) else 0

/-- Sanity: a right reference is retained even on an off-diagonal input block. -/
example (X : Matrix (A × R) (A × R) ℂ) :
    leftTensor (fun Y : Matrix A A ℂ => Y) X = X := by
  ext p q
  rfl

/-- Sanity: a basis-product purification has its expected unit diagonal entry. -/
example (a : A) (b : B) :
    productPurification (ket (a, a)) (ket (b, b)) ((a, b), (a, b)) ((a, b), (a, b)) = 1 := by
  simp [productPurification, pureDensity, ket]

/-- Sanity: complete dephasing leaves every diagonal entry unchanged. -/
example (X : Matrix A A ℂ) (a : A) : diagonalPart X a a = X a a := by
  simp [diagonalPart]

/-- Sanity: the named environmental vector appears on the matching basis column. -/
example (env : A → EuclideanSpace ℂ E) (a : A) (e : E) :
    dephasingIsometry env (a, e) a = env a e := by
  simp [dephasingIsometry]

/-- PDF pp.4--5: n copies of the fixed pure shared resource, regrouped into
sender and receiver blocks. The value at n=0 is the scalar unit state. -/
def pairTensorPower (n : ℕ) (v : EuclideanSpace ℂ (A × R)) :
    EuclideanSpace ℂ ((Fin n → A) × (Fin n → R)) :=
  WithLp.toLp 2 fun p => ∏ i, v (p.1 i, p.2 i)

/-- PDF p.5, (38): the full pure output retains the inaccessible E block.
Order is E^n (B^n R^n), where R is Bob's share of the initial resource.
The unitary V acts on Alice's block before the memoryless channel dilation. -/
def fullChannelVector (U : Matrix (B × E) A ℂ) (n : ℕ)
    (V : Matrix (Fin n → A) (Fin n → A) ℂ) (v : EuclideanSpace ℂ (A × R)) :
    EuclideanSpace ℂ ((Fin n → E) × ((Fin n → B) × (Fin n → R))) :=
  WithLp.toLp 2 fun p => ∑ x : Fin n → A,
    (∏ i, U (p.2.1 i, p.1 i) (x i)) *
      (∑ y : Fin n → A, V x y * pairTensorPower n v (y, p.2.2))

/-- PDF p.4: discard only the classical output of an instrument.
All quantum outputs, including the reference to the channel environment,
remain available to the restoration criterion. -/
def instrumentSum {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (D : CopyMeasurements.QuantumInstrument I O) : Superop I I :=
  fun X => ∑ k, CopyMeasurements.instrumentBranch D k X

/-- PDF p.4: the finite code consists of a message-independent family of
unitary encoders and a receiver instrument, not merely a success number. -/
structure SingleEACode (A B R : Type*) [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R] (n m : ℕ) where
  encode : Fin m → Matrix.unitaryGroup (Fin n → A) ℂ
  decode : CopyMeasurements.QuantumInstrument ((Fin n → B) × (Fin n → R)) (Fin m)

/-- PDF p.4, conditions (i), (ii), (iii), all for every message.
The restoration channel is the NONSELECTIVE instrument tensored with id_E. -/
def singleEACorrect {n m : ℕ} (U : Matrix (B × E) A ℂ)
    (v : EuclideanSpace ℂ (A × R)) (code : SingleEACode A B R n m) (eps : ℝ) : Prop :=
  ∀ k,
    let X := pureDensity (fullChannelVector U n (code.encode k : Matrix _ _ ℂ) v)
    let rho := traceRight (pureDensity (pairTensorPower n v))
    1 - eps ≤ (CopyMeasurements.instrumentBranch code.decode k (traceLeft X)).trace.re ∧
    conjSuperop (code.encode k : Matrix _ _ ℂ) rho = rho ∧
    traceNorm (idTensorSuperop (instrumentSum code.decode) X -
      pureDensity (fullChannelVector U n (1 : Matrix _ _ ℂ) v)) ≤ eps

/-- PDF p.5, (37)--(39): finite coherent EA implementation. The transferred
receiver unitaries describe (38); inverse controlled transfer implements W.
All quantum registers are A'^n, R^n, B^n, E^n and J=Fin m; the optional
coherently controlled sender label K=Fin m and any external reference F=Fin s are retained below. -/
structure CoherentEACode (A B R : Type*) [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R] (n m : ℕ) where
  encode : Fin m → Matrix.unitaryGroup (Fin n → A) ℂ
  transfer : Fin m → Matrix.unitaryGroup (Fin n → R) ℂ
  measurement : Fin m → Matrix ((Fin n → B) × (Fin n → R))
    ((Fin n → B) × (Fin n → R)) ℂ
  measurement_complete : IsPOVM measurement

/-- PDF p.5: D''=(W tensor id_B)D', with D' the positive-square-root
measurement isometry. This is a computed map, not an unconstrained decoder. -/
def explicitCoherentDecoder {n m : ℕ} (code : CoherentEACode A B R n m) :
    Matrix ((((Fin n → B) × (Fin n → R)) × Fin m))
      ((Fin n → B) × (Fin n → R)) ℂ :=
  Matrix.of fun p q =>
    (Matrix.kronecker (1 : Matrix (Fin n → B) (Fin n → B) ℂ)
      (code.transfer p.2 : Matrix (Fin n → R) (Fin n → R) ℂ)ᴴ *
        cfc Real.sqrt (code.measurement p.2)) p.1 q

/-- PDF p.5, (39): the complete pure decoded state, with E unmeasured. -/
def coherentDecodedVector {n m : ℕ} (U : Matrix (B × E) A ℂ)
    (v : EuclideanSpace ℂ (A × R)) (code : CoherentEACode A B R n m) (k : Fin m) :
    EuclideanSpace ℂ (((Fin n → E) × ((Fin n → B) × (Fin n → R))) × Fin m) :=
  WithLp.toLp 2 fun p => ∑ z,
    explicitCoherentDecoder code (p.1.2, p.2) z *
      fullChannelVector U n (code.encode k : Matrix _ _ ℂ) v (p.1.1, z)

/-- PDF p.5: error parameter supplied by packing. tau is the internal
 typicality tolerance, eta its internal rate slack; neither is the final accuracy. -/
def packingError (tau eta : ℝ) (n : ℕ) : ℝ :=
  4 * (tau + Real.sqrt (8 * tau)) + 16 * (2 : ℝ) ^ (-(n : ℝ) * eta)

/-- PDF p.5, (38)--(39), including the real-positive overlaps from Lemma 1.
The transfer identity is exact on the initial vector, so no message-dependent
phase is hidden by a density-matrix equality. -/
def coherentEACorrect {n m : ℕ} (U : Matrix (B × E) A ℂ)
    (v : EuclideanSpace ℂ (A × R)) (code : CoherentEACode A B R n m) (err : ℝ) : Prop :=
  (explicitCoherentDecoder code)ᴴ * explicitCoherentDecoder code = 1 ∧
  ∀ k,
    let V := (code.encode k : Matrix (Fin n → A) (Fin n → A) ℂ)
    let T := (code.transfer k : Matrix (Fin n → R) (Fin n → R) ℂ)
    let rho := traceRight (pureDensity (pairTensorPower n v))
    let target := appendLabel (fullChannelVector U n (1 : Matrix _ _ ℂ) v) k
    let actual := coherentDecodedVector U v code k
    conjSuperop V rho = rho ∧
    (∀ x r, (∑ y, V x y * pairTensorPower n v (y, r)) =
      ∑ s, T r s * pairTensorPower n v (x, s)) ∧
    1 - err ≤ effectProb (code.measurement k)
      (traceLeft (pureDensity (fullChannelVector U n V v))) ∧
    (inner ℂ target actual).im = 0 ∧ 1 - err ≤ (inner ℂ target actual).re ∧
    traceNorm (pureDensity actual - pureDensity target) ≤ Real.sqrt (8 * err)

/-- PDF pp.5--6: coherify while retaining the sender's label K, with J the
receiver's coherent output. An arbitrary external reference F=Fin s
is also retained, with the code fixed independently of its size. -/
def coherentlyControlledOutput {n m s : ℕ} (U : Matrix (B × E) A ℂ)
    (v : EuclideanSpace ℂ (A × R)) (code : CoherentEACode A B R n m)
    (amplitude : EuclideanSpace ℂ (Fin s × Fin m)) :
    EuclideanSpace ℂ ((Fin s × Fin m) × ((((Fin n → E) × ((Fin n → B) × (Fin n → R))) × Fin m))) :=
  WithLp.toLp 2 fun p => amplitude p.1 * coherentDecodedVector U v code p.1.2 p.2

/-- PDF p.5, (39): ideal coherent output has message-independent quantum
state, including the inaccessible environment. Sender label K and external
reference F=Fin s are retained. -/
def coherentlyControlledTarget {n m s : ℕ} (U : Matrix (B × E) A ℂ)
    (v : EuclideanSpace ℂ (A × R)) (amplitude : EuclideanSpace ℂ (Fin s × Fin m)) :
    EuclideanSpace ℂ ((Fin s × Fin m) × ((((Fin n → E) × ((Fin n → B) × (Fin n → R))) × Fin m))) :=
  WithLp.toLp 2 fun p => amplitude p.1 *
    appendLabel (fullChannelVector U n (1 : Matrix _ _ ℂ) v) p.1.2 p.2

/-- Sanity: zero copies of the shared resource form the scalar unit vector. -/
example (v : EuclideanSpace ℂ (A × R))
    (x : Fin 0 → A) (r : Fin 0 → R) : pairTensorPower 0 v (x, r) = 1 := by
  simp [pairTensorPower]

/-- Sanity: one copy has the original resource amplitudes. -/
example (v : EuclideanSpace ℂ (A × R)) (x : Fin 1 → A) (r : Fin 1 → R) :
    pairTensorPower 1 v (x, r) = v (x 0, r 0) := by
  simp [pairTensorPower]

/-- Sanity: an identity instrument does not discard its quantum state. -/
example (X : Matrix A A ℂ) :
    instrumentSum (CopyMeasurements.identityInstrument A) X = X := by
  simp [instrumentSum, CopyMeasurements.instrumentBranch,
    CopyMeasurements.identityInstrument, krausApply]

end QAlgorithms.Papers.Independent.Next46.P40


