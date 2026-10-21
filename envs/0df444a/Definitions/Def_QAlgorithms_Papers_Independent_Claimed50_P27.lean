-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27
-- name    : QAlgorithms_Papers_Independent_Claimed50_P27
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:14:43.978003+00:00
-- url     : https://prove2.me/theorems/f4954dc6-bee7-4f25-bc95-5cb6c241bc9a
-- title:
--   Definitions for Optimal cloning of unitary transformations
-- statement:
--   The objects the formalized statements of *Optimal cloning of unitary transformations* (arXiv:0804.0129) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PairReg`: PDF p.2: the two external d-dimensional registers, in B,E order.
--   - `CombReg`: PDF p.2: the one-slot network basis, in 0,1,2,3 wire order.
--   - `channelChoi`: PDF p.2: input-first unnormalized Choi operator, J(Phi)_(i,o),(j,p)=Phi(E_ij)_(o,p). This also explicitly fixes the permutation of the two target Choi copies.
--   - `onFirst`: PDF p.2, Fig.1a: apply Phi to the first wire while preserving all memory blocks.
--   - `DeviceCloner`: PDF p.1: a physical one-call cloner for arbitrary finite quantum devices. I can be one-dimensional for preparations; a POVM is represented by its classical-output measurement channel. Known devices may be implemented in the fixed preprocessing/postprocessing, which remain independent of the unknown label.
--   - `DeviceCloner.run`: PDF p.1: a single unknown-device invocation; discarded environments are already included in the CPTP pre/postprocessing maps.
--   - `OneCall`: PDF p.2, Fig.1a: specialize the general device circuit to a d-dimensional unitary slot. The memory and all processing are chosen before the unknown gate.
--   - `OneCall.run`: PDF p.2, Fig.1a: insert a unitary channel in the general one-use circuit.
--   - `CloningAdmissible`: PDF p.2, Eq.(3): positivity and both recursive trace constraints. Coordinates implement I_2 tensor R0 without reversing external wires.
--   - `insertedChoi`: PDF p.2, Eq.(2): insertion of one U; elementwise conjugation of the slot Choi vector gives the coefficients U_(k,i) conjugate(U_(l,j)).
--   - `targetChannel`: PDF p.2: target U tensor U on the external pair.
--   - `pointScore`: PDF p.2, Eq.(4): pointwise global channel fidelity, normalized by d^4. The target input dimension is d^2; both Choi operators are unnormalized.
--   - `combScore`: PDF p.2, Eq.(4): probability-Haar average on U(d), equivalent to SU(d) here. The integrand is continuous for a fixed finite comb, hence genuinely integrable.
--   - `familyScore`: PDF p.2, Eq.(4): the same score for an explicitly constructed channel family.
--   - `sectorProjector`: PDF p.3: true labels the symmetric (+) sector and false the antisymmetric (-) sector.
--   - `sectorDim`: PDF p.3: d_+=d(d+1)/2 and d_-=d(d-1)/2, in real arithmetic. All uses involving division have d>=2, so both dimensions are strictly positive.
--   - `optimalPre`: PDF p.3, Eq.(8): preprocessing, retaining the off-diagonal ± memory terms.
--   - `optimalPost`: PDF p.3, Eq.(9): postprocessing on the full two-dimensional memory. The coefficient is d/sqrt(d_i*d_j), including the off-diagonal sectors.
--   - `optimalFamily`: PDF p.3, Fig.1a: the stated preprocessing, one gate use, and postprocessing.
--   - `optimalFormula`: PDF p.3, Eq.(10): the resulting channel, with both sector indices retained.
--   - `cloningValue`: PDF p.3, Theorem 1: the exact optimal value (no rounded percentages).
--   - `covarianceAction`: PDF p.2, Eq.(5): V0^tensor2 tensor conjugate(V1) tensor conjugate(W2) tensor W3^tensor2. The stars here are elementwise conjugation, not adjoints.
--   - `CloningCovariant`: PDF p.2, Lemma 1: commuting with the full SU(d) x SU(d) action.
--   - `dephaseMemory`: PDF p.3: dephase only the memory, in the stated ± basis.
--   - `decoheredFamily`: PDF p.3: the physical circuit with the memory dephased after A.
--   - `decoheredFormula`: PDF p.3: the displayed decohered channel keeps just the diagonal sector terms.
--   - `randomFamily`: PDF p.3: apply U on B and an independent probability-Haar random gate on E.
--   - `trainingState`: PDF p.4: the normalized program obtained by applying U to half of a fixed probe.
--   - `learningFamily`: PDF p.4: deterministic learning: training is completed before the pair input arrives. An arbitrary U-independent decoder acts on input tensor program; its channel predicate includes any discarded ancillas/environment, without postselection.
--   - `LearnReg`: PDF p.4, Eq.(11): learning port order 1,((2B,2E,2A),3); H0 is one-dimensional.
--   - `LearningAdmissible`: PDF p.4, Eq.(11): a different causal constraint from cloning Eq.(3). The incoming register 2 has dimension d^3 and rho1 is a normalized density operator.
--   - `learningChoi`: PDF p.4, Fig.1b: slot insertion for learning, with external input order B,E.
--   - `learningScore`: PDF p.4: learning uses exactly the global channel score of Eq.(4).
--   - `estimationValue`: PDF p.4: exact restricted optimum, including the exceptional qubit value 5/16.
--   - `EstimateStrategy`: PDF pp.3–4: a one-call estimate-and-reprepare strategy. The arbitrary finite reference measure and integrable PSD POVM density include both discrete and continuous estimates. Outcomes are already the estimated gates, absorbing classical postprocessing.
--   - `estimateFamily`: PDF pp.3–4: measure the trained probe and apply the estimated gate twice. Weights are the actual Born probabilities, with no renormalization.
--   - `tensorDevices`: PDF p.1: tensor product of two devices, defined on every operator by the matrix-unit expansion, including entangled inputs and off-diagonal blocks.
--   - `ExactlyClonable`: PDF p.1: one common deterministic network implements the independent tensor square of every candidate, with equality on all operators, hence every joint input.
--   - `DeviceTest`: PDF p.1: a normalized one-call quantum discrimination procedure with arbitrary finite outcomes. A reference of input dimension suffices by purification/Schmidt compression; mixed probes and arbitrary POVMs include classical randomization. No unknown-device label is an argument of the chosen test.
--   - `DeviceTest.probability`: PDF p.1: the Born response of a physical one-call discrimination test.
--   - `worstError`: PDF p.1 and footnote [17], p.4: the worst conditional error, not an average-error objective with fixed equal priors. False identifies Phi0.
--   - `minimaxError`: PDF p.1: minimax one-call error. On the nonempty finite registers and CPTP candidates used below, the physical test space is nonempty and compact, and the continuous objective attains this infimum. These facts are conclusions below, not hypotheses assuming a discrimination procedure with the desired error.
--   - `PerfectlyDiscriminable`: PDF p.1 and footnote [18], p.4: a common one-call test identifies every label with certainty. Duplicate labels therefore must be removed before applying the duplicate-free finite-set formulation.
--   - `binaryDevices`: PDF p.1: the two known candidate devices; the label is not accessible to the network.
--   - `ClassicalOneCall`: PDF p.1: an ordinary classical one-evaluation circuit. Its query distribution and response-conditioned output kernel can depend on the two external inputs, but are fixed independently of the unknown permutation. Classical random memory is absorbed into these finite conditional kernels. There is no coherent oracle.
--   - `ClassicalOneCall.probability`: PDF p.1: output law after exactly one evaluation of a classical permutation.
-- source:
--   Optimal cloning of unitary transformations, arXiv:0804.0129v2, https://arxiv.org/abs/0804.0129v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Walk
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_ContinuousPOVMDensities

/-!
Statements from Chiribella, D'Ariano and Perinotti, arXiv:0804.0129v2.
All Choi operators are unnormalized and input-first. A pair is ordered B,E.
The cloning comb order is 0,(1,(2,3)); the learning order is 1,((2B,2E,2A),3).
The printed controlled-swap dilation is deferred: it lacks a memory Hadamard.
General finite quantum black boxes are represented by CPTP devices, including
preparations (one-dimensional input) and measuring devices (classical-output
channels). Their tests and cloning networks are physical one-call circuits.
-/

noncomputable section

open MeasureTheory QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.2: the two external d-dimensional registers, in B,E order. -/
abbrev PairReg (d : ℕ) := Fin d × Fin d

/-- PDF p.2: the one-slot network basis, in 0,1,2,3 wire order. -/
abbrev CombReg (d : ℕ) := PairReg d × (Fin d × (Fin d × PairReg d))

/-- PDF p.2: input-first unnormalized Choi operator, J(Phi)_(i,o),(j,p)=Phi(E_ij)_(o,p).
This also explicitly fixes the permutation of the two target Choi copies. -/
def channelChoi {I O : Type*} [DecidableEq I] (Phi : Superop I O) :
    Matrix (I × O) (I × O) ℂ :=
  fun a b => Phi (Matrix.single a.1 b.1 1) a.2 b.2

/-- PDF p.2, Fig.1a: apply Phi to the first wire while preserving all memory blocks. -/
def onFirst {I O M : Type*} (Phi : Superop I O) : Superop (I × M) (O × M) :=
  fun rho a b => Phi (fun i j => rho (i,a.2) (j,b.2)) a.1 b.1

/-- PDF p.1: a physical one-call cloner for arbitrary finite quantum devices.
I can be one-dimensional for preparations; a POVM is represented by its
classical-output measurement channel. Known devices may be implemented in the
fixed preprocessing/postprocessing, which remain independent of the unknown label. -/
structure DeviceCloner (I O : Type*) [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] where
  memoryDim : ℕ
  memory_pos : 0 < memoryDim
  pre : Superop (I × I) (I × Fin memoryDim)
  post : Superop (O × Fin memoryDim) (O × O)
  pre_channel : IsChannel pre
  post_channel : IsChannel post

/-- PDF p.1: a single unknown-device invocation; discarded environments are
already included in the CPTP pre/postprocessing maps. -/
def DeviceCloner.run {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (net : DeviceCloner I O)
    (Phi : Superop I O) : Superop (I × I) (O × O) :=
  net.post ∘ onFirst Phi ∘ net.pre

/-- PDF p.2, Fig.1a: specialize the general device circuit to a d-dimensional
unitary slot. The memory and all processing are chosen before the unknown gate. -/
abbrev OneCall (d : ℕ) := DeviceCloner (Fin d) (Fin d)

/-- PDF p.2, Fig.1a: insert a unitary channel in the general one-use circuit. -/
abbrev OneCall.run {d : ℕ} (net : OneCall d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    Superop (PairReg d) (PairReg d) :=
  DeviceCloner.run net (conjSuperop U.val)

/-- PDF p.2, Eq.(3): positivity and both recursive trace constraints.
Coordinates implement I_2 tensor R0 without reversing external wires. -/
def CloningAdmissible {d : ℕ} (R : Matrix (CombReg d) (CombReg d) ℂ) : Prop :=
  R.PosSemidef ∧ ∃ R0 : Matrix (PairReg d × Fin d) (PairReg d × Fin d) ℂ,
    R0.PosSemidef ∧
    (∀ a b i j k l,
      (∑ o : PairReg d, R (a,(i,(k,o))) (b,(j,(l,o)))) =
        if k = l then R0 (a,i) (b,j) else 0) ∧
    (∀ a b, (∑ i : Fin d, R0 (a,i) (b,i)) = if a = b then 1 else 0)

/-- PDF p.2, Eq.(2): insertion of one U; elementwise conjugation of the slot Choi
vector gives the coefficients U_(k,i) conjugate(U_(l,j)). -/
def insertedChoi {d : ℕ} (R : Matrix (CombReg d) (CombReg d) ℂ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    Matrix (PairReg d × PairReg d) (PairReg d × PairReg d) ℂ :=
  fun a b => ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
    U.val k i * conj (U.val l j) * R (a.1,(i,(k,a.2))) (b.1,(j,(l,b.2)))

/-- PDF p.2: target U tensor U on the external pair. -/
def targetChannel {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) : Superop (PairReg d) (PairReg d) :=
  conjSuperop (Matrix.kronecker U.val U.val)

/-- PDF p.2, Eq.(4): pointwise global channel fidelity, normalized by d^4.
The target input dimension is d^2; both Choi operators are unnormalized. -/
def pointScore {d : ℕ}
    (C : Matrix (PairReg d × PairReg d) (PairReg d × PairReg d) ℂ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) : ℝ :=
  (C * channelChoi (targetChannel U)).trace.re / (d : ℝ)^4

/-- PDF p.2, Eq.(4): probability-Haar average on U(d), equivalent to SU(d) here.
The integrand is continuous for a fixed finite comb, hence genuinely integrable. -/
def combScore {d : ℕ} (R : Matrix (CombReg d) (CombReg d) ℂ) : ℝ :=
  ∫ U : (Matrix.unitaryGroup (Fin d) ℂ), pointScore (insertedChoi R U) U ∂Schur.unitaryHaar d

/-- PDF p.2, Eq.(4): the same score for an explicitly constructed channel family. -/
def familyScore {d : ℕ} (C : (Matrix.unitaryGroup (Fin d) ℂ) → Superop (PairReg d) (PairReg d)) : ℝ :=
  ∫ U : (Matrix.unitaryGroup (Fin d) ℂ), pointScore (channelChoi (C U)) U ∂Schur.unitaryHaar d

/-- PDF p.3: true labels the symmetric (+) sector and false the antisymmetric (-) sector. -/
def sectorProjector (d : ℕ) (s : Bool) : Matrix (PairReg d) (PairReg d) ℂ :=
  (1 / 2 : ℂ) • (1 + (if s then 1 else -1 : ℂ) • (swapOp (ι := Fin d)))

/-- PDF p.3: d_+=d(d+1)/2 and d_-=d(d-1)/2, in real arithmetic.
All uses involving division have d>=2, so both dimensions are strictly positive. -/
def sectorDim (d : ℕ) (s : Bool) : ℝ :=
  (d : ℝ) * ((d : ℝ) + if s then 1 else -1) / 2

/-- PDF p.3, Eq.(8): preprocessing, retaining the off-diagonal ± memory terms. -/
def optimalPre (d : ℕ) : Superop (PairReg d) (Fin d × Bool) :=
  fun rho a b =>
    traceRight (sectorProjector d a.2 * rho * sectorProjector d b.2) a.1 b.1

/-- PDF p.3, Eq.(9): postprocessing on the full two-dimensional memory.
The coefficient is d/sqrt(d_i*d_j), including the off-diagonal sectors. -/
def optimalPost (d : ℕ) : Superop (Fin d × Bool) (PairReg d) :=
  fun sigma => ∑ i : Bool, ∑ j : Bool,
    (((d : ℝ) / Real.sqrt (sectorDim d i * sectorDim d j) : ℝ) : ℂ) •
      (sectorProjector d i *
        Matrix.kronecker (fun a b => sigma (a,i) (b,j)) (1 : Matrix (Fin d) (Fin d) ℂ) *
          sectorProjector d j)

/-- PDF p.3, Fig.1a: the stated preprocessing, one gate use, and postprocessing. -/
def optimalFamily (d : ℕ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) : Superop (PairReg d) (PairReg d) :=
  optimalPost d ∘ onFirst (conjSuperop U.val) ∘ optimalPre d

/-- PDF p.3, Eq.(10): the resulting channel, with both sector indices retained. -/
def optimalFormula (d : ℕ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) : Superop (PairReg d) (PairReg d) :=
  fun rho => ∑ i : Bool, ∑ j : Bool,
    (((d : ℝ) / Real.sqrt (sectorDim d i * sectorDim d j) : ℝ) : ℂ) •
      (sectorProjector d i * Matrix.kronecker
        (U.val * traceRight (sectorProjector d i * rho * sectorProjector d j) * U.valᴴ)
        (1 : Matrix (Fin d) (Fin d) ℂ) * sectorProjector d j)

/-- PDF p.3, Theorem 1: the exact optimal value (no rounded percentages). -/
def cloningValue (d : ℕ) : ℝ :=
  ((d : ℝ) + Real.sqrt ((d : ℝ)^2 - 1)) / (d : ℝ)^3

/-- PDF p.2, Eq.(5): V0^tensor2 tensor conjugate(V1) tensor conjugate(W2)
tensor W3^tensor2. The stars here are elementwise conjugation, not adjoints. -/
def covarianceAction {d : ℕ} (V W : (Matrix.unitaryGroup (Fin d) ℂ)) : Matrix (CombReg d) (CombReg d) ℂ :=
  fun a b => V.val a.1.1 b.1.1 * V.val a.1.2 b.1.2 *
    conj (V.val a.2.1 b.2.1) * conj (W.val a.2.2.1 b.2.2.1) *
    W.val a.2.2.2.1 b.2.2.2.1 * W.val a.2.2.2.2 b.2.2.2.2

/-- PDF p.2, Lemma 1: commuting with the full SU(d) x SU(d) action. -/
def CloningCovariant {d : ℕ} (R : Matrix (CombReg d) (CombReg d) ℂ) : Prop :=
  ∀ V W : (Matrix.unitaryGroup (Fin d) ℂ), Matrix.det V.val = 1 → Matrix.det W.val = 1 →
    R * covarianceAction V W = covarianceAction V W * R

/-- Sanity: zero inserted Choi data has zero pointwise score, so admissibility
is essential to the characterization of score one. -/
example (d : ℕ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) : pointScore 0 U = 0 := by
  simp [pointScore]

/-- Sanity: the linking contraction itself sends zero comb data to zero. -/
example (d : ℕ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    insertedChoi (0 : Matrix (CombReg d) (CombReg d) ℂ) U = 0 := by
  ext a b
  simp [insertedChoi]

/-- Sanity: the two sector dimensions at d=2 are 3 and 1. -/
example : sectorDim 2 true = 3 ∧ sectorDim 2 false = 1 := by
  norm_num [sectorDim]

/-- Sanity: the symmetric basis vector |00> has no antisymmetric component. -/
example : sectorProjector 2 true (0,0) (0,0) = 1 ∧
    sectorProjector 2 false (0,0) (0,0) = 0 := by
  norm_num [sectorProjector, swapOp, Matrix.one_apply]

/-- Sanity: retaining memory blocks does not dephase the off-diagonal memory entry. -/
example {d : ℕ} (X : Matrix (Fin d × Bool) (Fin d × Bool) ℂ) (a b : Fin d) :
    onFirst (fun Y : Matrix (Fin d) (Fin d) ℂ => Y) X (a,true) (b,false) =
      X (a,true) (b,false) := by
  rfl

/-- PDF p.3: dephase only the memory, in the stated ± basis. -/
def dephaseMemory (d : ℕ) : Superop (Fin d × Bool) (Fin d × Bool) :=
  fun sigma a b => if a.2 = b.2 then sigma a b else 0

/-- PDF p.3: the physical circuit with the memory dephased after A. -/
def decoheredFamily (d : ℕ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) : Superop (PairReg d) (PairReg d) :=
  optimalPost d ∘ onFirst (conjSuperop U.val) ∘ dephaseMemory d ∘ optimalPre d

/-- PDF p.3: the displayed decohered channel keeps just the diagonal sector terms. -/
def decoheredFormula (d : ℕ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) : Superop (PairReg d) (PairReg d) :=
  fun rho => ∑ i : Bool, (((d : ℝ) / sectorDim d i : ℝ) : ℂ) •
    (sectorProjector d i * Matrix.kronecker
      (U.val * traceRight (sectorProjector d i * rho * sectorProjector d i) * U.valᴴ)
      (1 : Matrix (Fin d) (Fin d) ℂ) * sectorProjector d i)

/-- PDF p.3: apply U on B and an independent probability-Haar random gate on E. -/
def randomFamily (d : ℕ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) : Superop (PairReg d) (PairReg d) :=
  fun rho => ∫ V : (Matrix.unitaryGroup (Fin d) ℂ),
    conjSuperop (Matrix.kronecker U.val V.val) rho ∂Schur.unitaryHaar d

/-- Sanity: dephasing kills exactly a cross-sector memory entry. -/
example {d : ℕ} (X : Matrix (Fin d × Bool) (Fin d × Bool) ℂ) (a b : Fin d) :
    dephaseMemory d X (a,true) (b,false) = 0 := by
  simp [dephaseMemory]

/-- PDF p.4: the normalized program obtained by applying U to half of a fixed probe. -/
def trainingState {d : ℕ} (sigma : Matrix (PairReg d) (PairReg d) ℂ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    Matrix (PairReg d) (PairReg d) ℂ :=
  conjSuperop (Matrix.kronecker U.val (1 : Matrix (Fin d) (Fin d) ℂ)) sigma

/-- PDF p.4: deterministic learning: training is completed before the pair input arrives.
An arbitrary U-independent decoder acts on input tensor program; its channel predicate
includes any discarded ancillas/environment, without postselection. -/
def learningFamily {d : ℕ} (sigma : Matrix (PairReg d) (PairReg d) ℂ)
    (decoder : Superop (PairReg d × PairReg d) (PairReg d))
    (U : (Matrix.unitaryGroup (Fin d) ℂ)) : Superop (PairReg d) (PairReg d) :=
  fun rho => decoder (Matrix.kronecker rho (trainingState sigma U))

/-- PDF p.4, Eq.(11): learning port order 1,((2B,2E,2A),3); H0 is one-dimensional. -/
abbrev LearnReg (d : ℕ) := Fin d × ((PairReg d × Fin d) × PairReg d)

/-- PDF p.4, Eq.(11): a different causal constraint from cloning Eq.(3).
The incoming register 2 has dimension d^3 and rho1 is a normalized density operator. -/
def LearningAdmissible {d : ℕ} (L : Matrix (LearnReg d) (LearnReg d) ℂ) : Prop :=
  L.PosSemidef ∧ ∃ rho1 : Matrix (Fin d) (Fin d) ℂ,
    IsDensityMatrix rho1 ∧ ∀ i j a b k l,
      (∑ o : PairReg d, L (i,((a,k),o)) (j,((b,l),o))) =
        if (a,k) = (b,l) then rho1 i j else 0

/-- PDF p.4, Fig.1b: slot insertion for learning, with external input order B,E. -/
def learningChoi {d : ℕ} (L : Matrix (LearnReg d) (LearnReg d) ℂ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    Matrix (PairReg d × PairReg d) (PairReg d × PairReg d) ℂ :=
  fun a b => ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
    U.val k i * conj (U.val l j) * L (i,((a.1,k),a.2)) (j,((b.1,l),b.2))

/-- PDF p.4: learning uses exactly the global channel score of Eq.(4). -/
def learningScore {d : ℕ} (L : Matrix (LearnReg d) (LearnReg d) ℂ) : ℝ :=
  ∫ U : (Matrix.unitaryGroup (Fin d) ℂ), pointScore (learningChoi L U) U ∂Schur.unitaryHaar d

/-- PDF p.4: exact restricted optimum, including the exceptional qubit value 5/16. -/
def estimationValue (d : ℕ) : ℝ :=
  if d = 2 then 5 / 16 else 6 / (d : ℝ)^4

/-- PDF pp.3–4: a one-call estimate-and-reprepare strategy. The arbitrary finite
reference measure and integrable PSD POVM density include both discrete and continuous
estimates. Outcomes are already the estimated gates, absorbing classical postprocessing. -/
structure EstimateStrategy (d : ℕ) where
  probe : Matrix (PairReg d) (PairReg d) ℂ
  probe_density : IsDensityMatrix probe
  measurement : Measurements.DensityPOVM (PairReg d) ((Matrix.unitaryGroup (Fin d) ℂ))

/-- PDF pp.3–4: measure the trained probe and apply the estimated gate twice.
Weights are the actual Born probabilities, with no renormalization. -/
def estimateFamily {d : ℕ} (est : EstimateStrategy d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    Superop (PairReg d) (PairReg d) :=
  fun rho => ∫ V : (Matrix.unitaryGroup (Fin d) ℂ),
    (effectProb (est.measurement.density V) (trainingState est.probe U)) •
      targetChannel V rho ∂est.measurement.reference

/-- Sanity: the qubit comparison value is exactly 5/16, not a rounded percentage. -/
example : estimationValue 2 = 5 / 16 := by
  simp [estimationValue]

/-- PDF p.1: tensor product of two devices, defined on every operator by the
matrix-unit expansion, including entangled inputs and off-diagonal blocks. -/
def tensorDevices {I J O P : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Phi : Superop I O) (Psi : Superop J P) :
    Superop (I × J) (O × P) :=
  fun rho a b => ∑ i : I, ∑ j : I, ∑ k : J, ∑ l : J,
    rho (i,k) (j,l) * Phi (Matrix.single i j 1) a.1 b.1 *
      Psi (Matrix.single k l 1) a.2 b.2

/-- PDF p.1: one common deterministic network implements the independent tensor
square of every candidate, with equality on all operators, hence every joint input. -/
def ExactlyClonable {I O K : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (family : K → Superop I O) : Prop :=
  ∃ net : DeviceCloner I O, ∀ k,
    DeviceCloner.run net (family k) = tensorDevices (family k) (family k)

/-- PDF p.1: a normalized one-call quantum discrimination procedure with arbitrary
finite outcomes. A reference of input dimension suffices by purification/Schmidt
compression; mixed probes and arbitrary POVMs include classical randomization.
No unknown-device label is an argument of the chosen test. -/
structure DeviceTest (I O K : Type*) [Fintype I] [Fintype O] [Fintype K]
    [DecidableEq O] [DecidableEq I] where
  probe : Matrix (I × I) (I × I) ℂ
  probe_density : IsDensityMatrix probe
  effects : K → Matrix (O × I) (O × I) ℂ
  effects_povm : IsPOVM effects

/-- PDF p.1: the Born response of a physical one-call discrimination test. -/
def DeviceTest.probability {I O K : Type*} [Fintype I] [Fintype O] [Fintype K]
    [DecidableEq I] [DecidableEq O] (test : DeviceTest I O K)
    (Phi : Superop I O) (k : K) : ℝ :=
  effectProb (test.effects k) (onFirst Phi test.probe)

/-- PDF p.1 and footnote [17], p.4: the worst conditional error, not an
average-error objective with fixed equal priors. False identifies Phi0. -/
def worstError {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (Phi0 Phi1 : Superop I O)
    (test : DeviceTest I O Bool) : ℝ :=
  max (test.probability Phi0 true) (test.probability Phi1 false)

/-- PDF p.1: minimax one-call error. On the nonempty finite registers and CPTP
candidates used below, the physical test space is nonempty and compact, and the
continuous objective attains this infimum. These facts are conclusions below,
not hypotheses assuming a discrimination procedure with the desired error. -/
def minimaxError {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (Phi0 Phi1 : Superop I O) : ℝ :=
  sInf (Set.range (worstError Phi0 Phi1))

/-- PDF p.1 and footnote [18], p.4: a common one-call test identifies every label
with certainty. Duplicate labels therefore must be removed before applying the
duplicate-free finite-set formulation. -/
def PerfectlyDiscriminable {I O K : Type*} [Fintype I] [Fintype O] [Fintype K]
    [DecidableEq I] [DecidableEq O] (family : K → Superop I O) : Prop :=
  ∃ test : DeviceTest I O K, ∀ k, test.probability (family k) k = 1

/-- PDF p.1: the two known candidate devices; the label is not accessible to the network. -/
def binaryDevices {I O : Type*} (Phi0 Phi1 : Superop I O) : Bool → Superop I O :=
  fun b => if b then Phi1 else Phi0

/-- Sanity: the correct and incorrect hypotheses are not interchanged. -/
example {I O : Type*} (Phi0 Phi1 : Superop I O) :
    binaryDevices Phi0 Phi1 false = Phi0 ∧ binaryDevices Phi0 Phi1 true = Phi1 := by
  simp [binaryDevices]

/-- PDF p.1: an ordinary classical one-evaluation circuit. Its query distribution
and response-conditioned output kernel can depend on the two external inputs,
but are fixed independently of the unknown permutation. Classical random memory
is absorbed into these finite conditional kernels. There is no coherent oracle. -/
structure ClassicalOneCall where
  query : PairReg 3 → Fin 3 → ℝ
  query_nonnegative : ∀ x q, 0 ≤ query x q
  query_total : ∀ x, ∑ q, query x q = 1
  output : PairReg 3 → Fin 3 → Fin 3 → PairReg 3 → ℝ
  output_nonnegative : ∀ x q r y, 0 ≤ output x q r y
  output_total : ∀ x q r, ∑ y, output x q r y = 1

/-- PDF p.1: output law after exactly one evaluation of a classical permutation. -/
def ClassicalOneCall.probability (net : ClassicalOneCall) (f : Equiv.Perm (Fin 3))
    (x y : PairReg 3) : ℝ :=
  ∑ q, net.query x q * net.output x q (f q) y

/-- Sanity: the target output in a classical call consists of the two independently
specified external letters, not two evaluations on the same query letter. -/
example (net : ClassicalOneCall) (f : Equiv.Perm (Fin 3)) (a b : Fin 3) :
    net.probability f (a,b) (f a,f b) =
      ∑ q, net.query (a,b) q * net.output (a,b) q (f q) (f a,f b) := by
  rfl

end QAlgorithms.Papers.Independent.Claimed50.P27


