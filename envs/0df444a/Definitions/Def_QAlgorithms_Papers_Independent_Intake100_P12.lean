-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12
-- name    : QAlgorithms_Papers_Independent_Intake100_P12
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:57:26.267336+00:00
-- url     : https://prove2.me/theorems/0887a5d2-9964-43b3-939a-2a2c3b872f78
-- title:
--   Definitions for Probabilistic exact universal quantum circuits for transforming unitary operations
-- statement:
--   The objects the formalized statements of *Probabilistic exact universal quantum circuits for transforming unitary operations* (arXiv:1909.01366) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `taskOutputChoi`: PDF p.2, Eq. (1): transport the accepted input-first Choi matrix to output-first order, preserving the unnormalized convention.
--   - `taskFromOutputChoi`: PDF p.2, Eq. (2): reconstruct using the accepted Choi inverse after explicitly swapping the output-first coordinates back to input-first order.
--   - `gateChoi`: PDF p.2: Choi matrix of a single-Kraus operation, in the chosen basis.
--   - `OracleWireDimensions`: PDF pp.4–6: dimensions of every physical wire; positivity is PositiveWires.
--   - `PositiveWires`: PDF pp.2–6: no zero-dimensional physical wires.
--   - `Inputs`: PDF p.4: tensor product input computational basis.
--   - `Outputs`: PDF p.4: tensor product output computational basis.
--   - `ProcessBasis`: PDF pp.5–7: the source's explicitly reordered I0,I,O,O0 basis.
--   - `uniformWires`: PDF p.4: homogeneous d-dimensional wires in the universal transformation tasks.
--   - `slotTensor`: PDF pp.4–6: Choi matrix of a tensor product of independently supplied slots.
--   - `evaluateOracleSlots`: PDF p.7, Eq. (16): full transpose on contracted IO factors, expanded entrywise. The same row/column indices in S and J are the effect of that transpose; no adjoint occurs.
--   - `ParallelRealizes`: PDF p.5: one simultaneous tensor batch with fixed CPTP encoder and decoder. Memory is first in both tensor products. Equality is on every combined slot map and every operator, rather than just the repeated-unitary inputs.
--   - `DelayedRealizes`: PDF pp.8–9, Eq. (32): the encoder prepares a normalized resource, before the input state exists. The decoder gets input,state in that explicit tensor order.
--   - `sequentialRun`: PDF p.5, Eq. (11): evaluation of k ordered oracle slots. Each fold entry contains exactly one oracle application, followed by a fixed channel E_i.
--   - `SequentialRealizes`: PDF p.5, Eq. (11): fixed-order sequential circuit; all memory and channels are quantified before the independent slot maps. At k=0 the oracle fold is empty.
--   - `GeneralDeterministic`: PDF pp.4–6: completely CP preserving general process in Choi coordinates. Positivity is precisely complete CP preservation; normalization is required on arbitrary independent slot channels, not merely equal unitary slots. Eq. (14) is deliberately not used.
--   - `ProtocolClass`: PDF pp.4–7: the three protocol classes are distinct.
--   - `ClassRealizable`: PDF pp.4–7: deterministic physical implementation in the named class. Sequential means Eq. (11), with k actual oracle calls, never General.
--   - `WireLabel`: PDF pp.5–6: labels for the homogeneous physical wires.
--   - `wireCoordinate`: PDF p.5: computational-basis coordinate on a labelled wire.
--   - `replaceCoordinates`: PDF p.5: replace exactly the selected coordinates by coordinates of z.
--   - `traceReplace`: PDF pp.5–6: trace-and-replace, R_A C = (Tr_A C) tensor I_A/d_A, in the ORIGINAL wire order. Summing over a full dummy register duplicates the unselected coordinates d^(2k+2-|A|) times; the denominator d^(2k+2) cancels that multiplicity and gives exactly the source's 1/d_A normalization.
--   - `outputWires`: PDF p.5: all oracle output wires plus the final external output.
--   - `futureWires`: PDF p.5: all wires except the external input.
--   - `ParallelNormalized`: PDF p.5, Eq. (10): explicit finite affine parallel normalization equations.
--   - `laterWires`: PDF p.5, Eq. (12): wires strictly later than slot i, plus the final output.
--   - `SequentialNormalized`: PDF p.5, Eq. (12): finite sequential comb normalization, in fixed slot order. The recursive partial traces are expressed as trace-and-replace in the full space.
--   - `ChannelFamily`: PDF pp.4–6: an actual family of independent CPTP slot-channel Choi matrices.
--   - `channelAffineSpan`: PDF pp.5–7: augmented span encodes the affine, rather than homogeneous, normalization constraints. Its generators are actual independent channel tuples.
--   - `IsNormalizationBasis`: PDF pp.5–7: finite exact normalization tests from a basis of the actual augmented independent-channel span. No assertion about a numerical rank is used.
--   - `GeneralFiniteNormalized`: PDF pp.4–7: finite general-process normalization on independent slot channels. Each output partial trace is an affine linear equality in C; C>=0 supplies complete CP preservation. This replaces no printed Eq. (14) by fiat.
--   - `FiniteClassNormalized`: PDF pp.5–7: the three explicit finite normalization systems.
--   - `HeraldedRealizable`: PDF pp.6–7: both CP branches are retained and normalized jointly.
--   - `DelayedInstrument`: PDF pp.9–10: a delayed parallel superinstrument, including its failure branch.
--   - `repeatedChoi`: PDF pp.6–7: identical uses of the unknown unitary channel.
--   - `UnitaryTask`: PDF pp.7,10,12,18: the unitary task, with channel equality removing global phases.
--   - `targetChoi`: PDF pp.7,10,12,18: transpose, entrywise conjugation, and inverse are different.
--   - `ExactUnitarySuccess`: PDF pp.6–7: exact success as an equality of unnormalized channel Choi matrices. This is equality on all inputs, including entangled references, with constant p.
--   - `Attainable`: PDF pp.6–7: a single physical protocol precedes the universal unknown input.
--   - `DelayedAttainable`: PDF pp.9,14–16: constant-success delayed-input protocols.
--   - `unitarySpan`: PDF p.7, Eq. (19): the actual repeated-unitary Choi span, not the ambient space.
--   - `IsUnitaryBasis`: PDF p.7, Eq. (19): a finite basis consisting of actual unitary operations.
--   - `UnitaryLinearTarget`: PDF pp.6–7, footnote 7: Section III assumes a linear channel target.
--   - `TestedFeasible`: PDF p.7: finitely tested SDP feasibility, with both branches and a physical class.
--   - `DelayedNormalized`: PDF p.9, Eq. (34): all identities are explicitly placed on I0 and O. The remaining marginal is on I, with its source normalization preserved.
--   - `totalDimension`: PDF p.10, Lemma 1: product of all wire dimensions, including both external wires.
--   - `bellZeroKraus`: PDF pp.12–13: the zero-Bell-outcome Kraus contraction, including the two normalized maximally entangled amplitudes. Its matrix entries are U_(b,a)/d.
--   - `storageWires`: PDF p.14, footnote 14: a storage process has no external input and a finite memory output; its k oracle slots may use any allowed causal ordering.
--   - `storedProgram`: PDF pp.14–16: the stored program is the memory state after all oracle uses. The input to storage is the unique scalar state on the one-dimensional wire.
--   - `LearningAttainable`: PDF pp.14–16 and footnote 14: exact probabilistic learning, allowing the most general storage process before the target input arrives. Its one-dimensional past and common future are fixed; this introduces no undefined delayed-input indefinite-order class. Retrieval has no oracle access, and both linear CP retrieval branches sum to a CPTP channel. Ref. [24] permits parallel storage without loss for attainable success; Lemma 3 supplies the task equivalence.
--   - `switchMatrix`: PDF p.17: coherent control of permutations of k slots. The controlled product acts on the system and leaves each order label untouched.
--   - `parallelTransposeProbability`: PDF pp.13,16: parallel transposition success; positive denominator when d,k>0.
--   - `adaptiveTransposeProbability`: PDF p.17: ceil(k/d) attempts, each successful with probability 1/d^2.
--   - `adaptiveInverseProbability`: PDF pp.18–19: floor((k+1)/d) inversion attempts.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, https://arxiv.org/abs/1909.01366v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

/-!
Statements from arXiv:1909.01366v2. All Choi matrices are unnormalized.
Channel indices are (output,input). Process indices are I0,I,O,O0.
The printed three-slot Eq. (14) and uncertified numerical tables are deferred.
The paper-local operational definitions below never use that equation.
Accepted matrix/channel primitives are imported; Choi adapters explicitly swap legs.
-/

noncomputable section

open QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.2, Eq. (1): transport the accepted input-first Choi matrix to
output-first order, preserving the unnormalized convention. -/
def taskOutputChoi {I O : Type} [Fintype I] [DecidableEq I]
    (Phi : Superop I O) : Op (O × I) :=
  (QAlgorithms.Papers.Independent.Information100.P34.choi Phi).submatrix
    Prod.swap Prod.swap

/-- PDF p.2, Eq. (2): reconstruct using the accepted Choi inverse after
explicitly swapping the output-first coordinates back to input-first order. -/
def taskFromOutputChoi {I O : Type} [Fintype I]
    (J : Op (O × I)) : Superop I O :=
  QAlgorithms.Papers.Independent.Information100.P34.fromChoi
    (J.submatrix Prod.swap Prod.swap)

/-- The accepted Choi adapter puts output coordinates first without scaling. -/
example {I O : Type} [Fintype I] [DecidableEq I]
    (Phi : Superop I O) (a b : O × I) :
    taskOutputChoi Phi a b = Phi (Matrix.single a.2 b.2 1) a.1 b.1 := rfl

/-- Reconstruction keeps every off-diagonal input coefficient. -/
example {I O : Type} [Fintype I] (J : Op (O × I)) (X : Op I) (a b : O) :
    taskFromOutputChoi J X a b = ∑ i, ∑ j, X i j * J (a,i) (b,j) := rfl

/-- PDF p.2: Choi matrix of a single-Kraus operation, in the chosen basis. -/
def gateChoi {I O : Type} (V : Matrix O I ℂ) : Op (O × I) :=
  fun a b => V a.1 a.2 * conj (V b.1 b.2)

/-- PDF pp.4–6: dimensions of every physical wire; positivity is PositiveWires. -/
structure OracleWireDimensions (k : ℕ) where
  inputExternal : ℕ
  outputExternal : ℕ
  inputSlot : Fin k → ℕ
  outputSlot : Fin k → ℕ

/-- PDF pp.2–6: no zero-dimensional physical wires. -/
def PositiveWires {k : ℕ} (w : OracleWireDimensions k) : Prop :=
  0 < w.inputExternal ∧ 0 < w.outputExternal ∧
    (∀ i, 0 < w.inputSlot i) ∧ (∀ i, 0 < w.outputSlot i)

/-- PDF p.4: tensor product input computational basis. -/
abbrev Inputs {k : ℕ} (w : OracleWireDimensions k) := (i : Fin k) → Fin (w.inputSlot i)

/-- PDF p.4: tensor product output computational basis. -/
abbrev Outputs {k : ℕ} (w : OracleWireDimensions k) := (i : Fin k) → Fin (w.outputSlot i)

/-- PDF pp.5–7: the source's explicitly reordered I0,I,O,O0 basis. -/
abbrev ProcessBasis {k : ℕ} (w : OracleWireDimensions k) :=
  Fin w.inputExternal × (Inputs w × (Outputs w × Fin w.outputExternal))

/-- PDF p.4: homogeneous d-dimensional wires in the universal transformation tasks. -/
def uniformWires (d k : ℕ) : OracleWireDimensions k := ⟨d,d,fun _ => d,fun _ => d⟩

/-- PDF pp.4–6: Choi matrix of a tensor product of independently supplied slots. -/
def slotTensor {k : ℕ} {w : OracleWireDimensions k}
    (J : (i : Fin k) → Op (Fin (w.outputSlot i) × Fin (w.inputSlot i))) :
    Op (Outputs w × Inputs w) :=
  fun a b => ∏ i, J i (a.1 i,a.2 i) (b.1 i,b.2 i)

/-- PDF p.7, Eq. (16): full transpose on contracted IO factors, expanded entrywise.
The same row/column indices in S and J are the effect of that transpose; no adjoint occurs. -/
def evaluateOracleSlots {k : ℕ} {w : OracleWireDimensions k} (S : Op (ProcessBasis w))
    (J : Op (Outputs w × Inputs w)) :
    Op (Fin w.outputExternal × Fin w.inputExternal) :=
  fun a b => ∑ x : Inputs w, ∑ y : Inputs w,
    ∑ u : Outputs w, ∑ v : Outputs w,
      S (a.2,x,u,a.1) (b.2,y,v,b.1) * J (u,x) (v,y)

/-- PDF p.5: one simultaneous tensor batch with fixed CPTP encoder and decoder.
Memory is first in both tensor products. Equality is on every combined slot map
and every operator, rather than just the repeated-unitary inputs. -/
def ParallelRealizes {k : ℕ} (w : OracleWireDimensions k) (C : Op (ProcessBasis w)) : Prop :=
  ∃ m : ℕ, 0 < m ∧
  ∃ E : Superop (Fin w.inputExternal) (Fin m × Inputs w),
  ∃ D : Superop (Fin m × Outputs w) (Fin w.outputExternal),
    IsChannel E ∧ IsChannel D ∧
    ∀ (J : Op (Outputs w × Inputs w)) X,
      taskFromOutputChoi (evaluateOracleSlots C J) X = D (idTensorSuperop (R := Fin m) (taskFromOutputChoi J) (E X))

/-- PDF pp.8–9, Eq. (32): the encoder prepares a normalized resource, before the
input state exists. The decoder gets input,state in that explicit tensor order. -/
def DelayedRealizes {k : ℕ} (w : OracleWireDimensions k) (C : Op (ProcessBasis w)) : Prop :=
  ∃ m : ℕ, 0 < m ∧
  ∃ sigma : Op (Fin m × Inputs w), IsDensityMatrix sigma ∧
  ∃ D : Superop (Fin w.inputExternal × (Fin m × Outputs w)) (Fin w.outputExternal),
    IsChannel D ∧ ∀ (J : Op (Outputs w × Inputs w)) X,
      taskFromOutputChoi (evaluateOracleSlots C J) X =
        D (X ⊗ₖ idTensorSuperop (R := Fin m) (taskFromOutputChoi J) sigma)

/-- PDF p.5, Eq. (11): evaluation of k ordered oracle slots. Each fold entry
contains exactly one oracle application, followed by a fixed channel E_i. -/
def sequentialRun {d k m : ℕ}
    (E : Fin k → Superop (Fin m × Fin d) (Fin m × Fin d))
    (J : Fin k → Op (Fin d × Fin d)) (X : Op (Fin m × Fin d)) :
    Op (Fin m × Fin d) :=
  (List.finRange k).foldl
    (fun Y i => E i (idTensorSuperop (R := Fin m) (taskFromOutputChoi (J i)) Y)) X

/-- PDF p.5, Eq. (11): fixed-order sequential circuit; all memory and channels
are quantified before the independent slot maps. At k=0 the oracle fold is empty. -/
def SequentialRealizes (d k : ℕ) (C : Op (ProcessBasis (uniformWires d k))) : Prop :=
  ∃ m : ℕ, 0 < m ∧
  ∃ E0 : Superop (Fin d) (Fin m × Fin d),
  ∃ E : Fin k → Superop (Fin m × Fin d) (Fin m × Fin d),
  ∃ D : Superop (Fin m × Fin d) (Fin d),
    IsChannel E0 ∧ (∀ i, IsChannel (E i)) ∧ IsChannel D ∧
    ∀ (J : Fin k → Op (Fin d × Fin d)) X,
      taskFromOutputChoi (evaluateOracleSlots C (slotTensor (w := uniformWires d k) J)) X =
        D (sequentialRun E J (E0 X))

/-- PDF pp.4–6: completely CP preserving general process in Choi coordinates.
Positivity is precisely complete CP preservation; normalization is required on
arbitrary independent slot channels, not merely equal unitary slots. Eq. (14)
is deliberately not used. -/
def GeneralDeterministic {k : ℕ} (w : OracleWireDimensions k) (C : Op (ProcessBasis w)) : Prop :=
  PositiveWires w ∧ C.PosSemidef ∧
    ∀ J : (i : Fin k) → Op (Fin (w.outputSlot i) × Fin (w.inputSlot i)),
      (∀ i, ChannelChoi (J i)) → ChannelChoi (evaluateOracleSlots C (slotTensor J))

/-- PDF pp.4–7: the three protocol classes are distinct. -/
inductive ProtocolClass where
  | parallel
  | adaptive
  | general
  deriving DecidableEq

/-- PDF pp.4–7: deterministic physical implementation in the named class.
Sequential means Eq. (11), with k actual oracle calls, never General. -/
def ClassRealizable (c : ProtocolClass) (d k : ℕ)
    (C : Op (ProcessBasis (uniformWires d k))) : Prop :=
  0 < d ∧ C.PosSemidef ∧ match c with
    | .parallel => ParallelRealizes (uniformWires d k) C
    | .adaptive => SequentialRealizes d k C
    | .general => GeneralDeterministic (uniformWires d k) C

/-- PDF pp.5–6: labels for the homogeneous physical wires. -/
inductive WireLabel (k : ℕ) where
  | inputExternal
  | inputSlot (i : Fin k)
  | outputSlot (i : Fin k)
  | outputExternal
  deriving DecidableEq, Fintype

/-- PDF p.5: computational-basis coordinate on a labelled wire. -/
def wireCoordinate {d k : ℕ} (x : ProcessBasis (uniformWires d k)) :
    WireLabel k → Fin d
  | .inputExternal => x.1
  | .inputSlot i => x.2.1 i
  | .outputSlot i => x.2.2.1 i
  | .outputExternal => x.2.2.2

/-- PDF p.5: replace exactly the selected coordinates by coordinates of z. -/
def replaceCoordinates {d k : ℕ} (A : Finset (WireLabel k))
    (x z : ProcessBasis (uniformWires d k)) : ProcessBasis (uniformWires d k) :=
  (if WireLabel.inputExternal ∈ A then z.1 else x.1,
    (fun i => if WireLabel.inputSlot i ∈ A then z.2.1 i else x.2.1 i),
    (fun i => if WireLabel.outputSlot i ∈ A then z.2.2.1 i else x.2.2.1 i),
    if WireLabel.outputExternal ∈ A then z.2.2.2 else x.2.2.2)

/-- PDF pp.5–6: trace-and-replace, R_A C = (Tr_A C) tensor I_A/d_A,
in the ORIGINAL wire order. Summing over a full dummy register duplicates the
unselected coordinates d^(2k+2-|A|) times; the denominator d^(2k+2) cancels
that multiplicity and gives exactly the source's 1/d_A normalization. -/
def traceReplace {d k : ℕ} (A : Finset (WireLabel k))
    (C : Op (ProcessBasis (uniformWires d k))) : Op (ProcessBasis (uniformWires d k)) :=
  fun x y => if ∀ a ∈ A, wireCoordinate x a = wireCoordinate y a then
    ((d : ℂ)^(2*k+2))⁻¹ * ∑ z : ProcessBasis (uniformWires d k),
      C (replaceCoordinates A x z) (replaceCoordinates A y z)
    else 0

/-- PDF p.5: all oracle output wires plus the final external output. -/
def outputWires (k : ℕ) : Finset (WireLabel k) :=
  insert .outputExternal (Finset.univ.image WireLabel.outputSlot)

/-- PDF p.5: all wires except the external input. -/
def futureWires (k : ℕ) : Finset (WireLabel k) :=
  (Finset.univ : Finset (WireLabel k)).erase .inputExternal

/-- PDF p.5, Eq. (10): explicit finite affine parallel normalization equations. -/
def ParallelNormalized (d k : ℕ) (C : Op (ProcessBasis (uniformWires d k))) : Prop :=
  C.PosSemidef ∧
    traceReplace {WireLabel.outputExternal} C = traceReplace (outputWires k) C ∧
    traceReplace (futureWires k) C = traceReplace Finset.univ C ∧
    C.trace = (d : ℂ)^(k+1)

/-- PDF p.5, Eq. (12): wires strictly later than slot i, plus the final output. -/
def laterWires {k : ℕ} (i : Fin k) : Finset (WireLabel k) :=
  insert .outputExternal
    (((Finset.univ.filter (fun j : Fin k => i < j)).image WireLabel.inputSlot) ∪
     ((Finset.univ.filter (fun j : Fin k => i < j)).image WireLabel.outputSlot))

/-- PDF p.5, Eq. (12): finite sequential comb normalization, in fixed slot order.
The recursive partial traces are expressed as trace-and-replace in the full space. -/
def SequentialNormalized (d k : ℕ) (C : Op (ProcessBasis (uniformWires d k))) : Prop :=
  C.PosSemidef ∧
    (∀ i : Fin k, traceReplace (laterWires i) C =
      traceReplace (insert (WireLabel.outputSlot i) (laterWires i)) C) ∧
    traceReplace (futureWires k) C = traceReplace Finset.univ C ∧
    C.trace = (d : ℂ)^(k+1)

/-- PDF pp.4–6: an actual family of independent CPTP slot-channel Choi matrices. -/
abbrev ChannelFamily {k : ℕ} (w : OracleWireDimensions k) :=
  {J : (i : Fin k) → Op (Fin (w.outputSlot i) × Fin (w.inputSlot i)) //
    ∀ i, ChannelChoi (J i)}

/-- PDF pp.5–7: augmented span encodes the affine, rather than homogeneous,
normalization constraints. Its generators are actual independent channel tuples. -/
def channelAffineSpan {k : ℕ} (w : OracleWireDimensions k) :=
  Submodule.span ℝ (Set.range (fun J : ChannelFamily w => (slotTensor J.val, (1 : ℝ))))

/-- PDF pp.5–7: finite exact normalization tests from a basis of the actual
augmented independent-channel span. No assertion about a numerical rank is used. -/
def IsNormalizationBasis {k : ℕ} (w : OracleWireDimensions k) (n : ℕ)
    (B : Fin n → ChannelFamily w) : Prop :=
  LinearIndependent ℝ (fun i => (slotTensor (B i).val, (1 : ℝ))) ∧
    Submodule.span ℝ (Set.range (fun i => (slotTensor (B i).val, (1 : ℝ)))) =
      channelAffineSpan w

/-- PDF pp.4–7: finite general-process normalization on independent slot
channels. Each output partial trace is an affine linear equality in C; C>=0
supplies complete CP preservation. This replaces no printed Eq. (14) by fiat. -/
def GeneralFiniteNormalized {k n : ℕ} (w : OracleWireDimensions k)
    (B : Fin n → ChannelFamily w) (C : Op (ProcessBasis w)) : Prop :=
  C.PosSemidef ∧ ∀ i, ChannelChoi (evaluateOracleSlots C (slotTensor (B i).val))

/-- PDF pp.5–7: the three explicit finite normalization systems. -/
def FiniteClassNormalized {d k n : ℕ} (c : ProtocolClass)
    (B : Fin n → ChannelFamily (uniformWires d k))
    (C : Op (ProcessBasis (uniformWires d k))) : Prop :=
  match c with
  | .parallel => ParallelNormalized d k C
  | .adaptive => SequentialNormalized d k C
  | .general => GeneralFiniteNormalized (uniformWires d k) B C

/-- PDF pp.6–7: both CP branches are retained and normalized jointly. -/
def HeraldedRealizable (c : ProtocolClass) (d k : ℕ)
    (S F : Op (ProcessBasis (uniformWires d k))) : Prop :=
  S.PosSemidef ∧ F.PosSemidef ∧ ClassRealizable c d k (S + F)

/-- PDF pp.9–10: a delayed parallel superinstrument, including its failure branch. -/
def DelayedInstrument {k : ℕ} (w : OracleWireDimensions k)
    (S F : Op (ProcessBasis w)) : Prop :=
  PositiveWires w ∧ S.PosSemidef ∧ F.PosSemidef ∧ DelayedRealizes w (S + F)

/-- PDF pp.6–7: identical uses of the unknown unitary channel. -/
def repeatedChoi {d : ℕ} (k : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Op (Outputs (uniformWires d k) × Inputs (uniformWires d k)) :=
  slotTensor (w := uniformWires d k) (fun _ => gateChoi (U : Op (Fin d)))

/-- PDF pp.7,10,12,18: the unitary task, with channel equality removing global phases. -/
inductive UnitaryTask where
  | identity
  | transpose
  | conjugate
  | inverse
  deriving DecidableEq

/-- PDF pp.7,10,12,18: transpose, entrywise conjugation, and inverse are different. -/
def targetChoi {d : ℕ} (task : UnitaryTask)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : Op (Fin d × Fin d) :=
  match task with
  | .identity => gateChoi (U : Op (Fin d))
  | .transpose => gateChoi ((U : Op (Fin d)).transpose)
  | .conjugate => gateChoi (fun i j => conj ((U : Op (Fin d)) i j))
  | .inverse => gateChoi ((U : Op (Fin d))ᴴ)

/-- PDF pp.6–7: exact success as an equality of unnormalized channel Choi matrices.
This is equality on all inputs, including entangled references, with constant p. -/
def ExactUnitarySuccess {d k : ℕ} (S : Op (ProcessBasis (uniformWires d k)))
    (target : Matrix.unitaryGroup (Fin d) ℂ → Op (Fin d × Fin d)) (p : ℝ) : Prop :=
  ∀ U, evaluateOracleSlots S (repeatedChoi k U) = (p : ℂ) • target U

/-- PDF pp.6–7: a single physical protocol precedes the universal unknown input. -/
def Attainable (c : ProtocolClass) (d k : ℕ)
    (target : Matrix.unitaryGroup (Fin d) ℂ → Op (Fin d × Fin d)) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ ∃ S F, HeraldedRealizable c d k S F ∧ ExactUnitarySuccess S target p

/-- PDF pp.9,14–16: constant-success delayed-input protocols. -/
def DelayedAttainable (d k : ℕ)
    (target : Matrix.unitaryGroup (Fin d) ℂ → Op (Fin d × Fin d)) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ ∃ S F,
    DelayedInstrument (uniformWires d k) S F ∧ ExactUnitarySuccess S target p

/-- PDF p.7, Eq. (19): the actual repeated-unitary Choi span, not the ambient space. -/
def unitarySpan (d k : ℕ) :=
  Submodule.span ℂ (Set.range (repeatedChoi (d := d) k))

/-- PDF p.7, Eq. (19): a finite basis consisting of actual unitary operations. -/
def IsUnitaryBasis (d k n : ℕ) (B : Fin n → Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  LinearIndependent ℂ (fun i => repeatedChoi k (B i)) ∧
    Submodule.span ℂ (Set.range (fun i => repeatedChoi k (B i))) = unitarySpan d k

/-- PDF pp.6–7, footnote 7: Section III assumes a linear channel target. -/
def UnitaryLinearTarget {d : ℕ}
    (f : Op (Fin d × Fin d) →ₗ[ℂ] Op (Fin d × Fin d)) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    ∃ V : Matrix.unitaryGroup (Fin d) ℂ, f (gateChoi (U : Op (Fin d))) = gateChoi (V : Op (Fin d))

/-- PDF p.7: finitely tested SDP feasibility, with both branches and a physical class. -/
def TestedFeasible {d k n : ℕ} (c : ProtocolClass)
    (f : Op (Fin d × Fin d) →ₗ[ℂ] Op (Fin d × Fin d))
    (B : Fin n → Matrix.unitaryGroup (Fin d) ℂ) (p : ℝ)
    (S F : Op (ProcessBasis (uniformWires d k))) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ HeraldedRealizable c d k S F ∧
    ∀ i, evaluateOracleSlots S (repeatedChoi k (B i)) = (p : ℂ) • f (gateChoi (B i : Op (Fin d)))

/-- PDF p.9, Eq. (34): all identities are explicitly placed on I0 and O.
The remaining marginal is on I, with its source normalization preserved. -/
def DelayedNormalized {k : ℕ} (w : OracleWireDimensions k) (C : Op (ProcessBasis w)) : Prop :=
  C.PosSemidef ∧
  (∀ (i j : Fin w.inputExternal) (a b : Inputs w) (u v : Outputs w),
    (∑ o, C (i,a,u,o) (j,b,v,o)) =
      ((1 : Op (Fin w.inputExternal)) i j / (w.inputExternal : ℂ)) *
      (∑ t : Fin w.inputExternal, ∑ z : Outputs w, ∑ o : Fin w.outputExternal,
        C (t,a,z,o) (t,b,z,o)) *
      ((1 : Op (Outputs w)) u v / (Fintype.card (Outputs w) : ℂ))) ∧
  C.trace = ((w.inputExternal * Fintype.card (Outputs w) : ℕ) : ℂ)

/-- PDF p.10, Lemma 1: product of all wire dimensions, including both external wires. -/
def totalDimension {k : ℕ} (w : OracleWireDimensions k) : ℕ :=
  w.inputExternal * w.outputExternal *
    (∏ i, w.inputSlot i) * (∏ i, w.outputSlot i)

/-- PDF pp.12–13: the zero-Bell-outcome Kraus contraction, including the two
normalized maximally entangled amplitudes. Its matrix entries are U_(b,a)/d. -/
def bellZeroKraus {d : ℕ} (U : Op (Fin d)) : Op (Fin d) :=
  fun a b => ∑ x, (if x = b then (d : ℂ)⁻¹ else 0) * U x a

/-- PDF p.14, footnote 14: a storage process has no external input and a
finite memory output; its k oracle slots may use any allowed causal ordering. -/
def storageWires (d k m : ℕ) : OracleWireDimensions k := ⟨1,m,fun _ => d,fun _ => d⟩

/-- PDF pp.14–16: the stored program is the memory state after all oracle uses.
The input to storage is the unique scalar state on the one-dimensional wire. -/
def storedProgram {d k m : ℕ} (C : Op (ProcessBasis (storageWires d k m)))
    (U : Matrix.unitaryGroup (Fin d) ℂ) : Op (Fin m) :=
  let J := slotTensor (w := storageWires d k m) (fun _ => gateChoi (U : Op (Fin d)))
  fun a b => evaluateOracleSlots C J (a, (⟨0, by decide⟩ : Fin 1))
    (b, (⟨0, by decide⟩ : Fin 1))

/-- PDF pp.14–16 and footnote 14: exact probabilistic learning, allowing the
most general storage process before the target input arrives. Its one-dimensional
past and common future are fixed; this introduces no undefined delayed-input
indefinite-order class. Retrieval has no oracle access, and both linear CP
retrieval branches sum to a CPTP channel. Ref. [24] permits parallel storage
without loss for attainable success; Lemma 3 supplies the task equivalence. -/
def LearningAttainable (d k : ℕ) (p : ℝ) : Prop :=
  0 < d ∧ 0 ≤ p ∧ p ≤ 1 ∧
  ∃ m : ℕ, 0 < m ∧ ∃ C : Op (ProcessBasis (storageWires d k m)),
    GeneralDeterministic (storageWires d k m) C ∧
    ∃ DS DF : Op (Fin d × Fin m) →ₗ[ℂ] Op (Fin d),
      (taskOutputChoi DS).PosSemidef ∧ (taskOutputChoi DF).PosSemidef ∧
      IsChannel (fun X => DS X + DF X) ∧
      ∀ (U : Matrix.unitaryGroup (Fin d) ℂ) X,
        DS (X ⊗ₖ storedProgram C U) = (p : ℂ) • conjSuperop (U : Op (Fin d)) X

/-- PDF p.17: coherent control of permutations of k slots. The controlled product
acts on the system and leaves each order label untouched. -/
def switchMatrix {d k : ℕ} (U : Fin k → Op (Fin d)) :
    Op ((Equiv.Perm (Fin k)) × Fin d) :=
  fun a b => if a.1 = b.1 then
    (((List.finRange k).map (fun i => U (a.1 i))).foldl (fun V W => W * V) (1 : Op (Fin d))) a.2 b.2
    else 0

/-- PDF pp.13,16: parallel transposition success; positive denominator when d,k>0. -/
def parallelTransposeProbability (d k : ℕ) : ℝ :=
  1 - ((d : ℝ)^2 - 1) / ((k : ℝ) + (d : ℝ)^2 - 1)

/-- PDF p.17: ceil(k/d) attempts, each successful with probability 1/d^2. -/
def adaptiveTransposeProbability (d k : ℕ) : ℝ :=
  1 - (1 - 1 / (d : ℝ)^2)^((k + d - 1) / d)

/-- PDF pp.18–19: floor((k+1)/d) inversion attempts. -/
def adaptiveInverseProbability (d k : ℕ) : ℝ :=
  1 - (1 - 1 / (d : ℝ)^2)^((k + 1) / d)

/-- PDF p.2: gate Choi trace normalization is d for the identity gate. -/
example (d : ℕ) : (gateChoi (1 : Op (Fin d))).trace = (d : ℂ) := by
  simp [gateChoi, Matrix.trace, Fintype.sum_prod_type, Matrix.one_apply]

/-- PDF p.5: replacing no coordinates leaves the basis tuple unchanged. -/
example {d k : ℕ} (x z : ProcessBasis (uniformWires d k)) :
    replaceCoordinates ∅ x z = x := by
  rcases x with ⟨i,a,u,o⟩
  simp [replaceCoordinates]

/-- PDF p.5: a zero-slot sequential computation is independent of its slot argument. -/
example {d m : ℕ} (E : Fin 0 → Superop (Fin m × Fin d) (Fin m × Fin d))
    (J : Fin 0 → Op (Fin d × Fin d)) (X : Op (Fin m × Fin d)) :
    sequentialRun E J X = X := by
  simp [sequentialRun]

/-- PDF pp.12–13: the contraction has the transpose orientation and factor 1/d. -/
example {d : ℕ} (U : Op (Fin d)) (a b : Fin d) :
    bellZeroKraus U a b = (d : ℂ)⁻¹ * U b a := by
  simp [bellZeroKraus]

/-- PDF p.16: the one-qubit one-use optimum is 1/4. -/
example : parallelTransposeProbability 2 1 = 1/4 := by
  norm_num [parallelTransposeProbability]

/-- PDF p.17: k=3,d=2 gives two transpose attempts; inversion gives two as well. -/
example : adaptiveTransposeProbability 2 3 = 7/16 ∧
    adaptiveInverseProbability 2 3 = 7/16 := by
  norm_num [adaptiveTransposeProbability, adaptiveInverseProbability]

end QAlgorithms.Papers.Independent.Intake100.P12


