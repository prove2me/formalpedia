-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44
-- name    : QAlgorithms_Papers_Independent_Dependency50_P44
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:25:21.845383+00:00
-- url     : https://prove2.me/theorems/a64ea3c9-bd70-48c8-9eb1-1c262a9cedae
-- title:
--   Definitions for A father protocol for quantum broadcast channels
-- statement:
--   The objects the formalized statements of *A father protocol for quantum broadcast channels* (arXiv:quant-ph/0612155) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BroadcastBasis`: PDF pp.1–2: an arbitrary nonzero register with its fixed basis; actual dimension is `d+1`.
--   - `regroupPartialTrace`: PDF p.2: partial trace, with explicit retained and discarded coordinates. Every use below has `(keep, discard)` a bijective regrouping of tensor factors.
--   - `tensorChannels`: PDF p.2: tensor product of heterogeneous channels, defined on all operators by matrix units. Thus this acts on entangled inputs, not just product inputs.
--   - `Broadcast`: PDF p.2: one input and `m` outputs, with a fixed rectangular Stinespring isometry. Tracing its fixed environment defines exactly the channel used throughout.
--   - `Broadcast.channel`: PDF p.2: the CPTP broadcast map realized by the prescribed Stinespring isometry.
--   - `Broadcast.block`: PDF pp.2,7: memoryless `n` uses, regrouped by receiver. At `n=0` the product is empty.
--   - `quantumInitial`: PDF p.2: independent reference/message EPR pairs and independent Alice/receiver EPR pairs. Coordinates are (all references, (Alice's joint input, all receiver assistance)).
--   - `BroadcastTransmissionCode`: PDF p.2: arbitrary joint CPTP encoder and local CPTP decoders, for simultaneous entanglement transmission through `n` uses. Local ancillas/garbage are included in CPTP maps. There is no receiver communication or initial receiver/receiver entanglement.
--   - `BroadcastTransmissionCode.decoded`: PDF p.2: actual joint decoded reference/output density, from the specified independent EPRs.
--   - `quantumTarget`: PDF p.2: the joint product target of all reference/decoded EPR pairs.
--   - `BroadcastTransmissionCode.error`: PDF p.2: JOINT unhalved trace-distance error; separate broadcastMarginal success is insufficient.
--   - `BroadcastTransmissionCode.rate`: PDF pp.2,6: log base two of message dimension per channel use. The value at zero uses is irrelevant to the eventual-rate conditions.
--   - `quantumAchievable`: PDF p.2: operational achievable rates, with vanishing joint error and liminf rate bounds written as eventual arbitrary positive slack. `assisted=false` forces every assistance space one-dimensional. The entire code sequence is chosen before its rates/errors are evaluated.
--   - `broadcastQuantumCapacity`: PDF p.2: the capacity region includes the closure of operational achievable rates.
--   - `InputState`: PDF pp.4,7: unrestricted auxiliary registers and discarded purifier D, including arbitrary mixed reduced states on the auxiliaries and the entire channel input.
--   - `broadcastOutputDensity`: PDF pp.4,7: compute the channel-output density from the pure input, tracing D and the fixed channel environment. D is unrestricted, rather than silently restricting reduced inputs to pure.
--   - `Subregister`: PDF p.7: basis configurations on a specified subset of registers.
--   - `broadcastMarginal`: PDF pp.2,7: retain exactly the auxiliary registers in K and output registers in L.
--   - `auxEntropy`: PDF p.2: H(A_K), in bits, with all complementary registers traced out.
--   - `outEntropy`: PDF p.2: H(B_L), in bits. The empty auxiliary configuration is a singleton factor.
--   - `receiverMutual`: PDF p.2: I(A_j;B_j) = H(A_j)+H(B_j)-H(A_j B_j), in bits.
--   - `receiverCoherent`: PDF pp.2,6–7: coherent information I(A_j⟩B_j), with no factor of one half.
--   - `totalCorrelation`: PDF p.7, (21): J(A_K) = sum H(A_j) - H(A_K), including K empty.
--   - `fatherRegion`: PDF p.4, (9), p.7, (21): all nonnegative rates and every subset inequality. At two receivers these are precisely the two individual bounds and the sum bound (9).
--   - `coherentRegion`: PDF pp.6–7: the coherent-information rectangle; a negative bound gives an empty region.
--   - `assistedBlockRegion`: PDF p.7, (16): full block inputs and every auxiliary dimension, with rates divided by n.
--   - `unassistedBlockRegion`: PDF p.7, (20): coherent information divided by n, with no sum-rate bound.
--   - `regularizedAssisted`: PDF p.7, Theorem 3: closed convex hull, following the operational closure on p.2. Printed: convex hull. Changed: closed convex hull. Reason: limiting errors/rate slack in the converse give approximate membership, not finite-block attainment (source correction, trap 30).
--   - `regularizedUnassisted`: PDF p.7, Theorem 4: the same explicit closure correction as in Theorem 3.
--   - `SourceGarbageBasis`: PDF p.2: garbage factors of the literal purified source code, including the full fixed Stinespring environment for every channel use.
--   - `SourceDecodedBasis`: PDF p.2: all tensor factors in the literal source code's purified decoded state.
--   - `SourceQuantumCode`: PDF p.2: LITERAL source code: joint encoding isometry, local decoding isometries, retained purifying garbage, and a normalized pure target on all garbage. Its full-output finite error is a different quantity from `BroadcastTransmissionCode.error`; no finite-epsilon equivalence is assumed.
--   - `SourceQuantumCode.decodedVector`: PDF p.2: explicit tensor contraction of independent EPRs, encoder, fixed Stinespring tensor power, and all LOCAL decoders. The environment and all purifying garbage remain present.
--   - `SourceQuantumCode.targetVector`: PDF p.2: product of normalized pure garbage and the JOINT EPR transmission target.
--   - `SourceQuantumCode.error`: PDF p.2: the source's unhalved trace norm on the ENTIRE purified output.
--   - `SourceQuantumCode.rate`: PDF pp.2,6: source code rates, with the missing factor n on p.2 corrected using p.6.
--   - `sourceQuantumAchievable`: PDF p.2: literal source operational achievability, with the full purified-output error. The liminf convention handles integral dimensions by vanishing rate slack.
--   - `sourceQuantumCapacity`: PDF p.2: capacity as defined in the source, including closure.
--   - `flaggedVector`: PDF p.7, Lemma 2: the exact constructed pure vector with the orthogonal D flag. f need be neither injective nor surjective; the component pure states need not be orthogonal.
--   - `ShotDimensions`: PDF p.3: one-shot message, assistance, retrieved-entanglement, and encoder garbage dimensions. All actual dimensions are one greater than these parameters.
--   - `ShotBasis`: PDF pp.3–4: the exact tensor factors of psi and of the two comparison density operators.
--   - `ShotInput`: PDF p.3: sender's input halves of the four independent EPR pairs.
--   - `ShotEncoded`: PDF p.3: output of Alice's one-shot encoder.
--   - `pairOutputs`: PDF p.2: bijective two-receiver grouping with heterogeneous output dimensions.
--   - `shotVector`: PDF pp.3–4: psi = U_N W phi, computed by contracting the four EPR inputs and the FIXED channel isometry. W is not assumed to be a successful code.
--   - `ShotDecodedBasis`: PDF p.4, (4): all factors of the decoded one-shot state, including retrieved Alice/Bob EPRs.
--   - `ShotGarbageBasis`: PDF p.4: the pure leftover state on decoder garbage, encoder garbage, and the environment.
--   - `ShotDecoder1`: PDF p.3: Bob 1's local decoding isometry, with arbitrary garbage and the retrieved EPR half.
--   - `ShotDecoder2`: PDF p.3: Bob 2's local decoding isometry, with arbitrary garbage.
--   - `shotDecoded`: PDF pp.3–4: the actual vector after the replacement encoder U and the two local decoders.
--   - `shotTarget`: PDF p.4, (4): the JOINT product of all three target EPRs and one pure garbage state.
--   - `shotComplement1`: PDF p.4, (4): receiver 1's complementary broadcastMarginal R2 Btilde2 B2 Ahat E.
--   - `shotComplement2`: PDF p.4, (4): receiver 2's complementary broadcastMarginal R1 Btilde1 Aretrieved B1 Ahat E.
--   - `shotPurity1`: PDF p.4, (4): the comparison broadcastMarginal obtained by tracing B1 (not its assistance).
--   - `shotPurity2`: PDF p.4, (4): the comparison broadcastMarginal obtained by tracing B2.
--   - `shotErrorBound`: PDF pp.3–4, (4): the finite one-shot error functional. Fourth roots, dimensions, ranks, purities, and comparison errors are copied from the split display, inspected in the PDF.
--   - `deterministicChannel`: PDF pp.7–8: the FULL deterministic classical channel, including dephasing of its input. The environment flag in the source Stinespring map removes every off-diagonal input term.
--   - `deterministicInputVector`: PDF p.7, VII: explicit purification with D of the special classically correlated density sum_i p_i |f1(i)><f1(i)| ⊗ |f2(i)><f2(i)| ⊗ |i><i|.
--   - `deterministicOutput`: PDF pp.7–8: channel output computed from that specified purification, tracing D.
--   - `deterministicRegion`: PDF pp.7–8: closed time-sharing hull of the restricted single-letter input family.
--   - `classicalAssistance`: PDF p.1: independent pairwise entanglement used for assisted classical communication.
--   - `AssistedBroadcastClassicalCode`: PDF p.1: usual assisted classical codes implicit in superdense coding: independent uniform messages, arbitrary message-dependent CPTP preparation acting on Alice's shared halves, and one local POVM per receiver. There is no secrecy, confidentiality, or leakage constraint.
--   - `AssistedBroadcastClassicalCode.received`: PDF p.1: actual joint receiver state conditioned on both messages, including their assistance halves; preparation may create arbitrary mixed block channel inputs.
--   - `AssistedBroadcastClassicalCode.error`: PDF p.1: average JOINT decoding error under independent uniform messages.
--   - `AssistedBroadcastClassicalCode.rate`: PDF p.1: classical bits per channel use, log2 of message cardinality divided by block size.
--   - `classicalAchievable`: PDF p.1: operational assisted classical achievable rates, using vanishing average joint error and liminf rate bounds. The uniform-message convention is explicit.
--   - `assistedBroadcastClassicalCapacity`: PDF p.1: the closed operational assisted classical capacity region.
-- source:
--   A father protocol for quantum broadcast channels, arXiv:quant-ph/0612155v4, https://arxiv.org/abs/quant-ph/0612155v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-!
Statements from Dupuis, Hayden and Li, *A father protocol for quantum broadcast channels*,
arXiv:quant-ph/0612155v4. All page references are PDF pages.

The local substrate uses arbitrary positive register dimensions: `BroadcastBasis d = Fin (d+1)`.
The parameter `d` is thus dimension minus one. In particular `d = 0` is a singleton,
not an empty space. Tensor coordinates and every retained/discarded factor are explicit.
Capacity is operational, defined through independent EPR inputs, a joint CPTP encoder,
local CPTP decoders, JOINT unhalved trace-norm error, asymptotic rate slack, and closure.
No secrecy condition is introduced.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate
open Filter Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)
open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF pp.1–2: an arbitrary nonzero register with its fixed basis; actual dimension is `d+1`. -/
abbrev BroadcastBasis (d : ℕ) := Fin (d + 1)

/-- PDF p.2: partial trace, with explicit retained and discarded coordinates.
Every use below has `(keep, discard)` a bijective regrouping of tensor factors. -/
def regroupPartialTrace {I J K : Type} [Fintype I] (keep : I → J) (discard : I → K)
    (rho : Operator I) : Operator J :=
  fun x y => ∑ i, ∑ i',
    if keep i = x ∧ keep i' = y ∧ discard i = discard i' then rho i i' else 0

/-- PDF p.2: tensor product of heterogeneous channels, defined on all operators by matrix units.
Thus this acts on entangled inputs, not just product inputs. -/
def tensorChannels {J : Type} [Fintype J] {I O : J → Type}
    [∀ j, Fintype (I j)] (F : ∀ j, Superop (I j) (O j)) :
    Superop ((j : J) → I j) ((j : J) → O j) :=
  fun rho y y' => ∑ x, ∑ x',
    rho x x' * ∏ j, F j (Matrix.single (x j) (x' j) 1) (y j) (y' j)

/-- PDF p.2: one input and `m` outputs, with a fixed rectangular Stinespring isometry.
Tracing its fixed environment defines exactly the channel used throughout. -/
structure Broadcast (m a : ℕ) (b : Fin m → ℕ) where
  environment : ℕ
  stinespring : Matrix (((j : Fin m) → BroadcastBasis (b j)) × BroadcastBasis environment) (BroadcastBasis a) ℂ
  isometry : stinespringᴴ * stinespring = 1

/-- PDF p.2: the CPTP broadcast map realized by the prescribed Stinespring isometry. -/
def Broadcast.channel {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b) :
    Superop (BroadcastBasis a) ((j : Fin m) → BroadcastBasis (b j)) :=
  fun rho => traceRight (N.stinespring * rho * N.stinespringᴴ)

/-- PDF pp.2,7: memoryless `n` uses, regrouped by receiver. At `n=0` the product is empty. -/
def Broadcast.block {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b) (n : ℕ) :
    Superop (Fin n → BroadcastBasis a) ((j : Fin m) → Fin n → BroadcastBasis (b j)) :=
  fun rho y y' =>
    tensorChannels (fun _ : Fin n => N.channel) rho
      (fun t j => y j t) (fun t j => y' j t)

/-- PDF p.2: independent reference/message EPR pairs and independent Alice/receiver EPR pairs.
Coordinates are (all references, (Alice's joint input, all receiver assistance)). -/
def quantumInitial {m : ℕ} (k e : Fin m → ℕ) :
    EuclideanSpace ℂ (((j : Fin m) → BroadcastBasis (k j)) ×
      (((j : Fin m) → BroadcastBasis (k j) × BroadcastBasis (e j)) × ((j : Fin m) → BroadcastBasis (e j)))) :=
  WithLp.toLp 2 fun x => ∏ j,
    finiteMaxEntangled (BroadcastBasis (k j)) (x.1 j, (x.2.1 j).1) *
    finiteMaxEntangled (BroadcastBasis (e j)) ((x.2.1 j).2, x.2.2 j)

/-- PDF p.2: arbitrary joint CPTP encoder and local CPTP decoders, for simultaneous
entanglement transmission through `n` uses. Local ancillas/garbage are included in CPTP maps.
There is no receiver communication or initial receiver/receiver entanglement. -/
structure BroadcastTransmissionCode {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b) (n : ℕ) where
  message : Fin m → ℕ
  assistance : Fin m → ℕ
  encoder : Superop ((j : Fin m) → BroadcastBasis (message j) × BroadcastBasis (assistance j)) (Fin n → BroadcastBasis a)
  encoder_cptp : IsChannel encoder
  decoder : (j : Fin m) → Superop ((Fin n → BroadcastBasis (b j)) × BroadcastBasis (assistance j)) (BroadcastBasis (message j))
  decoder_cptp : ∀ j, IsChannel (decoder j)

/-- PDF p.2: actual joint decoded reference/output density, from the specified independent EPRs. -/
def BroadcastTransmissionCode.decoded {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : BroadcastTransmissionCode N n) :
    Operator (((j : Fin m) → BroadcastBasis (C.message j)) × ((j : Fin m) → BroadcastBasis (C.message j))) :=
  let encoded := idTensorSuperop (mapFirst C.encoder)
    (pureDensity (quantumInitial C.message C.assistance))
  let transmitted := idTensorSuperop (mapFirst (N.block n)) encoded
  let regrouped : Operator (((j : Fin m) → BroadcastBasis (C.message j)) ×
      ((j : Fin m) → (Fin n → BroadcastBasis (b j)) × BroadcastBasis (C.assistance j))) :=
    fun x y => transmitted
      (x.1, ((fun j => (x.2 j).1), (fun j => (x.2 j).2)))
      (y.1, ((fun j => (y.2 j).1), (fun j => (y.2 j).2)))
  idTensorSuperop (tensorChannels C.decoder) regrouped

/-- PDF p.2: the joint product target of all reference/decoded EPR pairs. -/
def quantumTarget {m : ℕ} (k : Fin m → ℕ) :
    EuclideanSpace ℂ (((j : Fin m) → BroadcastBasis (k j)) × ((j : Fin m) → BroadcastBasis (k j))) :=
  WithLp.toLp 2 fun x => ∏ j, finiteMaxEntangled (BroadcastBasis (k j)) (x.1 j, x.2 j)

/-- PDF p.2: JOINT unhalved trace-distance error; separate broadcastMarginal success is insufficient. -/
def BroadcastTransmissionCode.error {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : BroadcastTransmissionCode N n) : ℝ :=
  traceNorm (C.decoded - pureDensity (quantumTarget C.message))

/-- PDF pp.2,6: log base two of message dimension per channel use.
The value at zero uses is irrelevant to the eventual-rate conditions. -/
def BroadcastTransmissionCode.rate {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : BroadcastTransmissionCode N n) (j : Fin m) : ℝ :=
  Real.logb 2 (C.message j + 1 : ℕ) / (n : ℝ)

/-- PDF p.2: operational achievable rates, with vanishing joint error and liminf rate bounds
written as eventual arbitrary positive slack. `assisted=false` forces every assistance space
one-dimensional. The entire code sequence is chosen before its rates/errors are evaluated. -/
def quantumAchievable {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b)
    (assisted : Bool) : Set (Fin m → ℝ) :=
  {q | (∀ j, 0 ≤ q j) ∧ ∃ C : (n : ℕ) → BroadcastTransmissionCode N n,
    (∀ n, assisted = true ∨ ∀ j, (C n).assistance j = 0) ∧
    Tendsto (fun n => (C n).error) atTop (nhds 0) ∧
    ∀ j, ∀ delta : ℝ, 0 < delta → ∀ᶠ n in atTop, q j - delta ≤ (C n).rate j}

/-- PDF p.2: the capacity region includes the closure of operational achievable rates. -/
def broadcastQuantumCapacity {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b)
    (assisted : Bool) : Set (Fin m → ℝ) := closure (quantumAchievable N assisted)

/-- PDF pp.4,7: unrestricted auxiliary registers and discarded purifier D, including arbitrary
mixed reduced states on the auxiliaries and the entire channel input. -/
structure InputState (m : ℕ) (A : Type) [Fintype A] where
  auxiliary : Fin m → ℕ
  discarded : ℕ
  vector : EuclideanSpace ℂ (((j : Fin m) → BroadcastBasis (auxiliary j)) × (A × BroadcastBasis discarded))
  normalized : ‖vector‖ = 1

/-- PDF pp.4,7: compute the channel-output density from the pure input, tracing D and the fixed
channel environment. D is unrestricted, rather than silently restricting reduced inputs to pure. -/
def broadcastOutputDensity {m : ℕ} {A : Type} [Fintype A] {B : Fin m → Type}
    (F : Superop A ((j : Fin m) → B j)) (S : InputState m A) :
    Operator (((j : Fin m) → BroadcastBasis (S.auxiliary j)) × ((j : Fin m) → B j)) :=
  idTensorSuperop F (fun x y => ∑ d : BroadcastBasis S.discarded,
    pureDensity S.vector (x.1, (x.2, d)) (y.1, (y.2, d)))

/-- PDF p.7: basis configurations on a specified subset of registers. -/
abbrev Subregister {m : ℕ} (I : Fin m → Type) (K : Finset (Fin m)) :=
  (j : {j : Fin m // j ∈ K}) → I j.1

/-- PDF pp.2,7: retain exactly the auxiliary registers in K and output registers in L. -/
def broadcastMarginal {m : ℕ} {A B : Fin m → Type} [∀ j, Fintype (A j)] [∀ j, Fintype (B j)]
    (rho : Operator (((j : Fin m) → A j) × ((j : Fin m) → B j)))
    (K L : Finset (Fin m)) : Operator (Subregister A K × Subregister B L) :=
  regroupPartialTrace (fun x : ((j : Fin m) → A j) × ((j : Fin m) → B j) =>
      ((fun j => x.1 j.1), (fun j => x.2 j.1)))
    (fun x => ((fun j : {j : Fin m // j ∈ Kᶜ} => x.1 j.1),
      (fun j : {j : Fin m // j ∈ Lᶜ} => x.2 j.1))) rho

/-- PDF p.2: H(A_K), in bits, with all complementary registers traced out. -/
def auxEntropy {m : ℕ} {A B : Fin m → Type} [∀ j, Fintype (A j)] [∀ j, Fintype (B j)]
    (rho : Operator (((j : Fin m) → A j) × ((j : Fin m) → B j))) (K : Finset (Fin m)) : ℝ :=
  vnEntropy (broadcastMarginal rho K ∅)

/-- PDF p.2: H(B_L), in bits. The empty auxiliary configuration is a singleton factor. -/
def outEntropy {m : ℕ} {A B : Fin m → Type} [∀ j, Fintype (A j)] [∀ j, Fintype (B j)]
    (rho : Operator (((j : Fin m) → A j) × ((j : Fin m) → B j))) (L : Finset (Fin m)) : ℝ :=
  vnEntropy (broadcastMarginal rho ∅ L)

/-- PDF p.2: I(A_j;B_j) = H(A_j)+H(B_j)-H(A_j B_j), in bits. -/
def receiverMutual {m : ℕ} {A B : Fin m → Type} [∀ j, Fintype (A j)] [∀ j, Fintype (B j)]
    (rho : Operator (((j : Fin m) → A j) × ((j : Fin m) → B j))) (j : Fin m) : ℝ :=
  auxEntropy rho {j} + outEntropy rho {j} - vnEntropy (broadcastMarginal rho {j} {j})

/-- PDF pp.2,6–7: coherent information I(A_j⟩B_j), with no factor of one half. -/
def receiverCoherent {m : ℕ} {A B : Fin m → Type} [∀ j, Fintype (A j)] [∀ j, Fintype (B j)]
    (rho : Operator (((j : Fin m) → A j) × ((j : Fin m) → B j))) (j : Fin m) : ℝ :=
  outEntropy rho {j} - vnEntropy (broadcastMarginal rho {j} {j})

/-- PDF p.7, (21): J(A_K) = sum H(A_j) - H(A_K), including K empty. -/
def totalCorrelation {m : ℕ} {A B : Fin m → Type}
    [∀ j, Fintype (A j)] [∀ j, Fintype (B j)]
    (rho : Operator (((j : Fin m) → A j) × ((j : Fin m) → B j))) (K : Finset (Fin m)) : ℝ :=
  (∑ j ∈ K, auxEntropy rho {j}) - auxEntropy rho K

/-- PDF p.4, (9), p.7, (21): all nonnegative rates and every subset inequality.
At two receivers these are precisely the two individual bounds and the sum bound (9). -/
def fatherRegion {m : ℕ} {A B : Fin m → Type} [∀ j, Fintype (A j)] [∀ j, Fintype (B j)]
    (rho : Operator (((j : Fin m) → A j) × ((j : Fin m) → B j))) : Set (Fin m → ℝ) :=
  {q | (∀ j, 0 ≤ q j) ∧ ∀ K : Finset (Fin m),
    (∑ j ∈ K, q j) ≤ ((∑ j ∈ K, receiverMutual rho j) - totalCorrelation rho K) / 2}

/-- PDF pp.6–7: the coherent-information rectangle; a negative bound gives an empty region. -/
def coherentRegion {m : ℕ} {A B : Fin m → Type} [∀ j, Fintype (A j)] [∀ j, Fintype (B j)]
    (rho : Operator (((j : Fin m) → A j) × ((j : Fin m) → B j))) : Set (Fin m → ℝ) :=
  {q | ∀ j, 0 ≤ q j ∧ q j ≤ receiverCoherent rho j}

/-- PDF p.7, (16): full block inputs and every auxiliary dimension, with rates divided by n. -/
def assistedBlockRegion {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b)
    (n : ℕ) : Set (Fin m → ℝ) :=
  {q | ∃ S : InputState m (Fin n → BroadcastBasis a),
    (fun j => (n : ℝ) * q j) ∈ fatherRegion (broadcastOutputDensity (N.block n) S)}

/-- PDF p.7, (20): coherent information divided by n, with no sum-rate bound. -/
def unassistedBlockRegion {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b)
    (n : ℕ) : Set (Fin m → ℝ) :=
  {q | ∃ S : InputState m (Fin n → BroadcastBasis a),
    (fun j => (n : ℝ) * q j) ∈ coherentRegion (broadcastOutputDensity (N.block n) S)}

/-- PDF p.7, Theorem 3: closed convex hull, following the operational closure on p.2.
Printed: convex hull. Changed: closed convex hull. Reason: limiting errors/rate slack in the
converse give approximate membership, not finite-block attainment (source correction, trap 30). -/
def regularizedAssisted {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b) : Set (Fin m → ℝ) :=
  closure (convexHull ℝ {q | ∃ n : ℕ, 0 < n ∧ q ∈ assistedBlockRegion N n})

/-- PDF p.7, Theorem 4: the same explicit closure correction as in Theorem 3. -/
def regularizedUnassisted {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b) : Set (Fin m → ℝ) :=
  closure (convexHull ℝ {q | ∃ n : ℕ, 0 < n ∧ q ∈ unassistedBlockRegion N n})

/-- PDF p.2: garbage factors of the literal purified source code, including the full fixed
Stinespring environment for every channel use. -/
structure SourceGarbageBasis {m : ℕ} (g : Fin m → ℕ) (sender env n : ℕ) where
  senderGarbage : BroadcastBasis sender
  decoderGarbage : (j : Fin m) → BroadcastBasis (g j)
  environment : Fin n → BroadcastBasis env
  deriving Fintype, DecidableEq

/-- PDF p.2: all tensor factors in the literal source code's purified decoded state. -/
structure SourceDecodedBasis {m : ℕ} (k g : Fin m → ℕ) (sender environment n : ℕ) where
  reference : (j : Fin m) → BroadcastBasis (k j)
  decoded : (j : Fin m) → BroadcastBasis (k j)
  garbage : SourceGarbageBasis g sender environment n
  deriving Fintype, DecidableEq

/-- PDF p.2: LITERAL source code: joint encoding isometry, local decoding isometries, retained
purifying garbage, and a normalized pure target on all garbage. Its full-output finite error
is a different quantity from `BroadcastTransmissionCode.error`; no finite-epsilon equivalence is assumed. -/
structure SourceQuantumCode {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b) (n : ℕ) where
  message : Fin m → ℕ
  assistance : Fin m → ℕ
  senderGarbage : ℕ
  receiverGarbage : Fin m → ℕ
  encoder : Matrix ((Fin n → BroadcastBasis a) × BroadcastBasis senderGarbage)
    ((j : Fin m) → BroadcastBasis (message j) × BroadcastBasis (assistance j)) ℂ
  encoder_isometry : encoderᴴ * encoder = 1
  decoder : (j : Fin m) → Matrix (BroadcastBasis (message j) × BroadcastBasis (receiverGarbage j))
    ((Fin n → BroadcastBasis (b j)) × BroadcastBasis (assistance j)) ℂ
  decoder_isometry : ∀ j, (decoder j)ᴴ * decoder j = 1
  targetGarbage : EuclideanSpace ℂ (SourceGarbageBasis receiverGarbage senderGarbage N.environment n)
  targetGarbage_normalized : ‖targetGarbage‖ = 1

/-- PDF p.2: explicit tensor contraction of independent EPRs, encoder, fixed Stinespring tensor
power, and all LOCAL decoders. The environment and all purifying garbage remain present. -/
def SourceQuantumCode.decodedVector {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : SourceQuantumCode N n) :
    EuclideanSpace ℂ (SourceDecodedBasis C.message C.receiverGarbage
      C.senderGarbage N.environment n) :=
  WithLp.toLp 2 fun x =>
    ∑ input : Fin n → BroadcastBasis a,
    ∑ out : (j : Fin m) → Fin n → BroadcastBasis (b j),
    ∑ assist : (j : Fin m) → BroadcastBasis (C.assistance j),
      C.encoder (input, x.garbage.senderGarbage) (fun j => (x.reference j, assist j)) *
      (∏ t, N.stinespring ((fun j => out j t), x.garbage.environment t) (input t)) *
      (∏ j, C.decoder j (x.decoded j, x.garbage.decoderGarbage j) (out j, assist j)) *
      (∏ j, finiteMaxEntangled (BroadcastBasis (C.message j)) (x.reference j, x.reference j) *
        finiteMaxEntangled (BroadcastBasis (C.assistance j)) (assist j, assist j))

/-- PDF p.2: product of normalized pure garbage and the JOINT EPR transmission target. -/
def SourceQuantumCode.targetVector {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : SourceQuantumCode N n) :
    EuclideanSpace ℂ (SourceDecodedBasis C.message C.receiverGarbage
      C.senderGarbage N.environment n) :=
  WithLp.toLp 2 fun x => C.targetGarbage x.garbage *
    ∏ j, finiteMaxEntangled (BroadcastBasis (C.message j)) (x.reference j, x.decoded j)

/-- PDF p.2: the source's unhalved trace norm on the ENTIRE purified output. -/
def SourceQuantumCode.error {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : SourceQuantumCode N n) : ℝ :=
  traceNorm (pureDensity C.decodedVector - pureDensity C.targetVector)

/-- PDF pp.2,6: source code rates, with the missing factor n on p.2 corrected using p.6. -/
def SourceQuantumCode.rate {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : SourceQuantumCode N n) (j : Fin m) : ℝ :=
  Real.logb 2 (C.message j + 1 : ℕ) / (n : ℝ)

/-- PDF p.2: literal source operational achievability, with the full purified-output error.
The liminf convention handles integral dimensions by vanishing rate slack. -/
def sourceQuantumAchievable {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b)
    (assisted : Bool) : Set (Fin m → ℝ) :=
  {q | (∀ j, 0 ≤ q j) ∧ ∃ C : (n : ℕ) → SourceQuantumCode N n,
    (∀ n, assisted = true ∨ ∀ j, (C n).assistance j = 0) ∧
    Tendsto (fun n => (C n).error) atTop (nhds 0) ∧
    ∀ j, ∀ delta : ℝ, 0 < delta → ∀ᶠ n in atTop, q j - delta ≤ (C n).rate j}

/-- PDF p.2: capacity as defined in the source, including closure. -/
def sourceQuantumCapacity {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b)
    (assisted : Bool) : Set (Fin m → ℝ) := closure (sourceQuantumAchievable N assisted)

/-- PDF p.7, Lemma 2: the exact constructed pure vector with the orthogonal D flag.
f need be neither injective nor surjective; the component pure states need not be orthogonal. -/
def flaggedVector {A B C D : Type} [Fintype D] (f : D → B) (alpha : D → ℂ)
    (mu : D → EuclideanSpace ℂ A) (nu : D → EuclideanSpace ℂ C) :
    EuclideanSpace ℂ (A × (B × (C × D))) :=
  WithLp.toLp 2 fun x => alpha x.2.2.2 * mu x.2.2.2 x.1 *
    (if x.2.1 = f x.2.2.2 then 1 else 0) * nu x.2.2.2 x.2.2.1

/-- Sanity test for the local positive-dimension basis. -/
example : Fintype.card (BroadcastBasis 0) = 1 := rfl

example {I J : Type} [Fintype J] (rho : Operator (I × J)) (i i' : I) :
    traceRight rho i i' = ∑ j, rho (i, j) (i', j) := rfl

example {I S : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (rho : Operator (I × S)) :
    mapFirst (fun X : Operator I => X) rho = rho := rfl

example : quantumTarget (m := 1) (fun _ => 0) (fun _ => 0, fun _ => 0) = 1 := by
  simp [quantumTarget, finiteMaxEntangled, BroadcastBasis]

example {m : ℕ} {A B : Fin m → Type} [∀ j, Fintype (A j)] [∀ j, Fintype (B j)]
    (rho : Operator (((j : Fin m) → A j) × ((j : Fin m) → B j))) (q : Fin m → ℝ)
    (h : q ∈ coherentRegion rho) (j : Fin m) (hj : receiverCoherent rho j < 0) : False := by
  exact (not_le_of_gt hj) (le_trans (h j).1 (h j).2)

/-- PDF p.3: one-shot message, assistance, retrieved-entanglement, and encoder garbage dimensions.
All actual dimensions are one greater than these parameters. -/
structure ShotDimensions where
  message1 : ℕ
  message2 : ℕ
  assistance1 : ℕ
  assistance2 : ℕ
  retrieved : ℕ
  trash : ℕ

/-- PDF pp.3–4: the exact tensor factors of psi and of the two comparison density operators. -/
structure ShotBasis (P : ShotDimensions) (b : Fin 2 → ℕ) (env : ℕ) where
  reference1 : BroadcastBasis P.message1
  reference2 : BroadcastBasis P.message2
  assistance1 : BroadcastBasis P.assistance1
  assistance2 : BroadcastBasis P.assistance2
  retrieved : BroadcastBasis P.retrieved
  output1 : BroadcastBasis (b 0)
  output2 : BroadcastBasis (b 1)
  trash : BroadcastBasis P.trash
  environment : BroadcastBasis env
  deriving DecidableEq

/-- Finite enumeration via ordinary tensor products, avoiding dependent Sigma search. -/
instance shotBasisFintype (P : ShotDimensions) (b : Fin 2 → ℕ) (env : ℕ) : Fintype (ShotBasis P b env) :=
  Fintype.ofEquiv (BroadcastBasis P.message1 × BroadcastBasis P.message2 × BroadcastBasis P.assistance1 × BroadcastBasis P.assistance2 × BroadcastBasis P.retrieved × BroadcastBasis (b 0) × BroadcastBasis (b 1) × BroadcastBasis P.trash × BroadcastBasis env)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2⟩
      invFun := fun x => (x.reference1, x.reference2, x.assistance1, x.assistance2, x.retrieved, x.output1, x.output2, x.trash, x.environment)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- PDF p.3: sender's input halves of the four independent EPR pairs. -/
abbrev ShotInput (P : ShotDimensions) :=
  (BroadcastBasis P.message1 × BroadcastBasis P.assistance1) × (BroadcastBasis P.message2 × BroadcastBasis P.assistance2)

/-- PDF p.3: output of Alice's one-shot encoder. -/
abbrev ShotEncoded (P : ShotDimensions) (a : ℕ) := BroadcastBasis a × (BroadcastBasis P.retrieved × BroadcastBasis P.trash)

/-- PDF p.2: bijective two-receiver grouping with heterogeneous output dimensions. -/
def pairOutputs {b : Fin 2 → ℕ} (x : BroadcastBasis (b 0)) (y : BroadcastBasis (b 1)) :
    (j : Fin 2) → BroadcastBasis (b j) := Fin.cases x (Fin.cases y (fun i => Fin.elim0 i))

/-- PDF pp.3–4: psi = U_N W phi, computed by contracting the four EPR inputs and the FIXED
channel isometry. W is not assumed to be a successful code. -/
def shotVector {a : ℕ} {b : Fin 2 → ℕ} (N : Broadcast 2 a b) (P : ShotDimensions)
    (W : Matrix (ShotEncoded P a) (ShotInput P) ℂ) :
    EuclideanSpace ℂ (ShotBasis P b N.environment) :=
  WithLp.toLp 2 fun x =>
    (∑ z : BroadcastBasis a,
      N.stinespring (pairOutputs x.output1 x.output2, x.environment) z *
      W (z, (x.retrieved, x.trash))
        ((x.reference1, x.assistance1), (x.reference2, x.assistance2))) *
    finiteMaxEntangled (BroadcastBasis P.message1) (x.reference1, x.reference1) *
    finiteMaxEntangled (BroadcastBasis P.assistance1) (x.assistance1, x.assistance1) *
    finiteMaxEntangled (BroadcastBasis P.message2) (x.reference2, x.reference2) *
    finiteMaxEntangled (BroadcastBasis P.assistance2) (x.assistance2, x.assistance2)

/-- PDF p.4, (4): all factors of the decoded one-shot state, including retrieved Alice/Bob EPRs. -/
structure ShotDecodedBasis (P : ShotDimensions) (g1 g2 env : ℕ) where
  reference1 : BroadcastBasis P.message1
  reference2 : BroadcastBasis P.message2
  aliceRetrieved : BroadcastBasis P.retrieved
  decoded1 : BroadcastBasis P.message1
  decoded2 : BroadcastBasis P.message2
  bobRetrieved : BroadcastBasis P.retrieved
  garbage1 : BroadcastBasis g1
  garbage2 : BroadcastBasis g2
  trash : BroadcastBasis P.trash
  environment : BroadcastBasis env
  deriving DecidableEq

/-- Finite enumeration via ordinary tensor products, avoiding dependent Sigma search. -/
instance shotDecodedBasisFintype (P : ShotDimensions) (g1 g2 env : ℕ) : Fintype (ShotDecodedBasis P g1 g2 env) :=
  Fintype.ofEquiv (BroadcastBasis P.message1 × BroadcastBasis P.message2 × BroadcastBasis P.retrieved × BroadcastBasis P.message1 × BroadcastBasis P.message2 × BroadcastBasis P.retrieved × BroadcastBasis g1 × BroadcastBasis g2 × BroadcastBasis P.trash × BroadcastBasis env)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2⟩
      invFun := fun x => (x.reference1, x.reference2, x.aliceRetrieved, x.decoded1, x.decoded2, x.bobRetrieved, x.garbage1, x.garbage2, x.trash, x.environment)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- PDF p.4: the pure leftover state on decoder garbage, encoder garbage, and the environment. -/
structure ShotGarbageBasis (P : ShotDimensions) (g1 g2 env : ℕ) where
  garbage1 : BroadcastBasis g1
  garbage2 : BroadcastBasis g2
  trash : BroadcastBasis P.trash
  environment : BroadcastBasis env
  deriving Fintype, DecidableEq

/-- PDF p.3: Bob 1's local decoding isometry, with arbitrary garbage and the retrieved EPR half. -/
abbrev ShotDecoder1 (P : ShotDimensions) (b : Fin 2 → ℕ) (g1 : ℕ) :=
  Matrix (BroadcastBasis P.message1 × (BroadcastBasis g1 × BroadcastBasis P.retrieved))
    (BroadcastBasis (b 0) × BroadcastBasis P.assistance1) ℂ

/-- PDF p.3: Bob 2's local decoding isometry, with arbitrary garbage. -/
abbrev ShotDecoder2 (P : ShotDimensions) (b : Fin 2 → ℕ) (g2 : ℕ) :=
  Matrix (BroadcastBasis P.message2 × BroadcastBasis g2) (BroadcastBasis (b 1) × BroadcastBasis P.assistance2) ℂ

/-- PDF pp.3–4: the actual vector after the replacement encoder U and the two local decoders. -/
def shotDecoded {a : ℕ} {b : Fin 2 → ℕ} (N : Broadcast 2 a b) (P : ShotDimensions)
    (U : Matrix (ShotEncoded P a) (ShotInput P) ℂ) {g1 g2 : ℕ}
    (V1 : ShotDecoder1 P b g1) (V2 : ShotDecoder2 P b g2) :
    EuclideanSpace ℂ (ShotDecodedBasis P g1 g2 N.environment) :=
  WithLp.toLp 2 fun x => ∑ t1 : BroadcastBasis P.assistance1, ∑ t2 : BroadcastBasis P.assistance2,
    ∑ y1 : BroadcastBasis (b 0), ∑ y2 : BroadcastBasis (b 1),
      V1 (x.decoded1, (x.garbage1, x.bobRetrieved)) (y1, t1) *
      V2 (x.decoded2, x.garbage2) (y2, t2) *
      shotVector N P U ⟨x.reference1, x.reference2, t1, t2, x.aliceRetrieved,
        y1, y2, x.trash, x.environment⟩

/-- PDF p.4, (4): the JOINT product of all three target EPRs and one pure garbage state. -/
def shotTarget (P : ShotDimensions) {g1 g2 environment : ℕ}
    (eta : EuclideanSpace ℂ (ShotGarbageBasis P g1 g2 environment)) :
    EuclideanSpace ℂ (ShotDecodedBasis P g1 g2 environment) :=
  WithLp.toLp 2 fun x =>
    eta ⟨x.garbage1, x.garbage2, x.trash, x.environment⟩ *
    finiteMaxEntangled (BroadcastBasis P.retrieved) (x.aliceRetrieved, x.bobRetrieved) *
    finiteMaxEntangled (BroadcastBasis P.message1) (x.reference1, x.decoded1) *
    finiteMaxEntangled (BroadcastBasis P.message2) (x.reference2, x.decoded2)

/-- PDF p.4, (4): receiver 1's complementary broadcastMarginal R2 Btilde2 B2 Ahat E. -/
def shotComplement1 {P : ShotDimensions} {b : Fin 2 → ℕ} {environment : ℕ}
    (rho : Operator (ShotBasis P b environment)) :=
  regroupPartialTrace (fun x : ShotBasis P b environment => (x.reference2, x.assistance2, x.output2, x.trash, x.environment))
    (fun x => (x.reference1, x.assistance1, x.retrieved, x.output1)) rho

/-- PDF p.4, (4): receiver 2's complementary broadcastMarginal R1 Btilde1 Aretrieved B1 Ahat E. -/
def shotComplement2 {P : ShotDimensions} {b : Fin 2 → ℕ} {environment : ℕ}
    (rho : Operator (ShotBasis P b environment)) :=
  regroupPartialTrace (fun x : ShotBasis P b environment => (x.reference1, x.assistance1, x.retrieved, x.output1, x.trash, x.environment))
    (fun x => (x.reference2, x.assistance2, x.output2)) rho

/-- PDF p.4, (4): the comparison broadcastMarginal obtained by tracing B1 (not its assistance). -/
def shotPurity1 {P : ShotDimensions} {b : Fin 2 → ℕ} {environment : ℕ}
    (rho : Operator (ShotBasis P b environment)) :=
  regroupPartialTrace (fun x : ShotBasis P b environment => (x.reference1, x.reference2, x.assistance1, x.assistance2,
      x.retrieved, x.output2, x.trash, x.environment))
    (fun x => x.output1) rho

/-- PDF p.4, (4): the comparison broadcastMarginal obtained by tracing B2. -/
def shotPurity2 {P : ShotDimensions} {b : Fin 2 → ℕ} {environment : ℕ}
    (rho : Operator (ShotBasis P b environment)) :=
  regroupPartialTrace (fun x : ShotBasis P b environment => (x.reference1, x.reference2, x.assistance1, x.assistance2,
      x.retrieved, x.output1, x.trash, x.environment))
    (fun x => x.output2) rho

/-- PDF pp.3–4, (4): the finite one-shot error functional. Fourth roots, dimensions, ranks,
purities, and comparison errors are copied from the split display, inspected in the PDF. -/
def shotErrorBound {P : ShotDimensions} {b : Fin 2 → ℕ} {environment : ℕ}
    (psi rho1 rho2 : Operator (ShotBasis P b environment)) : ℝ :=
  4 * Real.rpow
    (((P.message1 + 1 : ℕ) : ℝ) * (P.assistance1 + 1) * (P.retrieved + 1) *
      (Matrix.rank (shotComplement1 rho1) : ℝ) /
      ((P.assistance1 + 1 : ℕ) : ℝ) ^ 2 *
      ((shotPurity1 rho1 * shotPurity1 rho1).trace.re)) (1 / 4 : ℝ) +
  2 * Real.rpow
    (((P.message2 + 1 : ℕ) : ℝ) * (P.assistance2 + 1) *
      (Matrix.rank (shotComplement2 rho2) : ℝ) /
      ((P.assistance2 + 1 : ℕ) : ℝ) ^ 2 *
      ((shotPurity2 rho2 * shotPurity2 rho2).trace.re)) (1 / 4 : ℝ) +
  2 * traceNorm (psi - rho1) + traceNorm (psi - rho2)

/-- PDF pp.7–8: the FULL deterministic classical channel, including dephasing of its input.
The environment flag in the source Stinespring map removes every off-diagonal input term. -/
def deterministicChannel {a : ℕ} {b : Fin 2 → ℕ}
    (f : (j : Fin 2) → BroadcastBasis a → BroadcastBasis (b j)) : Superop (BroadcastBasis a) ((j : Fin 2) → BroadcastBasis (b j)) :=
  fun rho y y' => ∑ i : BroadcastBasis a,
    if y = (fun j => f j i) ∧ y' = (fun j => f j i) then rho i i else 0

/-- PDF p.7, VII: explicit purification with D of the special classically correlated density
sum_i p_i |f1(i)><f1(i)| ⊗ |f2(i)><f2(i)| ⊗ |i><i|. -/
def deterministicInputVector {a : ℕ} {b : Fin 2 → ℕ}
    (f : (j : Fin 2) → BroadcastBasis a → BroadcastBasis (b j)) (p : BroadcastBasis a → ℝ) :
    EuclideanSpace ℂ (((j : Fin 2) → BroadcastBasis (b j)) × (BroadcastBasis a × BroadcastBasis a)) :=
  WithLp.toLp 2 fun x =>
    if x.1 = (fun j => f j x.2.1) ∧ x.2.2 = x.2.1 then (Real.sqrt (p x.2.1) : ℂ) else 0

/-- PDF pp.7–8: channel output computed from that specified purification, tracing D. -/
def deterministicOutput {a : ℕ} {b : Fin 2 → ℕ} (N : Broadcast 2 a b)
    (f : (j : Fin 2) → BroadcastBasis a → BroadcastBasis (b j)) (p : BroadcastBasis a → ℝ) :
    Operator (((j : Fin 2) → BroadcastBasis (b j)) × ((j : Fin 2) → BroadcastBasis (b j))) :=
  idTensorSuperop N.channel (fun x y => ∑ d : BroadcastBasis a,
    pureDensity (deterministicInputVector f p) (x.1, (x.2, d)) (y.1, (y.2, d)))

/-- PDF pp.7–8: closed time-sharing hull of the restricted single-letter input family. -/
def deterministicRegion {a : ℕ} {b : Fin 2 → ℕ} (N : Broadcast 2 a b)
    (f : (j : Fin 2) → BroadcastBasis a → BroadcastBasis (b j)) : Set (Fin 2 → ℝ) :=
  closure (convexHull ℝ {q | ∃ p : BroadcastBasis a → ℝ,
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ q ∈ fatherRegion (deterministicOutput N f p)})

example {b : Fin 2 → ℕ} (x : BroadcastBasis (b 0)) (y : BroadcastBasis (b 1)) :
    pairOutputs x y 0 = x ∧ pairOutputs x y 1 = y := by
  exact ⟨rfl, rfl⟩

/-- PDF p.1: independent pairwise entanglement used for assisted classical communication. -/
def classicalAssistance {m : ℕ} (e : Fin m → ℕ) :
    EuclideanSpace ℂ (((j : Fin m) → BroadcastBasis (e j)) × ((j : Fin m) → BroadcastBasis (e j))) :=
  WithLp.toLp 2 fun x => ∏ j, finiteMaxEntangled (BroadcastBasis (e j)) (x.1 j, x.2 j)

/-- PDF p.1: usual assisted classical codes implicit in superdense coding: independent uniform
messages, arbitrary message-dependent CPTP preparation acting on Alice's shared halves, and
one local POVM per receiver. There is no secrecy, confidentiality, or leakage constraint. -/
structure AssistedBroadcastClassicalCode {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b) (n : ℕ) where
  message : Fin m → ℕ
  assistance : Fin m → ℕ
  encoder : ((j : Fin m) → BroadcastBasis (message j)) →
    Superop ((j : Fin m) → BroadcastBasis (assistance j)) (Fin n → BroadcastBasis a)
  encoder_cptp : ∀ x, IsChannel (encoder x)
  measurement : (j : Fin m) → BroadcastBasis (message j) →
    Operator ((Fin n → BroadcastBasis (b j)) × BroadcastBasis (assistance j))
  measurement_povm : ∀ j, IsPOVM (measurement j)

/-- PDF p.1: actual joint receiver state conditioned on both messages, including their
assistance halves; preparation may create arbitrary mixed block channel inputs. -/
def AssistedBroadcastClassicalCode.received {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : AssistedBroadcastClassicalCode N n) (message : (j : Fin m) → BroadcastBasis (C.message j)) :
    Operator ((j : Fin m) → (Fin n → BroadcastBasis (b j)) × BroadcastBasis (C.assistance j)) :=
  let encoded := mapFirst (C.encoder message) (pureDensity (classicalAssistance C.assistance))
  let transmitted := mapFirst (N.block n) encoded
  fun x y => transmitted
    ((fun j => (x j).1), (fun j => (x j).2))
    ((fun j => (y j).1), (fun j => (y j).2))

/-- PDF p.1: average JOINT decoding error under independent uniform messages. -/
def AssistedBroadcastClassicalCode.error {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : AssistedBroadcastClassicalCode N n) : ℝ :=
  1 - (∑ x : (j : Fin m) → BroadcastBasis (C.message j),
    effectProb (fun y y' => ∏ j, C.measurement j (x j) (y j) (y' j)) (C.received x)) /
      (∏ j, (C.message j + 1 : ℝ))

/-- PDF p.1: classical bits per channel use, log2 of message cardinality divided by block size. -/
def AssistedBroadcastClassicalCode.rate {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : AssistedBroadcastClassicalCode N n) (j : Fin m) : ℝ :=
  Real.logb 2 (C.message j + 1 : ℕ) / (n : ℝ)

/-- PDF p.1: operational assisted classical achievable rates, using vanishing average joint
error and liminf rate bounds. The uniform-message convention is explicit. -/
def classicalAchievable {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b) : Set (Fin m → ℝ) :=
  {c | (∀ j, 0 ≤ c j) ∧ ∃ C : (n : ℕ) → AssistedBroadcastClassicalCode N n,
    Tendsto (fun n => (C n).error) atTop (nhds 0) ∧
    ∀ j, ∀ delta : ℝ, 0 < delta → ∀ᶠ n in atTop, c j - delta ≤ (C n).rate j}

/-- PDF p.1: the closed operational assisted classical capacity region. -/
def assistedBroadcastClassicalCapacity {m a : ℕ} {b : Fin m → ℕ} (N : Broadcast m a b) : Set (Fin m → ℝ) :=
  closure (classicalAchievable N)

example : classicalAssistance (m := 1) (fun _ => 0) (fun _ => 0, fun _ => 0) = 1 := by
  simp [classicalAssistance, finiteMaxEntangled, BroadcastBasis]

example {a : ℕ} {b : Fin 2 → ℕ} (f : (j : Fin 2) → BroadcastBasis a → BroadcastBasis (b j))
    (i : BroadcastBasis a) : deterministicInputVector f (fun _ => 1)
      ((fun j => f j i), (i, i)) = 1 := by
  simp [deterministicInputVector]

/-- Zero-dimensional parameters mean singleton assistance and singleton messages. -/
example : quantumInitial (m := 1) (fun _ => 0) (fun _ => 0)
    (fun _ => 0, (fun _ => (0, 0), fun _ => 0)) = 1 := by
  simp [quantumInitial, finiteMaxEntangled, BroadcastBasis]

/-- Independent references are paired with their own decoded outputs, simultaneously. -/
example {m : ℕ} (k : Fin m → ℕ) (x : (j : Fin m) → BroadcastBasis (k j)) :
    quantumTarget k (x, x) = ∏ j, ((Real.sqrt (k j + 1 : ℕ))⁻¹ : ℂ) := by
  simp [quantumTarget, finiteMaxEntangled, BroadcastBasis]

/-- A singleton message has zero rate even at the harmless zero-use index. -/
example {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : BroadcastTransmissionCode N n) (j : Fin m) (h : C.message j = 0) : C.rate j = 0 := by
  simp [BroadcastTransmissionCode.rate, h]

/-- The deterministic classical channel erases all input coherences. -/
example {a : ℕ} {b : Fin 2 → ℕ} (f : (j : Fin 2) → BroadcastBasis a → BroadcastBasis (b j))
    (rho sigma : Operator (BroadcastBasis a)) (h : ∀ i, rho i i = sigma i i) :
    deterministicChannel f rho = deterministicChannel f sigma := by
  funext y y'
  simp only [deterministicChannel, h]

/-- With no tensor factors the product-channel expansion contains no channel operation. -/
example (F : (j : Fin 0) → Superop Unit Unit) (rho : Operator (Fin 0 → Unit))
    (y y' : Fin 0 → Unit) :
    tensorChannels F rho y y' = ∑ x, ∑ x', rho x x' := by
  simp [tensorChannels]

/-- A singleton classical message contributes zero bits per use. -/
example {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : AssistedBroadcastClassicalCode N n) (j : Fin m) (h : C.message j = 0) : C.rate j = 0 := by
  simp [AssistedBroadcastClassicalCode.rate, h]

/-- The literal source code also measures a singleton message at zero rate. -/
example {m a : ℕ} {b : Fin m → ℕ} {N : Broadcast m a b} {n : ℕ}
    (C : SourceQuantumCode N n) (j : Fin m) (h : C.message j = 0) : C.rate j = 0 := by
  simp [SourceQuantumCode.rate, h]

end QAlgorithms.Papers.Independent.Dependency50.P44


