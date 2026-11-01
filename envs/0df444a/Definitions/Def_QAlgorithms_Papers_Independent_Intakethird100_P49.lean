-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P49
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P49
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:34:53.112937+00:00
-- url     : https://prove2.me/theorems/1dec12cf-4aa4-4671-a687-dc0abfc67251
-- title:
--   Definitions for Fundamental limits to quantum channel discrimination
-- statement:
--   The objects the formalized statements of *Fundamental limits to quantum channel discrimination* (arXiv:1803.02834) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Ports`: PDF pp.2--3, (6): M labelled ports, each of dimension d.
--   - `pbtSignal`: PDF pp.2--3, (6)--(7), Supplement I (65)--(66): Bell projector on C,A_i, identity on the other Alice ports. The common signal normalization cancels in SRM.
--   - `pbtPOVM`: PDF p.3, standard square-root measurement: generalized inverse on the support, with the missing kernel projector shared equally among all M outcomes.
--   - `pbtSelection`: PDF pp.3--4, Fig.2: Alice measures C,A and sends i; Bob keeps B_i and traces out every other port. Formula on ALL joint operators preserves reference coherences. Alice's remaining output is Unit, so this has an explicit LOCC cut.
--   - `bellPorts`: PDF p.3, (6): M independent NORMALIZED Bell pairs, grouped Alice:Bob.
--   - `pbtChannel`: PDF p.3, (7): operational PBT channel, obtained from measurement and port selection with standard Bell resources. This is not defined as a depolarizing map.
--   - `pbtError`: PDF p.3, (8): UNHALVED diamond simulation error of the actual protocol.
--   - `pbtEntanglementFidelity`: PDF p.3, (8): entanglement fidelity against the normalized Bell ket.
--   - `pbtNumber`: PDF p.3, (10): extract depolarizing probability from attenuation of |0><1|. Only d>=2 is used; the otherwise branch is unused and explicitly zero. The theorem, rather than a structure field, identifies the whole channel as depolarizing.
--   - `simulated`: PDF p.4, (12): approximate channel is E composed with the actual PBT channel.
--   - `choiPorts`: PDF p.4, (13): actual M-copy normalized Choi resource, grouped Alice:Bob.
--   - `pbtSimulationInput`: PDF p.4, (13): input and grouped Choi copies at the simulation's correct cut.
--   - `symmetricAdaptiveError`: PDF p.2, (1)--(2): equal-prior operational optimum over the frozen genuine adaptive tests. Each test is fixed before the unknown label and counts n actual calls. At zero calls, every label-independent preparation/POVM has error 1/2. For CPTP pairs the positive-use infimum is nonempty and contained in [0,1].
--   - `testOutput`: PDF p.2: terminal register before the final POVM, for a positive-use test.
--   - `AdaptiveProtocol`: PDF pp.1--2, arbitrary-task protocol: arbitrary finite retained memory, normalized preparation and CPTP interleavings, independent of E. A fixed maximum memory accommodates changing finite dimensions. Both terminal channels are explicit; only terminalZero is used at n=0, and only terminal is used at positive n.
--   - `protocolInput`: PDF p.2: state entering the next actual call; the kth interleaving follows it.
--   - `adaptiveProtocolOutput`: PDF pp.2,4: computed general-task terminal output, including the no-call case.
--   - `universalBound`: PDF p.4, (20): the unclipped bound at the integer port count M.
--   - `meanSimulationError`: PDF p.6, (30): the average of the two actual unhalved channel errors.
--   - `qubitNumberFormula`: PDF p.3, (11): k=(M-1)/2-s is an integer. Real exponents avoid truncated M-4 at M=2,3. The sum includes the s=0 term when M is odd.
--   - `dampingFidelity`: PDF p.7, (35): explicit root fidelity scalar, not its square.
--   - `dampingSimulationError`: PDF p.7, (36): explicit candidate for the actual simulation error.
--   - `bellProbeBlockError`: PDF pp.6--7, (34): independent Bell probes and optimal JOINT measurement.
--   - `opticalChannel`: Supplement II, PDF p.15, (117)--(124): coherent vacuum/one-photon qubit-to-qutrit imaging channel. sign=false/true selects the plus/minus position. Output order is vacuum, symmetric mode, antisymmetric mode. Printed (121) has a fixed minus; the relative sign here follows the defining (117),(118),(124).
--   - `opticalAntiBell`: Supplement II, PDF p.15: the source's anti-Bell input, reference FIRST.
--   - `opticalChoi`: Supplement II, PDF p.15, (125)--(126): source Choi states, computed from actual coherent channels using the anti-Bell convention.
--   - `opticalPsi`: Supplement II, PDF p.15, (127), with reference/output order made explicit. The leakage vacuum is the JOINT reference/output vacuum (0,0).
--   - `illuminationNoise`: Supplement III, PDF pp.16--17, (145)--(146): d one-photon modes plus vacuum, with one photon TOTAL. Physical range is b>=0, d*b<=1.
--   - `illuminationChannel`: Supplement III, PDF p.17, (146): target absent (replacement by tau_b), or present (mixture of that channel with identity). Defined on every operator.
--   - `illuminationOmegaSquared`: Supplement III, PDF p.17, (148): actual positive product sqrt(sigma)*rho*sqrt(sigma). Canonical reference-first Choi order is a common swap of the source's order.
--   - `illuminationBlock`: Supplement III, PDF p.17, corrected (149), already divided by (d+1)^2. Printed positive-mode diagonal b*(b+eta) is changed to (1-eta)*b^2+eta*b, as forced by exact (148). This correction requires independent moderation.
--   - `AdmissiblePrivateMeasure`: Supplement V, PDF p.19, (178)--(182): the source's admissible entanglement-measure properties on ACTUAL finite bipartite states. Continuity has an explicit full-norm domain and compared-state dimension, and applies to all errors at most gamma. Normalization uses private targets of arbitrary finite shield size; no uniform shield-dimension restriction is imposed.
--   - `realREE`: Supplement V, PDF p.20, (184): finite REAL state REE in bits, before any subtraction. For normalized finite-dimensional states the accepted REE is finite, since the normalized identity is a full-support separable comparison. The toReal default at infinity is therefore never used on the theorem's states.
--   - `amortizedREE`: Supplement V, PDF p.20, (184): amortized REE, an EXTENDED supremum of finite real differences. Positive finite memories on BOTH sides are optimized. The input cut is (a',a):b', correcting the printed b to b'; the output cut is a':(b,b'). The extension of the ACTUAL channel retains all coherences.
--   - `capacityContinuity`: Supplement V, PDF p.20, (186): continuity function, including 0*log(0)=0.
--   - `privateCapacityBound`: Supplement V, PDF p.20, (190): explicit bound for an INTEGER port count.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, https://arxiv.org/abs/1803.02834v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P07

/-!
Pirandola--Laurenza--Lupo--Pereira, arXiv:1803.02834v4.
Only the assigned paper's new definitions live here. Standard deterministic PBT
is computed from its square-root POVM and Bell resources, never postulated to be
depolarizing. All channel distances are unhalved; state distance is half trace norm.
Source issues and deferred approximate claims are recorded in HARD.md.
Compilation and independent moderation are pending their separate handoffs.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P49

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)
open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)
open QAlgorithms.Papers.Independent.Information100.P71 (diamond AdaptiveTest adaptiveInput adaptiveAccept)
open QAlgorithms.Papers.Independent.Bridge50.P25
  (LOCCOn normalizedChannelChoi TwoWayGenerationCode TwoWayChannelProtocol
   generationCodeError twoWayGenerationCapacity sendChannelRegister StateFunctional
   IsDimensionChangingLOCCMonotone privateStateInPartyOrder)
open QAlgorithms.Papers.Independent.Support50.P07 (amplitudeDampingChannel)

/-- PDF pp.2--3, (6): M labelled ports, each of dimension d. -/
abbrev Ports (d M : ℕ) := Fin M → Fin d

/-- PDF pp.2--3, (6)--(7), Supplement I (65)--(66): Bell projector on C,A_i,
identity on the other Alice ports. The common signal normalization cancels in SRM. -/
def pbtSignal (d M : ℕ) (i : Fin M) : Mat (Fin d × Ports d M) :=
  fun p q => if p.1 = p.2 i ∧ q.1 = q.2 i ∧
    (∀ j, j ≠ i → p.2 j = q.2 j) then (1 / (d : ℂ)) else 0

/-- PDF p.3, standard square-root measurement: generalized inverse on the support,
with the missing kernel projector shared equally among all M outcomes. -/
def pbtPOVM (d M : ℕ) (i : Fin M) : Mat (Fin d × Ports d M) :=
  let S := ∑ j : Fin M, pbtSignal d M j
  let R := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) S
  R * pbtSignal d M i * R + (1 / (M : ℂ)) • (1 - R * S * R)

/-- PDF pp.3--4, Fig.2: Alice measures C,A and sends i; Bob keeps B_i and
traces out every other port. Formula on ALL joint operators preserves reference
coherences. Alice's remaining output is Unit, so this has an explicit LOCC cut. -/
def pbtSelection (d e M : ℕ) :
    Superop ((Fin d × Ports d M) × Ports e M) (Unit × Fin e) :=
  fun X u v => ∑ i : Fin M, ∑ p : Fin d × Ports d M, ∑ q : Fin d × Ports d M,
    ∑ b : Ports e M, ∑ c : Ports e M,
      if b i = u.2 ∧ c i = v.2 ∧ (∀ j, j ≠ i → b j = c j)
      then pbtPOVM d M i q p * X (p,b) (q,c) else 0

/-- PDF p.3, (6): M independent NORMALIZED Bell pairs, grouped Alice:Bob. -/
def bellPorts (d M : ℕ) : Mat (Ports d M × Ports d M) :=
  fun p q => ∏ i, if p.1 i = p.2 i ∧ q.1 i = q.2 i then (1 / (d : ℂ)) else 0

/-- PDF p.3, (7): operational PBT channel, obtained from measurement and port
selection with standard Bell resources. This is not defined as a depolarizing map. -/
def pbtChannel (d M : ℕ) : Superop (Fin d) (Fin d) :=
  fun X a b => pbtSelection d d M
    (fun p q => X p.1.1 q.1.1 * bellPorts d M (p.1.2,p.2) (q.1.2,q.2))
    ((),a) ((),b)

/-- PDF p.3, (8): UNHALVED diamond simulation error of the actual protocol. -/
def pbtError (d M : ℕ) : ℝ := diamond (fun X => X - pbtChannel d M X)

/-- PDF p.3, (8): entanglement fidelity against the normalized Bell ket. -/
def pbtEntanglementFidelity (d M : ℕ) [NeZero d] : ℝ :=
  let v := finiteMaxEntangled (Fin d)
  (∑ a, ∑ b, conj (v a) * normalizedChannelChoi (pbtChannel d M) a b * v b).re

/-- PDF p.3, (10): extract depolarizing probability from attenuation of |0><1|.
Only d>=2 is used; the otherwise branch is unused and explicitly zero.
The theorem, rather than a structure field, identifies the whole channel as depolarizing. -/
def pbtNumber (d M : ℕ) : ℝ :=
  if hd : 2 ≤ d then
    let z : Fin d := ⟨0, by omega⟩
    let o : Fin d := ⟨1, by omega⟩
    1 - (pbtChannel d M (Matrix.single z o 1) z o).re
  else 0

/-- PDF p.4, (12): approximate channel is E composed with the actual PBT channel. -/
def simulated {d e : ℕ} (E : Superop (Fin d) (Fin e)) (M : ℕ) :
    Superop (Fin d) (Fin e) := E ∘ pbtChannel d M

/-- PDF p.4, (13): actual M-copy normalized Choi resource, grouped Alice:Bob. -/
def choiPorts {d e : ℕ} [NeZero d] (E : Superop (Fin d) (Fin e)) (M : ℕ) :
    Mat (Ports d M × Ports e M) :=
  fun p q => ∏ i, normalizedChannelChoi E (p.1 i,p.2 i) (q.1 i,q.2 i)

/-- PDF p.4, (13): input and grouped Choi copies at the simulation's correct cut. -/
def pbtSimulationInput {d e : ℕ} [NeZero d] (E : Superop (Fin d) (Fin e))
    (M : ℕ) (X : Mat (Fin d)) : Mat ((Fin d × Ports d M) × Ports e M) :=
  fun p q => X p.1.1 q.1.1 * choiPorts E M (p.1.2,p.2) (q.1.2,q.2)

/-- PDF p.2, (1)--(2): equal-prior operational optimum over the frozen genuine
adaptive tests. Each test is fixed before the unknown label and counts n actual
calls. At zero calls, every label-independent preparation/POVM has error 1/2.
For CPTP pairs the positive-use infimum is nonempty and contained in [0,1]. -/
def symmetricAdaptiveError {d e : ℕ} (n : ℕ) (E0 E1 : Superop (Fin d) (Fin e)) : ℝ :=
  if n = 0 then 1 / 2 else
    sInf {p | ∃ P : AdaptiveTest (Fin d) (Fin e) n,
      p = (1 - adaptiveAccept P E0 + adaptiveAccept P E1) / 2}

/-- PDF p.2: terminal register before the final POVM, for a positive-use test. -/
def testOutput {d e n : ℕ} (P : AdaptiveTest (Fin d) (Fin e) n)
    (E : Superop (Fin d) (Fin e)) : Mat (Fin P.memory × Fin e) :=
  idTensorSuperop E (adaptiveInput P E (n - 1))

/-- PDF pp.1--2, arbitrary-task protocol: arbitrary finite retained memory,
normalized preparation and CPTP interleavings, independent of E. A fixed maximum
memory accommodates changing finite dimensions. Both terminal channels are explicit;
only terminalZero is used at n=0, and only terminal is used at positive n. -/
structure AdaptiveProtocol (d e o n : ℕ) where
  memory : ℕ
  memory_pos : 0 < memory
  initial : Mat (Fin memory × Fin d)
  initial_density : IsDensityMatrix initial
  between : ℕ → Superop (Fin memory × Fin e) (Fin memory × Fin d)
  between_channels : ∀ k, IsChannel (between k)
  terminalZero : Superop (Fin memory × Fin d) (Fin o)
  terminalZero_channel : IsChannel terminalZero
  terminal : Superop (Fin memory × Fin e) (Fin o)
  terminal_channel : IsChannel terminal

/-- PDF p.2: state entering the next actual call; the kth interleaving follows it. -/
def protocolInput {d e o n : ℕ} (P : AdaptiveProtocol d e o n)
    (E : Superop (Fin d) (Fin e)) : ℕ → Mat (Fin P.memory × Fin d)
  | 0 => P.initial
  | k + 1 => P.between k (idTensorSuperop E (protocolInput P E k))

/-- PDF pp.2,4: computed general-task terminal output, including the no-call case. -/
def adaptiveProtocolOutput {d e o n : ℕ} (P : AdaptiveProtocol d e o n)
    (E : Superop (Fin d) (Fin e)) : Mat (Fin o) :=
  if n = 0 then P.terminalZero P.initial
  else P.terminal (idTensorSuperop E (protocolInput P E (n - 1)))

/-- PDF p.4, (20): the unclipped bound at the integer port count M. -/
def universalBound {d e : ℕ} [NeZero d] (n M : ℕ)
    (E0 E1 : Superop (Fin d) (Fin e)) : ℝ :=
  (1 - n * pbtError d M - traceDistance
    (tensorPower (n * M) (normalizedChannelChoi E0))
    (tensorPower (n * M) (normalizedChannelChoi E1))) / 2

/-- PDF p.6, (30): the average of the two actual unhalved channel errors. -/
def meanSimulationError {d e : ℕ} (M : ℕ)
    (E0 E1 : Superop (Fin d) (Fin e)) : ℝ :=
  (diamond (fun X => E0 X - simulated E0 M X) +
   diamond (fun X => E1 X - simulated E1 M X)) / 2

/-- PDF p.3, (11): k=(M-1)/2-s is an integer. Real exponents avoid truncated
M-4 at M=2,3. The sum includes the s=0 term when M is odd. -/
def qubitNumberFormula (M : ℕ) : ℝ :=
  ((M : ℝ) + 2) / (3 * (2 : ℝ) ^ ((M : ℝ) - 1)) +
    (1 / 3 : ℝ) * ∑ k ∈ Finset.range ((M - 1) / 2 + 1),
      let s := ((M : ℝ) - 1) / 2 - (k : ℝ)
      s * (s + 1) / (2 : ℝ) ^ ((M : ℝ) - 4) * (M.choose k : ℝ) *
        (((M : ℝ) + 2) - Real.sqrt (((M : ℝ) + 2)^2 - (2*s+1)^2)) /
          (((M : ℝ) + 2)^2 - (2*s+1)^2)

/-- PDF p.7, (35): explicit root fidelity scalar, not its square. -/
def dampingFidelity (p q : ℝ) : ℝ :=
  (1 + Real.sqrt ((1-p)*(1-q)) + Real.sqrt (p*q)) / 2

/-- PDF p.7, (36): explicit candidate for the actual simulation error. -/
def dampingSimulationError (M : ℕ) (p : ℝ) : ℝ :=
  pbtNumber 2 M * ((1-p)/2 + Real.sqrt (1-p))

/-- PDF pp.6--7, (34): independent Bell probes and optimal JOINT measurement. -/
def bellProbeBlockError {d e : ℕ} [NeZero d] (n : ℕ)
    (E0 E1 : Superop (Fin d) (Fin e)) : ℝ :=
  (1 - traceDistance (tensorPower n (normalizedChannelChoi E0))
    (tensorPower n (normalizedChannelChoi E1))) / 2

/-! Sanity examples pin operational construction and boundary conventions. -/

example {d e : ℕ} (E0 E1 : Superop (Fin d) (Fin e)) :
    symmetricAdaptiveError 0 E0 E1 = 1 / 2 := by simp [symmetricAdaptiveError]

example {d e o : ℕ} (P : AdaptiveProtocol d e o 0)
    (E : Superop (Fin d) (Fin e)) :
    adaptiveProtocolOutput P E = P.terminalZero P.initial := by simp [adaptiveProtocolOutput]

example (d M : ℕ) (i : Fin M) (p q : Fin d × Ports d M)
    (h : p.1 ≠ p.2 i) : pbtSignal d M i p q = 0 := by simp [pbtSignal, h]

example {d e : ℕ} [NeZero d] (E : Superop (Fin d) (Fin e))
    (p q : Ports d 0 × Ports e 0) : choiPorts E 0 p q = 1 := by simp [choiPorts]

example : dampingFidelity 0 1 = 1 / 2 := by norm_num [dampingFidelity]

/-- Supplement II, PDF p.15, (117)--(124): coherent vacuum/one-photon
qubit-to-qutrit imaging channel. sign=false/true selects the plus/minus position.
Output order is vacuum, symmetric mode, antisymmetric mode. Printed (121) has
a fixed minus; the relative sign here follows the defining (117),(118),(124). -/
def opticalChannel (eta delta : ℝ) (sign : Bool) : Superop (Fin 2) (Fin 3) :=
  let a := Real.sqrt ((1+delta)*eta/2)
  let b := (if sign then -1 else 1 : ℝ) * Real.sqrt ((1-delta)*eta/2)
  krausApply ![!![1, 0; 0, (a : ℂ); 0, (b : ℂ)],
    !![0, (Real.sqrt (1-eta) : ℂ); 0, 0; 0, 0]]

/-- Supplement II, PDF p.15: the source's anti-Bell input, reference FIRST. -/
def opticalAntiBell : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun p => if p.1 ≠ p.2 then ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- Supplement II, PDF p.15, (125)--(126): source Choi states, computed
from actual coherent channels using the anti-Bell convention. -/
def opticalChoi (eta delta : ℝ) (sign : Bool) : Mat (Fin 2 × Fin 3) :=
  idTensorSuperop (opticalChannel eta delta sign) (pureDensity opticalAntiBell)

/-- Supplement II, PDF p.15, (127), with reference/output order made explicit.
The leakage vacuum is the JOINT reference/output vacuum (0,0). -/
def opticalPsi (eta delta : ℝ) (sign : Bool) : EuclideanSpace ℂ (Fin 2 × Fin 3) :=
  WithLp.toLp 2 fun p =>
    ((if p = (1,0) then 1 else if p = (0,1) then Real.sqrt ((1+delta)*eta/2)
      else if p = (0,2) then (if sign then -1 else 1)*Real.sqrt ((1-delta)*eta/2)
      else 0 : ℝ) / Real.sqrt (1+eta) : ℂ)

/-- Supplement III, PDF pp.16--17, (145)--(146): d one-photon modes plus
vacuum, with one photon TOTAL. Physical range is b>=0, d*b<=1. -/
def illuminationNoise (d : ℕ) (b : ℝ) : Mat (Fin (d+1)) :=
  Matrix.diagonal fun j => ((if j.val = 0 then 1-d*b else b : ℝ) : ℂ)

/-- Supplement III, PDF p.17, (146): target absent (replacement by tau_b),
or present (mixture of that channel with identity). Defined on every operator. -/
def illuminationChannel (d : ℕ) (b eta : ℝ) : Superop (Fin (d+1)) (Fin (d+1)) :=
  fun X => ((1-eta : ℝ) : ℂ) • (X.trace • illuminationNoise d b) + (eta : ℂ) • X

/-- Supplement III, PDF p.17, (148): actual positive product sqrt(sigma)*rho*sqrt(sigma).
Canonical reference-first Choi order is a common swap of the source's order. -/
def illuminationOmegaSquared (d : ℕ) (b eta : ℝ) : Mat (Fin (d+1) × Fin (d+1)) :=
  let sigma := normalizedChannelChoi (illuminationChannel d b 0)
  let rho := normalizedChannelChoi (illuminationChannel d b eta)
  cfc Real.sqrt sigma * rho * cfc Real.sqrt sigma

/-- Supplement III, PDF p.17, corrected (149), already divided by (d+1)^2.
Printed positive-mode diagonal b*(b+eta) is changed to (1-eta)*b^2+eta*b,
as forced by exact (148). This correction requires independent moderation. -/
def illuminationBlock (d : ℕ) (b eta : ℝ) : Mat (Fin (d+1)) :=
  fun i j =>
    ((if i.val = 0 ∧ j.val = 0 then (1-eta)*(1-d*b)^2+eta*(1-d*b)
      else if i.val = 0 ∨ j.val = 0 then eta*Real.sqrt ((1-d*b)*b)
      else if i = j then (1-eta)*b^2+eta*b else eta*b : ℝ) /
      ((d : ℝ)+1)^2 : ℂ)

/-- Supplement V, PDF p.19, (178)--(182): the source's admissible
entanglement-measure properties on ACTUAL finite bipartite states. Continuity
has an explicit full-norm domain and compared-state dimension, and applies to
all errors at most gamma. Normalization uses private targets of arbitrary finite
shield size; no uniform shield-dimension restriction is imposed. -/
def AdmissiblePrivateMeasure (E : StateFunctional) (g h : ℝ → ℝ) (domain : Set ℝ) : Prop :=
  IsDimensionChangingLOCCMonotone E ∧
  Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
  Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
  domain ⊆ Set.Ici 0 ∧
  (∀ (A B C D : Type) [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype D] [DecidableEq D] [Nonempty D]
    (rho : Mat (A × B)) (sigma : Mat (C × D)),
    IsDensityMatrix rho → IsDensityMatrix sigma →
    E (A × C) (B × D) (bipartiteTensor rho sigma) ≤ E A B rho + E C D sigma) ∧
  (∀ (k s : ℕ) (sigma : Mat (Fin (s+1) × Fin (s+1)))
    (U : Fin (2^k) → Matrix.unitaryGroup (Fin (s+1) × Fin (s+1)) ℂ),
    IsDensityMatrix sigma →
    (k : ℝ) ≤ E (Fin (2^k) × Fin (s+1)) (Fin (2^k) × Fin (s+1))
      (privateStateInPartyOrder (2^k) s sigma U)) ∧
  (∀ (A B : Type) [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (rho sigma : Mat (A × B)) (gamma : ℝ),
    IsDensityMatrix rho → IsDensityMatrix sigma → gamma ∈ domain →
    traceNorm (rho-sigma) ≤ gamma →
    |E A B rho - E A B sigma| ≤
      g gamma * Real.logb 2 (Fintype.card A * Fintype.card B) + h gamma)

/-- Supplement V, PDF p.20, (184): finite REAL state REE in bits, before
any subtraction. For normalized finite-dimensional states the accepted REE is
finite, since the normalized identity is a full-support separable comparison.
The toReal default at infinity is therefore never used on the theorem's states. -/
def realREE {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (rho : Mat (A × B)) : ℝ :=
  (QAlgorithms.Papers.Independent.Information100.P54.relativeEntanglement rho).toReal

/-- Supplement V, PDF p.20, (184): amortized REE, an EXTENDED supremum of
finite real differences. Positive finite memories on BOTH sides are optimized.
The input cut is (a',a):b', correcting the printed b to b'; the output cut
is a':(b,b'). The extension of the ACTUAL channel retains all coherences. -/
def amortizedREE {d e : ℕ} [NeZero d] [NeZero e]
    (E : Superop (Fin d) (Fin e)) : EReal :=
  sSup {v | ∃ a b : ℕ, ∃ rho : Mat ((Fin (a+1) × Fin d) × Fin (b+1)),
    IsDensityMatrix rho ∧
    v = ((realREE (sendChannelRegister E rho) - realREE rho : ℝ) : EReal)}

/-- Supplement V, PDF p.20, (186): continuity function, including 0*log(0)=0. -/
def capacityContinuity (t : ℝ) : ℝ :=
  (1+t)*Real.logb 2 (1+t) - t*Real.logb 2 t

/-- Supplement V, PDF p.20, (190): explicit bound for an INTEGER port count. -/
def privateCapacityBound (d M : ℕ) [NeZero d]
    (E : Superop (Fin d) (Fin d)) : ℝ :=
  M * realREE (normalizedChannelChoi E) +
    2*(d : ℝ)*(d-1 : ℝ)/M * Real.logb 2 d +
    capacityContinuity ((d : ℝ)*(d-1 : ℝ)/M)

example (eta delta : ℝ) (s : Bool) :
    opticalPsi eta delta s (1,0) = ((1 / Real.sqrt (1+eta) : ℝ) : ℂ) := by
  simp [opticalPsi]

example (d : ℕ) (b : ℝ) (i : Fin (d+1)) :
    illuminationNoise d b i i = ((if i.val = 0 then 1-d*b else b : ℝ) : ℂ) := by
  simp [illuminationNoise]

example (d : ℕ) (b : ℝ) : illuminationChannel d b 1 = id := by
  funext X
  simp [illuminationChannel]

example {A B C D : Type} (rho : Mat (A × B)) (sigma : Mat (C × D))
    (p q : (A × C) × (B × D)) : bipartiteTensor rho sigma p q =
    rho (p.1.1,p.2.1) (q.1.1,q.2.1) * sigma (p.1.2,p.2.2) (q.1.2,q.2.2) := rfl

example : capacityContinuity 0 = 0 := by simp [capacityContinuity]

end QAlgorithms.Papers.Independent.Intakethird100.P49


