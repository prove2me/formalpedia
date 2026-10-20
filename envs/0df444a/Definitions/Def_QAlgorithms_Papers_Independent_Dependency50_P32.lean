-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32
-- name    : QAlgorithms_Papers_Independent_Dependency50_P32
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T14:44:11.791549+00:00
-- url     : https://prove2.me/theorems/465b9e16-9614-4c9b-8efc-1d5ac5fcaeb3
-- title:
--   Definitions for One-Shot Manipulation of Dynamical Quantum Resources
-- statement:
--   The objects the formalized statements of *One-Shot Manipulation of Dynamical Quantum Resources* (arXiv:2012.02215) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Port`: PDF p.2: positive finite input and output dimensions.
--   - `ChannelChoi`: PDF p.9 (A8): specialize the accepted raw input-first Choi carrier to positive port dimensions. CPTP below imposes the unnormalized trace din.
--   - `CPTP`: CPTP Choi condition: positivity and output partial trace equal to identity.
--   - `applyChoi`: The complex-linear matrix-unit reconstruction E(X), p.9 (A8). No transpose is omitted: J[(i,b),(j,c)] = E(|i><j|)[b,c].
--   - `ResourceTheory`: Allowed channel fibres and their designated free subsets, PDF p.2. Regular records the printed free-set assumptions; ClosedConvexAllowed separately records the extra allowed-set hypothesis used by the corrected conversion results.
--   - `Regular`: Printed standing assumptions, PDF p.2: nonempty closed convex free fibres contained in physically allowed CPTP channels. No regularity of the allowed subset is imposed here.
--   - `ClosedConvexAllowed`: Explicit correction to the unrestricted allowed-subset scope on PDF p.2. Printed: only the free fibres are assumed closed and convex. Changed: the conversion results additionally assume closed convex allowed fibres. Why: (B3),(B8),(D7) mix allowed channels, and their minimizing robustness witnesses can fail to exist on a nonclosed allowed set. The testing/support identities use Regular alone and retain the printed allowed-subset generality.
--   - `Deterministic`: Physical deterministic superchannel: a CPTP pre/post-processing dilation with finite positive memory, p.13 (D3). The equality holds on every input operator and every channel argument, hence includes entangled inputs.
--   - `FreeSuperchannel`: The maximal allowed-structure and free-preserving deterministic set S, p.2.
--   - `PureInput`: Normalized pure input and an input-sized reference, pp.2,8.
--   - `pureChannelOutput`: Reference-assisted channel output on a pure input.
--   - `worstCaseFidelity`: Worst-case, reference-assisted squared channel fidelity, p.2. The state domain is compact, nonempty and normalized for these positive dimensions.
--   - `PureTarget`: Purity after id tensor N on EVERY normalized pure reference-assisted input, Theorems 3 and 6, pp.3,12.
--   - `ball`: Fidelity ball inside the physically allowed fibre. Tolerances >=1 mean all allowed channels, as required by the oversmoothed bound in Theorem 1.
--   - `smooth`: Extended smoothing infimum, pp.2,10. No optimizer for arbitrary monotones is assumed; quantitative optimizer statements are separate conclusions.
--   - `robustness`: Eq.(1), p.2: multiplicative robustness with noise in the specified family. The witness noise is physical and the free mixture is an actual free channel.
--   - `standard`: Standard robustness: free noise, Eq.(1).
--   - `maximal`: Generalized robustness: all physically allowed noise, Eq.(1).
--   - `Test`: Feasible hypothesis test, with normalization built into PureInput, (A1).
--   - `inverseTestingValue`: The inverse ordinary testing resource, in the original max_M min_(psi,P) order (A3). All probability reciprocals are extended, including at zero.
--   - `testing`: Ordinary hypothesis-testing resource, Eq.(2), pp.2,8.
--   - `betaAffine`: Affine saddle extension (A6): the inner affine supremum is infinity for nonconstant free overlaps. This avoids reciprocals of signed affine outputs. Clipping individual real overlaps below zero does not change this supremum: the affine hull contains nonempty free CPTP channels and so has nonnegative sup.
--   - `testingAffine`: Affine hypothesis testing, pp.8-9 (A6)-(A7).
--   - `minimum`: Ordinary min-resource is zero-error ordinary testing, pp.2,9.
--   - `affineSupportValues`: The extended equal-overlap support domain, (A15) and the Remark, pp.10-11. An empty set gives infinity BEFORE inversion, hence affine min-resource zero.
--   - `minimumAffine`: Affine min-resource, distinct from zero-error affine testing.
--   - `gauge`: Reciprocal-threshold gauge (A9). The threshold formulation includes m=infinity as threshold zero, but never assigns G(E;0) a value.
--   - `gaugeAffine`: Equal-overlap affine gauge, with the printed supremum convention (A10).
--   - `pureTestValues`: The inverse testing program in Lemma 5; lambda is minimized jointly with psi and P, rather than postulated as an unrelated optimum.
--   - `ChoiTester`: Choi tester bounds 0<=Q<=rho tensor I, (A8).
--   - `choiTestValues`: (A8), with normalized rho, physical operator order, and actual lambda domain.
--   - `choiGaugeValues`: Choi gauge objective values (A10), jointly optimized over rho,W.
--   - `Dual`: Positive dual and affine annihilator (A11); all variables are Hermitian. The affine object is an annihilator, NOT the nonnegative dual of an affine hull.
--   - `choiTraceUnit`: Joint identity divided by INPUT dimension; its pairing with a CPTP Choi matrix is one, (A12), p.9.
--   - `coneTestValues`: Concrete dual-cone test program (A12).
--   - `coneGaugeValues`: Concrete dual-cone gauge program (A12), for strictly positive finite m.
--   - `SDPRepresentable`: Finite semidefinite representability: projection of one affine Hermitian positive-semidefinite pencil, with finitely many real auxiliary variables. Block diagonalization includes finite intersections and real linear equalities. No runtime or bit-complexity assertion is implicit in this predicate.
--   - `testFeasible`: Unprojected test feasible set. Its objective is the last, real coordinate.
--   - `gaugeFeasible`: Unprojected gauge feasible set; objective is the real linear Choi pairing.
--   - `bestFidelity`: Supremum channel fidelity; theorems explicitly supply a maximizing Theta.
--   - `Converts`: A conversion witness in the maximal physical free set.
--   - `References`: A reference family may contain channels of different finite dimensions.
--   - `ValidReferences`: Physically admissible references; neither nonemptiness nor compactness of an arbitrary reference family is assumed, (3),(C1)-(C3).
--   - `referenceValues`: Reference scale fixed to ordinary min-resource in Eq.(3).
--   - `referenceFloor`: Supremum over attainable reference VALUES below x, (C3), not Nat.floor.
--   - `referenceCeiling`: Infimum over attainable reference VALUES above x, (C3), not Nat.ceil.
--   - `oneShotDistillable`: Operational distillation, with the supremum convention of Eq.(3).
--   - `oneShotCost`: Operational dilution; conversion direction is reversed, Eq.(3).
--   - `QuantitativeAttainment`: Quantitative smoothing optimizers used in (B3),(B8),(B13), pp.10-12. They are conclusions for robustness, not assumptions about arbitrary monotones.
--   - `supportMaximum`: Support-overlap maximum for one normalized pure input, (A13).
--   - `transmissionPort`: Positive-dimensional identity target for Eq.(4), p.4.
--   - `identityChoi`: Unnormalized Choi operator of id_d.
--   - `Separable`: Separable density operators: convex hull of product density operators.
--   - `partialTranspose`: Partial transpose on the second tensor factor.
--   - `replacement`: Replacement-channel Choi matrix R_sigma(X)=Tr(X)sigma, p.4.
--   - `CommunicationKind`: The three communication resource theories on p.4.
--   - `communicationTheory`: Free TRANSMISSION channels. SEP uses the input/output Choi partition; PPT means CPTP with positive partial transpose, never trace-decreasing maps; NS assistance is the maximal replacement-preserving superchannel theory.
--   - `log2Resource`: Extended nonnegative base-two rate. Infinity is handled before toReal. Only resource values >=1 (or their integer reference rounding) occur below.
--   - `integerReferenceValues`: Attainable reference values d^k, for positive integer d.
--   - `integerFloor`: Reference floor for integer dimensions (k=1) or squares (k=2).
--   - `integerCeiling`: Reference ceiling for integer dimensions (k=1) or squares (k=2).
--   - `assistedOneShotCapacity`: Operational quantum capacity, Eq.(4). Attainment is stated below.
--   - `simulationCost`: Operational quantum simulation cost, Eq.(4), with reversed conversion.
--   - `RateAttainment`: Printed max/min in Eq.(4), supplying actual dimensions AND codes.
--   - `choiFidelity`: Fixed maximally entangled-input fidelity (D9): normalized Choi states.
--   - `bestChoiFidelity`: Optimal fixed-input fidelity, with the same deterministic free set.
--   - `preparationPort`: Trivial-input preparation port, pp.13-14.
--   - `preparationChoi`: Choi operator of the preparation P_rho; the input register has dimension one.
--   - `stateRobustness`: State-level multiplicative robustness, with physical noise specified.
--   - `stateStandard`: State standard robustness.
--   - `stateMaximal`: State generalized robustness, with all density operators as noise.
--   - `stateMinimum`: State min-resource; the support overlap is maximized over free states.
--   - `stateMinimumAffine`: Affine state min-resource: constant support overlap over all free states, with empty inverse domain interpreted exactly as in (A15).
--   - `PreparationTheory`: Underlying state free-operation convention, pp.13-14: all preparations are physically allowed, and free preparations produce exactly the free states. The iff exposes both the printed inclusion and the proof-used preservation of free states from the trivial free input; it is not an assumed resource equality.
--   - `stateReferences`: Reference preparations of a family of normalized pure state vectors.
--   - `Split`: Alice and Bob input/output dimensions for bipartite channels and boxes.
--   - `splitCode`: A tag preserves physical wire structure even when total dimensions agree.
--   - `bipartitePort`: Bipartite-channel port, with Alice/Bob partition included in the tag.
--   - `castChoi`: Re-express the same matrix in an equal port type.
--   - `groupedChoi`: Regroup input-first Choi wires as (Alice input,output):(Bob input,output). This differs from the transmission-channel input:output partition on p.4.
--   - `bipartiteTheory`: Bipartite SEP/PPT CHANNEL theories, Appendix E, p.14. At encoded ports all CPTP maps are allowed; the free condition uses the party grouping.
--   - `entangledTargetPort`: Preparation of the d-dimensional maximally entangled state, Eq.(E2).
--   - `entangledTarget`: Density matrix of the maximally entangled target, represented as a trivial-input preparation Choi matrix; its nonzero entries are 1/d.
--   - `entanglementDistillation`: One-shot distillable CHANNEL entanglement, Eq.(E2), log base two.
--   - `entanglementCost`: One-shot channel entanglement cost, Eq.(E2).
--   - `EntanglementAttainment`: Actual optimal entangled dimensions and physical codes in Eq.(E2).
--   - `boxPort`: Classical-classical box port; parties' classical wires remain tagged.
--   - `Kernel`: Conditional probabilities P(a,b|x,y) of a finite bipartite box.
--   - `NoSignalling`: Normalized nonnegative no-signalling boxes, p.4: neither marginal is allowed to depend on the other party's input.
--   - `deterministicKernel`: Deterministic local response, with arbitrary local input dependence.
--   - `IsLocalBox`: Local boxes are mixtures of deterministic local responses (shared randomness).
--   - `boxChoi`: Complete dephasing on both input and output embeds a classical box as an actual CPTP channel; off-diagonal joint input operators map to zero.
--   - `boxTheory`: Nonlocality resource theory: all no-signalling classical channels are allowed and all local shared-randomness boxes are free, p.4 and Appendix F.
--   - `binarySplit`: The standard two-input, two-output binary Bell scenario.
--   - `prKernel`: PR correlations P(a,b|x,y)=1/2 when a xor b=xy, and zero otherwise.
--   - `randomKernel`: White noise is the uniform box, Fig.1, p.15.
--   - `noisyKernel`: Convex mixing of binary boxes, with the NOISE weight equal to e.
--   - `isotropicKernel`: Isotropic box B_p=(1-p)B_PR+p B_random, Fig.1.
--   - `bitLabels`: Finite-copy register equivalence; the same labels are used for all wires.
--   - `copySplit`: n copies, grouped with all Alice wires together and all Bob wires together.
--   - `tensorKernel`: Tensor-product box probabilities, with collective local n-bit input/output registers. Local free boxes on these registers may correlate different copies.
--   - `MeasurementFamily`: A finite set of finite-outcome POVMs, Appendix G, pp.15-16.
--   - `ValidMeasurements`: Every setting is a normalized positive operator-valued measurement.
--   - `CompatiblePOVMs`: Compatibility: a finite normalized parent POVM and a genuine conditional probability distribution q(a|x,i), reproducing every measurement effect, p.4.
--   - `measurementPort`: Classical setting/quantum system as input, classical outcome as output.
--   - `measurementAction`: Complex-linear extension of (G3) to EVERY joint input operator. The summand M[i,j] X[(x,j),(x,i)] is Tr(M X_xx), with no real-part operation inside the channel. On sigma tensor rho this is exactly the displayed (G3).
--   - `measurementChoi`: The actual measurement-channel Choi matrix, (G2)-(G3).
--   - `measurementValues`: Physical noise families in the original incompatibility optimization (G1). The minimized quantity is 1+r with r>=0, not the additive robustness r.
--   - `incompatibility`: Original generalized incompatibility robustness, (G1).
-- source:
--   One-Shot Manipulation of Dynamical Quantum Resources, arXiv:2012.02215v3, https://arxiv.org/abs/2012.02215v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

/-!
Regula and Takagi, One-Shot Manipulation of Dynamical Quantum Resources,
arXiv:2012.02215v3. All page numbers are PDF pages.

Only definition bodies from the pinned accepted Information100 modules are reused:
P06.Choi is the raw input-first matrix type (its normalized channel predicate is
not used); P07.support is the orthogonal range projector; P34.choi is the
unnormalized matrix-unit construction; P53.fidelity is squared state fidelity.
The remaining paper-specific resource interfaces have distinct descriptive names.

Channels are represented by their unnormalized input-first Choi matrices.
Dimensions are positive, including dimension one. Resource values belong to
ENNReal; an empty infimum is infinity, and its reciprocal is zero. Arbitrary
monotones use EReal and are smoothed by infima, without assuming attainment.
The full affine endpoint in Theorem 6 and the unrestricted Remark (D10) are
recorded in HARD.md, rather than supplied with invented endpoint conventions.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P32

open QAlgorithms.Papers.Independent.Information100.P07 (support)

/-- PDF p.2: positive finite input and output dimensions. -/
structure Port where
  din : ℕ+
  dout : ℕ+
  /-- Distinguishes fibres with equal dimensions but different physical structure. -/
  tag : ℕ := 0
  deriving DecidableEq

/-- PDF p.9 (A8): specialize the accepted raw input-first Choi carrier to
positive port dimensions. CPTP below imposes the unnormalized trace din. -/
abbrev ChannelChoi (p : Port) :=
  QAlgorithms.Papers.Independent.Information100.P06.Choi (Fin p.din) (Fin p.dout)

/-- CPTP Choi condition: positivity and output partial trace equal to identity. -/
def CPTP {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (J : Matrix (A × B) (A × B) ℂ) : Prop :=
  J.PosSemidef ∧ ∀ i j, (∑ b, J (i, b) (j, b)) = if i = j then 1 else 0

/-- The complex-linear matrix-unit reconstruction E(X), p.9 (A8).
No transpose is omitted: J[(i,b),(j,c)] = E(|i><j|)[b,c]. -/
def applyChoi {A B : Type*} [Fintype A]
    (J : Matrix (A × B) (A × B) ℂ) : Superop A B :=
  fun X b c => ∑ i, ∑ j, X i j * J (i, b) (j, c)

/-- Allowed channel fibres and their designated free subsets, PDF p.2.
Regular records the printed free-set assumptions; ClosedConvexAllowed separately
records the extra allowed-set hypothesis used by the corrected conversion results. -/
structure ResourceTheory where
  allowed : ∀ p : Port, Set (ChannelChoi p)
  free : ∀ p : Port, Set (ChannelChoi p)

/-- Printed standing assumptions, PDF p.2: nonempty closed convex free
fibres contained in physically allowed CPTP channels. No regularity of the
allowed subset is imposed here. -/
def Regular (O : ResourceTheory) : Prop :=
  ∀ p, (O.free p).Nonempty ∧ IsClosed (O.free p) ∧ Convex ℝ (O.free p) ∧
    O.free p ⊆ O.allowed p ∧ ∀ J ∈ O.allowed p, CPTP J

/-- Explicit correction to the unrestricted allowed-subset scope on PDF p.2.
Printed: only the free fibres are assumed closed and convex. Changed: the
conversion results additionally assume closed convex allowed fibres. Why:
(B3),(B8),(D7) mix allowed channels, and their minimizing robustness witnesses
can fail to exist on a nonclosed allowed set. The testing/support identities
use Regular alone and retain the printed allowed-subset generality. -/
def ClosedConvexAllowed (O : ResourceTheory) : Prop :=
  ∀ p, IsClosed (O.allowed p) ∧ Convex ℝ (O.allowed p)

/-- Physical deterministic superchannel: a CPTP pre/post-processing dilation
with finite positive memory, p.13 (D3). The equality holds on every input
operator and every channel argument, hence includes entangled inputs. -/
def Deterministic {p q : Port} (Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi q) : Prop :=
  ∃ m : ℕ+, ∃ pre : Matrix (Fin q.din × (Fin m × Fin p.din))
      (Fin q.din × (Fin m × Fin p.din)) ℂ,
    ∃ post : Matrix ((Fin m × Fin p.dout) × Fin q.dout)
      ((Fin m × Fin p.dout) × Fin q.dout) ℂ,
    CPTP pre ∧ CPTP post ∧ ∀ J X,
      applyChoi (Theta J) X =
        applyChoi post (idTensorSuperop (R := Fin m) (applyChoi J) (applyChoi pre X))

/-- The maximal allowed-structure and free-preserving deterministic set S, p.2. -/
def FreeSuperchannel (O : ResourceTheory) {p q : Port}
    (Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi q) : Prop :=
  Deterministic Theta ∧
    (∀ J ∈ O.allowed p, Theta J ∈ O.allowed q) ∧
    ∀ J ∈ O.free p, Theta J ∈ O.free q

/-- Normalized pure input and an input-sized reference, pp.2,8. -/
abbrev PureInput (p : Port) :=
  {v : EuclideanSpace ℂ (Fin p.din × Fin p.din) // ‖v‖ = 1}

/-- Reference-assisted channel output on a pure input. -/
def pureChannelOutput {p : Port} (E : ChannelChoi p) (v : PureInput p) :=
  idTensorSuperop (R := Fin p.din) (applyChoi E) (pureDensity v.1)

/-- Worst-case, reference-assisted squared channel fidelity, p.2.
The state domain is compact, nonempty and normalized for these positive dimensions. -/
def worstCaseFidelity {p : Port} (E N : ChannelChoi p) : ℝ :=
  sInf {f | ∃ rho : Matrix (Fin p.din × Fin p.din) (Fin p.din × Fin p.din) ℂ,
    IsDensityMatrix rho ∧ f = QAlgorithms.Papers.Independent.Information100.P53.fidelity
      (idTensorSuperop (R := Fin p.din) (applyChoi E) rho)
      (idTensorSuperop (R := Fin p.din) (applyChoi N) rho)}

/-- Purity after id tensor N on EVERY normalized pure reference-assisted input,
Theorems 3 and 6, pp.3,12. -/
def PureTarget {p : Port} (N : ChannelChoi p) : Prop :=
  ∀ v : PureInput p, ∃ w : EuclideanSpace ℂ (Fin p.din × Fin p.dout),
    ‖w‖ = 1 ∧ pureChannelOutput N v = pureDensity w

/-- Fidelity ball inside the physically allowed fibre. Tolerances >=1 mean
all allowed channels, as required by the oversmoothed bound in Theorem 1. -/
def ball (O : ResourceTheory) {p : Port} (e : ℝ) (E : ChannelChoi p) : Set (ChannelChoi p) :=
  {N | N ∈ O.allowed p ∧ (1 ≤ e ∨ 1 - e ≤ worstCaseFidelity N E)}

/-- Extended smoothing infimum, pp.2,10. No optimizer for arbitrary monotones
is assumed; quantitative optimizer statements are separate conclusions. -/
def smooth {V : Type*} [CompleteLattice V] (O : ResourceTheory) {p : Port}
    (R : ChannelChoi p → V) (e : ℝ) (E : ChannelChoi p) : V := sInf (R '' ball O e E)

/-- Eq.(1), p.2: multiplicative robustness with noise in the specified family.
The witness noise is physical and the free mixture is an actual free channel. -/
def robustness (O : ResourceTheory) {p : Port} (noise : Set (ChannelChoi p)) (E : ChannelChoi p) : ℝ≥0∞ :=
  sInf {z | ∃ r : ℝ, 0 ≤ r ∧ z = ENNReal.ofReal (1 + r) ∧
    ∃ M ∈ noise, ∃ F ∈ O.free p, E + (r : ℂ) • M = ((1 + r : ℝ) : ℂ) • F}

/-- Standard robustness: free noise, Eq.(1). -/
def standard (O : ResourceTheory) {p : Port} (E : ChannelChoi p) : ℝ≥0∞ :=
  robustness O (O.free p) E

/-- Generalized robustness: all physically allowed noise, Eq.(1). -/
def maximal (O : ResourceTheory) {p : Port} (E : ChannelChoi p) : ℝ≥0∞ :=
  robustness O (O.allowed p) E

/-- Feasible hypothesis test, with normalization built into PureInput, (A1). -/
def Test {p : Port} (E : ChannelChoi p) (e : ℝ) (v : PureInput p)
    (P : Matrix (Fin p.din × Fin p.dout) (Fin p.din × Fin p.dout) ℂ) : Prop :=
  IsEffect P ∧ 1 - e ≤ effectProb P (pureChannelOutput E v)

/-- The inverse ordinary testing resource, in the original max_M min_(psi,P)
order (A3). All probability reciprocals are extended, including at zero. -/
def inverseTestingValue (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ) : ℝ≥0∞ :=
  sSup {z | ∃ M ∈ O.free p, z = sInf {t | ∃ v : PureInput p, ∃ P,
    Test E e v P ∧ t = ENNReal.ofReal (effectProb P (pureChannelOutput M v))}}

/-- Ordinary hypothesis-testing resource, Eq.(2), pp.2,8. -/
def testing (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ) : ℝ≥0∞ :=
  (inverseTestingValue O E e)⁻¹

/-- Affine saddle extension (A6): the inner affine supremum is infinity for
nonconstant free overlaps. This avoids reciprocals of signed affine outputs.
Clipping individual real overlaps below zero does not change this supremum:
the affine hull contains nonempty free CPTP channels and so has nonnegative sup. -/
def betaAffine (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ) : ℝ≥0∞ :=
  sInf {z | ∃ v : PureInput p, ∃ P, Test E e v P ∧
    z = sSup {t | ∃ M ∈ affineSpan ℝ (O.free p),
      t = ENNReal.ofReal (effectProb P (pureChannelOutput M v))}}

/-- Affine hypothesis testing, pp.8-9 (A6)-(A7). -/
def testingAffine (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ) : ℝ≥0∞ :=
  (betaAffine O E e)⁻¹

/-- Ordinary min-resource is zero-error ordinary testing, pp.2,9. -/
def minimum (O : ResourceTheory) {p : Port} (E : ChannelChoi p) : ℝ≥0∞ := testing O E 0

/-- The extended equal-overlap support domain, (A15) and the Remark, pp.10-11.
An empty set gives infinity BEFORE inversion, hence affine min-resource zero. -/
def affineSupportValues (O : ResourceTheory) {p : Port} (E : ChannelChoi p) : Set ℝ≥0∞ :=
  {z | ∃ v : PureInput p, ∃ t : ℝ, 0 ≤ t ∧ z = ENNReal.ofReal t ∧
    ∀ M ∈ O.free p, effectProb (support (pureChannelOutput E v)) (pureChannelOutput M v) = t}

/-- Affine min-resource, distinct from zero-error affine testing. -/
def minimumAffine (O : ResourceTheory) {p : Port} (E : ChannelChoi p) : ℝ≥0∞ :=
  (sInf (affineSupportValues O E))⁻¹

/-- Reciprocal-threshold gauge (A9). The threshold formulation includes
m=infinity as threshold zero, but never assigns G(E;0) a value. -/
def gauge (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (t : ℝ≥0∞) : ℝ≥0∞ :=
  sSup {z | ∃ v : PureInput p, ∃ W, IsEffect W ∧
    (∀ M ∈ O.free p, ENNReal.ofReal (effectProb W (pureChannelOutput M v)) ≤ t) ∧
    z = ENNReal.ofReal (effectProb W (pureChannelOutput E v))}

/-- Equal-overlap affine gauge, with the printed supremum convention (A10). -/
def gaugeAffine (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (t : ℝ≥0∞) : ℝ≥0∞ :=
  sSup {z | ∃ v : PureInput p, ∃ W, IsEffect W ∧
    (∀ M ∈ O.free p, ENNReal.ofReal (effectProb W (pureChannelOutput M v)) = t) ∧
    z = ENNReal.ofReal (effectProb W (pureChannelOutput E v))}

/-- The inverse testing program in Lemma 5; lambda is minimized jointly with
psi and P, rather than postulated as an unrelated optimum. -/
def pureTestValues (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ)
    (aff : Bool) : Set ℝ≥0∞ :=
  {z | ∃ v : PureInput p, ∃ P, ∃ t : ℝ, 0 ≤ t ∧ Test E e v P ∧
    (∀ M ∈ O.free p, if aff then effectProb P (pureChannelOutput M v) = t
      else effectProb P (pureChannelOutput M v) ≤ t) ∧ z = ENNReal.ofReal t}

/-- Choi tester bounds 0<=Q<=rho tensor I, (A8). -/
def ChoiTester {p : Port} (rho : Matrix (Fin p.din) (Fin p.din) ℂ) (Q : ChannelChoi p) : Prop :=
  IsDensityMatrix rho ∧ Q.PosSemidef ∧ (Matrix.kronecker rho 1 - Q).PosSemidef

/-- (A8), with normalized rho, physical operator order, and actual lambda domain. -/
def choiTestValues (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ)
    (aff : Bool) : Set ℝ≥0∞ :=
  {z | ∃ rho, ∃ Q : ChannelChoi p, ∃ t : ℝ, 0 ≤ t ∧ ChoiTester rho Q ∧
    1 - e ≤ effectProb Q E ∧
    (∀ M ∈ O.free p, if aff then effectProb Q M = t else effectProb Q M ≤ t) ∧
    z = ENNReal.ofReal t}

/-- Choi gauge objective values (A10), jointly optimized over rho,W. -/
def choiGaugeValues (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (t : ℝ≥0∞)
    (aff : Bool) : Set ℝ≥0∞ :=
  {z | ∃ rho, ∃ W : ChannelChoi p, ChoiTester rho W ∧
    (∀ M ∈ O.free p, if aff then ENNReal.ofReal (effectProb W M) = t
      else ENNReal.ofReal (effectProb W M) ≤ t) ∧ z = ENNReal.ofReal (effectProb W E)}

/-- Positive dual and affine annihilator (A11); all variables are Hermitian.
The affine object is an annihilator, NOT the nonnegative dual of an affine hull. -/
def Dual (O : ResourceTheory) {p : Port} (aff : Bool) : Set (ChannelChoi p) :=
  {X | X.IsHermitian ∧ ∀ M ∈ O.free p,
    if aff then effectProb X M = 0 else 0 ≤ effectProb X M}

/-- Joint identity divided by INPUT dimension; its pairing with a CPTP Choi
matrix is one, (A12), p.9. -/
def choiTraceUnit (p : Port) : ChannelChoi p := ((p.din : ℂ)⁻¹) • 1

/-- Concrete dual-cone test program (A12). -/
def coneTestValues (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ)
    (aff : Bool) : Set ℝ≥0∞ :=
  {z | ∃ rho, ∃ Q : ChannelChoi p, ∃ t : ℝ, 0 ≤ t ∧ ChoiTester rho Q ∧
    1 - e ≤ effectProb Q E ∧ (t : ℂ) • choiTraceUnit p - Q ∈ Dual O aff ∧
    z = ENNReal.ofReal t}

/-- Concrete dual-cone gauge program (A12), for strictly positive finite m. -/
def coneGaugeValues (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (m : ℝ)
    (aff : Bool) : Set ℝ≥0∞ :=
  {z | ∃ rho, ∃ W : ChannelChoi p, ChoiTester rho W ∧
    choiTraceUnit p - (m : ℂ) • W ∈ Dual O aff ∧
    z = ENNReal.ofReal (effectProb W E)}

/-- Finite semidefinite representability: projection of one affine Hermitian
positive-semidefinite pencil, with finitely many real auxiliary variables.
Block diagonalization includes finite intersections and real linear equalities.
No runtime or bit-complexity assertion is implicit in this predicate. -/
def SDPRepresentable {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V) : Prop :=
  ∃ n r : ℕ, ∃ B : Matrix (Fin n) (Fin n) ℂ,
    ∃ L : (V × (Fin r → ℝ)) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ,
    B.IsHermitian ∧ (∀ z, (L z).IsHermitian) ∧
      ∀ x, x ∈ S ↔ ∃ y, (B + L (x, y)).PosSemidef

/-- Unprojected test feasible set. Its objective is the last, real coordinate. -/
def testFeasible (O : ResourceTheory) (p : Port) (E : ChannelChoi p) (e : ℝ) (aff : Bool) :
    Set ((Matrix (Fin p.din) (Fin p.din) ℂ × ChannelChoi p) × ℝ) :=
  {z | 0 ≤ z.2 ∧ ChoiTester z.1.1 z.1.2 ∧ 1 - e ≤ effectProb z.1.2 E ∧
    (z.2 : ℂ) • choiTraceUnit p - z.1.2 ∈ Dual O aff}

/-- Unprojected gauge feasible set; objective is the real linear Choi pairing. -/
def gaugeFeasible (O : ResourceTheory) (p : Port) (m : ℝ) (aff : Bool) :
    Set (Matrix (Fin p.din) (Fin p.din) ℂ × ChannelChoi p) :=
  {z | ChoiTester z.1 z.2 ∧ choiTraceUnit p - (m : ℂ) • z.2 ∈ Dual O aff}

/-- Supremum channel fidelity; theorems explicitly supply a maximizing Theta. -/
def bestFidelity (O : ResourceTheory) {p q : Port} (E : ChannelChoi p) (N : ChannelChoi q) : ℝ≥0∞ :=
  sSup {z | ∃ Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi q, FreeSuperchannel O Theta ∧
    z = ENNReal.ofReal (worstCaseFidelity (Theta E) N)}

/-- A conversion witness in the maximal physical free set. -/
def Converts (O : ResourceTheory) {p q : Port} (E : ChannelChoi p) (N : ChannelChoi q) (e : ℝ) : Prop :=
  ∃ Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi q,
    FreeSuperchannel O Theta ∧ 1 - e ≤ worstCaseFidelity (Theta E) N

/-- A reference family may contain channels of different finite dimensions. -/
abbrev References := ∀ p : Port, Set (ChannelChoi p)

/-- Physically admissible references; neither nonemptiness nor compactness of
an arbitrary reference family is assumed, (3),(C1)-(C3). -/
def ValidReferences (O : ResourceTheory) (T : References) : Prop :=
  ∀ p, T p ⊆ O.allowed p

/-- Reference scale fixed to ordinary min-resource in Eq.(3). -/
def referenceValues (O : ResourceTheory) (T : References) : Set ℝ≥0∞ :=
  {z | ∃ p, ∃ N ∈ T p, z = minimum O N}

/-- Supremum over attainable reference VALUES below x, (C3), not Nat.floor. -/
def referenceFloor (O : ResourceTheory) (T : References) (x : ℝ≥0∞) : ℝ≥0∞ :=
  sSup {z | z ∈ referenceValues O T ∧ z ≤ x}

/-- Infimum over attainable reference VALUES above x, (C3), not Nat.ceil. -/
def referenceCeiling (O : ResourceTheory) (T : References) (x : ℝ≥0∞) : ℝ≥0∞ :=
  sInf {z | z ∈ referenceValues O T ∧ x ≤ z}

/-- Operational distillation, with the supremum convention of Eq.(3). -/
def oneShotDistillable (O : ResourceTheory) (T : References) {p : Port} (E : ChannelChoi p) (e : ℝ) : ℝ≥0∞ :=
  sSup {z | ∃ q, ∃ N ∈ T q, Converts O E N e ∧ z = minimum O N}

/-- Operational dilution; conversion direction is reversed, Eq.(3). -/
def oneShotCost (O : ResourceTheory) (T : References) {p : Port} (E : ChannelChoi p) (e : ℝ) : ℝ≥0∞ :=
  sInf {z | ∃ q, ∃ N ∈ T q, Converts O N E e ∧ z = minimum O N}

/-- Meaningful empty-reference boundary: no targets has infinite cost. -/
example (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ) :
    oneShotCost O (fun _ => ∅) E e = ⊤ := by
  simp [oneShotCost]

/-- Oversmoothing really means the complete allowed fibre. -/
example (O : ResourceTheory) {p : Port} (E : ChannelChoi p) : ball O 1 E = O.allowed p := by
  ext N
  simp [ball]

/-- The absent equal-support domain has zero affine min-resource. -/
example (O : ResourceTheory) {p : Port} (E : ChannelChoi p)
    (h : affineSupportValues O E = ∅) : minimumAffine O E = 0 := by
  simp [minimumAffine, h]

/-- Quantitative smoothing optimizers used in (B3),(B8),(B13), pp.10-12.
They are conclusions for robustness, not assumptions about arbitrary monotones. -/
def QuantitativeAttainment (O : ResourceTheory) {p : Port} (N : ChannelChoi p) (e : ℝ) : Prop :=
  (∃ N' ∈ ball O e N, standard O N' = smooth O (standard O) e N) ∧
  (∃ N' ∈ ball O e N, maximal O N' = smooth O (maximal O) e N)

/-- Support-overlap maximum for one normalized pure input, (A13). -/
def supportMaximum (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (v : PureInput p) : ℝ≥0∞ :=
  sSup {z | ∃ M ∈ O.free p,
    z = ENNReal.ofReal (effectProb (support (pureChannelOutput E v)) (pureChannelOutput M v))}

/-- Positive-dimensional identity target for Eq.(4), p.4. -/
def transmissionPort (d : ℕ+) : Port := ⟨d, d, 0⟩

/-- Unnormalized Choi operator of id_d. -/
def identityChoi (d : ℕ+) : ChannelChoi (transmissionPort d) := by
  classical
  exact fun i j => if i.1 = i.2 ∧ j.1 = j.2 then 1 else 0

/-- Separable density operators: convex hull of product density operators. -/
def Separable {A B : Type*} [Fintype A] [Fintype B]
    (X : Matrix (A × B) (A × B) ℂ) : Prop :=
  X ∈ convexHull ℝ {Y | ∃ rho : Matrix A A ℂ, ∃ sigma : Matrix B B ℂ,
    IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧ Y = Matrix.kronecker rho sigma}

/-- Partial transpose on the second tensor factor. -/
def partialTranspose {A B : Type*} (X : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  fun i j => X (i.1, j.2) (j.1, i.2)

/-- Replacement-channel Choi matrix R_sigma(X)=Tr(X)sigma, p.4. -/
def replacement {p : Port} (rho : Matrix (Fin p.dout) (Fin p.dout) ℂ) : ChannelChoi p :=
  fun i j => if i.1 = j.1 then rho i.2 j.2 else 0

/-- The three communication resource theories on p.4. -/
inductive CommunicationKind where
  | sep
  | ppt
  | ns
  deriving DecidableEq

/-- Free TRANSMISSION channels. SEP uses the input/output Choi partition;
PPT means CPTP with positive partial transpose, never trace-decreasing maps;
NS assistance is the maximal replacement-preserving superchannel theory. -/
def communicationTheory (k : CommunicationKind) : ResourceTheory where
  allowed p := {J | CPTP J}
  free p := {J | CPTP J ∧ match k with
    | .sep => Separable (((p.din : ℂ)⁻¹) • J)
    | .ppt => (partialTranspose J).PosSemidef
    | .ns => ∃ rho, IsDensityMatrix rho ∧ J = replacement rho}

/-- Extended nonnegative base-two rate. Infinity is handled before toReal.
Only resource values >=1 (or their integer reference rounding) occur below. -/
def log2Resource (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then ⊤ else ENNReal.ofReal (Real.logb 2 x.toReal)

/-- Attainable reference values d^k, for positive integer d. -/
def integerReferenceValues (k : ℕ) : Set ℝ≥0∞ :=
  {z | ∃ d : ℕ+, z = (d : ℝ≥0∞) ^ k}

/-- Reference floor for integer dimensions (k=1) or squares (k=2). -/
def integerFloor (k : ℕ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  sSup {z | z ∈ integerReferenceValues k ∧ z ≤ x}

/-- Reference ceiling for integer dimensions (k=1) or squares (k=2). -/
def integerCeiling (k : ℕ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  sInf {z | z ∈ integerReferenceValues k ∧ x ≤ z}

/-- Operational quantum capacity, Eq.(4). Attainment is stated below. -/
def assistedOneShotCapacity (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ) : ℝ≥0∞ :=
  sSup {z | ∃ d : ℕ+, Converts O E (identityChoi d) e ∧
    z = ENNReal.ofReal (Real.logb 2 (d : ℝ))}

/-- Operational quantum simulation cost, Eq.(4), with reversed conversion. -/
def simulationCost (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ) : ℝ≥0∞ :=
  sInf {z | ∃ d : ℕ+, Converts O (identityChoi d) E e ∧
    z = ENNReal.ofReal (Real.logb 2 (d : ℝ))}

/-- Printed max/min in Eq.(4), supplying actual dimensions AND codes. -/
def RateAttainment (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ) : Prop :=
  (∃ d : ℕ+, Converts O E (identityChoi d) e ∧
    assistedOneShotCapacity O E e = ENNReal.ofReal (Real.logb 2 (d : ℝ))) ∧
  (∃ d : ℕ+, Converts O (identityChoi d) E e ∧
    simulationCost O E e = ENNReal.ofReal (Real.logb 2 (d : ℝ)))

/-- Fixed maximally entangled-input fidelity (D9): normalized Choi states. -/
def choiFidelity {p : Port} (E N : ChannelChoi p) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P53.fidelity (((p.din : ℂ)⁻¹) • E) (((p.din : ℂ)⁻¹) • N)

/-- Optimal fixed-input fidelity, with the same deterministic free set. -/
def bestChoiFidelity (O : ResourceTheory) {p q : Port} (E : ChannelChoi p) (N : ChannelChoi q) : ℝ≥0∞ :=
  sSup {z | ∃ Theta : ChannelChoi p →ₗ[ℂ] ChannelChoi q, FreeSuperchannel O Theta ∧
    z = ENNReal.ofReal (choiFidelity (Theta E) N)}

/-- Trivial-input preparation port, pp.13-14. -/
def preparationPort (d : ℕ+) : Port := ⟨1, d, 0⟩

/-- Choi operator of the preparation P_rho; the input register has dimension one. -/
def preparationChoi {d : ℕ+} (rho : Matrix (Fin d) (Fin d) ℂ) : ChannelChoi (preparationPort d) :=
  fun i j => rho i.2 j.2

/-- State-level multiplicative robustness, with physical noise specified. -/
def stateRobustness {d : ℕ+} (F noise : Set (Matrix (Fin d) (Fin d) ℂ))
    (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ≥0∞ :=
  sInf {z | ∃ r : ℝ, 0 ≤ r ∧ z = ENNReal.ofReal (1 + r) ∧
    ∃ sigma ∈ noise, ∃ tau ∈ F, rho + (r : ℂ) • sigma = ((1 + r : ℝ) : ℂ) • tau}

/-- State standard robustness. -/
def stateStandard {d : ℕ+} (F : Set (Matrix (Fin d) (Fin d) ℂ))
    (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ≥0∞ := stateRobustness F F rho

/-- State generalized robustness, with all density operators as noise. -/
def stateMaximal {d : ℕ+} (F : Set (Matrix (Fin d) (Fin d) ℂ))
    (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ≥0∞ :=
  stateRobustness F {sigma | IsDensityMatrix sigma} rho

/-- State min-resource; the support overlap is maximized over free states. -/
def stateMinimum {d : ℕ+} (F : Set (Matrix (Fin d) (Fin d) ℂ))
    (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ≥0∞ :=
  (sSup {z | ∃ sigma ∈ F, z = ENNReal.ofReal (effectProb (support rho) sigma)})⁻¹

/-- Affine state min-resource: constant support overlap over all free states,
with empty inverse domain interpreted exactly as in (A15). -/
def stateMinimumAffine {d : ℕ+} (F : Set (Matrix (Fin d) (Fin d) ℂ))
    (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ≥0∞ :=
  (sInf {z | ∃ t : ℝ, 0 ≤ t ∧ z = ENNReal.ofReal t ∧
    ∀ sigma ∈ F, effectProb (support rho) sigma = t})⁻¹

/-- Underlying state free-operation convention, pp.13-14: all preparations
are physically allowed, and free preparations produce exactly the free states.
The iff exposes both the printed inclusion and the proof-used preservation of
free states from the trivial free input; it is not an assumed resource equality. -/
def PreparationTheory (O : ResourceTheory)
    (F : ∀ d : ℕ+, Set (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  ∀ d, (F d).Nonempty ∧ IsClosed (F d) ∧ Convex ℝ (F d) ∧
    (∀ rho ∈ F d, IsDensityMatrix rho) ∧
    (∀ J : ChannelChoi (preparationPort d), J ∈ O.allowed (preparationPort d) ↔ CPTP J) ∧
    ∀ rho, IsDensityMatrix rho →
      (preparationChoi rho ∈ O.free (preparationPort d) ↔ rho ∈ F d)

/-- Reference preparations of a family of normalized pure state vectors. -/
def stateReferences (T : ∀ d : ℕ+, Set (EuclideanSpace ℂ (Fin d))) : References :=
  fun p => {J | ∃ d, ∃ v ∈ T d, ∃ h : p = preparationPort d,
    h ▸ J = preparationChoi (pureDensity v)}

/-- The zero-noise-free mixture convention really uses multiplicative 1+r. -/
example {d : ℕ+} (F : Set (Matrix (Fin d) (Fin d) ℂ))
    (rho sigma : Matrix (Fin d) (Fin d) ℂ) (hrho : rho ∈ F) (hsigma : sigma ∈ F) :
    (1 : ℝ≥0∞) ∈ {z | ∃ r : ℝ, 0 ≤ r ∧ z = ENNReal.ofReal (1 + r) ∧
      ∃ tau ∈ F, ∃ omega ∈ F, rho + (r : ℂ) • tau = ((1 + r : ℝ) : ℂ) • omega} := by
  exact ⟨0, le_rfl, by simp, sigma, hsigma, rho, hrho, by simp⟩

/-- Alice and Bob input/output dimensions for bipartite channels and boxes. -/
structure Split where
  ai : ℕ+
  bi : ℕ+
  ao : ℕ+
  bo : ℕ+
  deriving DecidableEq

/-- A tag preserves physical wire structure even when total dimensions agree. -/
def splitCode (s : Split) : ℕ :=
  Nat.pair (Nat.pair s.ai s.bi) (Nat.pair s.ao s.bo)

/-- Bipartite-channel port, with Alice/Bob partition included in the tag. -/
def bipartitePort (s : Split) : Port := ⟨s.ai * s.bi, s.ao * s.bo, 2 * splitCode s + 1⟩

/-- Re-express the same matrix in an equal port type. -/
def castChoi {p q : Port} (h : p = q) (J : ChannelChoi p) : ChannelChoi q := h ▸ J

/-- Regroup input-first Choi wires as (Alice input,output):(Bob input,output).
This differs from the transmission-channel input:output partition on p.4. -/
def groupedChoi (s : Split) (J : ChannelChoi (bipartitePort s)) :
    Matrix ((Fin s.ai × Fin s.ao) × (Fin s.bi × Fin s.bo))
      ((Fin s.ai × Fin s.ao) × (Fin s.bi × Fin s.bo)) ℂ :=
  fun i j => J (finProdFinEquiv (i.1.1, i.2.1), finProdFinEquiv (i.1.2, i.2.2))
    (finProdFinEquiv (j.1.1, j.2.1), finProdFinEquiv (j.1.2, j.2.2))

/-- Bipartite SEP/PPT CHANNEL theories, Appendix E, p.14. At encoded ports
all CPTP maps are allowed; the free condition uses the party grouping. -/
def bipartiteTheory (ppt : Bool) : ResourceTheory where
  allowed p := {J | CPTP J}
  free p := {J | CPTP J ∧ ∃ s : Split, ∃ h : p = bipartitePort s,
    if ppt then (partialTranspose (groupedChoi s (castChoi h J))).PosSemidef
    else Separable (((p.din : ℂ)⁻¹) • groupedChoi s (castChoi h J))}

/-- Preparation of the d-dimensional maximally entangled state, Eq.(E2). -/
def entangledTargetPort (d : ℕ+) : Port := bipartitePort ⟨1, 1, d, d⟩

/-- Density matrix of the maximally entangled target, represented as a
trivial-input preparation Choi matrix; its nonzero entries are 1/d. -/
def entangledTarget (d : ℕ+) : ChannelChoi (entangledTargetPort d) :=
  fun i j =>
    let a : Fin d × Fin d := finProdFinEquiv.symm i.2
    let b : Fin d × Fin d := finProdFinEquiv.symm j.2
    if a.1 = a.2 ∧ b.1 = b.2 then (d : ℂ)⁻¹ else 0

/-- One-shot distillable CHANNEL entanglement, Eq.(E2), log base two. -/
def entanglementDistillation (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ) : ℝ≥0∞ :=
  sSup {z | ∃ d : ℕ+, Converts O E (entangledTarget d) e ∧
    z = ENNReal.ofReal (Real.logb 2 (d : ℝ))}

/-- One-shot channel entanglement cost, Eq.(E2). -/
def entanglementCost (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ) : ℝ≥0∞ :=
  sInf {z | ∃ d : ℕ+, Converts O (entangledTarget d) E e ∧
    z = ENNReal.ofReal (Real.logb 2 (d : ℝ))}

/-- Actual optimal entangled dimensions and physical codes in Eq.(E2). -/
def EntanglementAttainment (O : ResourceTheory) {p : Port} (E : ChannelChoi p) (e : ℝ) : Prop :=
  (∃ d : ℕ+, Converts O E (entangledTarget d) e ∧
    entanglementDistillation O E e = ENNReal.ofReal (Real.logb 2 (d : ℝ))) ∧
  (∃ d : ℕ+, Converts O (entangledTarget d) E e ∧
    entanglementCost O E e = ENNReal.ofReal (Real.logb 2 (d : ℝ)))

/-- Classical-classical box port; parties' classical wires remain tagged. -/
def boxPort (s : Split) : Port := ⟨s.ai * s.bi, s.ao * s.bo, 2 * splitCode s + 2⟩

/-- Conditional probabilities P(a,b|x,y) of a finite bipartite box. -/
abbrev Kernel (s : Split) := (Fin s.ai × Fin s.bi) → (Fin s.ao × Fin s.bo) → ℝ

/-- Normalized nonnegative no-signalling boxes, p.4: neither marginal
is allowed to depend on the other party's input. -/
def NoSignalling (s : Split) (P : Kernel s) : Prop :=
  (∀ x a, 0 ≤ P x a) ∧ (∀ x, ∑ a, P x a = 1) ∧
  (∀ x y y' a, (∑ b, P (x, y) (a, b)) = ∑ b, P (x, y') (a, b)) ∧
  (∀ x x' y b, (∑ a, P (x, y) (a, b)) = ∑ a, P (x', y) (a, b))

/-- Deterministic local response, with arbitrary local input dependence. -/
def deterministicKernel (s : Split) (f : Fin s.ai → Fin s.ao) (g : Fin s.bi → Fin s.bo) : Kernel s :=
  fun x a => if a.1 = f x.1 ∧ a.2 = g x.2 then 1 else 0

/-- Local boxes are mixtures of deterministic local responses (shared randomness). -/
def IsLocalBox (s : Split) (P : Kernel s) : Prop :=
  P ∈ convexHull ℝ {D | ∃ f g, D = deterministicKernel s f g}

/-- Complete dephasing on both input and output embeds a classical box as
an actual CPTP channel; off-diagonal joint input operators map to zero. -/
def boxChoi (s : Split) (P : Kernel s) : ChannelChoi (boxPort s) :=
  fun i j => if i.1 = j.1 ∧ i.2 = j.2 then
    (P (finProdFinEquiv.symm i.1) (finProdFinEquiv.symm i.2) : ℂ) else 0

/-- Nonlocality resource theory: all no-signalling classical channels are
allowed and all local shared-randomness boxes are free, p.4 and Appendix F. -/
def boxTheory : ResourceTheory where
  allowed p := {J | ∃ s, ∃ h : p = boxPort s, ∃ P : Kernel s,
    NoSignalling s P ∧ castChoi h J = boxChoi s P}
  free p := {J | ∃ s, ∃ h : p = boxPort s, ∃ P : Kernel s,
    NoSignalling s P ∧ IsLocalBox s P ∧ castChoi h J = boxChoi s P}

/-- The standard two-input, two-output binary Bell scenario. -/
def binarySplit : Split := ⟨2, 2, 2, 2⟩

/-- PR correlations P(a,b|x,y)=1/2 when a xor b=xy, and zero otherwise. -/
def prKernel : Kernel binarySplit :=
  fun x a => if (a.1.val + a.2.val) % 2 = x.1.val * x.2.val then 1 / 2 else 0

/-- White noise is the uniform box, Fig.1, p.15. -/
def randomKernel : Kernel binarySplit := fun _ _ => 1 / 4

/-- Convex mixing of binary boxes, with the NOISE weight equal to e. -/
def noisyKernel (P : Kernel binarySplit) (e : ℝ) : Kernel binarySplit :=
  fun x a => (1 - e) * prKernel x a + e * P x a

/-- Isotropic box B_p=(1-p)B_PR+p B_random, Fig.1. -/
def isotropicKernel (p : ℝ) : Kernel binarySplit := noisyKernel randomKernel p

/-- Finite-copy register equivalence; the same labels are used for all wires. -/
def bitLabels (n : ℕ) : (Fin n → Fin 2) ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (by simp)

/-- n copies, grouped with all Alice wires together and all Bob wires together. -/
def copySplit (n : ℕ) : Split := ⟨2 ^ n, 2 ^ n, 2 ^ n, 2 ^ n⟩

/-- Tensor-product box probabilities, with collective local n-bit input/output
registers. Local free boxes on these registers may correlate different copies. -/
def tensorKernel (n : ℕ) (P : Kernel binarySplit) : Kernel (copySplit n) :=
  fun x a => ∏ i : Fin n,
    P ((bitLabels n).symm x.1 i, (bitLabels n).symm x.2 i)
      ((bitLabels n).symm a.1 i, (bitLabels n).symm a.2 i)

/-- Hand normalization check: isotropic noise parameter one is white noise. -/
example : isotropicKernel 1 = randomKernel := by
  funext x a
  simp [isotropicKernel, noisyKernel]

/-- Zero noise is PR, so it is deliberately excluded from the no-distillation
hypotheses; at this endpoint the generalized resource is 4/3, not one. -/
example (P : Kernel binarySplit) : noisyKernel P 0 = prKernel := by
  funext x a
  simp [noisyKernel]

/-- A finite set of finite-outcome POVMs, Appendix G, pp.15-16. -/
abbrev MeasurementFamily (x a d : ℕ+) :=
  Fin x → Fin a → Matrix (Fin d) (Fin d) ℂ

/-- Every setting is a normalized positive operator-valued measurement. -/
def ValidMeasurements {x a d : ℕ+} (M : MeasurementFamily x a d) : Prop :=
  ∀ s, IsPOVM (M s)

/-- Compatibility: a finite normalized parent POVM and a genuine conditional
probability distribution q(a|x,i), reproducing every measurement effect, p.4. -/
def CompatiblePOVMs {x a d : ℕ+} (M : MeasurementFamily x a d) : Prop :=
  ValidMeasurements M ∧ ∃ k : ℕ+, ∃ P : Fin k → Matrix (Fin d) (Fin d) ℂ,
    ∃ q : Fin a → Fin x → Fin k → ℝ, IsPOVM P ∧
    (∀ o s i, 0 ≤ q o s i) ∧ (∀ s i, ∑ o, q o s i = 1) ∧
    ∀ s o, M s o = ∑ i, (q o s i : ℂ) • P i

/-- Classical setting/quantum system as input, classical outcome as output. -/
def measurementPort (x a d : ℕ+) : Port :=
  ⟨x * d, a, 3 * Nat.pair (Nat.pair x a) d + 3⟩

/-- Complex-linear extension of (G3) to EVERY joint input operator. The
summand M[i,j] X[(x,j),(x,i)] is Tr(M X_xx), with no real-part operation
inside the channel. On sigma tensor rho this is exactly the displayed (G3). -/
def measurementAction {x a d : ℕ+} (M : MeasurementFamily x a d) :
    Superop (Fin ((x * d : ℕ+) : ℕ)) (Fin a) :=
  fun X o o' => if o = o' then
    ∑ s : Fin x, ∑ i : Fin d, ∑ j : Fin d,
      M s o i j * X (finProdFinEquiv (s, j)) (finProdFinEquiv (s, i))
    else 0

/-- The actual measurement-channel Choi matrix, (G2)-(G3). -/
def measurementChoi {x a d : ℕ+} (M : MeasurementFamily x a d) :
    ChannelChoi (measurementPort x a d) := QAlgorithms.Papers.Independent.Information100.P34.choi (measurementAction M)

/-- Physical noise families in the original incompatibility optimization (G1).
The minimized quantity is 1+r with r>=0, not the additive robustness r. -/
def measurementValues {x a d : ℕ+} (M : MeasurementFamily x a d) : Set ℝ≥0∞ :=
  {z | ∃ r : ℝ, 0 ≤ r ∧ z = ENNReal.ofReal (1 + r) ∧
    ∃ N F : MeasurementFamily x a d, ValidMeasurements N ∧ CompatiblePOVMs F ∧
      ∀ s o, M s o + (r : ℂ) • N s o = ((1 + r : ℝ) : ℂ) • F s o}

/-- Original generalized incompatibility robustness, (G1). -/
def incompatibility {x a d : ℕ+} (M : MeasurementFamily x a d) : ℝ≥0∞ :=
  sInf (measurementValues M)

/-- The matrix-unit extension is complex-linear at zero, unlike a formula
with real-valued expectation on arbitrary input operators. -/
example {x a d : ℕ+} (M : MeasurementFamily x a d) : measurementAction M 0 = 0 := by
  ext o o'
  change (if o = o' then
    ∑ s : Fin x, ∑ i : Fin d, ∑ j : Fin d, M s o i j * (0 : ℂ)
    else 0) = 0
  simp

/-- Choi reconstruction pins the reference/input wire convention exactly. -/
example {A B : Type*} [Fintype A] [DecidableEq A]
    (J : Matrix (A × B) (A × B) ℂ) (i j : A) (b c : B) :
    applyChoi J (Matrix.single i j 1) b c = J (i, b) (j, c) := by
  simp [applyChoi, Matrix.single_apply, ite_mul, ite_and]

end QAlgorithms.Papers.Independent.Dependency50.P32


