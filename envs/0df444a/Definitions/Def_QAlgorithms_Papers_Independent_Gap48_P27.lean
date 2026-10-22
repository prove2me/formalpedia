-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P27
-- name    : QAlgorithms_Papers_Independent_Gap48_P27
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T23:14:35.495809+00:00
-- url     : https://prove2.me/theorems/0abcb227-d36a-4697-8d63-c00b76340261
-- title:
--   Definitions for A solution of the Gaussian optimizer conjecture
-- statement:
--   The objects the formalized statements of *A solution of the Gaussian optimizer conjecture* (arXiv:1312.2251) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `complexDisplacement`: PDF pp.4-5, (4)-(5): exact tensor product of accepted one-mode Weyl entries. The bra is the row index; in particular D(z)_{0,1} has the minus-conjugate sign.
--   - `complexWeylCharacteristic`: PDF p.5: Tr(X D(z)), multiplying bounded Weyl rows before the trace. On trace class each row pairing and the diagonal trace converge.
--   - `finiteSecondMoments`: PDF pp.9-10: finite mean occupation in each mode; no common energy cap.
--   - `complexQuadratic`: PDF p.5: z* mu z, with the source's complex column-vector convention.
--   - `GaugeChannel`: PDF pp.5-7, (7),(12): full Gaussian gauge channel, including both CP inequalities in the covariant case. `contravariant=true` applies Lambda AFTER K*, exactly as in (12). No entropy or optimizer property is a field.
--   - `quantumLimitedAttenuator`: PDF p.6, (9): quantum-limited attenuator, including zero coupling.
--   - `quantumLimitedAmplifier`: PDF p.6, (10): quantum-limited amplifier; gain is amplitude, not intensity.
--   - `quantumLimitedContravariant`: PDF p.7, (14): minimal contravariant noise, allowing gain zero.
--   - `modeUnitary`: PDF p.6: both-sided finite-dimensional unitary identity.
--   - `passiveImplementation`: PDF p.6, (11): passive Fock implementation through Weyl intertwining. This orientation is U* D(z) U = D(V z); it also fixes the vacuum vector's phase.
--   - `nonnegativeDiagonal`: PDF pp.6-7: rectangular diagonal with nonnegative singular values.
--   - `diagonalizableGaugeChannel`: PDF pp.6-7: passive diagonalization. The antilinear case conjugates the input unitary in K's factorization. Weyl laws of C express the independent one-mode normal form, including discarded inputs and extra output modes.
--   - `domainMinimumEntropy`: PDF pp.9-11: infimal output entropy on a specified full-density domain.
--   - `minimizesOn`: PDF pp.1,11: actual attaining input, separately from the infimum.
--   - `blockFiniteMoments`: PDF p.11: arbitrary correlated blocks have a finite occupation in each copy and mode. This is the S2 domain, without product-input restrictions.
--   - `blockVacuum`: PDF p.11: tensor product vacuum in the same block coordinates as the power.
--   - `GaugeFamily`: PDF pp.11-12: finite heterogeneous collections, with each channel's own input/output mode counts. Product coordinates are completed Hilbert coordinates.
--   - `GaugeFamily.input`: PDF p.11: input basis for a heterogeneous collection.
--   - `GaugeFamily.output`: PDF p.11: output basis for a heterogeneous collection.
--   - `GaugeFamily.operation`: PDF p.11: heterogeneous tensor product retaining all off-diagonal blocks.
--   - `GaugeFamily.vacuum`: PDF p.11: the product of the actual input vacua.
--   - `GaugeFamily.finiteMoments`: PDF p.11: all single-mode occupations of a heterogeneous joint state are finite, equivalently the S2 condition on its marginals.
--   - `GaugeFamily.vacuumEntropySum`: PDF p.11: sum of individually attained vacuum output entropies.
--   - `GaugeFamily.minimumSum`: PDF p.11: sum of the individual infimal entropies, distinct from vacuum values.
--   - `vacuumOptimizerAndAdditivity`: PDF p.11, (26)-(27): the full optimizer and both additivity conclusions. A proposition collecting conclusions; it is not assumed by any unconditional result.
--   - `singleModeAmplifierHypothesis`: PDF p.11, hypothesis (A): vacuum minimizes every one-mode limited amplifier. There is no arbitrary uniform energy cap on its competitors.
--   - `coherentMeasurePrepare`: PDF p.14, (31)-(33): exact heterodyne integral for an explicit preparation. Husimi already includes pi^{-a}; the measure here is ordinary complex volume.
--   - `skewPlus`: PDF p.14, (32): positive skew counterpart, constructed from its integral.
--   - `skewMinus`: PDF p.14, (33): negative skew counterpart.
--   - `connectingPartialIsometry`: PDF p.16: support-connecting partial isometry, with both intertwining identities. The support projections are characterized by their action on X,Y; no arbitrary projection or inverse of a noninvertible state is introduced.
--   - `CountablePureEnsemble`: PDF pp.17-18: finite/countable pure-state ensembles, padded by zero weights. Each positive component has finite moments; this follows from the source's finite-energy barycenter and is not a uniform bound on components.
--   - `traceSeries`: PDF p.17: actual trace-norm sum of a countable ensemble.
--   - `finiteMomentConvexClosure`: PDF pp.9-10: output-entropy convex closure, over all Borel probability laws supported on S2 with the given barycenter. Extended nonnegative integrals and infima retain infinity. Dirac ensembles make every S2 fiber nonempty.
--   - `bipartiteFiniteMoments`: PDF p.10: the two-channel S2 domain through the actual marginals.
--   - `outputEntropyAdditivity`: PDF pp.9-10, (20)-(21): convex-closure superadditivity and infimal minimum-output additivity. Auxiliary inputs may be entangled with the signal.
--   - `DisplacedFockGaussianLaw`: PDF pp.9-10: a general Gaussian channel, with arbitrary real-linear phase map, arbitrary displacement, and real symmetric Gaussian noise. CPTP is kept independently, so this includes squeezing and is not limited to gauge channels. The frozen Next46.P18.GaussianChannel instead specifies a CENTERED bounded-dual law for supplied real Weyl systems. This interface fixes complex Fock entries and also includes displacement; it does not redeclare that centered predicate.
--   - `vacuumOccupation`: PDF p.13, (30): noise occupation matrix of the vacuum output.
--   - `sourcePartialIsometry`: PDF p.16: a partial isometry that is isometric on the support of X. Its action off that support is irrelevant to the weighted decomposition.
--   - `SqueezedIdentification`: PDF p.21: a finite symplectic identification and its metaplectic implementation. The induced compatible complex structure is S^{-1} i S; this describes channels already covariant for that chosen structure.
--   - `squeezedComplexStructure`: PDF p.21: actual complex structure induced by a squeezed identification.
--   - `squeezedChannel`: PDF p.21: Gaussian channel expressed in the corresponding squeezed input/output structures, via the actual metaplectic conjugations.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, https://arxiv.org/abs/1312.2251v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

/-!
Giovannetti, Holevo and Garcia-Patron, arXiv:1312.2251v2.
Completed, untruncated finite-mode Fock spaces, normalized nuclear densities,
natural logarithms, and the source's S2 domain. Proofs are intentionally omitted.
All new interfaces are local. Compilation is pending the mechanical handoff.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P27

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass IsTraceClassChannel rankOne
   productCoeff tensorApply traceSize BreaksTraceClassEntanglement)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats GeneralizedEnsemble HasAverage
   finiteEnsembleCapacity ensembleHolevo)
open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff)
open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel vacuum productCoherentKernel modeEnergy husimi FockPOVM
   realFockTracePair)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Claimed50.P35
  (traceClassTensorMap traceClassChannelPower)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation partialRight partialLeft isometryCoeff conjugateKernel)

/-- PDF pp.4-5, (4)-(5): exact tensor product of accepted one-mode Weyl entries.
The bra is the row index; in particular D(z)_{0,1} has the minus-conjugate sign. -/
def complexDisplacement {s : ℕ} (z : Fin s → ℂ) : FockKernel s :=
  fun m n => ∏ j, QAlgorithms.Papers.Independent.Dependency50.P39.displacementMatrix
    (z j) (m j) (n j)

/-- PDF p.5: Tr(X D(z)), multiplying bounded Weyl rows before the trace.
On trace class each row pairing and the diagonal trace converge. -/
def complexWeylCharacteristic {s : ℕ} (X : FockKernel s) (z : Fin s → ℂ) : ℂ :=
  ∑' n, ∑' m, X n m * complexDisplacement z m n

/-- PDF pp.9-10: finite mean occupation in each mode; no common energy cap. -/
def finiteSecondMoments {s : ℕ} (X : FockKernel s) : Prop :=
  ∀ j, modeEnergy X j < ⊤

/-- PDF p.5: z* mu z, with the source's complex column-vector convention. -/
def complexQuadratic {s : ℕ} (mu : Matrix (Fin s) (Fin s) ℂ) (z : Fin s → ℂ) : ℂ :=
  ∑ i, ∑ j, star (z i) * mu i j * z j

/-- PDF pp.5-7, (7),(12): full Gaussian gauge channel, including both CP
inequalities in the covariant case. `contravariant=true` applies Lambda AFTER
K*, exactly as in (12). No entropy or optimizer property is a field. -/
structure GaugeChannel (a b : ℕ) where
  operation : Operation (NumberString a) (NumberString b)
  gain : Matrix (Fin b) (Fin a) ℂ
  noise : Matrix (Fin b) (Fin b) ℂ
  contravariant : Bool
  cptp : IsTraceClassChannel operation
  hermitian : noise.IsHermitian
  admissible : if contravariant then
      (noise - (1 / 2 : ℂ) • (1 + gain * gain.conjTranspose)).PosSemidef
    else
      (noise - (1 / 2 : ℂ) • (1 - gain * gain.conjTranspose)).PosSemidef ∧
      (noise + (1 / 2 : ℂ) • (1 - gain * gain.conjTranspose)).PosSemidef
  action : ∀ X, IsTraceClass X → ∀ z,
    complexWeylCharacteristic (operation X) z =
      complexWeylCharacteristic X
        (if contravariant then fun j => star (gain.conjTranspose.mulVec z j)
         else gain.conjTranspose.mulVec z) * Complex.exp (-complexQuadratic noise z)

/-- PDF p.6, (9): quantum-limited attenuator, including zero coupling. -/
def quantumLimitedAttenuator {a b : ℕ} (G : GaugeChannel a b) : Prop :=
  G.contravariant = false ∧ (1 - G.gain * G.gain.conjTranspose).PosSemidef ∧
    G.noise = (1 / 2 : ℂ) • (1 - G.gain * G.gain.conjTranspose)

/-- PDF p.6, (10): quantum-limited amplifier; gain is amplitude, not intensity. -/
def quantumLimitedAmplifier {a b : ℕ} (G : GaugeChannel a b) : Prop :=
  G.contravariant = false ∧ (G.gain * G.gain.conjTranspose - 1).PosSemidef ∧
    G.noise = (1 / 2 : ℂ) • (G.gain * G.gain.conjTranspose - 1)

/-- PDF p.7, (14): minimal contravariant noise, allowing gain zero. -/
def quantumLimitedContravariant {a b : ℕ} (G : GaugeChannel a b) : Prop :=
  G.contravariant = true ∧
    G.noise = (1 / 2 : ℂ) • (1 + G.gain * G.gain.conjTranspose)

/-- PDF p.6: both-sided finite-dimensional unitary identity. -/
def modeUnitary {s : ℕ} (V : Matrix (Fin s) (Fin s) ℂ) : Prop :=
  V.conjTranspose * V = 1 ∧ V * V.conjTranspose = 1

/-- PDF p.6, (11): passive Fock implementation through Weyl intertwining.
This orientation is U* D(z) U = D(V z); it also fixes the vacuum vector's phase. -/
def passiveImplementation {s : ℕ}
    (U : Hilbert (NumberString s) ≃ₗᵢ[ℂ] Hilbert (NumberString s))
    (V : Matrix (Fin s) (Fin s) ℂ) : Prop :=
  modeUnitary V ∧
  U (lp.single 2 (0 : NumberString s) 1) = lp.single 2 (0 : NumberString s) 1 ∧
  ∀ z, conjugateCoeff U.symm.toLinearIsometry.toContinuousLinearMap
    (complexDisplacement z) = complexDisplacement (V.mulVec z)

/-- PDF pp.6-7: rectangular diagonal with nonnegative singular values. -/
def nonnegativeDiagonal {a b : ℕ} (K : Matrix (Fin b) (Fin a) ℂ) : Prop :=
  (∀ i j, i.val ≠ j.val → K i j = 0) ∧
  (∀ i j, i.val = j.val → (K i j).im = 0 ∧ 0 ≤ (K i j).re)

/-- PDF pp.6-7: passive diagonalization. The antilinear case conjugates the
input unitary in K's factorization. Weyl laws of C express the independent
one-mode normal form, including discarded inputs and extra output modes. -/
def diagonalizableGaugeChannel {a b : ℕ} (G : GaugeChannel a b) : Prop :=
  ∃ (C : GaugeChannel a b) (VA : Matrix (Fin a) (Fin a) ℂ)
    (VB : Matrix (Fin b) (Fin b) ℂ)
    (UA : Hilbert (NumberString a) ≃ₗᵢ[ℂ] Hilbert (NumberString a))
    (UB : Hilbert (NumberString b) ≃ₗᵢ[ℂ] Hilbert (NumberString b)),
    C.contravariant = G.contravariant ∧ nonnegativeDiagonal C.gain ∧
    (∀ i j, i ≠ j → C.noise i j = 0) ∧
    passiveImplementation UA VA ∧ passiveImplementation UB VB.conjTranspose ∧
    G.gain = VB * C.gain * (if G.contravariant then VA.map star else VA) ∧
    G.noise = VB * C.noise * VB.conjTranspose ∧
    ∀ X, IsTraceClass X → G.operation X =
      conjugateCoeff UB.toLinearIsometry.toContinuousLinearMap
        (C.operation (conjugateCoeff UA.symm.toLinearIsometry.toContinuousLinearMap X))

/-- PDF pp.9-11: infimal output entropy on a specified full-density domain. -/
def domainMinimumEntropy {I J : Type} (T : Operation I J)
    (D : Matrix I I ℂ → Prop) : ℝ≥0∞ :=
  ⨅ rho : {rho : State I // D rho.coefficients}, extendedEntropyNats (T rho.val.coefficients)

/-- PDF pp.1,11: actual attaining input, separately from the infimum. -/
def minimizesOn {I J : Type} (T : Operation I J) (D : Matrix I I ℂ → Prop)
    (X : Matrix I I ℂ) : Prop :=
  IsDensity X ∧ D X ∧ ∀ rho : State I, D rho.coefficients →
    extendedEntropyNats (T X) ≤ extendedEntropyNats (T rho.coefficients)

/-- PDF p.11: arbitrary correlated blocks have a finite occupation in each
copy and mode. This is the S2 domain, without product-input restrictions. -/
def blockFiniteMoments {a n : ℕ}
    (X : Matrix (Fin n → NumberString a) (Fin n → NumberString a) ℂ) : Prop :=
  ∀ j k, (∑' u, ENNReal.ofReal ((u j k : ℝ) * (X u u).re)) < ⊤

/-- PDF p.11: tensor product vacuum in the same block coordinates as the power. -/
def blockVacuum (a n : ℕ) : Matrix (Fin n → NumberString a) (Fin n → NumberString a) ℂ :=
  fun u v => ∏ j, vacuum a (u j) (v j)

/-- PDF pp.11-12: finite heterogeneous collections, with each channel's own
input/output mode counts. Product coordinates are completed Hilbert coordinates. -/
inductive GaugeFamily where
  | nil
  | cons {a b : ℕ} (head : GaugeChannel a b) (tail : GaugeFamily)

/-- PDF p.11: input basis for a heterogeneous collection. -/
def GaugeFamily.input : GaugeFamily → Type
  | .nil => Unit
  | .cons (a := a) _ t => NumberString a × t.input

/-- PDF p.11: output basis for a heterogeneous collection. -/
def GaugeFamily.output : GaugeFamily → Type
  | .nil => Unit
  | .cons (b := b) _ t => NumberString b × t.output

/-- PDF p.11: heterogeneous tensor product retaining all off-diagonal blocks. -/
def GaugeFamily.operation : (F : GaugeFamily) → Operation F.input F.output
  | .nil => fun X => X
  | .cons G t => traceClassTensorMap G.operation t.operation

/-- PDF p.11: the product of the actual input vacua. -/
def GaugeFamily.vacuum : (F : GaugeFamily) → Matrix F.input F.input ℂ
  | .nil => fun _ _ => 1
  | .cons (a := a) _ t => productCoeff
      (QAlgorithms.Papers.Independent.Next46.P32.vacuum a) t.vacuum

/-- PDF p.11: all single-mode occupations of a heterogeneous joint state are
finite, equivalently the S2 condition on its marginals. -/
def GaugeFamily.finiteMoments : (F : GaugeFamily) → Matrix F.input F.input ℂ → Prop
  | .nil => fun _ => True
  | .cons _ t => fun X => finiteSecondMoments (partialRight X) ∧ t.finiteMoments (partialLeft X)

/-- PDF p.11: sum of individually attained vacuum output entropies. -/
def GaugeFamily.vacuumEntropySum : GaugeFamily → ℝ≥0∞
  | .nil => 0
  | .cons (a := a) G t => extendedEntropyNats
      (G.operation (QAlgorithms.Papers.Independent.Next46.P32.vacuum a)) + t.vacuumEntropySum

/-- PDF p.11: sum of the individual infimal entropies, distinct from vacuum values. -/
def GaugeFamily.minimumSum : GaugeFamily → ℝ≥0∞
  | .nil => 0
  | .cons G t => domainMinimumEntropy G.operation finiteSecondMoments + t.minimumSum

/-- PDF p.11, (26)-(27): the full optimizer and both additivity conclusions.
A proposition collecting conclusions; it is not assumed by any unconditional result. -/
def vacuumOptimizerAndAdditivity : Prop :=
  (∀ {a b : ℕ} (G : GaugeChannel a b),
    minimizesOn G.operation finiteSecondMoments (vacuum a) ∧
    domainMinimumEntropy G.operation finiteSecondMoments =
      extendedEntropyNats (G.operation (vacuum a)) ∧
    ∀ n : ℕ, 0 < n →
      minimizesOn (traceClassChannelPower G.operation n) blockFiniteMoments (blockVacuum a n) ∧
      extendedEntropyNats (traceClassChannelPower G.operation n (blockVacuum a n)) =
        (n : ℝ≥0∞) * extendedEntropyNats (G.operation (vacuum a)) ∧
      domainMinimumEntropy (traceClassChannelPower G.operation n) blockFiniteMoments =
        (n : ℝ≥0∞) * extendedEntropyNats (G.operation (vacuum a))) ∧
  ∀ F : GaugeFamily, F ≠ .nil →
    minimizesOn F.operation F.finiteMoments F.vacuum ∧
    domainMinimumEntropy F.operation F.finiteMoments = F.minimumSum ∧
    F.minimumSum = F.vacuumEntropySum

/-- PDF p.11, hypothesis (A): vacuum minimizes every one-mode limited amplifier.
There is no arbitrary uniform energy cap on its competitors. -/
def singleModeAmplifierHypothesis : Prop :=
  ∀ G : GaugeChannel 1 1, quantumLimitedAmplifier G →
    minimizesOn G.operation finiteSecondMoments (vacuum 1)

/-- PDF p.14, (31)-(33): exact heterodyne integral for an explicit preparation.
Husimi already includes pi^{-a}; the measure here is ordinary complex volume. -/
def coherentMeasurePrepare {a b : ℕ} (f : (Fin a → ℂ) → (Fin b → ℂ))
    (X : FockKernel a) : FockKernel b :=
  fun m n => ∫ z : Fin a → ℂ,
    (husimi X z : ℂ) * productCoherentKernel b (f z) m n

/-- PDF p.14, (32): positive skew counterpart, constructed from its integral. -/
def skewPlus {a b : ℕ} (K : Matrix (Fin b) (Fin a) ℂ) :
    Operation (NumberString a) (NumberString b) :=
  coherentMeasurePrepare (fun z => (K.map star).mulVec z)

/-- PDF p.14, (33): negative skew counterpart. -/
def skewMinus {a b : ℕ} (K : Matrix (Fin b) (Fin a) ℂ) :
    Operation (NumberString a) (NumberString b) :=
  coherentMeasurePrepare (fun z => -((K.map star).mulVec z))

/-- PDF p.16: support-connecting partial isometry, with both intertwining
identities. The support projections are characterized by their action on X,Y;
no arbitrary projection or inverse of a noninvertible state is introduced. -/
def connectingPartialIsometry {I J : Type}
    (V : Hilbert I →L[ℂ] Hilbert J) (X : Matrix I I ℂ) (Y : Matrix J J ℂ) : Prop :=
  V.comp ((ContinuousLinearMap.adjoint V).comp V) = V ∧
  Y = conjugateCoeff V X ∧ X = conjugateCoeff (ContinuousLinearMap.adjoint V) Y

/-- PDF pp.17-18: finite/countable pure-state ensembles, padded by zero weights.
Each positive component has finite moments; this follows from the source's
finite-energy barycenter and is not a uniform bound on components. -/
structure CountablePureEnsemble (s : ℕ) where
  weight : ℕ → ℝ
  nonnegative : ∀ i, 0 ≤ weight i
  summable : Summable weight
  total : (∑' i, weight i) = 1
  state : ℕ → PureState (NumberString s)
  moments : ∀ i, 0 < weight i → finiteSecondMoments (state i).val.coefficients

/-- PDF p.17: actual trace-norm sum of a countable ensemble. -/
def traceSeries {I : Type} (X : ℕ → Matrix I I ℂ) (Y : Matrix I I ℂ) : Prop :=
  (∀ i, IsTraceClass (X i)) ∧ IsTraceClass Y ∧
  Tendsto (fun n => traceSize (Y - ∑ i ∈ Finset.range n, X i)) atTop (𝓝 0)

/-- PDF pp.9-10: output-entropy convex closure, over all Borel probability
laws supported on S2 with the given barycenter. Extended nonnegative integrals
and infima retain infinity. Dirac ensembles make every S2 fiber nonempty. -/
def finiteMomentConvexClosure {I J : Type} (T : Operation I J)
    (D : Matrix I I ℂ → Prop) (rho : State I) : ℝ≥0∞ :=
  ⨅ mu : {mu : GeneralizedEnsemble I // HasAverage mu rho ∧
      ∀ᵐ sigma ∂(mu : Measure (State I)), D sigma.coefficients},
    ∫⁻ sigma : State I, extendedEntropyNats (T sigma.coefficients)
      ∂(mu.val : Measure (State I))

/-- PDF p.10: the two-channel S2 domain through the actual marginals. -/
def bipartiteFiniteMoments {a c : ℕ}
    (X : Matrix (NumberString a × NumberString c) (NumberString a × NumberString c) ℂ) : Prop :=
  finiteSecondMoments (partialRight X) ∧ finiteSecondMoments (partialLeft X)

/-- PDF pp.9-10, (20)-(21): convex-closure superadditivity and infimal
minimum-output additivity. Auxiliary inputs may be entangled with the signal. -/
def outputEntropyAdditivity {a b c d : ℕ}
    (T : Operation (NumberString a) (NumberString b))
    (S : Operation (NumberString c) (NumberString d)) : Prop :=
  (∀ rho : State (NumberString a × NumberString c), bipartiteFiniteMoments rho.coefficients →
    ∀ (rhoA : State (NumberString a)) (rhoC : State (NumberString c)),
      rhoA.coefficients = partialRight rho.coefficients →
      rhoC.coefficients = partialLeft rho.coefficients →
      finiteMomentConvexClosure T finiteSecondMoments rhoA +
        finiteMomentConvexClosure S finiteSecondMoments rhoC ≤
      finiteMomentConvexClosure (traceClassTensorMap T S) bipartiteFiniteMoments rho) ∧
  domainMinimumEntropy (traceClassTensorMap T S) bipartiteFiniteMoments =
    domainMinimumEntropy T finiteSecondMoments + domainMinimumEntropy S finiteSecondMoments

/-- PDF pp.9-10: a general Gaussian channel, with arbitrary real-linear phase
map, arbitrary displacement, and real symmetric Gaussian noise. CPTP is kept
independently, so this includes squeezing and is not limited to gauge channels.
The frozen Next46.P18.GaussianChannel instead specifies a CENTERED bounded-dual
law for supplied real Weyl systems. This interface fixes complex Fock entries
and also includes displacement; it does not redeclare that centered predicate. -/
structure DisplacedFockGaussianLaw (a b : ℕ) where
  operation : Operation (NumberString a) (NumberString b)
  cptp : IsTraceClassChannel operation
  linear : (Fin b → ℂ) →ₗ[ℝ] (Fin a → ℂ)
  mean : (Fin b → ℂ) →ₗ[ℝ] ℝ
  noise : (Fin b → ℂ) →ₗ[ℝ] ((Fin b → ℂ) →ₗ[ℝ] ℝ)
  symmetric : ∀ z w, noise z w = noise w z
  action : ∀ X, IsTraceClass X → ∀ z,
    complexWeylCharacteristic (operation X) z = complexWeylCharacteristic X (linear z) *
      Complex.exp (Complex.I * (mean z : ℂ) - (noise z z : ℂ))

/-- PDF p.13, (30): noise occupation matrix of the vacuum output. -/
def vacuumOccupation {a b : ℕ} (G : GaugeChannel a b) : Matrix (Fin b) (Fin b) ℂ :=
  G.noise + (1 / 2 : ℂ) • (G.gain * G.gain.conjTranspose - 1)

/-! Sanity checks fix source-domain and zero-mode conventions. -/

example : complexDisplacement (s := 0) 0 = fun _ _ => 1 := by
  funext m n
  simp [complexDisplacement]

example {s : ℕ} : finiteSecondMoments (vacuum s) ↔
    ∀ j, modeEnergy (vacuum s) j < ⊤ := Iff.rfl

example : GaugeFamily.vacuumEntropySum .nil = 0 := rfl

example {a b : ℕ} (G : GaugeChannel a b) :
    vacuumOccupation G = G.noise + (1 / 2 : ℂ) •
      (G.gain * G.gain.conjTranspose - 1) := rfl

example {a b : ℕ} (K : Matrix (Fin b) (Fin a) ℂ) :
    skewPlus K = coherentMeasurePrepare (fun z => (K.map star).mulVec z) := rfl

/-- PDF p.16: a partial isometry that is isometric on the support of X.
Its action off that support is irrelevant to the weighted decomposition. -/
def sourcePartialIsometry {I J : Type} (V : Hilbert I →L[ℂ] Hilbert J)
    (X : Matrix I I ℂ) : Prop :=
  V.comp ((ContinuousLinearMap.adjoint V).comp V) = V ∧
  conjugateCoeff (ContinuousLinearMap.adjoint V) (conjugateCoeff V X) = X

/-- PDF p.21: a finite symplectic identification and its metaplectic
implementation. The induced compatible complex structure is S^{-1} i S;
this describes channels already covariant for that chosen structure. -/
structure SqueezedIdentification (s : ℕ) where
  linear : (Fin s → ℂ) ≃ₗ[ℝ] (Fin s → ℂ)
  symplectic : ∀ z w,
    (∑ j, star (linear z j) * linear w j).im = (∑ j, star (z j) * w j).im
  unitary : Hilbert (NumberString s) ≃ₗᵢ[ℂ] Hilbert (NumberString s)
  implements : ∀ z,
    conjugateCoeff unitary.symm.toLinearIsometry.toContinuousLinearMap
      (complexDisplacement z) = complexDisplacement (linear z)

/-- PDF p.21: actual complex structure induced by a squeezed identification. -/
def squeezedComplexStructure {s : ℕ} (S : SqueezedIdentification s)
    (z : Fin s → ℂ) : Fin s → ℂ :=
  S.linear.symm (fun j => Complex.I * S.linear z j)

/-- PDF p.21: Gaussian channel expressed in the corresponding squeezed
input/output structures, via the actual metaplectic conjugations. -/
def squeezedChannel {a b : ℕ} (G : GaugeChannel a b)
    (SA : SqueezedIdentification a) (SB : SqueezedIdentification b) :
    Operation (NumberString a) (NumberString b) :=
  fun X => conjugateCoeff SB.unitary.toLinearIsometry.toContinuousLinearMap
    (G.operation (conjugateCoeff SA.unitary.symm.toLinearIsometry.toContinuousLinearMap X))

example {s : ℕ} (S : SqueezedIdentification s) :
    squeezedComplexStructure S 0 = 0 := by
  simp only [squeezedComplexStructure, map_zero, Pi.zero_apply, mul_zero]
  exact S.linear.symm.map_zero

example {I J : Type} (V : Hilbert I →L[ℂ] Hilbert J)
    (X : Matrix I I ℂ) (h : sourcePartialIsometry V X) :
    conjugateCoeff (ContinuousLinearMap.adjoint V) (conjugateCoeff V X) = X := h.2

/-- One-mode vacuum-to-vacuum Weyl coefficient fixes the normalization. -/
example (z : ℂ) :
    complexDisplacement (s := 1) (fun _ => z) (fun _ => 0) (fun _ => 0) =
      (Real.exp (-Complex.normSq z / 2) : ℂ) := by
  simp [complexDisplacement,
    QAlgorithms.Papers.Independent.Dependency50.P39.displacementMatrix]

/-- One photon to vacuum fixes the source's minus-conjugate convention. -/
example (z : ℂ) :
    complexDisplacement (s := 1) (fun _ => z) (fun _ => 0) (fun _ => 1) =
      (Real.exp (-Complex.normSq z / 2) : ℂ) * (-star z) := by
  simp [complexDisplacement,
    QAlgorithms.Papers.Independent.Dependency50.P39.displacementMatrix]

end QAlgorithms.Papers.Independent.Gap48.P27


