-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03
-- name    : QAlgorithms_Papers_Independent_Extend50_P03
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T12:50:22.816145+00:00
-- url     : https://prove2.me/theorems/dab0e374-47f3-470f-ba42-3157f20ee8c1
-- title:
--   Definitions for Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes
-- statement:
--   The objects the formalized statements of *Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes* (arXiv:2102.11835) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `hammingCharge`: PDF p.7: Hamming-weight charge.
--   - `chargeRotation`: PDF p.7: exp(+i theta Q).
--   - `Conserves`: PDF p.7: full centralizer, including all sector phases.
--   - `ChargeHaar`: PDF pp.6–7: Haar characterized by probability, support and full left invariance.
--   - `SpecialHaar`: PDF p.12: full SU(2^n) Haar, inside the ambient unitary group.
--   - `splitBits`: Definition 1, PDF p.7: split the first k wires.
--   - `Ancilla`: Definition 1, PDF p.7: fixed normalized charge eigenvector, independent of U.
--   - `pureEncoder`: PDF p.7: append a fixed pure vector and apply U, on all matrix units.
--   - `chargeEncoder`: Definition 1's encoding channel.
--   - `U1ChargeCovariant`: PDF p.5: channel covariance, with the ancilla scalar phase cancelled.
--   - `BitsOn`
--   - `joinBits`: Join assignments on disjoint complementary physical wire sets.
--   - `retain`: PDF p.8: partial trace retaining exactly S.
--   - `PatternLaw`: PDF p.12: classical distribution of t-wire erasure locations.
--   - `flaggedPatternErasure`: PDF p.12: direct-sum flagged erasure, padded with zeros on erased output wires.
--   - `purified`: PDF p.3: purified distance from root fidelity.
--   - `optimizedChoiFidelity`: PDF pp.3–4: optimal Choi fidelity. On channels, the feasible set is nonempty and bounded in [0,1]; the reference is normalized k EPR pairs, not a Haar average.
--   - `worstFidelity`: PDF p.4: one decoder precedes all positive finite reference dimensions and all normalized joint states. On channels both optimization sets are bounded/nonempty.
--   - `optimizedCodeError`: PDF pp.3–4: optimized error, with worst=true or Choi=false.
--   - `siteError`: Decoder receives the complement of the erased set S.
--   - `mixtureError`: Optimized error with the erasure location flag.
--   - `ChargeCodeParameters`
--   - `AdmissibleCodeSizes`: PDF pp.7–8: nontrivial asymptotic parameters. Finite formulas also allow k,t=0.
--   - `LinearSequence`: PDF pp.8,11: exact integer alpha=a*n; no rounding or floor.
--   - `relativeRemainder`: Distinct relative remainders in Theorems 1 and 2.
--   - `leadingError`: PDF pp.8,11: preserve every radical and factor.
--   - `ZeroErrorGuarantee`: Trivial regimes excluded from relative asymptotics: a zero logical register needs no recovery, and a zero erased register permits exact recovery. PDF pp.3–8.
--   - `AsymptoticGuarantee`: Theorem 1 or 2 with uniform C,c before sequences, ancillas, laws, and patterns. Integrability is a conclusion; exponential probability is an upper bound only.
--   - `endpointEntropy`: Entropy at the two charge interval endpoints.
--   - `ChargeInterior`: Compact interior charge endpoints for the linear-charge entropy estimate. Unlike Appendix C, this imposes no small-erasure condition.
--   - `Interior`: PDF p.24: compact interior and valid-sector conditions used in Appendix C.
--   - `chooseZ`: Negative/too-large signed binomial lower indices give zero, never Nat truncation.
--   - `weightSectorProjector`: PDF p.7: Hamming-weight sector projector. Invalid sectors vanish.
--   - `averageChoi`: PDF p.20: constructed joint averaged Choi state, reference first.
--   - `reducedAverage`: PDF p.21: constructed first-t-wire marginal of averageChoi.
--   - `averageSectorWeight`: Eq.(27), PDF p.21.
--   - `averageZeta`: PDF pp.21,25: computed environment marginal, not an arbitrary state.
--   - `comparisonChoi`: PDF p.21: I_R/2^k tensor zeta.
--   - `averageBasis`: PDF p.25: computed averaged environment output of a basis input.
--   - `averageEncodedUnit`: PDF p.25: the actual full physical average, before taking any marginal.
--   - `averageMatrixUnit`: PDF p.25: averaged environment matrix unit.
--   - `averageWorst`: PDF p.25: finite maximum auxiliary averaged-basis error.
--   - `ConcentrationGuarantee`: Lemma 2, PDF pp.10–11: uniform polynomial prefactors, with n/4 and n/2. No entropy conclusion is inserted as an assumption.
--   - `PatternGuarantee`: PDF p.12: one exceptional set for all sites and all flagged classical mixtures.
--   - `unitaryEntryMoment`: PDF p.14: matrix-entry (r,r) moments, including cross-sector correlations.
--   - `ExactDesign`: PDF pp.14–15: exact full symmetric second twirl and its first twirl.
--   - `minSdp`: PDF p.18, Eq.(24): feasible for all PSD rho on finite nonempty registers, with traces bounded below. Block inputs may be subnormalized or zero.
--   - `decouplingFactor`: PDF p.17: diagonal F on equal-charge A,Abar pairs. Its unused orthogonal complement adds only zero rows on the unconditioned side.
--   - `erasureChoi`: PDF p.18: normalized Choi matrix of tracing out the last n-t wires.
--   - `lambdaState`: Lemma 3, PDF p.17: F(Psi tensor tau)F†; P=(A,Abar), Q=(R,E).
--   - `ancillaChoiInput`: PDF p.17: pre-U Choi input with the fixed ancilla.
--   - `choiEntropy`: Appendix A's entropy of the constructed Lambda state.
--   - `basisInput`: Appendix C: normalized logical v appended with the ancilla, trivial reference.
--   - `decouplingInputEntropy`: PDF pp.23–24: entropy for a basis or two-basis input.
--   - `choiSectorKappa`: PDF p.20, Eq.(26): all actual residual sectors, signed binomial indices, positive denominator sectors under alpha≤n-k.
--   - `basisKappa`: PDF p.24: sum of squares over valid residual sectors.
--   - `twoBasis`: PDF p.23: four superpositions; x≠y ensures norm one.
--   - `orthogonalBlockOperator`: Lemma 4, PDF p.19: construct the orthogonal-block operator in order (P1,P2),Q.
--   - `singleErasureLaw`: PDF p.13: uniformly random single erasure with known location.
--   - `choiLowerCoefficient`: Eq.(21), PDF p.13: ceil(k/2)=(k+1)/2; lower coefficient cited from [11].
--   - `chargeCoefficient`: PDF p.12: common charge-dependent leading factor.
--   - `joinFirst`: Join the first t wires and last n-t wires with the exact size equality.
--   - `firstTrace`: The actual first-t-wire marginal, used to identify the constructed averages.
--   - `ChoiEntropyGrowth`: Appendix A, PDF p.20: alpha=a*n with fixed 0<a<1. The source permits all legal k,t, including alpha+k=n; no compact upper-endpoint margin is assumed.
--   - `ChoiEntropyLinear`: Appendix A, PDF p.20: the explicit Omega(n) corollary with k^2t^2=O(n). The exponent constant depends only on a; the threshold may depend on the sequence and its eventual O(n) constant. Ancilla choices remain uniform.
--   - `AverageWorstExpansion`: Appendix D, PDF p.25: equality to leading order, not a finite exact correction.
--   - `OptimalSingleLimit`: PDF p.13: ratios for mean flagged single-erasure errors. The sequence may have growing k in the worst metric; the Choi equality is only claimed at k=1.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, https://arxiv.org/abs/2102.11835v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

/-! Kong–Liu, arXiv:2102.11835v1. Root fidelity; binary logarithms.
Local constructions preserve the fixed physical wire ordering. Matrix integrals use the
finite-dimensional entrywise norm; conditional min-entropy reuses the accepted library.
Compilation pending the batch handoff. -/

noncomputable section

open MeasureTheory Filter
open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

/-- PDF pp.20–21,25: matrix expectations use the continuous extended norm of
finite entrywise function spaces, with the existing product topology. -/
local instance matrixContinuousENorm {I J : Type*} [Fintype I] [Fintype J] :
    ContinuousENorm (Matrix I J ℂ) :=
  inferInstanceAs (ContinuousENorm (I → J → ℂ))

/-- The local continuity instance preserves the entrywise extended norm exactly. -/
example {I J : Type*} [Fintype I] [Fintype J] (M : Matrix I J ℂ) :
    ‖M‖ₑ = ‖(fun i j => M i j)‖ₑ := rfl

/-- Borel ensemble outcomes, PDF pp.6–7. -/
instance unitaryMeasurable (n : ℕ) : MeasurableSpace ((Matrix.unitaryGroup (Qubits n) ℂ)) := borel _

/-- PDF p.7: Hamming-weight charge. -/
def hammingCharge (n : ℕ) : (Matrix (Qubits n) (Qubits n) ℂ) := Matrix.diagonal fun x => (hammingWeight x : ℂ)

/-- PDF p.7: exp(+i theta Q). -/
def chargeRotation (n : ℕ) (theta : ℝ) : (Matrix (Qubits n) (Qubits n) ℂ) :=
  Matrix.diagonal fun x => Complex.exp (Complex.I * (theta : ℂ) * (hammingWeight x : ℂ))

/-- PDF p.7: full centralizer, including all sector phases. -/
def Conserves {n : ℕ} (U : (Matrix.unitaryGroup (Qubits n) ℂ)) : Prop :=
  (U : (Matrix (Qubits n) (Qubits n) ℂ)) * hammingCharge n = hammingCharge n * (U : (Matrix (Qubits n) (Qubits n) ℂ))

/-- PDF pp.6–7: Haar characterized by probability, support and full left invariance. -/
def ChargeHaar (n : ℕ) (mu : Measure ((Matrix.unitaryGroup (Qubits n) ℂ))) : Prop :=
  IsProbabilityMeasure mu ∧ (∀ᵐ (U : Matrix.unitaryGroup (Qubits n) ℂ) ∂mu, Conserves U) ∧
    ∀ V : (Matrix.unitaryGroup (Qubits n) ℂ), Conserves V → Measure.map (fun U => V * U) mu = mu

/-- PDF p.12: full SU(2^n) Haar, inside the ambient unitary group. -/
def SpecialHaar (n : ℕ) (mu : Measure ((Matrix.unitaryGroup (Qubits n) ℂ))) : Prop :=
  IsProbabilityMeasure mu ∧ (∀ᵐ (U : Matrix.unitaryGroup (Qubits n) ℂ) ∂mu, Matrix.det (U : (Matrix (Qubits n) (Qubits n) ℂ)) = 1) ∧
    ∀ V : (Matrix.unitaryGroup (Qubits n) ℂ), Matrix.det (V : (Matrix (Qubits n) (Qubits n) ℂ)) = 1 → Measure.map (fun U => V * U) mu = mu

/-- Definition 1, PDF p.7: split the first k wires. -/
def splitBits (n k : ℕ) (h : k ≤ n) (z : Qubits n) : Qubits k × Qubits (n-k) :=
  qubitsAppendEquiv k (n-k) (fun i => z (Fin.cast (Nat.add_sub_of_le h) i))

/-- Definition 1, PDF p.7: fixed normalized charge eigenvector, independent of U. -/
structure Ancilla (n k alpha : ℕ) where
  logical_le : k ≤ n
  charge_le : alpha ≤ n-k
  vector : EuclideanSpace ℂ (Qubits (n-k))
  normalized : IsState vector
  eigen : act (hammingCharge (n-k)) vector = (alpha : ℂ) • vector

/-- PDF p.7: append a fixed pure vector and apply U, on all matrix units. -/
def pureEncoder {n k : ℕ} (h : k ≤ n) (psi : EuclideanSpace ℂ (Qubits (n-k)))
    (U : (Matrix.unitaryGroup (Qubits n) ℂ)) : Superop (Qubits k) (Qubits n) := fun rho =>
  (U : (Matrix (Qubits n) (Qubits n) ℂ)) * (Matrix.of fun z w => rho (splitBits n k h z).1 (splitBits n k h w).1 *
    psi (splitBits n k h z).2 * conj (psi (splitBits n k h w).2)) * (U : (Matrix (Qubits n) (Qubits n) ℂ))ᴴ

/-- Definition 1's encoding channel. -/
def chargeEncoder {n k alpha : ℕ} (A : Ancilla n k alpha) (U : (Matrix.unitaryGroup (Qubits n) ℂ)) :
    Superop (Qubits k) (Qubits n) := pureEncoder A.logical_le A.vector U

/-- PDF p.5: channel covariance, with the ancilla scalar phase cancelled. -/
def U1ChargeCovariant {n k : ℕ} (E : Superop (Qubits k) (Qubits n)) : Prop :=
  ∀ theta : ℝ, ∀ rho : (Matrix (Qubits k) (Qubits k) ℂ), IsDensityMatrix rho →
    E (chargeRotation k theta * rho * (chargeRotation k theta)ᴴ) =
      chargeRotation n theta * E rho * (chargeRotation n theta)ᴴ

abbrev BitsOn {n : ℕ} (S : Finset (Fin n)) := {i : Fin n // i ∈ S} → Bool

/-- Join assignments on disjoint complementary physical wire sets. -/
def joinBits {n : ℕ} (S : Finset (Fin n)) (u : BitsOn S) (v : BitsOn Sᶜ) : Qubits n :=
  fun i => if h : i ∈ S then u ⟨i,h⟩ else v ⟨i, by simpa using h⟩

/-- PDF p.8: partial trace retaining exactly S. -/
def retain {n : ℕ} (S : Finset (Fin n)) : Superop (Qubits n) (BitsOn S) :=
  fun rho => Matrix.of fun u v => ∑ z : BitsOn Sᶜ, rho (joinBits S u z) (joinBits S v z)

/-- PDF p.12: classical distribution of t-wire erasure locations. -/
def PatternLaw (n t : ℕ) (p : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ p S) ∧ (∑ S, p S) = 1 ∧ ∀ S, S.card ≠ t → p S = 0

/-- PDF p.12: direct-sum flagged erasure, padded with zeros on erased output wires. -/
def flaggedPatternErasure {n : ℕ} (p : Finset (Fin n) → ℝ) :
    Superop (Qubits n) (Finset (Fin n) × Qubits n) :=
  fun rho => Matrix.of fun y z =>
    if y.1 = z.1 ∧ (∀ i ∈ y.1, y.2 i = false) ∧ (∀ i ∈ z.1, z.2 i = false) then
      (p y.1 : ℂ) * ∑ e : BitsOn y.1,
        rho (joinBits y.1 e (fun i => y.2 i)) (joinBits y.1 e (fun i => z.2 i))
    else 0

/-- PDF p.3: purified distance from root fidelity. -/
def purified {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) : ℝ :=
  Real.sqrt (1 - rootFidelity rho sigma ^ 2)

/-- PDF pp.3–4: optimal Choi fidelity. On channels, the feasible set is nonempty
and bounded in [0,1]; the reference is normalized k EPR pairs, not a Haar average. -/
def optimizedChoiFidelity {k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (N : Superop (Qubits k) B) : ℝ :=
  sSup {f : ℝ | ∃ D : Superop B (Qubits k), IsChannel D ∧
    f = rootFidelity (pureDensity (maxEntangled k))
      (idTensorSuperop (R := Qubits k) (D ∘ N) (pureDensity (maxEntangled k)))}

/-- PDF p.4: one decoder precedes all positive finite reference dimensions and
all normalized joint states. On channels both optimization sets are bounded/nonempty. -/
def worstFidelity {k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (N : Superop (Qubits k) B) : ℝ :=
  sSup {f : ℝ | ∃ D : Superop B (Qubits k), IsChannel D ∧
    f = sInf {g : ℝ | ∃ r : ℕ, ∃ rho : Matrix (Fin (r+1) × Qubits k)
        (Fin (r+1) × Qubits k) ℂ, IsDensityMatrix rho ∧
      g = rootFidelity rho (idTensorSuperop (R := Fin (r+1)) (D ∘ N) rho)}}

/-- PDF pp.3–4: optimized error, with worst=true or Choi=false. -/
def optimizedCodeError {k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (worst : Bool) (N : Superop (Qubits k) B) : ℝ :=
  Real.sqrt (1 - (if worst then worstFidelity N else optimizedChoiFidelity N) ^ 2)

/-- Decoder receives the complement of the erased set S. -/
def siteError {n k alpha : ℕ} (worst : Bool) (A : Ancilla n k alpha)
    (S : Finset (Fin n)) (U : (Matrix.unitaryGroup (Qubits n) ℂ)) : ℝ :=
  optimizedCodeError worst (retain Sᶜ ∘ chargeEncoder A U)

/-- Optimized error with the erasure location flag. -/
def mixtureError {n k alpha : ℕ} (worst : Bool) (A : Ancilla n k alpha)
    (p : Finset (Fin n) → ℝ) (U : (Matrix.unitaryGroup (Qubits n) ℂ)) : ℝ :=
  optimizedCodeError worst (flaggedPatternErasure p ∘ chargeEncoder A U)

structure ChargeCodeParameters where
  n : ℕ
  k : ℕ
  alpha : ℕ
  t : ℕ

/-- PDF pp.7–8: nontrivial asymptotic parameters. Finite formulas also allow k,t=0. -/
def AdmissibleCodeSizes (d : ChargeCodeParameters) : Prop :=
  1 ≤ d.n ∧ 1 ≤ d.k ∧ d.k ≤ d.n ∧ d.alpha ≤ d.n-d.k ∧ 1 ≤ d.t ∧ d.t ≤ d.n

/-- PDF pp.8,11: exact integer alpha=a*n; no rounding or floor. -/
def LinearSequence (a : ℝ) (d : ℕ → ChargeCodeParameters) : Prop :=
  Tendsto (fun i => (d i).n) atTop atTop ∧
    ∀ i, AdmissibleCodeSizes (d i) ∧ ((d i).alpha : ℝ) = a * (d i).n

/-- Distinct relative remainders in Theorems 1 and 2. -/
def relativeRemainder (worst : Bool) (d : ChargeCodeParameters) : ℝ :=
  if worst then (d.k : ℝ) * (d.t : ℝ)^2 / d.n
  else (d.k : ℝ)^2 * (d.t : ℝ)^2 / d.n

/-- PDF pp.8,11: preserve every radical and factor. -/
def leadingError (worst : Bool) (a : ℝ) (d : ChargeCodeParameters) : ℝ :=
  (if worst then (d.k : ℝ) * Real.sqrt d.t else Real.sqrt ((d.t : ℝ) * d.k)) /
    (4 * d.n * Real.sqrt (a * (1-a)))

/-- Trivial regimes excluded from relative asymptotics: a zero logical register
needs no recovery, and a zero erased register permits exact recovery. PDF pp.3–8. -/
def ZeroErrorGuarantee (worst : Bool) : Prop :=
  (∀ n alpha : ℕ, ∀ A : Ancilla n 0 alpha, ∀ S : Finset (Fin n),
    ∀ U : (Matrix.unitaryGroup (Qubits n) ℂ), siteError worst A S U = 0) ∧
  (∀ n k alpha : ℕ, ∀ A : Ancilla n k alpha, ∀ U : (Matrix.unitaryGroup (Qubits n) ℂ),
    siteError worst A ∅ U = 0)

/-- Theorem 1 or 2 with uniform C,c before sequences, ancillas, laws, and patterns.
Integrability is a conclusion; exponential probability is an upper bound only. -/
def AsymptoticGuarantee (L : (n : ℕ) → Measure ((Matrix.unitaryGroup (Qubits n) ℂ)) → Prop) (worst : Bool) : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 → ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∀ d : ℕ → ChargeCodeParameters, LinearSequence a d →
      Tendsto (fun i => relativeRemainder worst (d i)) atTop (nhds 0) →
      ∃ N : ℕ, ∀ i ≥ N, ∀ A : Ancilla (d i).n (d i).k (d i).alpha,
      ∀ mu : Measure ((Matrix.unitaryGroup (Qubits (d i).n) ℂ)), L (d i).n mu →
      ∀ S : Finset (Fin (d i).n), S.card = (d i).t →
      let B := leadingError worst a (d i) * (1 + C * relativeRemainder worst (d i))
      Integrable (siteError worst A S) mu ∧ (∫ U, siteError worst A S U ∂mu) ≤ B ∧
      mu {U | B < siteError worst A S U} ≤ ENNReal.ofReal (Real.exp (-c * (d i).n))

/-- Entropy at the two charge interval endpoints. -/
def endpointEntropy (d : ChargeCodeParameters) : ℝ :=
  min (binEntropy2 ((d.alpha : ℝ) / d.n))
    (binEntropy2 (((d.alpha : ℝ) + d.k) / d.n))

/-- Compact interior charge endpoints for the linear-charge entropy estimate.
Unlike Appendix C, this imposes no small-erasure condition. -/
def ChargeInterior (b : ℝ) (d : ChargeCodeParameters) : Prop :=
  1 ≤ d.n ∧ d.k ≤ d.n ∧ d.alpha ≤ d.n-d.k ∧ d.t ≤ d.n ∧
    b ≤ (d.alpha : ℝ)/d.n ∧ ((d.alpha : ℝ)+d.k)/d.n ≤ 1-b

/-- PDF p.24: compact interior and valid-sector conditions used in Appendix C. -/
def Interior (b : ℝ) (d : ChargeCodeParameters) : Prop :=
  AdmissibleCodeSizes d ∧ b ≤ (d.alpha : ℝ)/d.n ∧ ((d.alpha : ℝ)+d.k)/d.n ≤ 1-b ∧
    d.t ≤ d.alpha ∧ d.alpha + d.k ≤ d.n-d.t

/-- Negative/too-large signed binomial lower indices give zero, never Nat truncation. -/
def chooseZ (n : ℕ) (q : ℤ) : ℝ :=
  if 0 ≤ q ∧ q ≤ (n : ℤ) then (n.choose q.toNat : ℝ) else 0

/-- PDF p.7: Hamming-weight sector projector. Invalid sectors vanish. -/
def weightSectorProjector (n : ℕ) (q : ℤ) : (Matrix (Qubits n) (Qubits n) ℂ) :=
  Matrix.diagonal fun x => if (hammingWeight x : ℤ) = q then 1 else 0

/-- PDF p.20: constructed joint averaged Choi state, reference first. -/
def averageChoi (n k alpha : ℕ) : Matrix (Qubits k × Qubits n) (Qubits k × Qubits n) ℂ :=
  ∑ j ∈ Finset.range (k+1), (((2 : ℝ)^k)⁻¹ / chooseZ n (j+alpha) : ℂ) •
    Matrix.kronecker (weightSectorProjector k j) (weightSectorProjector n (j+alpha))

/-- PDF p.21: constructed first-t-wire marginal of averageChoi. -/
def reducedAverage (n k alpha t : ℕ) :
    Matrix (Qubits k × Qubits t) (Qubits k × Qubits t) ℂ :=
  ∑ j ∈ Finset.range (k+1), ∑ i ∈ Finset.range (t+1),
    ((((2 : ℝ)^k)⁻¹ * chooseZ (n-t) ((j : ℤ)+alpha-i) /
      chooseZ n ((j : ℤ)+alpha) : ℝ) : ℂ) •
      Matrix.kronecker (weightSectorProjector k j) (weightSectorProjector t i)

/-- Eq.(27), PDF p.21. -/
def averageSectorWeight (n k alpha t i : ℕ) : ℝ :=
  ((2 : ℝ)^k)⁻¹ * ∑ j ∈ Finset.range (k+1),
    (k.choose j : ℝ) * chooseZ (n-t) ((j : ℤ)+alpha-i) / chooseZ n ((j : ℤ)+alpha)

/-- PDF pp.21,25: computed environment marginal, not an arbitrary state. -/
def averageZeta (n k alpha t : ℕ) : (Matrix (Qubits t) (Qubits t) ℂ) :=
  ∑ i ∈ Finset.range (t+1), (averageSectorWeight n k alpha t i : ℂ) • weightSectorProjector t i

/-- PDF p.21: I_R/2^k tensor zeta. -/
def comparisonChoi (n k alpha t : ℕ) :
    Matrix (Qubits k × Qubits t) (Qubits k × Qubits t) ℂ :=
  Matrix.kronecker (((((2 : ℝ)^k)⁻¹ : ℝ) : ℂ) • (1 : (Matrix (Qubits k) (Qubits k) ℂ))) (averageZeta n k alpha t)

/-- PDF p.25: computed averaged environment output of a basis input. -/
def averageBasis {k : ℕ} (n alpha t : ℕ) (x : Qubits k) : (Matrix (Qubits t) (Qubits t) ℂ) :=
  ∑ i ∈ Finset.range (t+1),
    ((chooseZ (n-t) ((hammingWeight x : ℤ)+alpha-i) /
      chooseZ n ((hammingWeight x : ℤ)+alpha) : ℝ) : ℂ) • weightSectorProjector t i

/-- PDF p.25: the actual full physical average, before taking any marginal. -/
def averageEncodedUnit {k : ℕ} (n alpha : ℕ) (x y : Qubits k) : (Matrix (Qubits n) (Qubits n) ℂ) :=
  if x = y then ((chooseZ n ((hammingWeight x : ℤ)+alpha))⁻¹ : ℂ) •
    weightSectorProjector n ((hammingWeight x : ℤ)+alpha) else 0

/-- PDF p.25: averaged environment matrix unit. -/
def averageMatrixUnit {k : ℕ} (n alpha t : ℕ) (x y : Qubits k) : (Matrix (Qubits t) (Qubits t) ℂ) :=
  if x = y then averageBasis n alpha t x else 0

/-- PDF p.25: finite maximum auxiliary averaged-basis error. -/
def averageWorst (n k alpha t : ℕ) : ℝ :=
  sSup {p : ℝ | ∃ x : Qubits k,
    p = purified (averageBasis n alpha t x) (averageZeta n k alpha t)}

/-- Lemma 2, PDF pp.10–11: uniform polynomial prefactors, with n/4 and n/2.
No entropy conclusion is inserted as an assumption. -/
def ConcentrationGuarantee (L : (n : ℕ) → Measure ((Matrix.unitaryGroup (Qubits n) ℂ)) → Prop) : Prop :=
  ∀ b : ℝ, 0 < b → b < 1/2 → ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ,
    ∀ d : ℕ → ChargeCodeParameters, Tendsto (fun i => (d i).n) atTop atTop →
      (∀ᶠ i in atTop, Interior b (d i)) → ∃ N : ℕ, ∀ i ≥ N,
      ∀ A : Ancilla (d i).n (d i).k (d i).alpha,
      ∀ mu : Measure ((Matrix.unitaryGroup (Qubits (d i).n) ℂ)), L (d i).n mu →
      ∀ S : Finset (Fin (d i).n), S.card = (d i).t →
      ∀ epsilon delta deltaPrime : ℝ, 0 ≤ epsilon → 0 < delta → 0 < deltaPrime →
      ∀ zeta : (Matrix (Qubits (d i).t) (Qubits (d i).t) ℂ), IsDensityMatrix zeta →
      (∀ x : Qubits (d i).k, purified (averageBasis (d i).n (d i).alpha (d i).t x) zeta ≤ epsilon) →
      mu {U | epsilon + delta + (2 : ℝ)^(d i).k * Real.sqrt deltaPrime <
        siteError true A S U} ≤ ENNReal.ofReal
        (C * ((d i).n : ℝ)^D *
          ((2 : ℝ)^((d i).k - ((d i).n : ℝ)/4 * endpointEntropy (d i) + (d i).t/2) / delta +
           (2 : ℝ)^(2*(d i).k - ((d i).n : ℝ)/2 * endpointEntropy (d i) + (d i).t) / deltaPrime))

/-- PDF p.12: one exceptional set for all sites and all flagged classical mixtures. -/
def PatternGuarantee (L : (n : ℕ) → Measure ((Matrix.unitaryGroup (Qubits n) ℂ)) → Prop) : Prop :=
  ∀ worst : Bool, ∀ a : ℝ, 0 < a → a < 1 → ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∀ d : ℕ → ChargeCodeParameters, LinearSequence a d →
      Tendsto (fun i => relativeRemainder worst (d i)) atTop (nhds 0) →
      ∃ N : ℕ, ∀ i ≥ N, ∀ A : Ancilla (d i).n (d i).k (d i).alpha,
      ∀ mu : Measure ((Matrix.unitaryGroup (Qubits (d i).n) ℂ)), L (d i).n mu →
      let B := leadingError worst a (d i) * (1 + C * relativeRemainder worst (d i))
      (∀ p : Finset (Fin (d i).n) → ℝ, PatternLaw (d i).n (d i).t p →
        Integrable (mixtureError worst A p) mu ∧ (∫ U, mixtureError worst A p U ∂mu) ≤ B) ∧
      mu {U | (∃ S : Finset (Fin (d i).n), S.card = (d i).t ∧ B < siteError worst A S U) ∨
        (∃ p : Finset (Fin (d i).n) → ℝ, PatternLaw (d i).n (d i).t p ∧
          B < mixtureError worst A p U)} ≤ ENNReal.ofReal (Real.exp (-c * (d i).n))

/-- PDF p.14: matrix-entry (r,r) moments, including cross-sector correlations. -/
def unitaryEntryMoment {n : ℕ} (r : ℕ) (a b c d : Fin r → Qubits n) (U : (Matrix.unitaryGroup (Qubits n) ℂ)) : ℂ :=
  (∏ i, (U : (Matrix (Qubits n) (Qubits n) ℂ)) (a i) (b i)) * conj (∏ i, (U : (Matrix (Qubits n) (Qubits n) ℂ)) (c i) (d i))

/-- PDF pp.14–15: exact full symmetric second twirl and its first twirl. -/
def ExactDesign (n : ℕ) (mu : Measure ((Matrix.unitaryGroup (Qubits n) ℂ))) : Prop :=
  IsProbabilityMeasure mu ∧ (∀ᵐ (U : Matrix.unitaryGroup (Qubits n) ℂ) ∂mu, Conserves U) ∧
    ∃ nu : Measure ((Matrix.unitaryGroup (Qubits n) ℂ)), ChargeHaar n nu ∧
      ∀ r ∈ ({1,2} : Finset ℕ), ∀ a b c d : Fin r → Qubits n,
        Integrable (unitaryEntryMoment r a b c d) mu ∧ Integrable (unitaryEntryMoment r a b c d) nu ∧
        (∫ U, unitaryEntryMoment r a b c d U ∂mu) = ∫ U, unitaryEntryMoment r a b c d U ∂nu

/-- PDF p.18, Eq.(24): feasible for all PSD rho on finite nonempty registers,
with traces bounded below. Block inputs may be subnormalized or zero. -/
def minSdp {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (rho : Matrix (P × Q) (P × Q) ℂ) : ℝ :=
  sInf {s : ℝ | ∃ sigma : Matrix Q Q ℂ, sigma.PosSemidef ∧
    (Matrix.kronecker (1 : Matrix P P ℂ) sigma - rho).PosSemidef ∧ s = sigma.trace.re}

/-- PDF p.17: diagonal F on equal-charge A,Abar pairs. Its unused orthogonal
complement adds only zero rows on the unconditioned side. -/
def decouplingFactor (n : ℕ) (a b : Qubits n) : ℝ :=
  if hammingWeight a = hammingWeight b then
    Real.sqrt ((2 : ℝ)^n / chooseZ n (hammingWeight a)) else 0

/-- PDF p.18: normalized Choi matrix of tracing out the last n-t wires. -/
def erasureChoi (n t : ℕ) : Matrix (Qubits n × Qubits t) (Qubits n × Qubits t) ℂ :=
  Matrix.of fun p q =>
    if (∀ i : Fin t, ∀ h : i.val < n, p.1 ⟨i.val,h⟩ = p.2 i ∧ q.1 ⟨i.val,h⟩ = q.2 i) ∧
      (∀ i : Fin n, t ≤ i.val → p.1 i = q.1 i) then (((2 : ℝ)^n)⁻¹ : ℂ) else 0

/-- Lemma 3, PDF p.17: F(Psi tensor tau)F†; P=(A,Abar), Q=(R,E). -/
def lambdaState {R : Type*} (n t : ℕ)
    (Psi : Matrix (R × Qubits n) (R × Qubits n) ℂ) :
    Matrix ((Qubits n × Qubits n) × (R × Qubits t))
      ((Qubits n × Qubits n) × (R × Qubits t)) ℂ :=
  Matrix.of fun p q =>
    (decouplingFactor n p.1.1 p.1.2 : ℂ) * (decouplingFactor n q.1.1 q.1.2 : ℂ) *
      Psi (p.2.1,p.1.1) (q.2.1,q.1.1) * erasureChoi n t (p.1.2,p.2.2) (q.1.2,q.2.2)

/-- PDF p.17: pre-U Choi input with the fixed ancilla. -/
def ancillaChoiInput {n k alpha : ℕ} (A : Ancilla n k alpha) :
    Matrix (Qubits k × Qubits n) (Qubits k × Qubits n) ℂ :=
  idTensorSuperop (R := Qubits k) (chargeEncoder A 1) (pureDensity (maxEntangled k))

/-- Appendix A's entropy of the constructed Lambda state. -/
def choiEntropy {n k alpha : ℕ} (A : Ancilla n k alpha) (t : ℕ) : EReal :=
  minEntropy (lambdaState n t (ancillaChoiInput A))

/-- Appendix C: normalized logical v appended with the ancilla, trivial reference. -/
def basisInput {n k alpha : ℕ} (A : Ancilla n k alpha)
    (v : EuclideanSpace ℂ (Qubits k)) : Matrix (Unit × Qubits n) (Unit × Qubits n) ℂ :=
  Matrix.of fun p q => chargeEncoder A 1 (pureDensity v) p.2 q.2

/-- PDF pp.23–24: entropy for a basis or two-basis input. -/
def decouplingInputEntropy {n k alpha : ℕ} (A : Ancilla n k alpha) (t : ℕ)
    (v : EuclideanSpace ℂ (Qubits k)) : EReal :=
  minEntropy (lambdaState n t (basisInput A v))

/-- PDF p.20, Eq.(26): all actual residual sectors, signed binomial indices,
positive denominator sectors under alpha≤n-k. -/
def choiSectorKappa (n k alpha t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n-t+1), (∑ j ∈ Finset.range (k+1),
    chooseZ t ((j : ℤ)+alpha-i) * (k.choose j : ℝ) /
      Real.sqrt ((2 : ℝ)^k * chooseZ n ((j : ℤ)+alpha)))^2

/-- PDF p.24: sum of squares over valid residual sectors. -/
def basisKappa (n q t : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (n-t+1), (chooseZ t ((q : ℤ)-i))^2) / chooseZ n q

/-- PDF p.23: four superpositions; x≠y ensures norm one. -/
def twoBasis {k : ℕ} (x y : Qubits k) (imaginary negative : Bool) :
    EuclideanSpace ℂ (Qubits k) :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (ket x +
    ((if negative then -1 else 1) * (if imaginary then Complex.I else 1) : ℂ) • ket y)

/-- Lemma 4, PDF p.19: construct the orthogonal-block operator in order (P1,P2),Q. -/
def orthogonalBlockOperator {P1 P2 Q : Type*} {m : ℕ}
    (Pi : Fin m → Matrix P1 P1 ℂ) (rho : Fin m → Matrix (P2 × Q) (P2 × Q) ℂ) :
    Matrix ((P1 × P2) × Q) ((P1 × P2) × Q) ℂ :=
  Matrix.of fun p q => ∑ i, Pi i p.1.1 q.1.1 * rho i (p.1.2,p.2) (q.1.2,q.2)

/-- PDF p.13: uniformly random single erasure with known location. -/
def singleErasureLaw (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  if S.card = 1 then (n : ℝ)⁻¹ else 0

/-- Eq.(21), PDF p.13: ceil(k/2)=(k+1)/2; lower coefficient cited from [11]. -/
def choiLowerCoefficient (k : ℕ) : ℝ :=
  ((k.choose ((k+1)/2) : ℝ) * (((k+1)/2 : ℕ) : ℝ)) / (2 : ℝ)^k

/-- PDF p.12: common charge-dependent leading factor. -/
def chargeCoefficient (a : ℝ) : ℝ := (4 * Real.sqrt (a*(1-a)))⁻¹

example : chooseZ 3 (-1) = 0 := by norm_num [chooseZ]

example : chooseZ 3 4 = 0 := by norm_num [chooseZ]

example : chooseZ 3 0 = 1 := by norm_num [chooseZ]

example : chargeCoefficient (1/2) = 1/2 := by norm_num [chargeCoefficient]

example : choiLowerCoefficient 1 = 1/2 := by norm_num [choiLowerCoefficient]

example : binEntropy2 0 = 0 := by simp [QAlgorithms.binEntropy2]

example {n : ℕ} (S : Finset (Fin n)) (rho : (Matrix (Qubits n) (Qubits n) ℂ)) (u v : BitsOn S) :
    retain S rho u v = ∑ z : BitsOn Sᶜ, rho (joinBits S u z) (joinBits S v z) := rfl

example {k : ℕ} (n alpha t : ℕ) (x y : Qubits k) (h : x ≠ y) :
    averageMatrixUnit n alpha t x y = 0 := by simp [averageMatrixUnit,h]

example (worst : Bool) (a : ℝ) (n alpha : ℕ) :
    leadingError worst a ⟨n,0,alpha,0⟩ = 0 := by cases worst <;> simp [leadingError]

/-- Sanity: the zero group angle acts as identity on every basis amplitude. -/
example (n : ℕ) (x : Qubits n) : chargeRotation n 0 x x = 1 := by simp [chargeRotation]

/-- Sanity: the physical charge has the source's eigenvalues on basis strings. -/
example (n : ℕ) (x : Qubits n) : hammingCharge n x x = (hammingWeight x : ℂ) := by simp [hammingCharge]

/-- Sanity: the trivial complementary-channel Choi state is normalized. -/
example : erasureChoi 0 0 (fun _ => false, fun _ => false)
    (fun _ => false, fun _ => false) = 1 := by simp [erasureChoi]

/-- Sanity: the scalar F on the zero-qubit charge sector is one. -/
example : decouplingFactor 0 (fun _ => false) (fun _ => false) = 1 := by
  norm_num [decouplingFactor, chooseZ, hammingWeight]

/-- Sanity: a zero moment order has no spurious sector-phase restriction. -/
example {n : ℕ} (a b c d : Fin 0 → Qubits n) (U : (Matrix.unitaryGroup (Qubits n) ℂ)) :
    unitaryEntryMoment 0 a b c d U = 1 := by simp [unitaryEntryMoment]

/-- Sanity: a distinct-input averaged physical coherence is zero. -/
example {k : ℕ} (n alpha : ℕ) (x y : Qubits k) (h : x ≠ y) :
    averageEncodedUnit n alpha x y = 0 := by simp [averageEncodedUnit,h]

/-- Join the first t wires and last n-t wires with the exact size equality. -/
def joinFirst (n t : ℕ) (h : t ≤ n) (u : Qubits t) (v : Qubits (n-t)) : Qubits n :=
  fun i => Fin.append u v (Fin.cast (Nat.add_sub_of_le h).symm i)

/-- The actual first-t-wire marginal, used to identify the constructed averages. -/
def firstTrace (n t : ℕ) (h : t ≤ n) : Superop (Qubits n) (Qubits t) :=
  fun rho => Matrix.of fun u v => ∑ z : Qubits (n-t),
    rho (joinFirst n t h u z) (joinFirst n t h v z)

/-- Appendix A, PDF p.20: alpha=a*n with fixed 0<a<1. The source permits
all legal k,t, including alpha+k=n; no compact upper-endpoint margin is assumed. -/
def ChoiEntropyGrowth : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
    ∀ d : ChargeCodeParameters, N ≤ d.n → 1 ≤ d.n → d.t ≤ d.n →
      (d.alpha : ℝ) = a * d.n → ∀ A : Ancilla d.n d.k d.alpha,
      ((d.n * endpointEntropy d - 2*d.t - d.k - C*Real.logb 2 (d.n+1) : ℝ) : EReal) ≤
        choiEntropy A d.t

/-- Appendix A, PDF p.20: the explicit Omega(n) corollary with k^2t^2=O(n).
The exponent constant depends only on a; the threshold may depend on the sequence
and its eventual O(n) constant. Ancilla choices remain uniform. -/
def ChoiEntropyLinear : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 → ∃ c : ℝ, 0 < c ∧
    ∀ d : ℕ → ChargeCodeParameters, LinearSequence a d →
      (∃ K : ℝ, 0 < K ∧ ∀ᶠ i in atTop, relativeRemainder false (d i) ≤ K) →
      ∃ N : ℕ, ∀ i ≥ N, ∀ A : Ancilla (d i).n (d i).k (d i).alpha,
        ((c*(d i).n : ℝ) : EReal) ≤ choiEntropy A (d i).t

/-- Appendix D, PDF p.25: equality to leading order, not a finite exact correction. -/
def AverageWorstExpansion : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 → ∃ C : ℝ, 0 < C ∧
    ∀ d : ℕ → ChargeCodeParameters, LinearSequence a d →
      Tendsto (fun i => relativeRemainder true (d i)) atTop (nhds 0) →
      ∃ N : ℕ, ∀ i ≥ N,
        |averageWorst (d i).n (d i).k (d i).alpha (d i).t /
          leadingError true a (d i) - 1| ≤ C * relativeRemainder true (d i)

/-- PDF p.13: ratios for mean flagged single-erasure errors. The sequence may
have growing k in the worst metric; the Choi equality is only claimed at k=1. -/
def OptimalSingleLimit (worst : Bool) : Prop :=
  ∀ d : ℕ → ChargeCodeParameters, LinearSequence (1/2) d →
    (∀ i, (d i).t = 1 ∧ Even (d i).n) →
    (if worst then Tendsto (fun i => ((d i).k : ℝ)/(d i).n) atTop (nhds 0)
     else ∀ i, (d i).k = 1) →
    ∀ A : (i : ℕ) → Ancilla (d i).n (d i).k (d i).alpha,
    ∀ mu : (i : ℕ) → Measure ((Matrix.unitaryGroup (Qubits (d i).n) ℂ)), (∀ i, ChargeHaar (d i).n (mu i)) →
      Tendsto (fun i => (∫ U, mixtureError worst (A i) (singleErasureLaw (d i).n) U ∂(mu i)) /
        leadingError worst (1/2) (d i)) atTop (nhds 1)

end QAlgorithms.Papers.Independent.Extend50.P03


