-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P21
-- name    : QAlgorithms_Papers_Independent_Claimed50_P21
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:03:14.64353+00:00
-- url     : https://prove2.me/theorems/21cba3db-6918-44e8-af64-8435c768b0f7
-- title:
--   Definitions for Information - Disturbance Tradeoff in the Estimation of a Unitary Transformation
-- statement:
--   The objects the formalized statements of *Information - Disturbance Tradeoff in the Estimation of a Unitary Transformation* (arXiv:1006.5665) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Wire`: PDF p.4: one d-dimensional wire in the fixed computational basis.
--   - `Four`: PDF p.4: the four wires, in descending order ((3,2),(1,0)).
--   - `Three`: PDF p.8: wires (1,1',0'), or (2,1',0') after the unknown use.
--   - `SU`: PDF p.4: the unknown and the estimate both range over SU(d).
--   - `unitaryMatrix`: PDF p.4: matrix of a special unitary in the fixed basis.
--   - `HaarLaw`: PDF p.4: normalized Haar law, specified by its probability and both translation invariances. Such a law is unique; no input- or outcome-dependent prior is permitted.
--   - `IsDeterministicTwoComb`: PDF pp.3–4, Eqs.(5),(14): deterministic two-comb, including both causal traces.
--   - `linkedChoi`: PDF pp.3,5, link product: insert exactly one U into wires 1 to 2.
--   - `insertedOutput`: PDF p.3, Eq.(9): actual conditional output operation, without normalization.
--   - `outcomeDensity`: PDF p.5, Eq.(15): conditional outcome density relative to normalized Haar.
--   - `fidelityVector`: PDF p.5, Eq.(20): vector |U>>_30 |U*>>_21 in descending wire order.
--   - `fidelityKernel`: PDF p.5, Eq.(20): subnormalized channel entanglement-fidelity kernel.
--   - `gainKernel`: PDF p.5, Eqs.(15),(16),(19): information kernel for the input I/d.
--   - `pureKernel`: PDF p.5, following Eq.(20): pure-state fidelity kernel; its trace weighting is already included in the subnormalized conditional output.
--   - `IsHaarCombInstrument`: PDF pp.4–5: measurable PSD density, integrable entries and actual scalar score kernels, whose Haar integral is a deterministic comb. No pointwise trace bound is imposed. The pure-state kernel uses the uniform pure-state measure from the accepted library.
--   - `channelScore`: PDF p.5, Eq.(20): average entanglement fidelity with independent U,V integrations.
--   - `gain`: PDF p.5, Eq.(19): average information gain for rho=I/d.
--   - `averagePureFidelity`: PDF p.5, following Eq.(20): actual triple average of subnormalized state fidelities.
--   - `representation`: PDF p.6, Eqs.(22)–(24): full left/right representation V3 V2* W1 W0*.
--   - `covarianceAction`: PDF p.6: channels in the covariance formulas act by conjugation.
--   - `SeedCommutes`: PDF p.6, Eq.(23): the seed commutes with the diagonal representation.
--   - `covariantDensity`: PDF p.6, Eq.(22): the displayed continuous representative of a covariant density.
--   - `twirl`: PDF p.6, Eq.(24): twirl of the original measurable density.
--   - `entangledProjector`: PDF p.6: normalized maximally entangled projector P=|I>><<I|/d.
--   - `lambdaF`: PDF p.6, Eq.(27): explicit fidelity score operator.
--   - `middleProjector`: PDF p.6, Eq.(28): I3 tensor P21 tensor I0, reindexed to ((3,2),(1,0)).
--   - `lambdaG`: PDF p.6, Eq.(28): information score operator, including the coefficient 1-2/d^2.
--   - `gainBellContraction`: PDF p.6, corrected Eq.(27): contract A with <<I| and |I>> on wires (3,0), then tensor identities on 3,0 and divide by d. The printed bare Tr30[A] contradicts Eq.(19) and Eq.(28): for A=lambdaF it would give I/d^3. Independent moderation of this source correction is required.
--   - `NormalizedParameters`: PDF pp.6–7, Eq.(31): nonnegative frontier parameters, including both endpoints.
--   - `optimalVector`: PDF p.6, Eq.(30): unnormalized vector of the optimal physical instrument.
--   - `optimalDensity`: PDF p.6, Eq.(30): the attained rank-one instrument density.
--   - `normalizedInformation`: PDF p.7, Eq.(33): normalized information; Gmin is a reference value.
--   - `disturbance`: PDF p.7, Eq.(33): normalized disturbance; asserted frontier has d>=2.
--   - `attainableDisturbances`: PDF p.7: the full physically attainable set at a prescribed information value. Minimum statements use IsLeast, never a bare real sInf with an empty-set default.
--   - `firstIsometry`: PDF p.8: first isometry in the fixed bases, with output wires (1,1',0').
--   - `bellKraus`: PDF p.8, Eq.(40): sqrt(d) V_(0'->3) <<V|_(2,1'); independent of x,y.
--   - `bellEffect`: PDF p.8: Bell POVM density d |V>><<V| on wires (2,1').
--   - `unknownUse`: PDF p.8: the single unknown use U on the first wire, ancillas unchanged.
--   - `realizedVector`: PDF p.8: contract the two known stages, leaving the unknown slot open.
--   - `realizedDensity`: PDF p.8: Choi density of the explicit two-stage network.
--   - `conditionalMatrix`: PDF p.8, corrected final evolution: the trace is Tr[V dagger U], as follows from the Bell bra and Eq.(40), rather than the printed Tr[V U dagger].
-- source:
--   Information - Disturbance Tradeoff in the Estimation of a Unitary Transformation, arXiv:1006.5665v2, https://arxiv.org/abs/1006.5665v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Defs_ContinuousPOVMDensities

/-!
Information–disturbance tradeoff for one use of an unknown SU(d) channel.
Source: Bisio et al., arXiv:1006.5665v2, PDF pp.2–9.
Four-wire indices are ((3,2),(1,0)); Choi vectors are unnormalized and output first.
Paper-specific concepts have distinct names from unrelated accepted declarations.
Matrix.vec, pureDensity, and Measurements.quadraticFunctional are reused directly.
Compilation is pending the batch handoff.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P21

/-- PDF p.4: one d-dimensional wire in the fixed computational basis. -/
abbrev Wire (d : ℕ) := Fin d

/-- PDF p.4: the four wires, in descending order ((3,2),(1,0)). -/
abbrev Four (d : ℕ) := (Wire d × Wire d) × (Wire d × Wire d)

/-- PDF p.8: wires (1,1',0'), or (2,1',0') after the unknown use. -/
abbrev Three (d : ℕ) := Wire d × (Wire d × Wire d)

/-- PDF p.4: the unknown and the estimate both range over SU(d). -/
abbrev SU (d : ℕ) := Matrix.specialUnitaryGroup (Wire d) ℂ

/-- PDF p.4: Borel outcome convention, without continuity of instrument densities. -/
instance suMeasurable (d : ℕ) : MeasurableSpace (SU d) := borel _

/-- PDF p.4: the outcome sigma algebra is exactly the Borel sigma algebra. -/
instance suBorel (d : ℕ) : BorelSpace (SU d) := ⟨rfl⟩

/-- PDF p.4: matrix of a special unitary in the fixed basis. -/
def unitaryMatrix {d : ℕ} (U : SU d) : Matrix (Wire d) (Wire d) ℂ := U.val

/-- PDF p.4: normalized Haar law, specified by its probability and both translation
invariances. Such a law is unique; no input- or outcome-dependent prior is permitted. -/
structure HaarLaw (d : ℕ) where
  law : Measure (SU d)
  probability : IsProbabilityMeasure law
  left_invariant : ∀ V : SU d, Measure.map (fun U => V * U) law = law
  right_invariant : ∀ V : SU d, Measure.map (fun U => U * V) law = law

/-- PDF pp.4–5: Borel matrices with the scoped finite-dimensional operator norm. -/
local instance matrixMeasurable (I : Type*) [Fintype I] :
    MeasurableSpace (Matrix I I ℂ) := borel _

/-- PDF pp.3–4, Eqs.(5),(14): deterministic two-comb, including both causal traces. -/
def IsDeterministicTwoComb {d : ℕ} (R : Matrix (Four d) (Four d) ℂ) : Prop :=
  R.PosSemidef ∧ ∃ Rone : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ,
    Rone.PosSemidef ∧
    (∀ b c e bnew cnew enew,
      (∑ a : Wire d, R ((a,b),(c,e)) ((a,bnew),(cnew,enew))) =
        (if b = bnew then 1 else 0) * Rone (c,e) (cnew,enew)) ∧
    (∀ e enew, (∑ c : Wire d, Rone (c,e) (c,enew)) =
      if e = enew then 1 else 0)

/-- PDF pp.3,5, link product: insert exactly one U into wires 1 to 2. -/
def linkedChoi {d : ℕ} (R : Matrix (Four d) (Four d) ℂ) (U : SU d) :
    Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ :=
  fun i j => ∑ b : Wire d, ∑ c : Wire d, ∑ bnew : Wire d, ∑ cnew : Wire d,
    unitaryMatrix U b c * R ((i.1,b),(c,i.2)) ((j.1,bnew),(cnew,j.2)) *
      conj (unitaryMatrix U bnew cnew)

/-- PDF p.3, Eq.(9): actual conditional output operation, without normalization. -/
def insertedOutput {d : ℕ} (R : Matrix (Four d) (Four d) ℂ) (U : SU d)
    (rho : Matrix (Wire d) (Wire d) ℂ) : Matrix (Wire d) (Wire d) ℂ :=
  fun a anew => ∑ e : Wire d, ∑ enew : Wire d,
    linkedChoi R U (a,e) (anew,enew) * rho e enew

/-- PDF p.5, Eq.(15): conditional outcome density relative to normalized Haar. -/
def outcomeDensity {d : ℕ} (R : Matrix (Four d) (Four d) ℂ) (U : SU d)
    (rho : Matrix (Wire d) (Wire d) ℂ) : ℝ := (insertedOutput R U rho).trace.re

/-- PDF p.5, Eq.(20): vector |U>>_30 |U*>>_21 in descending wire order. -/
def fidelityVector {d : ℕ} (U : SU d) : Four d → ℂ :=
  fun i => unitaryMatrix U i.1.1 i.2.2 * conj (unitaryMatrix U i.1.2 i.2.1)

/-- PDF p.5, Eq.(20): subnormalized channel entanglement-fidelity kernel. -/
def fidelityKernel {d : ℕ} (R : Matrix (Four d) (Four d) ℂ) (U : SU d) : ℝ :=
  (Measurements.quadraticFunctional (fidelityVector U) R).re / (d : ℝ)^2

/-- PDF p.5, Eqs.(15),(16),(19): information kernel for the input I/d. -/
def gainKernel {d : ℕ} (R : Matrix (Four d) (Four d) ℂ) (U V : SU d) : ℝ :=
  outcomeDensity R U (((d : ℂ)⁻¹) • 1) *
    Complex.normSq ((unitaryMatrix V)ᴴ * unitaryMatrix U).trace / (d : ℝ)^2

/-- PDF p.5, following Eq.(20): pure-state fidelity kernel; its trace weighting is
already included in the subnormalized conditional output. -/
def pureKernel {d : ℕ} (R : Matrix (Four d) (Four d) ℂ) (U : SU d)
    (psi : EuclideanSpace ℂ (Wire d)) : ℝ :=
  (Measurements.quadraticFunctional (act (unitaryMatrix U) psi)
    (insertedOutput R U (pureDensity psi))).re

/-- PDF pp.4–5: measurable PSD density, integrable entries and actual scalar score
kernels, whose Haar integral is a deterministic comb. No pointwise trace bound is imposed.
The pure-state kernel uses the uniform pure-state measure from the accepted library. -/
def IsHaarCombInstrument {d : ℕ} (H : HaarLaw d) (hd : 0 < d)
    (R : SU d → Matrix (Four d) (Four d) ℂ) : Prop :=
  Measurable R ∧ (∀ V, (R V).PosSemidef) ∧ Integrable R H.law ∧
  (∀ i j, Integrable (fun V => R V i j) H.law) ∧
  IsDeterministicTwoComb (∫ V, R V ∂H.law) ∧
  Integrable (fun t : SU d × SU d => fidelityKernel (R t.2) t.1) (H.law.prod H.law) ∧
  Integrable (fun t : SU d × SU d => gainKernel (R t.2) t.1 t.2) (H.law.prod H.law) ∧
  Integrable (fun t : EuclideanSpace ℂ (Wire d) × (SU d × SU d) =>
    pureKernel (R t.2.2) t.2.1 t.1)
    ((QuditFidelity.haarPureStateLaw d hd).prod (H.law.prod H.law))

/-- PDF p.5, Eq.(20): average entanglement fidelity with independent U,V integrations. -/
def channelScore {d : ℕ} (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) : ℝ :=
  ∫ t : SU d × SU d, fidelityKernel (R t.2) t.1 ∂H.law.prod H.law

/-- PDF p.5, Eq.(19): average information gain for rho=I/d. -/
def gain {d : ℕ} (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) : ℝ :=
  ∫ t : SU d × SU d, gainKernel (R t.2) t.1 t.2 ∂H.law.prod H.law

/-- PDF p.5, following Eq.(20): actual triple average of subnormalized state fidelities. -/
def averagePureFidelity {d : ℕ} (H : HaarLaw d) (hd : 0 < d)
    (R : SU d → Matrix (Four d) (Four d) ℂ) : ℝ :=
  ∫ t : EuclideanSpace ℂ (Wire d) × (SU d × SU d), pureKernel (R t.2.2) t.2.1 t.1
    ∂(QuditFidelity.haarPureStateLaw d hd).prod (H.law.prod H.law)

/-- PDF p.6, Eqs.(22)–(24): full left/right representation V3 V2* W1 W0*. -/
def representation {d : ℕ} (V W : SU d) : Matrix (Four d) (Four d) ℂ :=
  ((unitaryMatrix V) ⊗ₖ (unitaryMatrix V).map conj) ⊗ₖ
    ((unitaryMatrix W) ⊗ₖ (unitaryMatrix W).map conj)

/-- PDF p.6: channels in the covariance formulas act by conjugation. -/
def covarianceAction {d : ℕ} (V W : SU d) (X : Matrix (Four d) (Four d) ℂ) :
    Matrix (Four d) (Four d) ℂ := representation V W * X * (representation V W)ᴴ

/-- PDF p.6, Eq.(23): the seed commutes with the diagonal representation. -/
def SeedCommutes {d : ℕ} (X : Matrix (Four d) (Four d) ℂ) : Prop :=
  ∀ V : SU d, X * representation V V = representation V V * X

/-- PDF p.6, Eq.(22): the displayed continuous representative of a covariant density. -/
def covariantDensity {d : ℕ} (X : Matrix (Four d) (Four d) ℂ) (V : SU d) :=
  covarianceAction V 1 X

/-- PDF p.6, Eq.(24): twirl of the original measurable density. -/
def twirl {d : ℕ} (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ)
    (V : SU d) : Matrix (Four d) (Four d) ℂ :=
  ∫ L : SU d, ∫ W : SU d, covarianceAction L W (R (L⁻¹ * V * W)) ∂H.law ∂H.law

/-- PDF p.6: normalized maximally entangled projector P=|I>><<I|/d. -/
def entangledProjector (d : ℕ) : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ :=
  ((d : ℂ)⁻¹) • pureDensity (WithLp.toLp 2
    (Matrix.vec (1 : Matrix (Wire d) (Wire d) ℂ).transpose))

/-- PDF p.6, Eq.(27): explicit fidelity score operator. -/
def lambdaF (d : ℕ) : Matrix (Four d) (Four d) ℂ :=
  (((d : ℂ)^2 * ((d : ℂ)^2 - 1))⁻¹) •
    (1 + ((d : ℂ)^2) • (entangledProjector d ⊗ₖ entangledProjector d) -
      entangledProjector d ⊗ₖ (1 : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ) -
      (1 : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ) ⊗ₖ entangledProjector d)

/-- PDF p.6, Eq.(28): I3 tensor P21 tensor I0, reindexed to ((3,2),(1,0)). -/
def middleProjector (d : ℕ) : Matrix (Four d) (Four d) ℂ :=
  fun i j => (if i.1.1 = j.1.1 then 1 else 0) *
    entangledProjector d (i.1.2,i.2.1) (j.1.2,j.2.1) *
      (if i.2.2 = j.2.2 then 1 else 0)

/-- PDF p.6, Eq.(28): information score operator, including the coefficient 1-2/d^2. -/
def lambdaG (d : ℕ) : Matrix (Four d) (Four d) ℂ :=
  (((d : ℂ)^2 * ((d : ℂ)^2 - 1))⁻¹) •
    (((1 - 2 / (d : ℂ)^2) : ℂ) • 1 + middleProjector d)

/-- PDF p.6, corrected Eq.(27): contract A with <<I| and |I>> on wires (3,0),
then tensor identities on 3,0 and divide by d. The printed bare Tr30[A] contradicts
Eq.(19) and Eq.(28): for A=lambdaF it would give I/d^3. Independent moderation
of this source correction is required. -/
def gainBellContraction {d : ℕ} (A : Matrix (Four d) (Four d) ℂ) :
    Matrix (Four d) (Four d) ℂ :=
  fun i j => (d : ℂ)⁻¹ * (if i.1.1 = j.1.1 then 1 else 0) *
    (∑ a : Wire d, ∑ e : Wire d, A ((a,i.1.2),(i.2.1,a)) ((e,j.1.2),(j.2.1,e))) *
    (if i.2.2 = j.2.2 then 1 else 0)

/-- PDF pp.6–7, Eq.(31): nonnegative frontier parameters, including both endpoints. -/
def NormalizedParameters (d : ℕ) (x y : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧ x^2 + y^2 + 2*x*y/(d : ℝ) = 1

/-- PDF p.6, Eq.(30): unnormalized vector of the optimal physical instrument. -/
def optimalVector {d : ℕ} (x y : ℝ) (V : SU d) : Four d → ℂ :=
  fun i => (x : ℂ) * unitaryMatrix V i.1.1 i.2.2 * conj (unitaryMatrix V i.1.2 i.2.1) +
    (y : ℂ) * (if i.1.1 = i.1.2 then 1 else 0) * (if i.2.1 = i.2.2 then 1 else 0)

/-- PDF p.6, Eq.(30): the attained rank-one instrument density. -/
def optimalDensity {d : ℕ} (x y : ℝ) (V : SU d) : Matrix (Four d) (Four d) ℂ :=
  pureDensity (WithLp.toLp 2 (optimalVector x y V))

/-- PDF p.7, Eq.(33): normalized information; Gmin is a reference value. -/
def normalizedInformation {d : ℕ} (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) : ℝ :=
  (d : ℝ)^2 * gain H R - 1

/-- PDF p.7, Eq.(33): normalized disturbance; asserted frontier has d>=2. -/
def disturbance {d : ℕ} (H : HaarLaw d) (R : SU d → Matrix (Four d) (Four d) ℂ) : ℝ :=
  (1 - channelScore H R) / (1 - 2/(d : ℝ)^2)

/-- PDF p.7: the full physically attainable set at a prescribed information value.
Minimum statements use IsLeast, never a bare real sInf with an empty-set default. -/
def attainableDisturbances {d : ℕ} (H : HaarLaw d) (hd : 0 < d) (i : ℝ) : Set ℝ :=
  {z | ∃ R : SU d → Matrix (Four d) (Four d) ℂ,
    IsHaarCombInstrument H hd R ∧ normalizedInformation H R = i ∧ disturbance H R = z}

/-- PDF p.8: first isometry in the fixed bases, with output wires (1,1',0'). -/
def firstIsometry (d : ℕ) (x y : ℝ) : Matrix (Three d) (Wire d) ℂ :=
  fun i a => ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
    ((y : ℂ) * (if i.1 = a then 1 else 0) * (if i.2.1 = i.2.2 then 1 else 0) +
     (x : ℂ) * (if i.1 = i.2.1 then 1 else 0) * (if i.2.2 = a then 1 else 0))

/-- PDF p.8, Eq.(40): sqrt(d) V_(0'->3) <<V|_(2,1'); independent of x,y. -/
def bellKraus {d : ℕ} (V : SU d) : Matrix (Wire d) (Three d) ℂ :=
  fun a i => (Real.sqrt (d : ℝ) : ℂ) * unitaryMatrix V a i.2.2 *
    conj (unitaryMatrix V i.1 i.2.1)

/-- PDF p.8: Bell POVM density d |V>><<V| on wires (2,1'). -/
def bellEffect {d : ℕ} (V : SU d) : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ :=
  (d : ℂ) • pureDensity (WithLp.toLp 2 (Matrix.vec (unitaryMatrix V).transpose))

/-- PDF p.8: the single unknown use U on the first wire, ancillas unchanged. -/
def unknownUse {d : ℕ} (U : SU d) : Matrix (Three d) (Three d) ℂ :=
  unitaryMatrix U ⊗ₖ (1 : Matrix (Wire d × Wire d) (Wire d × Wire d) ℂ)

/-- PDF p.8: contract the two known stages, leaving the unknown slot open. -/
def realizedVector {d : ℕ} (x y : ℝ) (V : SU d) : Four d → ℂ :=
  fun i => ∑ j : Wire d, ∑ k : Wire d,
    bellKraus V i.1.1 (i.1.2,(j,k)) * firstIsometry d x y (i.2.1,(j,k)) i.2.2

/-- PDF p.8: Choi density of the explicit two-stage network. -/
def realizedDensity {d : ℕ} (x y : ℝ) (V : SU d) := pureDensity (WithLp.toLp 2 (realizedVector x y V))

/-- PDF p.8, corrected final evolution: the trace is Tr[V dagger U], as follows
from the Bell bra and Eq.(40), rather than the printed Tr[V U dagger]. -/
def conditionalMatrix {d : ℕ} (x y : ℝ) (U V : SU d) : Matrix (Wire d) (Wire d) ℂ :=
  (y : ℂ) • unitaryMatrix U +
    ((x : ℂ) * ((unitaryMatrix V)ᴴ * unitaryMatrix U).trace) • unitaryMatrix V

/-- Sanity: output-first vectorization does not conjugate matrix entries (PDF p.2). -/
example {d : ℕ} (A : Matrix (Wire d) (Wire d) ℂ) (a b : Wire d) :
    Matrix.vec A.transpose (a,b) = A a b := rfl

/-- Sanity: the rank-one Choi convention has no division by d (PDF pp.2,6). -/
example {d : ℕ} (x y : ℝ) (V : SU d) (i j : Four d) :
    optimalDensity x y V i j = optimalVector x y V i * conj (optimalVector x y V j) := rfl

/-- Sanity: Bell feed-forward has no tradeoff parameters (PDF p.8). -/
example {d : ℕ} (V : SU d) (a : Wire d) (i : Three d) :
    bellKraus V a i = (Real.sqrt (d : ℝ) : ℂ) * unitaryMatrix V a i.2.2 *
      conj (unitaryMatrix V i.1 i.2.1) := rfl

/-- Sanity: at d=2 both no-information and maximum-information parameter endpoints
satisfy the same normalization (PDF p.7). -/
example : NormalizedParameters 2 0 1 ∧ NormalizedParameters 2 1 0 := by
  norm_num [NormalizedParameters]

/-- Sanity: the auxiliary d=1 first-stage formula is finite and normalized at x=0,y=1
(PDF p.8); the normalized tradeoff theorem itself excludes this dimension. -/
example : firstIsometry 1 0 1 (0,(0,0)) 0 = 1 := by
  norm_num [firstIsometry]

end QAlgorithms.Papers.Independent.Claimed50.P21


