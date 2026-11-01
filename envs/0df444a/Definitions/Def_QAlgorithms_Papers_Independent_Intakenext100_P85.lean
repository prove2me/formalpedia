-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P85
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P85
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:13:29.501136+00:00
-- url     : https://prove2.me/theorems/ffc18c46-ff12-4e4b-b66d-793c51acbddb
-- title:
--   Definitions for Quantum Illumination with Gaussian States
-- statement:
--   The objects the formalized statements of *Quantum Illumination with Gaussian States* (arXiv:0810.0534) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Occ`: Full occupation strings, source pp.2–3; n counts modes, not a cutoff.
--   - `Array`: Coefficient arrays on a complete number basis.
--   - `IlluminationOperator`: Generic bounded operators on that completed space.
--   - `basis`: The complete occupation basis, with conjugate-linear first inner argument.
--   - `HasArray`: All coefficients, not merely diagonal elements, pin an operator.
--   - `realizeOccupationArray`: Unique bounded realization when it exists. Every constructed-state target concludes HasArray and density, ruling out the zero fallback.
--   - `JointDecisionEffect`: A bounded binary effect decides H1. Both E and 1-E are positive, including self-adjointness. Source p.2, optimum joint quantum reception.
--   - `optimumError`: Equal-prior error, independently optimized over every joint binary effect. The extended nonnegative infimum never uses a real empty-infimum default.
--   - `signalS`: Eq.(2): S=2 NS+1.
--   - `correlationQ`: Eq.(2): Cq=2 sqrt(NS(NS+1)).
--   - `correlationC`: Classical positive-P correlation limit, p.2.
--   - `bathB`: Eq.(3): B=2 NB+1.
--   - `returnA`: Eq.(4): received variance A; the received background is NB.
--   - `phaseSensitiveWignerCov`: Standard-form interleaved covariance, with source vacuum variance 1/4.
--   - `spdcCov`: Eq.(2), constructed covariance matrix.
--   - `returnCov`: Eqs.(3)–(4), the two explicit returned covariance matrices.
--   - `SourceGaussian`: Actual Gaussian operator characteristic, in source normalization. The accepted predicate includes normalized positive trace class and symmetry.
--   - `CenteredMoments`: Symmetric, finite-energy second moments of arbitrary states, not just Gaussians. With accepted Weyl coordinates x=2(q,p), the directional second characteristic derivative is -4 xi^T Lambda xi. All trace sums converge. Symmetry is explicit, repairing the known defect of frozen P47 moments.
--   - `spdcCoefficient`: Eq.(1), all SPDC number coefficients, with NS=0 giving |0,0>.
--   - `spdcVector`: The constructed full SPDC vector. Its realization and unit norm are conclusions, rather than Gaussianity or covariance fields.
--   - `spdcArray`: Pure density from the constructed vector (1).
--   - `marginalPhotonNumber`: Marginal mean photon number; every use concludes summability.
--   - `coherentVector`: Full coherent vector, with coefficient and norm conclusions below.
--   - `coherentArray`: Exact coherent projector coefficients, independent of a fallback vector.
--   - `PositiveP`: Genuine positive P probability measure, including singular distributions at the classicality threshold. It is stronger than separability.
--   - `twoOcc`: Relabel the two occupation numbers without changing the Hilbert space.
--   - `pairArray`: Signal/idler pair arrays for invoking accepted complete separability.
--   - `signalChannel`: The actual single signal channel. H0 discards input and inserts theta(NB); H1 uses the thermal beam splitter with bath occupation NB/(1-k). No characteristic-function or output-moment law is assumed here.
--   - `coordinateChannel`: One named signal coordinate is sent through the channel; off-diagonal matrix slices are retained. Idler registers are never sent through this map.
--   - `signalBlock`: Independent channel uses on every signal mode, with no IID assumption on the input. The empty list is the identity; result nodes require M>=1.
--   - `targetBlock`: The signal block is transmitted and the entire idler is perfectly retained.
--   - `onePair`: Explicit relabeling of a two-mode density as a one-signal/one-idler pair.
--   - `fromOnePair`: Inverse relabeling; no physical operation is involved.
--   - `qiReturn`: Actual returned SPDC pair, applying the physical channel to (1).
--   - `coherentReturn`: Exact returned coherent states for any multimode amplitude vector.
--   - `constantAmplitude`: Source coherent energy NS in each transmitted mode.
--   - `coherentExponent`: Eq.(11): exact Chernoff exponent coefficient, not an optimal error definition.
--   - `coherentLower`: Eq.(13) at total transmitted energy E, exact at every finite parameter.
--   - `returnDiscriminant`: Eq.(16): positive square-root discriminant on the physical domain.
--   - `williamsonX`: Eq.(16): x+ and x-, with positive and negative choices respectively.
--   - `williamsonT`: Eq.(15): X+=diag(x+,x+), X-=diag(x-,-x-).
--   - `returnSpectrum`: Eq.(17), k_source=1,2 corresponding to Fin 2 values 0,1.
--   - `ClassicalDensity`: Eq.(19): genuine Lebesgue P density with ensemble average signal energy. There is no IID, peak-energy, per-realization, or idler-energy constraint.
--   - `classicalArray`: The actual correlated coherent-state mixture in (19). Coefficient integrability and density are conclusions of its target, not hypotheses.
--   - `genieIntegrand`: Genie error when the complete signal amplitude is revealed; this is independent all-effect optimal reception conditioned on that classical datum.
--   - `genieError`: Ensemble mean of the genie experiment, p.4.
--   - `BlockRealized`: Guard all single-mode bounded realizations used by the physical block, including off-diagonal slices and intermediate arrays. These are conclusions.
--   - `TargetRealized`: Every retained-idler matrix block has its actual channel realization.
-- source:
--   Quantum Illumination with Gaussian States, arXiv:0810.0534v1, https://arxiv.org/abs/0810.0534v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P41

/-!
Statements from Tan et al., arXiv:0810.0534v1, PDF pp.1–4.
All oscillator number spaces are completed, without photon cutoff. Source
quadratures are half the accepted P30 quadratures: means and covariances are
converted by u=2d and V=4 Lambda. No defective P47 moment predicate is used.
All local definitions have bodies. Five source-ambiguity nodes are in HARD.md.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P85

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)
open QAlgorithms.Papers.Independent.Renew46.P41 (coherentProductCoefficient)

namespace G
export QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator Quadrature PhaseVector numberKet numberBasis
   IsModeDensity GaussianMoments FockWeylSystem TraceSummable modeWeylTrace
   canonicalOmega Symplectic repeatedDiagonal chernoffTrace quantumChernoff)
end G

namespace B
export QAlgorithms.Papers.Independent.Dependency50.P39
  (coherentCoefficient fockKet HasFockMatrix operatorOfMatrix thermalMatrix)
export QAlgorithms.Papers.Independent.Claimed50.P39
  (thermalOutputMatrix thermalProbability beamAmplitude)
end B

namespace T
export QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsSeparable IsBarycenter rankOne tensorApply)
end T

/-- Full occupation strings, source pp.2–3; n counts modes, not a cutoff. -/
abbrev Occ (n : ℕ) := Fin n → ℕ

/-- Coefficient arrays on a complete number basis. -/
abbrev Array (I : Type) := Matrix I I ℂ

/-- Generic bounded operators on that completed space. -/
abbrev IlluminationOperator (I : Type) := QAlgorithms.RealRegisters.Hilbert I →L[ℂ] QAlgorithms.RealRegisters.Hilbert I

/-- The complete occupation basis, with conjugate-linear first inner argument. -/
def basis (I : Type) : HilbertBasis I ℂ (QAlgorithms.RealRegisters.Hilbert I) :=
  ⟨LinearIsometryEquiv.refl ℂ (QAlgorithms.RealRegisters.Hilbert I)⟩

/-- All coefficients, not merely diagonal elements, pin an operator. -/
def HasArray {I : Type} (A : IlluminationOperator I) (X : Array I) : Prop :=
  ∀ i j, A (basis I j) i = X i j

/-- Unique bounded realization when it exists. Every constructed-state target
concludes HasArray and density, ruling out the zero fallback. -/
def realizeOccupationArray {I : Type} (X : Array I) : IlluminationOperator I :=
  if h : ∃ A : IlluminationOperator I, HasArray A X then Classical.choose h else 0

/-- A bounded binary effect decides H1. Both E and 1-E are positive,
including self-adjointness. Source p.2, optimum joint quantum reception. -/
def JointDecisionEffect {I : Type} (E : IlluminationOperator I) : Prop :=
  QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive E ∧
    QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive (1 - E)

/-- Equal-prior error, independently optimized over every joint binary effect.
The extended nonnegative infimum never uses a real empty-infimum default. -/
def optimumError {I : Type} (X0 X1 : Array I) : ℝ≥0∞ :=
  ⨅ E : {E : IlluminationOperator I // JointDecisionEffect E}, ENNReal.ofReal
    (((QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace (basis I) (E.val.comp (realizeOccupationArray X0))).re +
      (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace (basis I) ((1 - E.val).comp (realizeOccupationArray X1))).re) / 2)

/-- Eq.(2): S=2 NS+1. -/
def signalS (NS : ℝ) : ℝ := 2 * NS + 1

/-- Eq.(2): Cq=2 sqrt(NS(NS+1)). -/
def correlationQ (NS : ℝ) : ℝ := 2 * Real.sqrt (NS * (NS + 1))

/-- Classical positive-P correlation limit, p.2. -/
def correlationC (NS : ℝ) : ℝ := 2 * NS

/-- Eq.(3): B=2 NB+1. -/
def bathB (NB : ℝ) : ℝ := 2 * NB + 1

/-- Eq.(4): received variance A; the received background is NB. -/
def returnA (k NS NB : ℝ) : ℝ := 2 * k * NS + bathB NB

/-- Standard-form interleaved covariance, with source vacuum variance 1/4. -/
def phaseSensitiveWignerCov (a b c : ℝ) : Cov 2 := fun i j =>
  (if i = j then (if i.1 = 0 then a else b)
   else if i.1 ≠ j.1 ∧ i.2 = j.2 then (if i.2 = 0 then c else -c)
   else 0) / 4

/-- Eq.(2), constructed covariance matrix. -/
def spdcCov (NS : ℝ) : Cov 2 :=
  phaseSensitiveWignerCov (signalS NS) (signalS NS) (correlationQ NS)

/-- Eqs.(3)–(4), the two explicit returned covariance matrices. -/
def returnCov (present : Bool) (k NS NB : ℝ) : Cov 2 :=
  if present then phaseSensitiveWignerCov (returnA k NS NB) (signalS NS)
    (Real.sqrt k * correlationQ NS)
  else phaseSensitiveWignerCov (bathB NB) (signalS NS) 0

/-- Actual Gaussian operator characteristic, in source normalization.
The accepted predicate includes normalized positive trace class and symmetry. -/
def SourceGaussian {n : ℕ} (W : G.FockWeylSystem n) (X : Array (Occ n))
    (d : G.PhaseVector n) (V : Cov n) : Prop :=
  HasArray (realizeOccupationArray X) X ∧ G.GaussianMoments W (realizeOccupationArray X) (2 • d) (4 • V)

/-- Symmetric, finite-energy second moments of arbitrary states, not just
Gaussians. With accepted Weyl coordinates x=2(q,p), the directional second
characteristic derivative is -4 xi^T Lambda xi. All trace sums converge.
Symmetry is explicit, repairing the known defect of frozen P47 moments. -/
def CenteredMoments {n : ℕ} (W : G.FockWeylSystem n) (X : Array (Occ n))
    (V : Cov n) : Prop :=
  HasArray (realizeOccupationArray X) X ∧ G.IsModeDensity (realizeOccupationArray X) ∧ V.transpose = V ∧
  Summable (fun j : Occ n => (∑ k, (j k : ℝ)) * (X j j).re) ∧
  (∀ xi, G.TraceSummable ((realizeOccupationArray X).comp (W.operator xi))) ∧
  ∀ xi : G.PhaseVector n,
    HasDerivAt (fun t : ℝ => G.modeWeylTrace W (realizeOccupationArray X) (t • xi)) 0 0 ∧
    HasDerivAt (deriv (fun t : ℝ => G.modeWeylTrace W (realizeOccupationArray X) (t • xi)))
      (((-4 * ∑ i, ∑ j, xi i * V i j * xi j : ℝ) : ℂ)) 0

/-- Eq.(1), all SPDC number coefficients, with NS=0 giving |0,0>. -/
def spdcCoefficient (NS : ℝ) (j : Occ 2) : ℂ :=
  if j 0 = j 1 then (Real.sqrt (NS ^ (j 0) / (NS + 1) ^ (j 0 + 1)) : ℂ)
  else 0

/-- The constructed full SPDC vector. Its realization and unit norm are
conclusions, rather than Gaussianity or covariance fields. -/
def spdcVector (NS : ℝ) : G.ModeHilbert 2 :=
  if h : ∃ v : G.ModeHilbert 2, ∀ j, v j = spdcCoefficient NS j then
    Classical.choose h else 0

/-- Pure density from the constructed vector (1). -/
def spdcArray (NS : ℝ) : Array (Occ 2) := T.rankOne (spdcVector NS)

/-- Marginal mean photon number; every use concludes summability. -/
def marginalPhotonNumber {n : ℕ} (X : Array (Occ n)) (k : Fin n) : ℝ :=
  ∑' j : Occ n, (j k : ℝ) * (X j j).re

/-- Full coherent vector, with coefficient and norm conclusions below. -/
def coherentVector {n : ℕ} (alpha : Fin n → ℂ) : G.ModeHilbert n :=
  if h : ∃ v : G.ModeHilbert n, ∀ j, v j = coherentProductCoefficient alpha j then
    Classical.choose h else 0

/-- Exact coherent projector coefficients, independent of a fallback vector. -/
def coherentArray {n : ℕ} (alpha : Fin n → ℂ) : Array (Occ n) :=
  fun i j => coherentProductCoefficient alpha i * star (coherentProductCoefficient alpha j)

/-- Genuine positive P probability measure, including singular distributions
at the classicality threshold. It is stronger than separability. -/
def PositiveP {n : ℕ} (X : Array (Occ n)) : Prop :=
  T.IsDensity X ∧ ∃ mu : Measure (Fin n → ℂ), IsProbabilityMeasure mu ∧
    T.IsBarycenter mu (fun alpha => coherentArray alpha) X

/-- Relabel the two occupation numbers without changing the Hilbert space. -/
def twoOcc (a b : ℕ) : Occ 2 := fun k => if k = 0 then a else b

/-- Signal/idler pair arrays for invoking accepted complete separability. -/
def pairArray (X : Array (Occ 2)) : Array (ℕ × ℕ) :=
  fun p q => X (twoOcc p.1 p.2) (twoOcc q.1 q.2)

/-- The actual single signal channel. H0 discards input and inserts theta(NB);
H1 uses the thermal beam splitter with bath occupation NB/(1-k).
No characteristic-function or output-moment law is assumed here. -/
def signalChannel (present : Bool) (k NB : ℝ) (X : Array ℕ) : Array ℕ :=
  if present then B.thermalOutputMatrix k (NB / (1 - k)) (B.operatorOfMatrix X)
  else fun i j => B.thermalMatrix (bathB NB) i j * (∑' m : ℕ, X m m)

/-- One named signal coordinate is sent through the channel; off-diagonal
matrix slices are retained. Idler registers are never sent through this map. -/
def coordinateChannel {M : ℕ} (present : Bool) (k NB : ℝ) (r : Fin M)
    (X : Array (Occ M)) : Array (Occ M) := fun i j =>
  signalChannel present k NB
    (fun a b => X (Function.update i r a) (Function.update j r b)) (i r) (j r)

/-- Independent channel uses on every signal mode, with no IID assumption
on the input. The empty list is the identity; result nodes require M>=1. -/
def signalBlock (M : ℕ) (present : Bool) (k NB : ℝ)
    (X : Array (Occ M)) : Array (Occ M) :=
  (List.ofFn (fun r : Fin M => r)).foldl
    (fun Y r => coordinateChannel present k NB r Y) X

/-- The signal block is transmitted and the entire idler is perfectly retained. -/
def targetBlock (M : ℕ) (present : Bool) (k NB : ℝ)
    (X : Array (Occ M × Occ M)) : Array (Occ M × Occ M) :=
  T.tensorApply (signalBlock M present k NB) X

/-- Explicit relabeling of a two-mode density as a one-signal/one-idler pair. -/
def onePair (X : Array (Occ 2)) : Array (Occ 1 × Occ 1) :=
  fun p q => X (twoOcc (p.1 0) (p.2 0)) (twoOcc (q.1 0) (q.2 0))

/-- Inverse relabeling; no physical operation is involved. -/
def fromOnePair (X : Array (Occ 1 × Occ 1)) : Array (Occ 2) :=
  fun p q => X ((fun _ => p 0), (fun _ => p 1))
    ((fun _ => q 0), (fun _ => q 1))

/-- Actual returned SPDC pair, applying the physical channel to (1). -/
def qiReturn (present : Bool) (k NS NB : ℝ) : Array (Occ 2) :=
  fromOnePair (targetBlock 1 present k NB (onePair (spdcArray NS)))

/-- Exact returned coherent states for any multimode amplitude vector. -/
def coherentReturn {M : ℕ} (present : Bool) (k NB : ℝ)
    (alpha : Fin M → ℂ) : Array (Occ M) :=
  signalBlock M present k NB (coherentArray alpha)

/-- Source coherent energy NS in each transmitted mode. -/
def constantAmplitude (M : ℕ) (NS : ℝ) : Fin M → ℂ :=
  fun _ => (Real.sqrt NS : ℂ)

/-- Eq.(11): exact Chernoff exponent coefficient, not an optimal error definition. -/
def coherentExponent (k NS NB : ℝ) : ℝ :=
  k * NS * (Real.sqrt (NB + 1) - Real.sqrt NB) ^ 2

/-- Eq.(13) at total transmitted energy E, exact at every finite parameter. -/
def coherentLower (k E NB : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - Real.exp (-2 * coherentExponent k E NB))) / 2

/-- Eq.(16): positive square-root discriminant on the physical domain. -/
def returnDiscriminant (k NS NB : ℝ) : ℝ :=
  Real.sqrt ((returnA k NS NB + signalS NS) ^ 2 - 4 * k * correlationQ NS ^ 2)

/-- Eq.(16): x+ and x-, with positive and negative choices respectively. -/
def williamsonX (plus : Bool) (k NS NB : ℝ) : ℝ :=
  Real.sqrt ((returnA k NS NB + signalS NS +
    (if plus then returnDiscriminant k NS NB else -returnDiscriminant k NS NB)) / (2 * returnDiscriminant k NS NB))

/-- Eq.(15): X+=diag(x+,x+), X-=diag(x-,-x-). -/
def williamsonT (k NS NB : ℝ) : Cov 2 := fun i j =>
  if i.2 ≠ j.2 then 0 else if i.1 = j.1 then williamsonX true k NS NB
  else if i.2 = 0 then williamsonX false k NS NB else -williamsonX false k NS NB

/-- Eq.(17), k_source=1,2 corresponding to Fin 2 values 0,1. -/
def returnSpectrum (present : Bool) (k NS NB : ℝ) : Fin 2 → ℝ := fun r =>
  if present then (((-1 : ℝ) ^ (r.val + 1)) * (signalS NS - returnA k NS NB) +
    returnDiscriminant k NS NB) / 8
  else if r = 0 then bathB NB / 4 else signalS NS / 4

/-- Eq.(19): genuine Lebesgue P density with ensemble average signal energy.
There is no IID, peak-energy, per-realization, or idler-energy constraint. -/
def ClassicalDensity (M : ℕ) (NS : ℝ) (P : ((Fin M → ℂ) × (Fin M → ℂ)) → ℝ) : Prop :=
  Measurable P ∧ (∀ a, 0 ≤ P a) ∧ Integrable P ∧ (∫ a, P a) = 1 ∧
  Integrable (fun a => P a * ∑ r, Complex.normSq (a.1 r)) ∧
    (∫ a, P a * ∑ r, Complex.normSq (a.1 r)) = (M : ℝ) * NS

/-- The actual correlated coherent-state mixture in (19). Coefficient
integrability and density are conclusions of its target, not hypotheses. -/
def classicalArray (M : ℕ) (P : ((Fin M → ℂ) × (Fin M → ℂ)) → ℝ) :
    Array (Occ M × Occ M) := fun i j => ∫ a,
  (P a : ℂ) * coherentArray a.1 i.1 j.1 * coherentArray a.2 i.2 j.2

/-- Genie error when the complete signal amplitude is revealed; this is
independent all-effect optimal reception conditioned on that classical datum. -/
def genieIntegrand (M : ℕ) (k NB : ℝ)
    (P : ((Fin M → ℂ) × (Fin M → ℂ)) → ℝ)
    (a : (Fin M → ℂ) × (Fin M → ℂ)) : ℝ :=
  P a * (optimumError (coherentReturn false k NB a.1)
    (coherentReturn true k NB a.1)).toReal

/-- Ensemble mean of the genie experiment, p.4. -/
def genieError (M : ℕ) (k NB : ℝ)
    (P : ((Fin M → ℂ) × (Fin M → ℂ)) → ℝ) : ℝ :=
  ∫ a, genieIntegrand M k NB P a

/-! Sanity examples pinning normalization, signs, endpoints and register maps. -/

example : signalS 0 = 1 ∧ correlationQ 0 = 0 ∧ correlationC 0 = 0 := by
  norm_num [signalS, correlationQ, correlationC]

example (NS : ℝ) : spdcCoefficient NS (twoOcc 0 1) = 0 := by
  simp [spdcCoefficient, twoOcc]

example (a b : ℕ) : twoOcc a b 0 = a ∧ twoOcc a b 1 = b := by
  simp [twoOcc]

example (NS : ℝ) : spdcCov NS (0, 0) (1, 0) = correlationQ NS / 4 := by
  simp [spdcCov, phaseSensitiveWignerCov]

example (NS : ℝ) : spdcCov NS (0, 1) (1, 1) = -correlationQ NS / 4 := by
  simp [spdcCov, phaseSensitiveWignerCov]

example {n : ℕ} (alpha : Fin n → ℂ) (i j : Occ n) :
    coherentArray alpha i j = coherentProductCoefficient alpha i * star (coherentProductCoefficient alpha j) := rfl

example (k NB : ℝ) (X : Array (Occ 0)) : signalBlock 0 true k NB X = X := by
  simp [signalBlock]

example (k NB : ℝ) : coherentExponent k 0 NB = 0 := by
  simp [coherentExponent]

example (k NB : ℝ) : coherentLower k 0 NB = 1 / 2 := by
  norm_num [coherentLower, coherentExponent]

example (k NS NB : ℝ) : returnSpectrum false k NS NB 0 = bathB NB / 4 := by
  simp [returnSpectrum]

example (k NS NB : ℝ) : williamsonT k NS NB (0, 1) (1, 1) =
    -williamsonX false k NS NB := by simp [williamsonT]

/-- Guard all single-mode bounded realizations used by the physical block,
including off-diagonal slices and intermediate arrays. These are conclusions. -/
def BlockRealized (M : ℕ) (present : Bool) (k NB : ℝ) (X : Array (Occ M)) : Prop :=
  ∀ t : Fin (M + 1),
    let Y := ((List.ofFn (fun r : Fin M => r)).take t.val).foldl
      (fun Z r => coordinateChannel present k NB r Z) X
    ∀ (r : Fin M) (i j : Occ M),
      let slice := fun a b => Y (Function.update i r a) (Function.update j r b)
      B.HasFockMatrix (B.operatorOfMatrix slice) slice

/-- Every retained-idler matrix block has its actual channel realization. -/
def TargetRealized (M : ℕ) (present : Bool) (k NB : ℝ)
    (X : Array (Occ M × Occ M)) : Prop :=
  ∀ a b : Occ M, BlockRealized M present k NB (fun i j => X (i, a) (j, b))

end QAlgorithms.Papers.Independent.Intakenext100.P85


