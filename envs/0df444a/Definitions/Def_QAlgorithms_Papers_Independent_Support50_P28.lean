-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P28
-- name    : QAlgorithms_Papers_Independent_Support50_P28
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:11:21.268746+00:00
-- url     : https://prove2.me/theorems/753bc132-d4d2-4abf-bc70-c3139583e289
-- title:
--   Definitions for Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs
-- statement:
--   The objects the formalized statements of *Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs* (arXiv:quant-ph/0406065) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `OscillatorPhase`: PDF p.2: the source interleaved coordinate order.
--   - `OscillatorCovariance`: PDF p.2: real covariance arrays, not density matrices.
--   - `OscillatorCoeff`: PDF pp.2--3: arrays of actual oscillator-operator oscillatorCoefficients.
--   - `interleavedSigma`: PDF p.2: canonical interleavedSigma with sigma_xp=+1, sigma_px=-1.
--   - `groupedIndex`: PDF p.2: permutation to the accepted grouped Weyl coordinates; no rescaling.
--   - `groupedVector`: PDF p.2: source phase vector in the accepted grouped coordinates.
--   - `groupedCovariance`: PDF p.2: covariance permutation used only for the accepted Weyl formula.
--   - `oscillatorCharacteristic`: PDF p.2, (4): oscillatorCharacteristic of the actual density, with the fixed Fock Weyl kernel.
--   - `WeylTraceSummable`: PDF p.2, (4): convergence of both sums in the trace/Weyl pairing. Each row is an l2 pairing; the outer series is a trace-class/bounded trace.
--   - `PhysicalOscillatorCovariance`: PDF p.2, corrected (6)--(8): physical symmetric doubled covariance.
--   - `HasCenteredGaussianCovariance`: PDF pp.2--3: centered Gaussian ACTUAL density with its covariance. Normalization and nuclear trace class are carried by State. The corrected oscillatorCharacteristic exponent is -xi^T interleavedSigma^T G interleavedSigma xi/4, not printed (6).
--   - `IsCenteredGaussianDensity`: PDF p.2: all centered Gaussian densities, without an energy bound.
--   - `IsPureOscillatorDensity`: PDF pp.2,4: purity is a rank-one density of a unit vector; no infinite squeezing.
--   - `OscillatorOperator`: PDF p.3: operators on the completed oscillator space, never a photon truncation.
--   - `oscillatorNumberBasis`: PDF p.3: complete number basis of l2.
--   - `oscillatorCoefficients`: PDF p.3: row=bra, column=ket, with conjugate-linearity on the bra.
--   - `realizeOscillatorCoeff`: PDF p.3: unique bounded realization of an operator array when it exists. All arrays used as states are nuclear (State or CPTP output), hence have a unique realization on the completed number basis. The off-domain zero is not a state.
--   - `positivePower`: PDF p.3, (24): genuine positive spectral functional calculus, independent of G.
--   - `tracePower`: PDF pp.3--4, (24),(27): positive spectral trace, retaining infinity rather than a default-zero nonsummable real trace. On a density and p>1 it is finite.
--   - `pNorm`: PDF p.3, (24): Schatten p-norm of an actual density, extended off its domain.
--   - `gaussianCovarianceMap`: PDF p.3, (18): fixed covariance action; the transpose is on the left.
--   - `GaussianCPCondition`: PDF p.3, (16): full Hermitian CP condition, including singular noise.
--   - `gaussianWeylArgument`: PDF p.3: the Weyl-coordinate pullback compatible with (18).
--   - `noiseMultiplier`: PDF p.3: source quadratic noise in the same Weyl coordinates, with /4.
--   - `CenteredOscillatorChannel`: PDF p.3, (15)--(19), interpreted consistently with (18): an actual CPTP map on ALL trace class. Its defining Weyl law holds for every density, not just Gaussian inputs. No output-purity or multiplicativity assertion is a field.
--   - `maximalOutputPurity`: PDF p.4, (31): supremum on actual centered Gaussian input densities. ENNReal suprema avoid empty/unbounded real defaults; the physical set is nonempty and <=1.
--   - `pureMaximalOutputPurity`: PDF p.4, (34): the same supremum restricted to pure Gaussian densities.
--   - `replaceOccupation`: PDF pp.3--4: replace one whole channel's occupation string, keeping all other modes.
--   - `applyOscillatorBlock`: PDF pp.3--4, (36): apply a local map to every off-diagonal block. The other factors form an arbitrary completed oscillator ancilla.
--   - `tensorOscillatorChannel`: PDF pp.3--4, (36): actual finite tensor product of the full channel maps. The fold applies each factor once; it is not a rule only on product inputs.
--   - `GaussianPurityMultiplicative`: PDF p.4, (37): global Gaussian inputs may be entangled across channel blocks.
--   - `scalarX`: PDF p.5, (40): canonical X computed from its factor, including det X=0.
--   - `scalarY`: PDF p.5, (40): canonical Y computed from its factor, including det Y=0.
--   - `EqualSigns`: PDF p.5: equal determinant signs, including the common zero sign.
--   - `PreservesInterleavedSigma`: PDF p.2, (9): source convention S^T interleavedSigma S=interleavedSigma.
--   - `WilliamsonSpectrum`: PDF p.2, (12): Williamson spectrum with multiplicity, not singular values of the generally nonnormal i interleavedSigma G. Ordering is immaterial to products.
--   - `fp`: PDF p.4, (28): reuse the exact accepted f_p.
--   - `spectralFp`: PDF p.4, (29): F_p from an explicitly identified symplectic spectrum.
--   - `kyFan`: PDF p.4, (30): intrinsic Ky Fan sum over all r-dimensional orthonormal frames. For nonempty mode sets this equals the sum of the r largest density eigenvalues with zero padding. ENNReal prevents an unbounded-real default.
--   - `OscillatorMajorizes`: PDF p.4, (30): spectral majorization of actual positive trace-one densities.
--   - `productInput`: PDF pp.3--5: oscillatorCoefficients of an actual tensor product of factor states.
--   - `sourceBeta`: PDF p.8, (A1): the one-mode sourceBeta matrix.
--   - `sourceDelta`: PDF p.8, (A1): the one-mode sourceDelta matrix.
--   - `oneModeGenerator`: PDF p.8, (A2): sigma2, sourceBeta and sourceDelta. Ordering does not affect a basis.
--   - `GeneratorIndex`: PDF p.8, (A2)--(A5): three single-mode and four unordered-pair generators.
--   - `sourceSymplecticGenerator`: PDF p.8, (A2)--(A4): the actual embedded one/two-mode matrices. Pair labels 0,1 are the two skew generators in (A3); 2,3 are the symmetric ones in (A4).
--   - `InSymplecticAlgebra`: PDF p.8: infinitesimal symplecticity, not a subgroup of symmetric matrices.
--   - `CompactGeneratorIndex`: PDF p.8: skew infinitesimal generators of the compact passive subgroup.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, https://arxiv.org/abs/quant-ph/0406065v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

/-!
Serafini--Eisert--Wolf, arXiv:quant-ph/0406065v1.
Full occupation-number Hilbert spaces, no cutoff or energy constraint.
The paper's proof convention is vacuum-I doubled covariance and hbar=1.
Printed (6),(7),(15),(38),(69),(71),(B6) have the discrepancies recorded in
MODERATION_NOTES.md. No frozen definition is changed. The defective
P47.HasBipartiteMoments predicate is never used. Spectral powers are powers of
actual bounded density operators; the Gaussian spectral formula is a theorem.
Compilation and independent moderation are pending the separate batch handoff.
-/

noncomputable section

open scoped BigOperators ENNReal ComplexOrder Matrix

namespace QAlgorithms.Papers.Independent.Support50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel rankOne)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation gaussianStateCharacteristic singleCharacteristic weylKernel)
open QAlgorithms.Papers.Independent.Claimed50.P30 (phiMinus)

/-- PDF p.2: the source interleaved coordinate order. -/
abbrev OscillatorPhase (I : Type) := I × Fin 2

/-- PDF p.2: real covariance arrays, not density matrices. -/
abbrev OscillatorCovariance (I : Type) := Matrix (OscillatorPhase I) (OscillatorPhase I) ℝ

/-- PDF pp.2--3: arrays of actual oscillator-operator oscillatorCoefficients. -/
abbrev OscillatorCoeff (I : Type) := Matrix (Occupation I) (Occupation I) ℂ

/-- PDF p.2: canonical interleavedSigma with sigma_xp=+1, sigma_px=-1. -/
def interleavedSigma (I : Type) : OscillatorCovariance I :=
  fun i j => if i.1 = j.1 then
    if i.2 = j.2 then 0 else if i.2 = 0 then 1 else -1
  else 0

/-- PDF p.2: permutation to the accepted grouped Weyl coordinates; no rescaling. -/
def groupedIndex {I : Type} : I ⊕ I → OscillatorPhase I
  | Sum.inl i => (i, 0)
  | Sum.inr i => (i, 1)

/-- PDF p.2: source phase vector in the accepted grouped coordinates. -/
def groupedVector {I : Type} (xi : OscillatorPhase I → ℝ) : I ⊕ I → ℝ := xi ∘ groupedIndex

/-- PDF p.2: covariance permutation used only for the accepted Weyl formula. -/
def groupedCovariance {I : Type} (G : OscillatorCovariance I) : Matrix (I ⊕ I) (I ⊕ I) ℝ :=
  G.submatrix groupedIndex groupedIndex

/-- PDF p.2, (4): oscillatorCharacteristic of the actual density, with the fixed Fock Weyl kernel. -/
def oscillatorCharacteristic {I : Type} [Fintype I] (A : OscillatorCoeff I) (xi : OscillatorPhase I → ℝ) : ℂ :=
  singleCharacteristic A (groupedVector xi)

/-- PDF p.2, (4): convergence of both sums in the trace/Weyl pairing.
Each row is an l2 pairing; the outer series is a trace-class/bounded trace. -/
def WeylTraceSummable {I : Type} [Fintype I] (A : OscillatorCoeff I) (xi : OscillatorPhase I → ℝ) : Prop :=
  (∀ u, Summable (fun v => A u v * weylKernel (groupedVector xi) v u)) ∧
    Summable (fun u => ∑' v, A u v * weylKernel (groupedVector xi) v u)

/-- PDF p.2, corrected (6)--(8): physical symmetric doubled covariance. -/
def PhysicalOscillatorCovariance {I : Type} [Fintype I] (G : OscillatorCovariance I) : Prop :=
  G.transpose = G ∧
    (G.map (fun x : ℝ => (x : ℂ)) +
      Complex.I • (interleavedSigma I).map (fun x : ℝ => (x : ℂ))).PosSemidef

/-- PDF pp.2--3: centered Gaussian ACTUAL density with its covariance.
Normalization and nuclear trace class are carried by State. The corrected
oscillatorCharacteristic exponent is -xi^T interleavedSigma^T G interleavedSigma xi/4, not printed (6). -/
def HasCenteredGaussianCovariance {I : Type} [Fintype I]
    (rho : State (Occupation I)) (G : OscillatorCovariance I) : Prop :=
  PhysicalOscillatorCovariance G ∧ ∀ xi,
    WeylTraceSummable rho.coefficients xi ∧
    oscillatorCharacteristic rho.coefficients xi =
      gaussianStateCharacteristic 0 (groupedCovariance G) (groupedVector xi)

/-- PDF p.2: all centered Gaussian densities, without an energy bound. -/
def IsCenteredGaussianDensity {I : Type} [Fintype I] (rho : State (Occupation I)) : Prop :=
  ∃ G, HasCenteredGaussianCovariance rho G

/-- PDF pp.2,4: purity is a rank-one density of a unit vector; no infinite squeezing. -/
def IsPureOscillatorDensity {I : Type} (rho : State (Occupation I)) : Prop :=
  ∃ u : Hilbert (Occupation I), ‖u‖ = 1 ∧ rho.coefficients = rankOne u

/-- PDF p.3: operators on the completed oscillator space, never a photon truncation. -/
abbrev OscillatorOperator (I : Type) := Hilbert (Occupation I) →L[ℂ] Hilbert (Occupation I)

/-- PDF p.3: complete number basis of l2. -/
def oscillatorNumberBasis (I : Type) : HilbertBasis (Occupation I) ℂ (Hilbert (Occupation I)) :=
  ⟨LinearIsometryEquiv.refl ℂ (Hilbert (Occupation I))⟩

/-- PDF p.3: row=bra, column=ket, with conjugate-linearity on the bra. -/
def oscillatorCoefficients {I : Type} (T : OscillatorOperator I) : OscillatorCoeff I :=
  fun u v => inner ℂ (oscillatorNumberBasis I u) (T (oscillatorNumberBasis I v))

/-- PDF p.3: unique bounded realization of an operator array when it exists.
All arrays used as states are nuclear (State or CPTP output), hence have a unique
realization on the completed number basis. The off-domain zero is not a state. -/
def realizeOscillatorCoeff {I : Type} (A : OscillatorCoeff I) : OscillatorOperator I :=
  if h : ∃ T : OscillatorOperator I, oscillatorCoefficients T = A then Classical.choose h else 0

/-- PDF p.3, (24): genuine positive spectral functional calculus, independent of G. -/
def positivePower {I : Type} (A : OscillatorCoeff I) (p : ℝ) : OscillatorOperator I := by
  letI : ContinuousFunctionalCalculus ℂ (OscillatorOperator I) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus (A := OscillatorOperator I)
  letI : ContinuousFunctionalCalculus ℝ (OscillatorOperator I) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus (A := OscillatorOperator I)
  exact CFC.rpow (realizeOscillatorCoeff A) p

/-- PDF pp.3--4, (24),(27): positive spectral trace, retaining infinity rather
than a default-zero nonsummable real trace. On a density and p>1 it is finite. -/
def tracePower {I : Type} (p : ℝ) (A : OscillatorCoeff I) : ℝ≥0∞ :=
  ∑' u, ENNReal.ofReal
    (inner ℂ (oscillatorNumberBasis I u) (positivePower A p (oscillatorNumberBasis I u))).re

/-- PDF p.3, (24): Schatten p-norm of an actual density, extended off its domain. -/
def pNorm {I : Type} (p : ℝ) (A : OscillatorCoeff I) : ℝ≥0∞ :=
  (tracePower p A).rpow (1 / p)

/-- PDF p.3, (18): fixed covariance action; the transpose is on the left. -/
def gaussianCovarianceMap {I : Type} [Fintype I] (X Y G : OscillatorCovariance I) : OscillatorCovariance I :=
  X.transpose * G * X + Y

/-- PDF p.3, (16): full Hermitian CP condition, including singular noise. -/
def GaussianCPCondition {I : Type} [Fintype I] (X Y : OscillatorCovariance I) : Prop :=
  Y.transpose = Y ∧
    (Y.map (fun x : ℝ => (x : ℂ)) + Complex.I •
      (interleavedSigma I - X.transpose * interleavedSigma I * X).map (fun x : ℝ => (x : ℂ))).PosSemidef

/-- PDF p.3: the Weyl-coordinate pullback compatible with (18). -/
def gaussianWeylArgument {I : Type} [Fintype I] (X : OscillatorCovariance I) (xi : OscillatorPhase I → ℝ) : OscillatorPhase I → ℝ :=
  ((interleavedSigma I).transpose * X * interleavedSigma I).mulVec xi

/-- PDF p.3: source quadratic noise in the same Weyl coordinates, with /4. -/
def noiseMultiplier {I : Type} [Fintype I] (Y : OscillatorCovariance I) (xi : OscillatorPhase I → ℝ) : ℂ :=
  gaussianStateCharacteristic 0 (groupedCovariance Y) (groupedVector xi)

/-- PDF p.3, (15)--(19), interpreted consistently with (18): an actual CPTP
map on ALL trace class. Its defining Weyl law holds for every density, not just
Gaussian inputs. No output-purity or multiplicativity assertion is a field. -/
structure CenteredOscillatorChannel (I : Type) [Fintype I] where
  X : OscillatorCovariance I
  Y : OscillatorCovariance I
  admissible : GaussianCPCondition X Y
  map : OscillatorCoeff I → OscillatorCoeff I
  cptp : IsTraceClassChannel map
  output : State (Occupation I) → State (Occupation I)
  output_coefficients : ∀ rho, (output rho).coefficients = map rho.coefficients
  characteristic_law : ∀ rho xi,
    WeylTraceSummable (output rho).coefficients xi ∧
    oscillatorCharacteristic (output rho).coefficients xi =
      oscillatorCharacteristic rho.coefficients (gaussianWeylArgument X xi) * noiseMultiplier Y xi

/-- PDF p.4, (31): supremum on actual centered Gaussian input densities. ENNReal
suprema avoid empty/unbounded real defaults; the physical set is nonempty and <=1. -/
def maximalOutputPurity {I : Type} [Fintype I] (p : ℝ) (E : OscillatorCoeff I → OscillatorCoeff I) : ℝ≥0∞ :=
  ⨆ rho : {rho : State (Occupation I) // IsCenteredGaussianDensity rho}, pNorm p (E rho.val.coefficients)

/-- PDF p.4, (34): the same supremum restricted to pure Gaussian densities. -/
def pureMaximalOutputPurity {I : Type} [Fintype I] (p : ℝ) (E : OscillatorCoeff I → OscillatorCoeff I) : ℝ≥0∞ :=
  ⨆ rho : {rho : State (Occupation I) // IsCenteredGaussianDensity rho ∧ IsPureOscillatorDensity rho},
    pNorm p (E rho.val.coefficients)

/-- PDF pp.3--4: replace one whole channel's occupation string, keeping all other modes. -/
def replaceOccupation {r : ℕ} {m : Fin r → ℕ} (i : Fin r)
    (u : Occupation (Σ j, Fin (m j))) (a : Occupation (Fin (m i))) :
    Occupation (Σ j, Fin (m j)) :=
  fun j => if h : j.1 = i then a (h ▸ j.2) else u j

/-- PDF pp.3--4, (36): apply a local map to every off-diagonal block.
The other factors form an arbitrary completed oscillator ancilla. -/
def applyOscillatorBlock {r : ℕ} {m : Fin r → ℕ} (i : Fin r)
    (E : OscillatorCoeff (Fin (m i)) → OscillatorCoeff (Fin (m i)))
    (A : OscillatorCoeff (Σ j, Fin (m j))) : OscillatorCoeff (Σ j, Fin (m j)) :=
  fun u v => E (fun a b => A (replaceOccupation i u a) (replaceOccupation i v b))
    (fun k => u ⟨i, k⟩) (fun k => v ⟨i, k⟩)

/-- PDF pp.3--4, (36): actual finite tensor product of the full channel maps.
The fold applies each factor once; it is not a rule only on product inputs. -/
def tensorOscillatorChannel {r : ℕ} {m : Fin r → ℕ}
    (E : (i : Fin r) → CenteredOscillatorChannel (Fin (m i)))
    (A : OscillatorCoeff (Σ j, Fin (m j))) : OscillatorCoeff (Σ j, Fin (m j)) :=
  (List.finRange r).foldl (fun B i => applyOscillatorBlock i (E i).map B) A

/-- PDF p.4, (37): global Gaussian inputs may be entangled across channel blocks. -/
def GaussianPurityMultiplicative {r : ℕ} {m : Fin r → ℕ} (p : ℝ)
    (E : (i : Fin r) → CenteredOscillatorChannel (Fin (m i))) : Prop :=
  maximalOutputPurity p (tensorOscillatorChannel E) = ∏ i, maximalOutputPurity p (E i).map

/-- PDF p.5, (40): canonical X computed from its factor, including det X=0. -/
def scalarX (E : CenteredOscillatorChannel (Fin 1)) : OscillatorCovariance (Fin 1) :=
  Real.sqrt |E.X.det| • 1

/-- PDF p.5, (40): canonical Y computed from its factor, including det Y=0. -/
def scalarY (E : CenteredOscillatorChannel (Fin 1)) : OscillatorCovariance (Fin 1) :=
  Real.sqrt E.Y.det • 1

/-- PDF p.5: equal determinant signs, including the common zero sign. -/
def EqualSigns {r : ℕ} (E : Fin r → CenteredOscillatorChannel (Fin 1)) : Prop :=
  ∀ i j, (if (E i).X.det < 0 then (-1 : ℤ) else if (E i).X.det = 0 then 0 else 1) =
    (if (E j).X.det < 0 then (-1 : ℤ) else if (E j).X.det = 0 then 0 else 1)

/-- PDF p.2, (9): source convention S^T interleavedSigma S=interleavedSigma. -/
def PreservesInterleavedSigma {I : Type} [Fintype I] (S : OscillatorCovariance I) : Prop :=
  S.transpose * interleavedSigma I * S = interleavedSigma I

/-- PDF p.2, (12): Williamson spectrum with multiplicity, not singular values
of the generally nonnormal i interleavedSigma G. Ordering is immaterial to products. -/
def WilliamsonSpectrum {I : Type} [Fintype I] (G : OscillatorCovariance I) (nu : I → ℝ) : Prop :=
  (∀ i, 1 ≤ nu i) ∧ ∃ S : OscillatorCovariance I, PreservesInterleavedSigma S ∧
    S.transpose * G * S = Matrix.diagonal (fun i => nu i.1)

/-- PDF p.4, (28): reuse the exact accepted f_p. -/
def fp (p x : ℝ) : ℝ := phiMinus p x

/-- PDF p.4, (29): F_p from an explicitly identified symplectic spectrum. -/
def spectralFp {I : Type} [Fintype I] (p : ℝ) (nu : I → ℝ) : ℝ := ∏ i, fp p (nu i)

/-- PDF p.4, (30): intrinsic Ky Fan sum over all r-dimensional orthonormal
frames. For nonempty mode sets this equals the sum of the r largest density
eigenvalues with zero padding. ENNReal prevents an unbounded-real default. -/
def kyFan {I : Type} (A : OscillatorCoeff I) (r : ℕ) : ℝ≥0∞ :=
  ⨆ v : {v : Fin r → Hilbert (Occupation I) // Orthonormal ℂ v},
    ∑ j, ENNReal.ofReal (inner ℂ (v.val j) (realizeOscillatorCoeff A (v.val j))).re

/-- PDF p.4, (30): spectral majorization of actual positive trace-one densities. -/
def OscillatorMajorizes {I : Type} (A B : OscillatorCoeff I) : Prop := ∀ r : ℕ, kyFan B r ≤ kyFan A r

/-- PDF pp.3--5: oscillatorCoefficients of an actual tensor product of factor states. -/
def productInput {r : ℕ} {m : Fin r → ℕ}
    (rho : (i : Fin r) → State (Occupation (Fin (m i)))) : OscillatorCoeff (Σ j, Fin (m j)) :=
  fun u v => ∏ i, (rho i).coefficients (fun k => u ⟨i, k⟩) (fun k => v ⟨i, k⟩)

/-- PDF p.8, (A1): the one-mode sourceBeta matrix. -/
def sourceBeta : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- PDF p.8, (A1): the one-mode sourceDelta matrix. -/
def sourceDelta : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- PDF p.8, (A2): sigma2, sourceBeta and sourceDelta. Ordering does not affect a basis. -/
def oneModeGenerator (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℝ :=
  if a = 0 then !![0, 1; -1, 0] else if a = 1 then sourceBeta else sourceDelta

/-- PDF p.8, (A2)--(A5): three single-mode and four unordered-pair generators. -/
abbrev GeneratorIndex (n : ℕ) :=
  (Fin n × Fin 3) ⊕ ({ij : Fin n × Fin n // ij.1 < ij.2} × Fin 4)

/-- PDF p.8, (A2)--(A4): the actual embedded one/two-mode matrices. Pair labels
0,1 are the two skew generators in (A3); 2,3 are the symmetric ones in (A4). -/
def sourceSymplecticGenerator {n : ℕ} (a : GeneratorIndex n) : OscillatorCovariance (Fin n) :=
  match a with
  | Sum.inl a => fun i j =>
      if i.1 = a.1 ∧ j.1 = a.1 then oneModeGenerator a.2 i.2 j.2 else 0
  | Sum.inr a => fun i j =>
      if i.1 = a.1.val.1 ∧ j.1 = a.1.val.2 then
        if a.2 = 0 then !![0, 1; -1, 0] i.2 j.2
        else if a.2 = 1 then -(1 : Matrix (Fin 2) (Fin 2) ℝ) i.2 j.2
        else if a.2 = 2 then sourceDelta i.2 j.2 else sourceBeta i.2 j.2
      else if i.1 = a.1.val.2 ∧ j.1 = a.1.val.1 then
        if a.2 = 0 then !![0, 1; -1, 0] i.2 j.2
        else if a.2 = 1 then (1 : Matrix (Fin 2) (Fin 2) ℝ) i.2 j.2
        else if a.2 = 2 then sourceDelta i.2 j.2 else sourceBeta i.2 j.2
      else 0

/-- PDF p.8: infinitesimal symplecticity, not a subgroup of symmetric matrices. -/
def InSymplecticAlgebra {n : ℕ} (K : OscillatorCovariance (Fin n)) : Prop :=
  K.transpose * interleavedSigma (Fin n) + interleavedSigma (Fin n) * K = 0

/-- PDF p.8: skew infinitesimal generators of the compact passive subgroup. -/
abbrev CompactGeneratorIndex (n : ℕ) :=
  {a : GeneratorIndex n // (sourceSymplecticGenerator a).transpose = -sourceSymplecticGenerator a}

example : interleavedSigma (Fin 1) (0, 0) (0, 1) = 1 := by simp [interleavedSigma]

example : interleavedSigma (Fin 1) (0, 1) (0, 0) = -1 := by simp [interleavedSigma]

example (X G : OscillatorCovariance (Fin 1)) : gaussianCovarianceMap X 0 G = X.transpose * G * X := by
  simp [gaussianCovarianceMap]

example {I : Type} (T : OscillatorOperator I) : oscillatorCoefficients (realizeOscillatorCoeff (oscillatorCoefficients T)) = oscillatorCoefficients T := by
  unfold realizeOscillatorCoeff
  split_ifs with h
  · exact Classical.choose_spec h
  · exact (h ⟨T, rfl⟩).elim

example : fp 2 1 = 4 := by
  norm_num [fp, phiMinus, Real.rpow_natCast]

example : sourceSymplecticGenerator (Sum.inl ((0 : Fin 1), (0 : Fin 3))) (0, 0) (0, 1) = 1 := by
  simp [sourceSymplecticGenerator, oneModeGenerator]

example : sourceSymplecticGenerator (Sum.inl ((0 : Fin 1), (1 : Fin 3))) (0, 1) (0, 1) = -1 := by
  norm_num [sourceSymplecticGenerator, oneModeGenerator, sourceBeta]

example (m : Fin 0 → ℕ) (E : (i : Fin 0) → CenteredOscillatorChannel (Fin (m i)))
    (A : OscillatorCoeff (Σ j, Fin (m j))) : tensorOscillatorChannel E A = A := by
  simp [tensorOscillatorChannel]

example : sourceSymplecticGenerator (Sum.inr (⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩, (1 : Fin 4)))
    (0, 0) (1, 0) = -1 := by
  norm_num [sourceSymplecticGenerator]

example : sourceSymplecticGenerator (Sum.inr (⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩, (1 : Fin 4)))
    (1, 0) (0, 0) = 1 := by
  norm_num [sourceSymplecticGenerator]

end QAlgorithms.Papers.Independent.Support50.P28


