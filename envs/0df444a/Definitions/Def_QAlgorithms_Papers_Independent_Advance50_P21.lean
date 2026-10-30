-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21
-- name    : QAlgorithms_Papers_Independent_Advance50_P21
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T21:46:58.090992+00:00
-- url     : https://prove2.me/theorems/3dab769b-b03a-456e-a059-e76086045184
-- title:
--   Definitions for Entropy power inequalities for qudits
-- statement:
--   The objects the formalized statements of *Entropy power inequalities for qudits* (arXiv:1503.04213) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `simplexShannonNats`: PDF p.16: natural-log Shannon entropy; zero-weight terms have value zero. Specializes accepted Information100.P39.entropy at order one; the frozen Information100.P27.shannon is in bits and cannot be used without a unit conversion.
--   - `decreasingStateSpectrum`: PDF p.5, (2.3): decreasing spectrum; the extension off Hermitian matrices is unused. Uses accepted orderedSpectrum; Renew46.P26.spectrum is a group-algebra weight set.
--   - `partialSwapUnitary`: PDF p.9, Definition 8, (4.7): the constructed partial swap, with positive i.
--   - `partialSwapChannel`: PDF p.9, (4.9): full linear operator action, including entangled inputs.
--   - `quditAddition`: PDF pp.6,10, (3.1),(4.17): source qudit addition with minus i times the commutator.
--   - `StateConcave`: PDF pp.5–6, Definition 3: concavity on precisely the normalized state space.
--   - `ConcaveSpectralClass`: PDF pp.5–6, Definition 3: concave state functions depending only on the unordered spectrum. Equality of the computed decreasing spectra identifies exactly unordered eigenvalue multisets. No continuity, differentiability, or concavity outside the state space is imposed.
--   - `quditEntropyPower`: PDF p.6, (3.2): qudit entropy power exp(c H) in nats. Dependency50.P05.entropyPower instead maps an extended entropy to 2^(-H).
--   - `quditEntropyPhotonNumber`: PDF p.6, (3.3): inverse is restricted to the nonnegative occupation branch of g. Support50.P06.entropyPhotonNumber takes mode count and extended oscillator entropy.
--   - `renyiNats`: PDF p.7, corrected (3.9): standard Renyi entropy in nats, with support rank at order zero. The printed coefficient 1/(alpha-1) is changed to 1/(1-alpha): the printed sign contradicts the claimed EPI on two orthogonal pure qubits. Independent moderation is required.
--   - `subentropyNats`: PDF pp.7–8, (3.10): subentropy in nats, including the continuous extension at repeated and zero eigenvalues. Reuses the accepted Haar-average formula and its harmonic offset.
--   - `partialSwapKraus`: PDF p.10, (4.15): exactly d rectangular Kraus matrices; columns index both input ports.
--   - `qubitBlochVector`: PDF pp.10,32: density-matrix Bloch coordinates in Pauli order X,Y,Z, with the Euclidean norm. Accepted bloch declarations take pure kets or construct Pauli observables from coordinate vectors; they have different domains.
--   - `blochCross`: PDF p.33, (A.8): right-handed cross product in Euclidean Bloch space.
--   - `logSecondMoment`: PDF p.16: the logarithmic second moment; 0*(log 0)^2 is its continuous value zero.
--   - `simplexInformationVariance`: PDF p.19, (6.29): classical information variance in nats squared, including distributions uniform on their support. Information100.P63.informationVariance instead takes a density matrix and uses bits squared.
--   - `oneHeavy`: PDF pp.20–22, (6.31): d-1 equal small masses and one large final mass.
--   - `peakEntropy`: PDF p.22, (6.46): s_r with r=d-1. The zero-weight convention includes x=0.
--   - `peakVariance`: PDF p.22, (6.47): w_r with r=d-1. The branch x=0 explicitly supplies its limiting value.
--   - `fixedPort`: PDF p.26, (7.1): fixed second port, constructed on every operator. Its fixed-state term on arbitrary X is (1-a)*Tr(X)*sigma, not (1-a)*sigma.
--   - `outputEntropyValues`: PDF p.26, (7.3): minimum-output entropy value. Only positive-dimensional channels are used; the application statements retain attainment, so the real infimum has no junk-value reading.
--   - `finiteMinimumOutputEntropyNats`: PDF p.26, (7.3): real infimum of finite-dimensional output entropies in nats. Next46.P42.minimumOutputEntropy uses countable trace-class states and extended nonnegative values. This finite formulation retains attainment in the statements.
--   - `outputBound`: PDF p.26, (7.4)–(7.6): the three actual scalar bounds, indexed 0,1,2. The reciprocal constants are used only when d >= 2.
--   - `radialEntropy`: PDF p.32, (A.3): qubit entropy as a function of Bloch radius, in nats.
--   - `radialInverse`: PDF pp.26,32: inverse of ell on the decreasing nonnegative branch [0,1]. For entropy in [0,ln 2] this nonempty compact set has infimum equal to the unique root; no inverse of the even extension to [-1,1] is used.
--   - `holevoNats`: PDF p.27, (7.9): single-use Holevo quantity, explicitly converted from bits to nats.
--   - `diagonalPort`: PDF p.26: diagonal qubit port with eigenvalues delta and 1-delta.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, https://arxiv.org/abs/1503.04213v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P11
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P36
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

/-!
Audenaert, Datta and Ozols, Entropy power inequalities for qudits,
arXiv:1503.04213v3. All page references are PDF pages; all entropies are in nats.
Only theorem statements contain sorry. Compilation is pending the batch handoff.
Functions on matrices are constrained only on density matrices: their arbitrary
extension off the state space imposes no regularity assumption on state functions.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)
open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)
open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)
open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)
open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.16: natural-log Shannon entropy; zero-weight terms have value zero.
Specializes accepted Information100.P39.entropy at order one; the frozen
Information100.P27.shannon is in bits and cannot be used without a unit conversion. -/
abbrev simplexShannonNats {d : ℕ} (q : Fin d → ℝ) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P39.entropy 1 q

/-- PDF p.5, (2.3): decreasing spectrum; the extension off Hermitian matrices is unused.
Uses accepted orderedSpectrum; Renew46.P26.spectrum is a group-algebra weight set. -/
def decreasingStateSpectrum {d : ℕ} (rho : Mat d) : Fin d → ℝ :=
  if h : rho.IsHermitian then orderedSpectrum rho h else 0

/-- PDF p.9, Definition 8, (4.7): the constructed partial swap, with positive i. -/
def partialSwapUnitary (d : ℕ) (a : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (Real.sqrt a : ℂ) • 1 + (Complex.I * (Real.sqrt (1 - a) : ℂ)) • (swapMatrix (I := Fin d))

/-- PDF p.9, (4.9): full linear operator action, including entangled inputs. -/
def partialSwapChannel (d : ℕ) (a : ℝ) : Superop (Fin d × Fin d) (Fin d) :=
  fun X => traceRight (partialSwapUnitary d a * X * (partialSwapUnitary d a)ᴴ)

/-- PDF pp.6,10, (3.1),(4.17): source qudit addition with minus i times the commutator. -/
def quditAddition {d : ℕ} (a : ℝ) (rho sigma : Mat d) : Mat d :=
  a • rho + (1 - a) • sigma -
    ((Real.sqrt (a * (1 - a)) : ℂ) * Complex.I) • (rho * sigma - sigma * rho)

/-- PDF pp.5–6, Definition 3: concavity on precisely the normalized state space. -/
def StateConcave {d : ℕ} (f : Mat d → ℝ) : Prop :=
  ∀ rho sigma, IsDensityMatrix rho → IsDensityMatrix sigma →
    ∀ a ∈ Set.Icc (0 : ℝ) 1,
      a * f rho + (1 - a) * f sigma ≤ f (a • rho + (1 - a) • sigma)

/-- PDF pp.5–6, Definition 3: concave state functions depending only on the unordered spectrum.
Equality of the computed decreasing spectra identifies exactly unordered eigenvalue multisets.
No continuity, differentiability, or concavity outside the state space is imposed. -/
def ConcaveSpectralClass {d : ℕ} (f : Mat d → ℝ) : Prop :=
  StateConcave f ∧ ∀ rho sigma, IsDensityMatrix rho → IsDensityMatrix sigma →
    decreasingStateSpectrum rho = decreasingStateSpectrum sigma → f rho = f sigma

/-- PDF p.6, (3.2): qudit entropy power exp(c H) in nats.
Dependency50.P05.entropyPower instead maps an extended entropy to 2^(-H). -/
def quditEntropyPower {d : ℕ} (c : ℝ) (rho : Mat d) : ℝ := Real.exp (c * entropy rho)

/-- PDF p.6, (3.3): inverse is restricted to the nonnegative occupation branch of g.
Support50.P06.entropyPhotonNumber takes mode count and extended oscillator entropy. -/
def quditEntropyPhotonNumber {d : ℕ} (c : ℝ) (rho : Mat d) : ℝ :=
  thermalEntropyInverse (c * entropy rho)

/-- PDF p.7, corrected (3.9): standard Renyi entropy in nats, with support rank at order zero.
The printed coefficient 1/(alpha-1) is changed to 1/(1-alpha): the printed sign contradicts
the claimed EPI on two orthogonal pure qubits. Independent moderation is required. -/
def renyiNats {d : ℕ} (alpha : ℝ) (rho : Mat d) : ℝ :=
  Real.log 2 * QAlgorithms.Papers.Independent.Dependency50.P05.renyiEntropy alpha rho

/-- PDF pp.7–8, (3.10): subentropy in nats, including the continuous extension at repeated
and zero eigenvalues. Reuses the accepted Haar-average formula and its harmonic offset. -/
def subentropyNats {d : ℕ} (rho : Mat d) : ℝ :=
  Real.log 2 * QAlgorithms.Papers.Independent.Bridge50.P36.subentropy rho

/-- PDF p.10, (4.15): exactly d rectangular Kraus matrices; columns index both input ports. -/
def partialSwapKraus (d : ℕ) (a : ℝ) (k : Fin d) :
    Matrix (Fin d) (Fin d × Fin d) ℂ :=
  fun i p => (Real.sqrt a : ℂ) * (if i = p.1 ∧ k = p.2 then 1 else 0) +
    Complex.I * (Real.sqrt (1 - a) : ℂ) * (if k = p.1 ∧ i = p.2 then 1 else 0)

/-- PDF pp.10,32: density-matrix Bloch coordinates in Pauli order X,Y,Z,
with the Euclidean norm. Accepted bloch declarations take pure kets or
construct Pauli observables from coordinate vectors; they have different domains. -/
def qubitBlochVector (rho : Mat 2) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 * (rho 0 1).re, -2 * (rho 0 1).im, (rho 0 0).re - (rho 1 1).re]

/-- PDF p.33, (A.8): right-handed cross product in Euclidean Bloch space. -/
def blochCross (v w : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (crossProduct (fun i => v i) (fun i => w i))

/-- PDF p.16: the logarithmic second moment; 0*(log 0)^2 is its continuous value zero. -/
def logSecondMoment {d : ℕ} (q : Fin d → ℝ) : ℝ :=
  ∑ i, q i * (Real.log (q i)) ^ 2

/-- PDF p.19, (6.29): classical information variance in nats squared,
including distributions uniform on their support. Information100.P63.informationVariance
instead takes a density matrix and uses bits squared. -/
def simplexInformationVariance {d : ℕ} (q : Fin d → ℝ) : ℝ :=
  logSecondMoment q - simplexShannonNats q ^ 2

/-- PDF pp.20–22, (6.31): d-1 equal small masses and one large final mass. -/
def oneHeavy (d : ℕ) (x : ℝ) : Fin d → ℝ :=
  fun i => if i.val + 1 = d then 1 - (d - 1 : ℕ) * x else x

/-- PDF p.22, (6.46): s_r with r=d-1. The zero-weight convention includes x=0. -/
def peakEntropy (d : ℕ) (x : ℝ) : ℝ :=
  -((d - 1 : ℕ) : ℝ) * x * Real.log x -
    (1 - (d - 1 : ℕ) * x) * Real.log (1 - (d - 1 : ℕ) * x)

/-- PDF p.22, (6.47): w_r with r=d-1. The branch x=0 explicitly supplies its limiting value. -/
def peakVariance (d : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    (d - 1 : ℕ) * x * (1 - (d - 1 : ℕ) * x) *
      (Real.log x - Real.log (1 - (d - 1 : ℕ) * x)) ^ 2

/-- PDF p.26, (7.1): fixed second port, constructed on every operator.
Its fixed-state term on arbitrary X is (1-a)*Tr(X)*sigma, not (1-a)*sigma. -/
def fixedPort {d : ℕ} (a : ℝ) (sigma : Mat d) : Superop (Fin d) (Fin d) :=
  fun X => partialSwapChannel d a (Matrix.kronecker X sigma)

/-- PDF p.26, (7.3): minimum-output entropy value. Only positive-dimensional channels are used;
the application statements retain attainment, so the real infimum has no junk-value reading. -/
def outputEntropyValues {e d : ℕ} (N : Superop (Fin e) (Fin d)) : Set ℝ :=
  {v | ∃ rho : Mat e, IsDensityMatrix rho ∧ v = entropy (N rho)}

/-- PDF p.26, (7.3): real infimum of finite-dimensional output entropies in nats.
Next46.P42.minimumOutputEntropy uses countable trace-class states and extended
nonnegative values. This finite formulation retains attainment in the statements. -/
def finiteMinimumOutputEntropyNats {e d : ℕ} (N : Superop (Fin e) (Fin d)) : ℝ :=
  sInf (outputEntropyValues N)

/-- PDF p.26, (7.4)–(7.6): the three actual scalar bounds, indexed 0,1,2.
The reciprocal constants are used only when d >= 2. -/
def outputBound (d : ℕ) (a s : ℝ) (j : Fin 3) (t : ℝ) : ℝ :=
  if j = 0 then a * t + (1 - a) * s
  else if j = 1 then
    let c := 1 / (Real.log (d : ℝ)) ^ 2
    Real.log (a * Real.exp (c * t) + (1 - a) * Real.exp (c * s)) / c
  else
    let c := 1 / ((d : ℝ) - 1)
    thermalEntropy (a * thermalEntropyInverse (c * t) +
      (1 - a) * thermalEntropyInverse (c * s)) / c

/-- PDF p.32, (A.3): qubit entropy as a function of Bloch radius, in nats. -/
def radialEntropy (r : ℝ) : ℝ := Real.binEntropy ((1 + r) / 2)

/-- PDF pp.26,32: inverse of ell on the decreasing nonnegative branch [0,1].
For entropy in [0,ln 2] this nonempty compact set has infimum equal to the unique root;
no inverse of the even extension to [-1,1] is used. -/
def radialInverse (s : ℝ) : ℝ :=
  sInf {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ radialEntropy r ≤ s}

/-- PDF p.27, (7.9): single-use Holevo quantity, explicitly converted from bits to nats. -/
def holevoNats {e d : ℕ} (N : Superop (Fin e) (Fin d)) : ℝ :=
  Real.log 2 * QAlgorithms.Papers.Independent.Information100.P08.channelHolevo N

/-- PDF p.26: diagonal qubit port with eigenvalues delta and 1-delta. -/
def diagonalPort (delta : ℝ) : Mat 2 :=
  Matrix.diagonal ![(delta : ℂ), ((1 - delta : ℝ) : ℂ)]

/-! Sanity examples pin endpoints, signs and the zero-weight conventions. -/

example (d : ℕ) : partialSwapUnitary d 1 = 1 := by
  simp [partialSwapUnitary]

example {d : ℕ} (rho sigma : Mat d) : quditAddition 0 rho sigma = sigma := by
  simp [quditAddition]

example {d : ℕ} (rho sigma : Mat d) : quditAddition 1 rho sigma = rho := by
  simp [quditAddition]

example {d : ℕ} (rho : Mat d) : quditEntropyPower 0 rho = 1 := by
  simp [quditEntropyPower]

example {d : ℕ} (rho : Mat d) : quditEntropyPhotonNumber 0 rho = 0 := by
  simp [quditEntropyPhotonNumber, thermalEntropyInverse]

example (d : ℕ) : peakVariance d 0 = 0 := by
  simp [peakVariance]

example : radialEntropy 1 = 0 := by
  norm_num [radialEntropy]

example (d : ℕ) (a s t : ℝ) : outputBound d a s 0 t = a * t + (1 - a) * s := by
  simp [outputBound]

example (d : ℕ) (i j : Fin d) : (swapMatrix (I := Fin d)) (i,j) (j,i) = 1 := by
  simp [QAlgorithms.Papers.Independent.Information100.P76.swapMatrix]

example : peakEntropy 2 0 = 0 := by
  norm_num [peakEntropy]

end QAlgorithms.Papers.Independent.Advance50.P21


