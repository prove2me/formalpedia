-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P39
-- name    : QAlgorithms_Papers_Independent_Renew46_P39
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T21:12:50.083078+00:00
-- url     : https://prove2.me/theorems/0bd6fd2a-9e40-4400-97b3-3ebf661a9200
-- title:
--   Definitions for On the impossibility of distilling Gaussian states with Gaussian operations
-- statement:
--   The objects the formalized statements of *On the impossibility of distilling Gaussian states with Gaussian operations* (arXiv:quant-ph/0204052) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `initialCovariance`: PDF p.2, (1): the essential opposite-sign correlation family.
--   - `AffineMultimodeGaussianUnitary`: PDF pp.1--2: actual completed n-oscillator Gaussian unitaries, including local displacements. The frozen Frontier30.P14.GaussianUnitary is a centered SINGLE-mode predicate; this distinct bundled multimode interface is required. The equation is U-adjoint W(v) U, so S acts actively on state covariances by S V S-transpose. No covariance update is assumed here.
--   - `Outcome`: PDF pp.1--2, Fig.1: the two communicated real P-homodyne outcomes.
--   - `TwoCopyHomodyneProtocol`: PDF pp.1--2, Fig.1, [7]: two independent local two-mode unitaries followed by arbitrary outcome-dependent local one-mode Gaussian unitary feedback. Each party can use BOTH communicated outcomes. There are no extra modes. The frozen Dependency50.P07.Protocol is a finite key-agreement protocol, not this oscillator homodyne protocol.
--   - `identityGaussianUnitary`: PDF p.1: the identity is a concrete admissible Gaussian unitary. This also checks that the bounded-Weyl action requirement has an actual inhabitant.
--   - `identityProtocol`: PDF p.1: identity preprocessing and identity feedback in the restricted Fig.1 family. Measurable feedback is the usual quantum-instrument convention.
--   - `joinModes`: PDF p.2: mode order A1,A2,B1,B2; retained indices are A1,B1.
--   - `twoCopies`: PDF p.2, (2): two identical independent copies of THIS density, in party order A1,A2,B1,B2, rather than two unrelated covariance witnesses.
--   - `localUnitaryKernel`: PDF p.2, (2): coefficients of the bounded unitary U_A tensor U_B.
--   - `beforeMeasurement`: PDF p.2, (2): the actual premeasurement density kernel.
--   - `feedbackKernel`: PDF p.1, step (ii): local feedback on the two retained modes, at the specified pair of real outcomes. Finite products are actual tensor coefficients.
--   - `afterFeedback`: PDF p.1, step (ii): the actual density after permitted feedback.
--   - `blockQuadrature`: PDF pp.2--3, (6): explicit retained/discarded quadrature permutation. block=0 retains A1,B1; block=1 selects A2,B2, with X,P interleaved.
--   - `retainedDiscardedBlock`: PDF p.2, (6): arbitrary four-mode covariance blocks after that permutation. C1=block 0 0, C2=block 1 1, C3=block 0 1. Unlike the frozen Frontier30.P04.covarianceBlock, this also includes OFF-DIAGONAL blocks.
--   - `seedCovariance`: PDF p.2, Lemma 1, corrected following (7)--(9): this is the SEED COVARIANCE V_d=D_d^2, with D_d the squeezing amplitude diag(1/d,d,...). Printed Lemma 1 instead calls D_d the covariance; see MODERATION_NOTES.md.
--   - `PureSeed`: PDF p.2, Lemma 1: pure normalized Gaussian seed. Its means are arbitrary; V_d is diagonal and hence the two discarded modes have a product seed. Purity is an actual norm-one vector representation on the full Fock space.
--   - `SeedAt`: PDF pp.2--3: pure seed centered at the measured P values y, with zero X means. Characteristic functions fix the actual seed density, not its update.
--   - `projectedKernel`: PDF p.2, Lemma 1: incomplete trace Tr_discard[(I tensor seed) rho]. This is the actual pure-state projection on A2,B2, with A1,B1 retained. The source results establish convergence on their Gaussian domain.
--   - `ProjectionSummable`: PDF p.2, Lemma 1: guards for every iterated contraction and normalization series. They are conclusions of the finite-projection theorem, not assumptions of a Schur covariance rule.
--   - `projectionWeight`: PDF p.2, Lemma 1: probability of a finite normalized rank-one projection.
--   - `finiteOutput`: PDF p.2, Lemma 1: normalized selective output, on the positive-weight summable domain. Values elsewhere are never used as physical states.
--   - `HomodyneOutcome`: PDF pp.2--3: ideal P-homodyne conditional density at a specified FINITE real outcome. It is a trace-norm limit of normalized physical seed projections, not an entrywise limit or a normalizable infinite-squeezing vector. This contains no formula for the resulting covariance, nor any entanglement assertion.
--   - `finiteSchur`: PDF p.2, (7), corrected seed convention: the finite Schur EXPRESSION. Identification with the actual selective density is the content of Lemma 1.
--   - `momentumProjection`: PDF p.3, (10), corrected: d->0+ for V_d leaves P, so piP=diag(0,1,0,1). The printed diag(1,0,1,0) corresponds to X instead; local rotations allow either.
--   - `homodyneCovariance`: PDF p.3, (10): the Moore--Penrose EXPRESSION. The accepted supportInverse is the MP inverse on the symmetric PSD matrix piP C2 piP, not a nonsingular inverse on all four discarded quadratures. Operational identification is Lemma 2.
--   - `bipartiteKernel`: PDF p.1: identify the oscillator functions with the ordered Alice,Bob product basis for the accepted partial-transpose operation.
--   - `FinitePartialTranspose`: PDF pp.1--2: a genuine finite, nonzero partial-transpose trace norm. This is established in the no-distillation theorem; it is not an input premise.
--   - `oscillatorLogNegativity`: PDF p.1: E_N=log_2 ||rho^{T_A}||_1. Only used together with proved FinitePartialTranspose conclusions; toReal(infinity)=0 is never used as an entanglement value. No covariance formula is made the definition of E_N. The frozen Dependency50.P24.logNegativity uses finite-dimensional Bob transposition; its trace norm does not cover full oscillator densities.
--   - `squeezedCoefficient`: PDF pp.1--2: two-mode squeezed-vacuum coefficients of strength r>=0, with no occupation cutoff. This fixes the parameter by tanh(r), not tanh(2r).
--   - `squeezedVacuum`: PDF pp.1--2: actual rank-one squeezed-vacuum density coefficients. Its covariance is initialCovariance(cosh(2r),sinh(2r)); it is not defined by an entanglement or covariance update hypothesis.
--   - `marginalAverage`: PDF p.2, (5): u=(det gamma_A+det gamma_B)/2 for any two-mode matrix.
--   - `sourceF`: PDF p.2, (5): squared least partially transposed symplectic eigenvalue. Real.sqrt is only interpreted on physical covariances in the theorem below.
--   - `sourceG`: PDF p.3, (13): the INNER determinant is square-rooted before subtraction. This is not the entropy function named f in some accepted Gaussian papers.
-- source:
--   On the impossibility of distilling Gaussian states with Gaussian operations, arXiv:quant-ph/0204052v4, https://arxiv.org/abs/quant-ph/0204052v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14

/-!
Eisert--Scheel--Plenio, quant-ph/0204052v4, PDF pp.1--4.
Full completed oscillator spaces, [X,P]=i, full anticommutator covariance,
vacuum covariance I, logarithmic negativity in bits. Pinned accepted paper
modules are used as definition providers under the independent-paper override.
Finite projections below contract actual density kernels, without assuming a
Schur update. Ideal P-homodyne is the normalized, trace-norm limit of displaced
pure P-squeezed projections. No infinitely squeezed normalizable vector is used.
The closing general-LOCC sketch is deferred; this module covers only Fig.1.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open Filter
open scoped BigOperators Topology ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Renew46.P39

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsTraceClass traceSize rankOne)
open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance standardFormCovariance
   modeCovarianceBlock productWeyl weylArgument CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue)
open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex interleavedSymplecticForm isSymplectic)
open QAlgorithms.Papers.Independent.Dependency50.P10
  (physicalCovariance supportInverse)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation)

/-- PDF p.2, (1): the essential opposite-sign correlation family. -/
def initialCovariance (a c : ℝ) : Cov 2 :=
  standardFormCovariance a a c (-c)

/-- PDF pp.1--2: actual completed n-oscillator Gaussian unitaries, including
local displacements. The frozen Frontier30.P14.GaussianUnitary is a centered
SINGLE-mode predicate; this distinct bundled multimode interface is required.
The equation is U-adjoint W(v) U, so S acts actively on
state covariances by S V S-transpose. No covariance update is assumed here. -/
structure AffineMultimodeGaussianUnitary (n : ℕ) where
  symplecticMatrix : Cov n
  displacement : QuadratureIndex n → ℝ
  unitary : Hilbert (FockIndex n) ≃ₗᵢ[ℂ] Hilbert (FockIndex n)
  preservesCCR : isSymplectic symplecticMatrix
  weylAction : ∀ v : QuadratureIndex n → ℝ,
    boundedUnitaryConjugation unitary.symm (productWeyl (weylArgument v)) =
      (Complex.exp (Complex.I * ((∑ i, displacement i * v i : ℝ) : ℂ))) •
        productWeyl (weylArgument (symplecticMatrix.transpose.mulVec v))

/-- PDF pp.1--2, Fig.1: the two communicated real P-homodyne outcomes. -/
abbrev Outcome := Fin 2 → ℝ

/-- PDF pp.1--2, Fig.1, [7]: two independent local two-mode unitaries followed
by arbitrary outcome-dependent local one-mode Gaussian unitary feedback.
Each party can use BOTH communicated outcomes. There are no extra modes.
The frozen Dependency50.P07.Protocol is a finite key-agreement protocol,
not this oscillator homodyne protocol. -/
structure TwoCopyHomodyneProtocol where
  alice : AffineMultimodeGaussianUnitary 2
  bob : AffineMultimodeGaussianUnitary 2
  feedbackAlice : Outcome → AffineMultimodeGaussianUnitary 1
  feedbackBob : Outcome → AffineMultimodeGaussianUnitary 1
  measurableAlice : ∀ i j : FockIndex 1,
    Measurable (fun y => unitaryCoeff (feedbackAlice y).unitary i j)
  measurableBob : ∀ i j : FockIndex 1,
    Measurable (fun y => unitaryCoeff (feedbackBob y).unitary i j)

/-- PDF p.1: the identity is a concrete admissible Gaussian unitary. This also
checks that the bounded-Weyl action requirement has an actual inhabitant. -/
def identityGaussianUnitary (n : ℕ) : AffineMultimodeGaussianUnitary n where
  symplecticMatrix := 1
  displacement := 0
  unitary := LinearIsometryEquiv.refl ℂ _
  preservesCCR := by simp [isSymplectic]
  weylAction := by
    intro v
    funext i j
    simp [boundedUnitaryConjugation, conjugateKernel, unitaryCoeff,
      QAlgorithms.Papers.Independent.Frontier30.P14.isometryCoeff, lp.single_apply,
      ite_mul, mul_ite]
    have identityInverse (x : Hilbert (FockIndex n)) :
        (LinearIsometryEquiv.refl ℂ (Hilbert (FockIndex n))).symm x = x :=
      (LinearIsometryEquiv.refl ℂ (Hilbert (FockIndex n))).symm_apply_apply x
    simp only [identityInverse]
    simp [lp.single_apply, Pi.single, Function.update_apply, eq_comm,
      ite_mul, mul_ite]

/-- PDF p.1: identity preprocessing and identity feedback in the restricted
Fig.1 family. Measurable feedback is the usual quantum-instrument convention. -/
def identityProtocol : TwoCopyHomodyneProtocol where
  alice := identityGaussianUnitary 2
  bob := identityGaussianUnitary 2
  feedbackAlice := fun _ => identityGaussianUnitary 1
  feedbackBob := fun _ => identityGaussianUnitary 1
  measurableAlice := by intro i j; exact measurable_const
  measurableBob := by intro i j; exact measurable_const

/-- PDF p.2: mode order A1,A2,B1,B2; retained indices are A1,B1. -/
def joinModes (keep discard : FockIndex 2) : FockIndex 4 :=
  ![keep 0, discard 0, keep 1, discard 1]

/-- PDF p.2, (2): two identical independent copies of THIS density, in party
order A1,A2,B1,B2, rather than two unrelated covariance witnesses. -/
def twoCopies (rho : DensityKernel 2) : DensityKernel 4 :=
  fun i j => rho ![i 0, i 2] ![j 0, j 2] * rho ![i 1, i 3] ![j 1, j 3]

/-- PDF p.2, (2): coefficients of the bounded unitary U_A tensor U_B. -/
def localUnitaryKernel (p : TwoCopyHomodyneProtocol) : DensityKernel 4 :=
  fun i j => unitaryCoeff p.alice.unitary ![i 0, i 1] ![j 0, j 1] *
    unitaryCoeff p.bob.unitary ![i 2, i 3] ![j 2, j 3]

/-- PDF p.2, (2): the actual premeasurement density kernel. -/
def beforeMeasurement (p : TwoCopyHomodyneProtocol) (rho : DensityKernel 2) : DensityKernel 4 :=
  conjugateKernel (localUnitaryKernel p) (twoCopies rho)

/-- PDF p.1, step (ii): local feedback on the two retained modes, at the
specified pair of real outcomes. Finite products are actual tensor coefficients. -/
def feedbackKernel (p : TwoCopyHomodyneProtocol) (y : Outcome) : DensityKernel 2 :=
  fun i j => unitaryCoeff (p.feedbackAlice y).unitary (fun _ => i 0) (fun _ => j 0) *
    unitaryCoeff (p.feedbackBob y).unitary (fun _ => i 1) (fun _ => j 1)

/-- PDF p.1, step (ii): the actual density after permitted feedback. -/
def afterFeedback (p : TwoCopyHomodyneProtocol) (y : Outcome) (sigma : DensityKernel 2) : DensityKernel 2 :=
  conjugateKernel (feedbackKernel p y) sigma

/-- PDF pp.2--3, (6): explicit retained/discarded quadrature permutation.
block=0 retains A1,B1; block=1 selects A2,B2, with X,P interleaved. -/
def blockQuadrature (block : Fin 2) (i : QuadratureIndex 2) : QuadratureIndex 4 :=
  ((if i.1 = 0 then (if block = 0 then 0 else 1)
    else (if block = 0 then 2 else 3)), i.2)

/-- PDF p.2, (6): arbitrary four-mode covariance blocks after that permutation.
C1=block 0 0, C2=block 1 1, C3=block 0 1. Unlike the frozen
Frontier30.P04.covarianceBlock, this also includes OFF-DIAGONAL blocks. -/
def retainedDiscardedBlock (gamma : Cov 4) (row col : Fin 2) : Cov 2 :=
  gamma.submatrix (blockQuadrature row) (blockQuadrature col)

/-- PDF p.2, Lemma 1, corrected following (7)--(9): this is the SEED
COVARIANCE V_d=D_d^2, with D_d the squeezing amplitude diag(1/d,d,...).
Printed Lemma 1 instead calls D_d the covariance; see MODERATION_NOTES.md. -/
def seedCovariance (d : ℝ) : Cov 2 :=
  Matrix.diagonal (fun i => if i.2 = 0 then d⁻¹ ^ 2 else d ^ 2)

/-- PDF p.2, Lemma 1: pure normalized Gaussian seed. Its means are arbitrary;
V_d is diagonal and hence the two discarded modes have a product seed.
Purity is an actual norm-one vector representation on the full Fock space. -/
def PureSeed (d : ℝ) (seed : DensityKernel 2) : Prop :=
  GaussianWithCovariance seed (seedCovariance d) ∧
    ∃ psi : Hilbert (FockIndex 2), ‖psi‖ = 1 ∧ seed = rankOne psi

/-- PDF pp.2--3: pure seed centered at the measured P values y, with zero X
means. Characteristic functions fix the actual seed density, not its update. -/
def SeedAt (d : ℝ) (y : Outcome) (seed : DensityKernel 2) : Prop :=
  PureSeed d seed ∧ ∀ v : QuadratureIndex 2 → ℝ,
    CharacteristicSummable seed v ∧
    multimodeWeylTrace seed v = covarianceCharacteristicValue (seedCovariance d)
      (fun i => if i.2 = 0 then 0 else y i.1) v

/-- PDF p.2, Lemma 1: incomplete trace Tr_discard[(I tensor seed) rho].
This is the actual pure-state projection on A2,B2, with A1,B1 retained.
The source results establish convergence on their Gaussian domain. -/
def projectedKernel (rho : DensityKernel 4) (seed : DensityKernel 2) : DensityKernel 2 :=
  fun i j => ∑' u : FockIndex 2, ∑' v : FockIndex 2,
    rho (joinModes i u) (joinModes j v) * seed v u

/-- PDF p.2, Lemma 1: guards for every iterated contraction and normalization
series. They are conclusions of the finite-projection theorem, not assumptions
of a Schur covariance rule. -/
def ProjectionSummable (rho : DensityKernel 4) (seed : DensityKernel 2) : Prop :=
  (∀ i j u, Summable (fun v : FockIndex 2 =>
    rho (joinModes i u) (joinModes j v) * seed v u)) ∧
  (∀ i j, Summable (fun u : FockIndex 2 => ∑' v : FockIndex 2,
    rho (joinModes i u) (joinModes j v) * seed v u)) ∧
  Summable (fun i => (projectedKernel rho seed i i).re)

/-- PDF p.2, Lemma 1: probability of a finite normalized rank-one projection. -/
def projectionWeight (rho : DensityKernel 4) (seed : DensityKernel 2) : ℝ :=
  ∑' i, (projectedKernel rho seed i i).re

/-- PDF p.2, Lemma 1: normalized selective output, on the positive-weight
summable domain. Values elsewhere are never used as physical states. -/
def finiteOutput (rho : DensityKernel 4) (seed : DensityKernel 2) : DensityKernel 2 :=
  ((projectionWeight rho seed : ℂ)⁻¹) • projectedKernel rho seed

/-- PDF pp.2--3: ideal P-homodyne conditional density at a specified FINITE
real outcome. It is a trace-norm limit of normalized physical seed projections,
not an entrywise limit or a normalizable infinite-squeezing vector. This contains
no formula for the resulting covariance, nor any entanglement assertion. -/
def HomodyneOutcome (rho : DensityKernel 4) (y : Outcome)
    (sigma : DensityKernel 2) : Prop :=
  IsDensity sigma ∧ ∃ seeds : ℝ → DensityKernel 2,
    (∀ d, 0 < d → SeedAt d y (seeds d) ∧
      ProjectionSummable rho (seeds d) ∧ 0 < projectionWeight rho (seeds d)) ∧
    Tendsto (fun d => traceSize (finiteOutput rho (seeds d) - sigma))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- PDF p.2, (7), corrected seed convention: the finite Schur EXPRESSION.
Identification with the actual selective density is the content of Lemma 1. -/
def finiteSchur (gamma : Cov 4) (d : ℝ) : Cov 2 :=
  retainedDiscardedBlock gamma 0 0 - retainedDiscardedBlock gamma 0 1 *
    (retainedDiscardedBlock gamma 1 1 + seedCovariance d)⁻¹ *
    (retainedDiscardedBlock gamma 0 1).transpose

/-- PDF p.3, (10), corrected: d->0+ for V_d leaves P, so piP=diag(0,1,0,1).
The printed diag(1,0,1,0) corresponds to X instead; local rotations allow either. -/
def momentumProjection : Cov 2 :=
  Matrix.diagonal (fun i => if i.2 = 0 then 0 else 1)

/-- PDF p.3, (10): the Moore--Penrose EXPRESSION. The accepted supportInverse
is the MP inverse on the symmetric PSD matrix piP C2 piP, not a nonsingular
inverse on all four discarded quadratures. Operational identification is Lemma 2. -/
def homodyneCovariance (gamma : Cov 4) : Cov 2 :=
  retainedDiscardedBlock gamma 0 0 - retainedDiscardedBlock gamma 0 1 *
    supportInverse (momentumProjection * retainedDiscardedBlock gamma 1 1 * momentumProjection) *
    (retainedDiscardedBlock gamma 0 1).transpose

/-- PDF p.1: identify the oscillator functions with the ordered Alice,Bob
product basis for the accepted partial-transpose operation. -/
def bipartiteKernel (rho : DensityKernel 2) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun i j => rho ![i.1, i.2] ![j.1, j.2]

/-- PDF pp.1--2: a genuine finite, nonzero partial-transpose trace norm.
This is established in the no-distillation theorem; it is not an input premise. -/
def FinitePartialTranspose (rho : DensityKernel 2) : Prop :=
  IsTraceClass (QAlgorithms.Entanglement.partialTransposeFirst (bipartiteKernel rho)) ∧
    traceSize (QAlgorithms.Entanglement.partialTransposeFirst (bipartiteKernel rho)) ≠ ⊤ ∧
    1 ≤ traceSize (QAlgorithms.Entanglement.partialTransposeFirst (bipartiteKernel rho))

/-- PDF p.1: E_N=log_2 ||rho^{T_A}||_1. Only used together with proved
FinitePartialTranspose conclusions; toReal(infinity)=0 is never used as an
entanglement value. No covariance formula is made the definition of E_N.
The frozen Dependency50.P24.logNegativity uses finite-dimensional Bob
transposition; its trace norm does not cover full oscillator densities. -/
def oscillatorLogNegativity (rho : DensityKernel 2) : ℝ :=
  Real.logb 2 (traceSize (QAlgorithms.Entanglement.partialTransposeFirst (bipartiteKernel rho))).toReal

/-- PDF pp.1--2: two-mode squeezed-vacuum coefficients of strength r>=0,
with no occupation cutoff. This fixes the parameter by tanh(r), not tanh(2r). -/
def squeezedCoefficient (r : ℝ) (i : FockIndex 2) : ℂ :=
  if i 0 = i 1 then ((Real.tanh r ^ i 0 / Real.cosh r : ℝ) : ℂ) else 0

/-- PDF pp.1--2: actual rank-one squeezed-vacuum density coefficients.
Its covariance is initialCovariance(cosh(2r),sinh(2r)); it is not defined by
an entanglement or covariance update hypothesis. -/
def squeezedVacuum (r : ℝ) : DensityKernel 2 :=
  fun i j => squeezedCoefficient r i * star (squeezedCoefficient r j)

/-- PDF p.2, (5): u=(det gamma_A+det gamma_B)/2 for any two-mode matrix. -/
def marginalAverage (gamma : Cov 2) : ℝ :=
  ((modeCovarianceBlock gamma 0 0).det + (modeCovarianceBlock gamma 1 1).det) / 2

/-- PDF p.2, (5): squared least partially transposed symplectic eigenvalue.
Real.sqrt is only interpreted on physical covariances in the theorem below. -/
def sourceF (gamma : Cov 2) : ℝ :=
  let t := marginalAverage gamma - (modeCovarianceBlock gamma 0 1).det
  t - Real.sqrt (t ^ 2 - gamma.det)

/-- PDF p.3, (13): the INNER determinant is square-rooted before subtraction.
This is not the entropy function named f in some accepted Gaussian papers. -/
def sourceG (gamma : Cov 2) : ℝ :=
  (Real.sqrt (marginalAverage gamma) -
    Real.sqrt (marginalAverage gamma - Real.sqrt gamma.det)) ^ 2

/-! Sanity examples for coordinate order, normalization and small parameters. -/

example (n : ℕ) : (identityGaussianUnitary n).symplecticMatrix = 1 := rfl

example (y : Outcome) : (identityProtocol.feedbackAlice y).displacement = 0 := rfl

example (a c : ℝ) : initialCovariance a c (0, 0) (1, 0) = c := by
  norm_num [initialCovariance, standardFormCovariance]

example (a c : ℝ) : initialCovariance a c (0, 1) (1, 1) = -c := by
  norm_num [initialCovariance, standardFormCovariance]

example (keep discard : FockIndex 2) : joinModes keep discard 2 = keep 1 := rfl

example : blockQuadrature 0 (1, 1) = (2, 1) := rfl

example : blockQuadrature 1 (1, 0) = (3, 0) := rfl

example : seedCovariance 1 = (1 : Cov 2) := by
  ext i j
  simp [seedCovariance, Matrix.diagonal, Matrix.one_apply]

example : momentumProjection (0, 0) (0, 0) = 0 := by
  norm_num [momentumProjection]

example : momentumProjection (1, 1) (1, 1) = 1 := by
  norm_num [momentumProjection]

example (seed : DensityKernel 2) : projectedKernel 0 seed = 0 := by
  funext i j
  simp [projectedKernel]

example (rho : DensityKernel 2) (i j k l : ℕ) :
    QAlgorithms.Entanglement.partialTransposeFirst (bipartiteKernel rho) (i, j) (k, l) = rho ![k, j] ![i, l] := rfl

example : squeezedVacuum 0 (fun _ => 0) (fun _ => 0) = 1 := by
  norm_num [squeezedVacuum, squeezedCoefficient]

end QAlgorithms.Papers.Independent.Renew46.P39


