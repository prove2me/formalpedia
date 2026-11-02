-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P71
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P71
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:57:14.818801+00:00
-- url     : https://prove2.me/theorems/460d4250-51d8-4eb4-b7ae-fafe6011044a
-- title:
--   Definitions for Classical Shadow Tomography with Locally Scrambled Quantum Dynamics
-- statement:
--   The objects the formalized statements of *Classical Shadow Tomography with Locally Scrambled Quantum Dynamics* (arXiv:2107.04817) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `localMatrix`: Tensor product of local unitaries, with no permutation of sites.
--   - `localConj`: Conjugating an operator by a local basis change, PDF p.3 Eq.(5).
--   - `ProjectiveEnsemble`: A measurement ensemble is fixed independently of the unknown state, PDF pp.1–3.
--   - `raw`: Raw rank-one snapshot U†|b><b|U, PDF p.2 Eq.(1).
--   - `prior`: Prior law: independent uniform computational outcome, PDF p.3 Eq.(2).
--   - `posteriorOf`: Posterior snapshot law with the Born likelihood D Tr(S rho), PDF Eqs.(1)–(3).
--   - `partialTrace`: Partial trace in region A. No density-matrix normalization is applied to X, PDF p.3 Eq.(8), p.6 Eq.(29), and Appendix B p.19.
--   - `reducedSnapshot`: X_A: partial trace on the complement, then normalized identity there, in original site order; includes empty/full regions, PDF p.3 and p.18 Appendix A.
--   - `partialPurity`: Unnormalized partial purity Tr((Tr_complement X)^2), PDF Eq.(8).
--   - `feature`: Second entanglement feature, PDF p.3 Eq.(8).
--   - `channelCoefficient`: Coefficients of the constructed measurement channel, PDF p.3 Eq.(3). Integration precedes linear extension, so the map acts on every complex operator.
--   - `snapshotMeasurementMap`: Measurement channel D E[S Tr(S X)], PDF p.3 Eq.(3).
--   - `Complete`: Tomographic completeness, PDF p.3 preceding Eq.(9).
--   - `snapshotInverse`: The actual inverse of the constructed measurement channel; no reconstruction certificate is an input, PDF p.3 Eq.(9).
--   - `LocallyScrambled`: Exact local conjugation invariance of the prior law, PDF p.3 Eq.(5).
--   - `regionalWg`: Two-copy regional Weingarten coefficient, PDF p.3 Eq.(7).
--   - `fusion`: Fusion coefficient, PDF p.4 Eq.(11), p.22 Eq.(C9). Negative exponents use reciprocals, not truncated natural subtraction.
--   - `CoefficientSystem`: The coefficient solve, PDF p.4 Eq.(12), not an assumed inverse identity.
--   - `efReconstruct`: EF reconstruction from coefficients, PDF pp.3–4 Eq.(9). Signed coefficients are allowed; complete positivity is not required of reconstruction.
--   - `snapshotMoment`: Moments of the prior snapshot law, PDF p.12 Eq.(43).
--   - `SnapshotPolynomialIntegrable`: Polynomial integrability, stated as a conclusion for the constructed ensembles. This prevents default-zero Bochner integrals from supplying the identities.
--   - `shadowEstimate`: Single-shot linear observable estimator, PDF p.4 Eq.(13).
--   - `secondMoment`: State-dependent second moment Q, PDF p.4 Eq.(14).
--   - `shotVariance`: Single-shot variance, PDF p.4 Eq.(14).
--   - `snapshotSampleLaw`: Independent snapshots on identical copies, PDF p.5 preceding Eq.(18).
--   - `shadowSampleMean`: Arithmetic mean of m single-shot predictions, PDF p.5.
--   - `averagedSecondMoment`: Local-Haar state average of Q, PDF p.5 Eq.(20). H is a normalized left-invariant measure on the compact local group, hence Haar.
--   - `observableFeature`: Observable EF from its local Haar orbit, PDF pp.5,19 Eq.(22), (B4).
--   - `varianceCoefficient`: Coefficient in Eq.(22). The signed power multiplies, and the exponent of d is an integer difference expressed by division, PDF pp.5,19.
--   - `Permutations`: The source product group (S_t)^N, never S_(tN), PDF p.4.
--   - `copyPermutation`: Copy permutations act independently at each original site, PDF Eq.(17).
--   - `wgThree`: Unitary three-copy Weingarten function in character form. At d=2, the three-row partition is omitted: this is the Moore–Penrose/spectral extension, not the inverse of the singular permutation Gram matrix, PDF p.4 Eq.(15).
--   - `productWgThree`: Three-copy coefficients factor over sites, PDF p.4 Eq.(15).
--   - `featureThree`: Third EF; individual permutation traces can be complex, PDF p.5 Eq.(17).
--   - `observableThree`: Generalized operator term d^N Tr((R[O] ⊗ R[O] ⊗ rho) chi_g), Eq.(16).
--   - `ToyFeature`: Toy-model feature vector (1,w,w,1), PDF p.5 Eq.(24).
--   - `toyCoefficients`: Two-qudit reconstruction coefficients, source order empty, first, second, full, PDF p.5 Eq.(26).
--   - `oneSiteInverse`: Local inverse superoperator, Eq.(27) extended linearly to arbitrary inputs.
--   - `twoSiteProduct`: Product input in original site order, used only for the Eq.(27) product-input specialization, PDF p.6.
--   - `localityNumerator`: Sum of the two unnormalized partial purities. This avoids dividing by Tr(O²), so the undivided Eq.(31) also includes O=0.
--   - `hsSquare`: Hilbert–Schmidt square for Hermitian O.
--   - `localObservable`: Local observable A ⊗ I, PDF p.6 Eq.(32).
--   - `gueOperator`: Trace-removed GUE, constructed from independent standard real Gaussians. Overall GUE scaling cancels from Eq.(34); diagonal and off-diagonal variances have the invariant GUE ratio. PDF p.6, interpreted in ensemble expectation.
--   - `gueCoordinates`: Independent Gaussian coordinates for the trace-removed GUE.
--   - `twirled`: Local twirling of a snapshot law, joint in V and snapshot, PDF p.12 Eq.(43).
--   - `framePotential`: Second frame potential with two independent snapshots, PDF p.12 Eq.(42).
--   - `frameGap`: Frame-potential gap, PDF p.12 Eq.(45).
--   - `localMomentAction`: Moment twirl of local-unitary law; t-design means equality of these superoperators for every X, PDF pp.2,11 (Clifford at the 3-design level).
--   - `IsLocalDesign`: Design equality at the specified moment order, not equality of laws.
--   - `sandwichRaw`: The prior snapshot from the fixed sandwich L U0 R, PDF p.11.
--   - `sandwichPrior`: Independent end factors and uniform prior b, with U0 fixed before rho.
--   - `fusionSite`: Scalar site tensor with axes (a,b,c); the displayed Eq.(C10) is a 2x2 array of 2-vectors, PDF p.22.
--   - `DualTableau`: Signed dual simulation tableau: stabilizers T and destabilizers D, with D_i anticommuting precisely with T_i. Appendix C.2 PDF pp.20–21.
--   - `tableauInput`: Input bits for the standard tableau postprocessor; header n, stabilizers, duals, then the signed Pauli. Preprocessing an arbitrary generator list is not charged as free work. PDF p.21 quadratic scalar routine.
--   - `pauliFactor`: Bond-one local factors in Eq.(C7), including identity Paulis.
--   - `scalarCode`: Signed scalar encoding: zero=0, +1=1, -1=2. It is a specification, not a primitive machine instruction for a dense trace.
--   - `tableauRecord`: Serialized bond-one MPS record: one scalar code and exactly two entries per site. Its target is computed by the charged machine in Proposition I.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, https://arxiv.org/abs/2107.04817v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Stabilizer
import Definitions.Def_QAlgorithms_Defs_ClassicalDecoderMachines
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Defs_LocalHamiltonian

/-!
Statements from Hu–Choi–You, arXiv:2107.04817v4. All page numbers are PDF pages.
Paper-specific definitions below are local to this paper. Configuration and
operator carriers and matrix tensor powers reuse pinned accepted definitions. In particular, a squared shadow
norm here is a second moment, never a supremum over input states.
-/

noncomputable section

open MeasureTheory
open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Intakethird100.P71

attribute [local instance] Classical.propDecidable

/- Computational configurations, PDF pp.2–3. -/
local notation "Config" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Config (P := Fin n) (fun _ => d)

/- Operators in the original site order, PDF p.3. -/
local notation "Op" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Op (Config n d)

/-- Continuous extended norm for the finite operator spaces in PDF pp.2–3.
Use the nested function-space instance underlying the elementwise matrix norm
and product topology, including tensor-copy registers. This is local instance
plumbing, not an extra regularity hypothesis on a snapshot ensemble. -/
local instance matrixContinuousENorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ContinuousENorm (Matrix ι κ ℂ) :=
  inferInstanceAs (ContinuousENorm (ι → κ → ℂ))

/-- Sanity: the snapshot operator carrier has a continuous extended norm. -/
example {n d : ℕ} : ContinuousENorm (Op n d) := inferInstance

/-- Sanity: the accepted tensor-power output carrier has the same instance. -/
example {n d t : ℕ} : ContinuousENorm
    (QAlgorithms.Papers.Independent.Information100.P63.Mat (Fin t → Config n d)) :=
  inferInstance

/-- Borel sigma algebra on finite-dimensional snapshot operators, PDF pp.2–3.
The prior pushforward and Born posterior use this measurable structure. -/
instance operatorMeasurable {n d : ℕ} : MeasurableSpace (Op n d) := borel _

/-- The operator measurable structure is the Borel structure, PDF pp.2–3. -/
instance operatorBorel {n d : ℕ} : BorelSpace (Op n d) := ⟨rfl⟩

/- Global measurement unitaries, PDF p.2. -/
local notation "Unitary" n:max d:max => Matrix.unitaryGroup (Config n d) ℂ

/-- The Borel sigma algebra on any finite unitary group, PDF pp.2–3. -/
instance unitaryMeasurable {ι : Type*} [Fintype ι] [DecidableEq ι] :
    MeasurableSpace (Matrix.unitaryGroup ι ℂ) := borel _

/-- The unitary ensemble carries its Borel measurable structure. -/
instance unitaryBorel {ι : Type*} [Fintype ι] [DecidableEq ι] :
    BorelSpace (Matrix.unitaryGroup ι ℂ) := ⟨rfl⟩

/- Local basis transformations, PDF p.3 Eq.(5). -/
local notation "Local" n:max d:max => Fin n → Matrix.unitaryGroup (Fin d) ℂ

/-- Tensor product of local unitaries, with no permutation of sites. -/
def localMatrix {n d : ℕ} (V : Local n d) : Op n d :=
  Matrix.of fun x y => ∏ i, (V i : Matrix (Fin d) (Fin d) ℂ) (x i) (y i)

/-- Conjugating an operator by a local basis change, PDF p.3 Eq.(5). -/
def localConj {n d : ℕ} (V : Local n d) (X : Op n d) : Op n d :=
  (localMatrix V)ᴴ * X * localMatrix V

/-- A measurement ensemble is fixed independently of the unknown state, PDF pp.1–3. -/
structure ProjectiveEnsemble (n d : ℕ) where
  law : Measure (Unitary n d)
  probability : IsProbabilityMeasure law

/-- Raw rank-one snapshot U†|b><b|U, PDF p.2 Eq.(1). -/
def raw {n d : ℕ} (U : Unitary n d) (b : Config n d) : Op n d :=
  (U : Op n d)ᴴ * Matrix.single b b 1 * (U : Op n d)

/-- Prior law: independent uniform computational outcome, PDF p.3 Eq.(2). -/
def prior {n d : ℕ} (E : ProjectiveEnsemble n d) : Measure (Op n d) :=
  (ENNReal.ofReal ((d : ℝ) ^ n)⁻¹) • ∑ b : Config n d, E.law.map (fun U => raw U b)

/-- Posterior snapshot law with the Born likelihood D Tr(S rho), PDF Eqs.(1)–(3). -/
def posteriorOf {n d : ℕ} (nu : Measure (Op n d)) (rho : Op n d) : Measure (Op n d) :=
  nu.withDensity (fun S => ENNReal.ofReal (((d : ℝ) ^ n) * (S * rho).trace.re))

/-- Partial trace in region A. No density-matrix normalization is applied to X,
PDF p.3 Eq.(8), p.6 Eq.(29), and Appendix B p.19. -/
def partialTrace {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset (Fin n)) (X : Matrix (Fin n → α) (Fin n → α) ℂ) :
    Matrix (A → α) (A → α) ℂ :=
  Matrix.of fun x y => ∑ z : (Aᶜ : Finset (Fin n)) → α,
    X (fun i => if h : i ∈ A then x ⟨i,h⟩ else z ⟨i,by simpa using h⟩)
      (fun i => if h : i ∈ A then y ⟨i,h⟩ else z ⟨i,by simpa using h⟩)

/-- X_A: partial trace on the complement, then normalized identity there, in
original site order; includes empty/full regions, PDF p.3 and p.18 Appendix A. -/
def reducedSnapshot {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset (Fin n)) (X : Matrix (Fin n → α) (Fin n → α) ℂ) :
    Matrix (Fin n → α) (Fin n → α) ℂ :=
  Matrix.of fun x y =>
    if ∀ i, i ∉ A → x i = y i then
      partialTrace A X (fun i => x i) (fun i => y i) /
        ((Fintype.card α : ℂ) ^ (n - A.card))
    else 0

/-- Unnormalized partial purity Tr((Tr_complement X)^2), PDF Eq.(8). -/
def partialPurity {n d : ℕ} (A : Finset (Fin n)) (X : Op n d) : ℝ :=
  ((partialTrace A X) * (partialTrace A X)).trace.re

/-- Second entanglement feature, PDF p.3 Eq.(8). -/
def feature {n d : ℕ} (nu : Measure (Op n d)) (A : Finset (Fin n)) : ℝ :=
  ∫ S, partialPurity A S ∂nu

/-- Coefficients of the constructed measurement channel, PDF p.3 Eq.(3).
Integration precedes linear extension, so the map acts on every complex operator. -/
def channelCoefficient {n d : ℕ} (nu : Measure (Op n d))
    (i j k l : Config n d) : ℂ :=
  ∫ S, ((d : ℂ) ^ n) * S i j * S l k ∂nu

/-- Measurement channel D E[S Tr(S X)], PDF p.3 Eq.(3). -/
def snapshotMeasurementMap {n d : ℕ} (nu : Measure (Op n d)) : Op n d →ₗ[ℂ] Op n d where
  toFun X := Matrix.of fun i j => ∑ k, ∑ l, channelCoefficient nu i j k l * X k l
  map_add' X Y := by ext i j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a X := by ext i j; simp [Finset.mul_sum, mul_left_comm]

/-- Tomographic completeness, PDF p.3 preceding Eq.(9). -/
def Complete {n d : ℕ} (nu : Measure (Op n d)) : Prop :=
  Function.Injective (snapshotMeasurementMap nu)

/-- The actual inverse of the constructed measurement channel; no reconstruction
certificate is an input, PDF p.3 Eq.(9). -/
def snapshotInverse {n d : ℕ} (nu : Measure (Op n d)) (h : Complete nu) : Op n d ≃ₗ[ℂ] Op n d :=
  (LinearEquiv.ofBijective (snapshotMeasurementMap nu)
    ⟨(show Function.Injective (snapshotMeasurementMap nu) from h),
      LinearMap.injective_iff_surjective.mp
        (show Function.Injective (snapshotMeasurementMap nu) from h)⟩).symm

/-- Exact local conjugation invariance of the prior law, PDF p.3 Eq.(5). -/
def LocallyScrambled {n d : ℕ} (nu : Measure (Op n d)) : Prop :=
  ∀ V : Local n d, nu.map (localConj V) = nu

/-- Two-copy regional Weingarten coefficient, PDF p.3 Eq.(7). -/
def regionalWg (n d : ℕ) (A B : Finset (Fin n)) : ℝ :=
  ((d : ℝ)^2 - 1)⁻¹ ^ n * (-1 / (d : ℝ)) ^ (symmDiff A B).card

/-- Fusion coefficient, PDF p.4 Eq.(11), p.22 Eq.(C9).
Negative exponents use reciprocals, not truncated natural subtraction. -/
def fusion (n d : ℕ) (A B C : Finset (Fin n)) : ℝ :=
  ((d : ℝ)^3 / ((d : ℝ)^2 - 1)) ^ n *
    ∑ D : Finset (Fin n), if B = A ∩ D then
      ((d : ℝ) ^ D.card)⁻¹ * (-1 / (d : ℝ)) ^ (symmDiff C D).card else 0

/-- The coefficient solve, PDF p.4 Eq.(12), not an assumed inverse identity. -/
def CoefficientSystem {n d : ℕ} (nu : Measure (Op n d))
    (r : Finset (Fin n) → ℝ) : Prop :=
  ∀ B : Finset (Fin n),
    (∑ A : Finset (Fin n), ∑ C : Finset (Fin n),
      r A * fusion n d A B C * feature nu C) = if B = Finset.univ then 1 else 0

/-- EF reconstruction from coefficients, PDF pp.3–4 Eq.(9). Signed coefficients
are allowed; complete positivity is not required of reconstruction. -/
def efReconstruct {n d : ℕ} (r : Finset (Fin n) → ℝ) (X : Op n d) : Op n d :=
  ((d : ℂ) ^ n) • ∑ A : Finset (Fin n), (r A : ℂ) • reducedSnapshot A X

-- The accepted matrix tensor power has exactly the copy-first coordinate formula.
open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- Moments of the prior snapshot law, PDF p.12 Eq.(43). -/
def snapshotMoment {n d : ℕ} (nu : Measure (Op n d)) (t : ℕ) :=
  ∫ S, tensorPower t S ∂nu

/-- Polynomial integrability, stated as a conclusion for the constructed ensembles.
This prevents default-zero Bochner integrals from supplying the identities. -/
def SnapshotPolynomialIntegrable {n d : ℕ} (nu : Measure (Op n d)) : Prop :=
  (∀ t : ℕ, Integrable (fun S => tensorPower t S) nu) ∧
  (∀ X : Op n d, Integrable (fun S => (S * X).trace • S) nu) ∧
  (∀ X Y : Op n d, Integrable (fun S => (X * S).trace.re ^ 2 * (S * Y).trace.re) nu)

/-- Single-shot linear observable estimator, PDF p.4 Eq.(13). -/
def shadowEstimate {n d : ℕ} (nu : Measure (Op n d)) (h : Complete nu)
    (O S : Op n d) : ℝ := (O * snapshotInverse nu h S).trace.re

/-- State-dependent second moment Q, PDF p.4 Eq.(14). -/
def secondMoment {n d : ℕ} (nu : Measure (Op n d)) (h : Complete nu)
    (rho O : Op n d) : ℝ :=
  ∫ S, shadowEstimate nu h O S ^ 2 ∂posteriorOf nu rho

/-- Single-shot variance, PDF p.4 Eq.(14). -/
def shotVariance {n d : ℕ} (nu : Measure (Op n d)) (h : Complete nu)
    (rho O : Op n d) : ℝ :=
  secondMoment nu h rho O - (∫ S, shadowEstimate nu h O S ∂posteriorOf nu rho) ^ 2

/-- Independent snapshots on identical copies, PDF p.5 preceding Eq.(18). -/
def snapshotSampleLaw {n d : ℕ} (nu : Measure (Op n d)) (rho : Op n d) (m : ℕ) :
    Measure (Fin m → Op n d) := Measure.pi fun _ => posteriorOf nu rho

/-- Arithmetic mean of m single-shot predictions, PDF p.5. -/
def shadowSampleMean {n d m : ℕ} (nu : Measure (Op n d)) (h : Complete nu)
    (O : Op n d) (shots : Fin m → Op n d) : ℝ :=
  (m : ℝ)⁻¹ * ∑ k, shadowEstimate nu h O (shots k)

/-- Local-Haar state average of Q, PDF p.5 Eq.(20).
H is a normalized left-invariant measure on the compact local group, hence Haar. -/
def averagedSecondMoment {n d : ℕ} (H : Measure (Local n d))
    (nu : Measure (Op n d)) (h : Complete nu) (rho O : Op n d) : ℝ :=
  ∫ V, secondMoment nu h (localConj V rho) O ∂H

/-- Observable EF from its local Haar orbit, PDF pp.5,19 Eq.(22), (B4). -/
def observableFeature {n d : ℕ} (H : Measure (Local n d))
    (O : Op n d) (A : Finset (Fin n)) : ℝ :=
  ∫ V, partialPurity A (localConj V O) ∂H

/-- Coefficient in Eq.(22). The signed power multiplies, and the exponent of d
is an integer difference expressed by division, PDF pp.5,19. -/
def varianceCoefficient {n : ℕ} (d : ℕ) (r : Finset (Fin n) → ℝ)
    (A B C D : Finset (Fin n)) : ℝ :=
  r A * r B * ((d : ℝ)^2 / ((d : ℝ)^2 - 1)) ^ n *
    ((d : ℝ) ^ (A ∩ B ∩ C).card / (d : ℝ) ^ C.card) *
    (-1 / (d : ℝ)) ^ (symmDiff C D).card

/-- The source product group (S_t)^N, never S_(tN), PDF p.4. -/
abbrev Permutations (n t : ℕ) := Fin n → Equiv.Perm (Fin t)

/-- Copy permutations act independently at each original site, PDF Eq.(17). -/
def copyPermutation {n d t : ℕ} (g : Permutations n t) :
    Matrix (Fin t → Config n d) (Fin t → Config n d) ℂ :=
  Matrix.of fun x y => if ∀ i k, x k i = y (g i k) i then 1 else 0

/-- Unitary three-copy Weingarten function in character form. At d=2, the
three-row partition is omitted: this is the Moore–Penrose/spectral extension,
not the inverse of the singular permutation Gram matrix, PDF p.4 Eq.(15). -/
def wgThree (d : ℕ) (p : Equiv.Perm (Fin 3)) : ℝ :=
  let a := (d : ℝ)
  let chi := ((Finset.univ.filter fun i : Fin 3 => p i = i).card : ℝ) - 1
  (1 / 6) * ((a * (a+1) * (a+2))⁻¹ +
    2 * chi / (a * (a+1) * (a-1)) +
    if 3 ≤ d then (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℝ) /
      (a * (a-1) * (a-2)) else 0)

/-- Three-copy coefficients factor over sites, PDF p.4 Eq.(15). -/
def productWgThree {n : ℕ} (d : ℕ) (g h : Permutations n 3) : ℝ :=
  ∏ i, wgThree d (g i * (h i)⁻¹)

/-- Third EF; individual permutation traces can be complex, PDF p.5 Eq.(17). -/
def featureThree {n d : ℕ} (nu : Measure (Op n d)) (h : Permutations n 3) : ℂ :=
  ∫ S, (tensorPower 3 S * copyPermutation h).trace ∂nu

/-- Generalized operator term d^N Tr((R[O] ⊗ R[O] ⊗ rho) chi_g), Eq.(16). -/
def observableThree {n d : ℕ} (nu : Measure (Op n d)) (hc : Complete nu)
    (rho O : Op n d) (g : Permutations n 3) : ℂ :=
  let R := snapshotInverse nu hc O
  let T : Matrix (Fin 3 → Config n d) (Fin 3 → Config n d) ℂ :=
    Matrix.of fun x y => R (x 0) (y 0) * R (x 1) (y 1) * rho (x 2) (y 2)
  ((d : ℂ)^n) * (T * copyPermutation g).trace

/-- Toy-model feature vector (1,w,w,1), PDF p.5 Eq.(24). -/
def ToyFeature {d : ℕ} (nu : Measure (Op 2 d)) (w : ℝ) : Prop :=
  ∀ A : Finset (Fin 2), feature nu A = if A.card = 1 then w else 1

/-- Two-qudit reconstruction coefficients, source order empty, first, second,
full, PDF p.5 Eq.(26). -/
def toyCoefficients (d : ℕ) (w : ℝ) (A : Finset (Fin 2)) : ℝ :=
  let a := (d : ℝ)
  if A.card = 0 then (a^3*w - 3*a^2 + 3*a*w - 2*w^2 + 1) /
    ((a*w-1)*(a^2-2*a*w+1))
  else if A.card = 1 then (-a^4*w + 2*a^3 - 2*a + w) /
    (a*(a*w-1)*(a^2-2*a*w+1))
  else (a^2-1)^2 / (a^2*(a^2-2*a*w+1))

/-- Local inverse superoperator, Eq.(27) extended linearly to arbitrary inputs. -/
def oneSiteInverse (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ((d : ℂ)+1) • X - X.trace • 1

/-- Product input in original site order, used only for the Eq.(27)
product-input specialization, PDF p.6. -/
def twoSiteProduct {d : ℕ} (X Y : Matrix (Fin d) (Fin d) ℂ) : Op 2 d :=
  Matrix.of fun x y => X (x 0) (y 0) * Y (x 1) (y 1)

/-- Sum of the two unnormalized partial purities. This avoids dividing by
Tr(O²), so the undivided Eq.(31) also includes O=0. -/
def localityNumerator {d : ℕ} (O : Op 2 d) : ℝ :=
  partialPurity {0} O + partialPurity {1} O

/-- Hilbert–Schmidt square for Hermitian O. -/
def hsSquare {n d : ℕ} (O : Op n d) : ℝ := (O * O).trace.re

/-- Local observable A ⊗ I, PDF p.6 Eq.(32). -/
def localObservable {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Op 2 d :=
  twoSiteProduct A 1

/-- Trace-removed GUE, constructed from independent standard real Gaussians.
Overall GUE scaling cancels from Eq.(34); diagonal and off-diagonal variances
have the invariant GUE ratio. PDF p.6, interpreted in ensemble expectation. -/
def gueOperator (d : ℕ) (z : Config 2 d × Config 2 d × Bool → ℝ) : Op 2 d :=
  let Z : Op 2 d := Matrix.of fun i j => (z (i,j,false) : ℂ) + Complex.I * z (i,j,true)
  let G := (2 : ℂ)⁻¹ • (Z + Zᴴ)
  G - (G.trace / ((d : ℂ)^2)) • 1

/-- Independent Gaussian coordinates for the trace-removed GUE. -/
def gueCoordinates (d : ℕ) : Measure (Config 2 d × Config 2 d × Bool → ℝ) :=
  Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1

/-- Local twirling of a snapshot law, joint in V and snapshot, PDF p.12 Eq.(43). -/
def twirled {n d : ℕ} (H : Measure (Local n d)) (nu : Measure (Op n d)) : Measure (Op n d) :=
  (H.prod nu).map (fun p => localConj p.1 p.2)

/-- Second frame potential with two independent snapshots, PDF p.12 Eq.(42). -/
def framePotential {n d : ℕ} (nu : Measure (Op n d)) : ℝ :=
  ∫ p, (p.1 * p.2).trace.re ^ 2 ∂nu.prod nu

/-- Frame-potential gap, PDF p.12 Eq.(45). -/
def frameGap {n d : ℕ} (H : Measure (Local n d)) (nu : Measure (Op n d)) : ℝ :=
  framePotential nu - framePotential (twirled H nu)

/-- Moment twirl of local-unitary law; t-design means equality of these
superoperators for every X, PDF pp.2,11 (Clifford at the 3-design level). -/
def localMomentAction {n d : ℕ} (mu : Measure (Local n d)) (t : ℕ)
    (X : Matrix (Fin t → Config n d) (Fin t → Config n d) ℂ) :=
  ∫ V, (tensorPower t (localMatrix V))ᴴ * X * tensorPower t (localMatrix V) ∂mu

/-- Design equality at the specified moment order, not equality of laws. -/
def IsLocalDesign {n d : ℕ} (mu H : Measure (Local n d)) (t : ℕ) : Prop :=
  ∀ X, localMomentAction mu t X = localMomentAction H t X

/-- The prior snapshot from the fixed sandwich L U0 R, PDF p.11. -/
def sandwichRaw {n d : ℕ} (U0 : Unitary n d) (L R : Local n d) (b : Config n d) : Op n d :=
  let U := localMatrix L * (U0 : Op n d) * localMatrix R
  Uᴴ * Matrix.single b b 1 * U

/-- Independent end factors and uniform prior b, with U0 fixed before rho. -/
def sandwichPrior {n d : ℕ} (U0 : Unitary n d) (muL muR : Measure (Local n d)) :
    Measure (Op n d) :=
  ENNReal.ofReal ((d : ℝ)^n)⁻¹ • ∑ b : Config n d,
    (muL.prod muR).map (fun p => sandwichRaw U0 p.1 p.2 b)

/-- Scalar site tensor with axes (a,b,c); the displayed Eq.(C10) is a 2x2
array of 2-vectors, PDF p.22. -/
def fusionSite (d : ℕ) (a b c : Bool) : ℝ :=
  if a then
    if b then if c then (d : ℝ)^2 / ((d : ℝ)^2-1) else -(d : ℝ) / ((d : ℝ)^2-1)
    else if c then -(d : ℝ)^2 / ((d : ℝ)^2-1) else (d : ℝ)^3 / ((d : ℝ)^2-1)
  else if b then 0 else if c then 0 else d

/-- Signed dual simulation tableau: stabilizers T and destabilizers D, with
D_i anticommuting precisely with T_i. Appendix C.2 PDF pp.20–21. -/
def DualTableau {n : ℕ} (T D : QAlgorithms.Stabilizer.Tableau n) : Prop :=
  QAlgorithms.Stabilizer.IsValidTableau T ∧ QAlgorithms.Stabilizer.IsValidTableau D ∧
  ∀ i j, (D i).toMatrix * (T j).toMatrix =
    (if i = j then (-1 : ℂ) else 1) • ((T j).toMatrix * (D i).toMatrix)

/-- Input bits for the standard tableau postprocessor; header n, stabilizers,
duals, then the signed Pauli. Preprocessing an arbitrary generator list is not
charged as free work. PDF p.21 quadratic scalar routine. -/
def tableauInput {n : ℕ} (T D : QAlgorithms.Stabilizer.Tableau n)
    (O : QAlgorithms.Stabilizer.PauliString n) : List ℕ :=
  [n] ++ ((QAlgorithms.Stabilizer.encodeTableau T ++ QAlgorithms.Stabilizer.encodeTableau D ++
    QAlgorithms.Stabilizer.encPhase O.phase ++
    (List.ofFn fun i => QAlgorithms.Stabilizer.encPauli (O.ops i)).flatten).map Bool.toNat)

/-- Bond-one local factors in Eq.(C7), including identity Paulis. -/
def pauliFactor {n : ℕ} (O : QAlgorithms.Stabilizer.PauliString n) (i : Fin n) (a : Bool) : ℂ :=
  if O.ops i = .I ∨ a = true then 1 else 0

/-- Signed scalar encoding: zero=0, +1=1, -1=2. It is a specification, not a
primitive machine instruction for a dense trace. -/
def scalarCode (z : ℂ) : ℕ := if z = 1 then 1 else if z = -1 then 2 else 0

/-- Serialized bond-one MPS record: one scalar code and exactly two entries
per site. Its target is computed by the charged machine in Proposition I. -/
def tableauRecord {n : ℕ} (T : QAlgorithms.Stabilizer.Tableau n)
    (O : QAlgorithms.Stabilizer.PauliString n) : List ℕ :=
  [scalarCode (O.toMatrix * QAlgorithms.Stabilizer.tableauProjector T).trace] ++
    (List.ofFn fun i => [if O.ops i = .I then 1 else 0, 1]).flatten

/-- Sanity: partial trace/reduction of zero is zero (normalization cannot create mass). -/
example {n d : ℕ} (A : Finset (Fin n)) : reducedSnapshot A (0 : Op n d) = 0 := by
  ext x y
  simp [reducedSnapshot, partialTrace]

/-- Sanity: the constructed channel maps zero to zero. -/
example {n d : ℕ} (nu : Measure (Op n d)) : snapshotMeasurementMap nu 0 = 0 := map_zero _

/-- Sanity: the scalar-register fusion coefficient is one. -/
example (d : ℕ) : fusion 0 d ∅ ∅ ∅ = 1 := by
  simp [fusion, Finset.eq_empty_of_isEmpty]

/-- Sanity: the two branches of the site tensor agree with the displayed
upper-left 2-vector (d,0), without a nonzero denominator assumption. -/
example (d : ℕ) : fusionSite d false false false = d ∧
    fusionSite d false false true = 0 := by simp [fusionSite]

/-- Sanity: no Gaussian input produces a spurious nonzero operator at zero. -/
example (d : ℕ) : gueOperator d (fun _ => 0) = 0 := by
  have hz : (Matrix.of (fun i j : Config 2 d =>
      ((0 : ℝ) : ℂ) + Complex.I * (0 : ℝ))) = (0 : Op 2 d) := by
    ext i j
    simp
  unfold gueOperator
  rw [hz]
  simp

/-- Sanity: Eq.(C7)'s included-site factor is one, even for a zero MPS scalar. -/
example {n : ℕ} (O : QAlgorithms.Stabilizer.PauliString n) (i : Fin n) :
    pauliFactor O i true = 1 := by simp [pauliFactor]

end QAlgorithms.Papers.Independent.Intakethird100.P71


