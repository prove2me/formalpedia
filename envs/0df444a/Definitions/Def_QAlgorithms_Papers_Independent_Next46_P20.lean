-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20
-- name    : QAlgorithms_Papers_Independent_Next46_P20
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T15:13:07.574961+00:00
-- url     : https://prove2.me/theorems/8dbfd3d6-1f15-47c0-bc71-f6b6d6a61649
-- title:
--   Definitions for Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations
-- statement:
--   The objects the formalized statements of *Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations* (arXiv:1209.1850) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `phasePosition`: PDF p.6, §1.2: the x coordinates of the accepted interleaved phase carrier.
--   - `phaseMomentum`: PDF p.6, §1.2: the p coordinates of the accepted interleaved phase carrier.
--   - `phasePoint`: PDF p.6, §1.2: assemble (x,p) in the accepted interleaved real coordinates. This is a coordinate constructor, not a second phase-space carrier.
--   - `DoublePhase`: PDF p.6, §1.2: double-phase coordinates ordered (x,p,xi_x,xi_p).
--   - `ConfigurationL2`: PDF p.6: the configuration Hilbert space, including its a.e. quotient.
--   - `PhaseL2`: PDF p.6: the phase Hilbert space with coordinate Lebesgue measure.
--   - `RealizesTensor`: PDF p.6, (2.1): characterize the tensor map by its actual a.e. formula. This property specifies no norm or spectral conclusion.
--   - `tensorEmbedding`: PDF p.6, (2.1): canonical continuous linear realization of psi tensor conjugate(chi), selected solely by its pointwise a.e. formula. The zero branch totalizes the definition; tensor_unitary_equivalence explicitly asserts realization for all unit windows, without a realizability hypothesis.
--   - `windowSpace`: PDF pp.7–8: H_chi is the actual range, rather than the whole phase L2.
--   - `transportGraph`: PDF pp.8–9, Definition 2.7: the graph of the transported unbounded operator. Both input and output are transported; no domain is extended to all of H_chi.
--   - `graphSymmetric`: PDF p.9: symmetry on the operator domain; density is not part of symmetry.
--   - `adjointGraphOn`: PDF p.9, (2.6): adjoint graph in the specified ambient Hilbert subspace. Inner products are conjugate-linear in the first entry.
--   - `graphSelfAdjointOn`: PDF p.9: self-adjointness means dense domain in the actual Hilbert space and equality with the adjoint graph. Nondense adjoints never get a junk value.
--   - `graphResolventOn`: PDF p.10, Theorem 2.10: the unbounded resolvent requires an everywhere-defined bounded inverse of A-lambda I on the ambient Hilbert subspace. The second identity includes every point of the original graph and gives injectivity.
--   - `graphSpectrumOn`: PDF p.10: the full spectrum, including continuous and residual parts.
--   - `strongSolution`: PDF pp.10–11: strong Schrodinger solution in the Hilbert norm. The graph clause forces membership of the domain at every real time.
--   - `positionGraph`: PDF p.9, Remark 2.8: maximal multiplication graph, with a.e. equality.
--   - `momentumGraph`: PDF p.9, Remark 2.8: the maximal L2 graph of -i times a weak directional derivative. Pairing with a Schwartz test is complex-linear, so integration by parts gives +i times the derivative of the test. No derivative of chi is used.
--   - `doubleSigma`: PDF pp.5–6: the double-phase symplectic form sigma_x plus sigma_p.
--   - `classicalS`: PDF p.5, (1.9): the explicit double-phase map S.
--   - `doublePhaseDilation`: PDF p.5: the dilation flow.
--   - `classicalR`: PDF p.5: the simultaneous rotation of (x,xi_p) and (p,xi_x).
--   - `dilationHamiltonian`: PDF p.5, (1.10): dilation Hamiltonian.
--   - `rotationHamiltonian`: PDF p.5, (1.11): rotation Hamiltonian, with both minus signs.
--   - `hamiltonField`: PDF pp.4–5: Hamilton vector field in the paper's coordinate order.
--   - `fourierFactor`: PDF p.6: the paper's unitary Fourier normalization.
--   - `RealizesL2Formula`: PDF pp.19–21: specify a continuous L2 operator by its a.e. action. The definition asserts no norm preservation or generator information.
--   - `l2FormulaOperator`: PDF pp.19–21: the unique bounded L2 realization, if it exists, of an explicit formula. All uses below have explicit realization conclusions.
--   - `dilationFormula`: PDF p.19, (5.3): the dilation action, independently of its generator.
--   - `dilationEvolution`: PDF p.19: bounded realization of the explicit dilation formula.
--   - `RealizesPartialFourier`: PDF p.20: characterize partial Fourier transform on dense Schwartz inputs; no Bochner Fourier integral is applied to an arbitrary L2 input.
--   - `partialFourier`: PDF p.20: the continuous L2 extension specified by the dense-domain formula. Unitarity is a conclusion of rotation_evolution_group, not a definition.
--   - `mixedRotation`: PDF p.20, (5.4): the inverse classical rotation in mixed (x,xi_p) coordinates.
--   - `coordinatePullback`: PDF pp.20–22: L2 pullback by an explicitly given coordinate map. Only the invertible mixed rotations and the distinguished shear are used.
--   - `rotationEvolution`: PDF p.20: rotation evolution is inverse partial Fourier, mixed-coordinate rotation pullback, then partial Fourier, with the rightmost operation first.
--   - `unitaryL2`: PDF pp.19–21: unitarity of a bounded endomorphism on phase L2.
--   - `strongUnitaryGroup`: PDF pp.19–21: a strongly continuous, one-parameter unitary group.
--   - `generatesGraph`: PDF pp.19–20: the full generator graph of e^(-itH), including its domain. The derivative is a Hilbert-norm derivative at zero.
--   - `weakPhaseGraph`: PDF pp.18–20: maximal distributional L2 graph from the transposed polynomial differential expression on Schwartz tests. Explicit integrability prevents total Bochner integrals on bad inputs from adding graph points.
--   - `dilationTestAction`: PDF p.19: transpose of -i(x dot d_x+p dot d_p+n) in the complex-linear distribution pairing. The transpose has +i and +n.
--   - `rotationTestAction`: PDF p.20: transpose of H_R=sum_j d_xj d_pj-x dot p; the second derivative and multiplication terms are unchanged by transposition.
--   - `moyalTransform`: PDF p.21, (5.7): U=U_D(-log sqrt(2)) U_R(-pi/4). The order of the two factors is essential.
--   - `mixedShear`: PDF p.21, (5.8): the distinguished mixed-coordinate shear.
--   - `RealizesConfigurationFourier`: PDF p.6: the normalized configuration Fourier transform on Schwartz inputs.
--   - `configurationFourier`: PDF p.6: continuous configuration Fourier extension determined on Schwartz.
--   - `wignerFormula`: PDF pp.3,21–22: normalized cross-Wigner formula, equal to (2*pi)^(n/2) times the conventional Wigner distribution. This is independent of U.
--   - `normalizedWigner`: PDF pp.21–22: the L2 class specified by the normalized Wigner integral. The conclusion of moyal_transform_wigner asserts its realization explicitly.
--   - `conjugatePhaseGraph`: PDF pp.22–23: transport an ambient phase operator graph by U. This is conjugation with U^-1 when U is unitary.
--   - `originalCoordinateGraph`: PDF pp.19,22: original maximal coordinate graphs in order X,P,Xi_x,Xi_p.
--   - `boppOnFunction`: PDF p.22, (5.10): the four Bopp expressions on functions, used only on the common invariant Schwartz core and its differentiated expressions.
--   - `boppCoordinateGraph`: PDF p.22: the independently defined maximal weak graphs of the four Bopp expressions; transposition reverses the first-derivative sign.
--   - `commutatorCoefficient`: PDF pp.1,23: canonical symplectic commutator coefficients in (X,P,Xi_x,Xi_p) order.
--   - `phaseDisplacementFormula`: PDF p.15, (4.10): phase-space Heisenberg-Weyl displacement formula.
--   - `phaseDisplacement`: PDF p.15: bounded realization of the explicit phase-space displacement.
--   - `moyalDisplacement`: PDF p.23, Theorem 5.6: Moyal displacement is defined by conjugation, independently of the claimed shift-and-phase formula.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, https://arxiv.org/abs/1209.1850v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P37

/-!
Statement targets from arXiv:1209.1850v1, §§1–3 and §5.1–5.2.
Accepted configuration and interleaved phase coordinates, dot products, and domain
restriction are imported; phasePoint and the two projections express (x,p).
All new objects are local to this paper. Configuration and phase Hilbert spaces
are genuine Lebesgue L2 spaces. Graphs retain unbounded operator domains.
The canonical tensor map is selected by its a.e. formula among continuous linear
maps, without assuming its isometry, inverse, or any spectral conclusion.
The first target includes realization of that formula, ruling out the selection's
totalization branch for every unit window. No frozen definition is changed.
Analytic interfaces not completed in this draft are recorded in HARD.md/GAPS.json.
Compilation is pending the separate mechanical stage.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)
open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)
open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF p.6, §1.2: the x coordinates of the accepted interleaved phase carrier. -/
def phasePosition {n : ℕ} (z : PhaseCoordinates n) : Configuration n :=
  fun j => z (j, 0)

/-- PDF p.6, §1.2: the p coordinates of the accepted interleaved phase carrier. -/
def phaseMomentum {n : ℕ} (z : PhaseCoordinates n) : Configuration n :=
  fun j => z (j, 1)

/-- PDF p.6, §1.2: assemble (x,p) in the accepted interleaved real coordinates.
This is a coordinate constructor, not a second phase-space carrier. -/
def phasePoint {n : ℕ} (x p : Configuration n) : PhaseCoordinates n :=
  fun j => ![x, p] j.2 j.1

example {n : ℕ} (x p : Configuration n) : phasePosition (phasePoint x p) = x := by
  rfl

example {n : ℕ} (x p : Configuration n) : phaseMomentum (phasePoint x p) = p := by
  rfl

example {n : ℕ} (z : PhaseCoordinates n) :
    phasePoint (phasePosition z) (phaseMomentum z) = z := by
  funext j
  rcases j with ⟨j, a⟩
  fin_cases a <;> rfl

/-- PDF p.6, §1.2: double-phase coordinates ordered (x,p,xi_x,xi_p). -/
abbrev DoublePhase (n : ℕ) := Fin 4 → Configuration n

/-- PDF p.6: the configuration Hilbert space, including its a.e. quotient. -/
abbrev ConfigurationL2 (n : ℕ) := Lp ℂ 2 (volume : Measure (Configuration n))

/-- PDF p.6: the phase Hilbert space with coordinate Lebesgue measure. -/
abbrev PhaseL2 (n : ℕ) := Lp ℂ 2 (volume : Measure (PhaseCoordinates n))

/-- PDF p.6, (2.1): characterize the tensor map by its actual a.e. formula.
This property specifies no norm or spectral conclusion. -/
def RealizesTensor {n : ℕ} (chi : ConfigurationL2 n)
    (T : ConfigurationL2 n →L[ℂ] PhaseL2 n) : Prop :=
  ∀ psi : ConfigurationL2 n, ∀ᵐ z : PhaseCoordinates n,
    T psi z = psi (phasePosition z) * star (chi (phaseMomentum z))

/-- PDF p.6, (2.1): canonical continuous linear realization of
psi tensor conjugate(chi), selected solely by its pointwise a.e. formula.
The zero branch totalizes the definition; tensor_unitary_equivalence explicitly
asserts realization for all unit windows, without a realizability hypothesis. -/
def tensorEmbedding {n : ℕ} (chi : ConfigurationL2 n) :
    ConfigurationL2 n →L[ℂ] PhaseL2 n :=
  if h : ∃ T : ConfigurationL2 n →L[ℂ] PhaseL2 n, RealizesTensor chi T
  then Classical.choose h else 0

example {n : ℕ} (chi : ConfigurationL2 n) :
    tensorEmbedding chi 0 = 0 := by
  exact map_zero (tensorEmbedding chi)

/-- PDF pp.7–8: H_chi is the actual range, rather than the whole phase L2. -/
def windowSpace {n : ℕ} (chi : ConfigurationL2 n) : Submodule ℂ (PhaseL2 n) :=
  (tensorEmbedding chi).toLinearMap.range

example {n : ℕ} (chi : ConfigurationL2 n) : (0 : PhaseL2 n) ∈ windowSpace chi := by
  exact (windowSpace chi).zero_mem

/-- PDF pp.8–9, Definition 2.7: the graph of the transported unbounded operator.
Both input and output are transported; no domain is extended to all of H_chi. -/
def transportGraph {n : ℕ} (chi : ConfigurationL2 n)
    (G : Set (ConfigurationL2 n × ConfigurationL2 n)) :
    Set (PhaseL2 n × PhaseL2 n) :=
  {q | ∃ u v, (u, v) ∈ G ∧ tensorEmbedding chi u = q.1 ∧
    tensorEmbedding chi v = q.2}

example {n : ℕ} (chi : ConfigurationL2 n) : transportGraph chi ∅ = ∅ := by
  ext q
  simp [transportGraph]

/-- PDF p.9: symmetry on the operator domain; density is not part of symmetry. -/
def graphSymmetric {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (G : Set (H × H)) : Prop :=
  ∀ u v x y, (u, v) ∈ G → (x, y) ∈ G → inner ℂ v x = inner ℂ u y

/-- PDF p.9, (2.6): adjoint graph in the specified ambient Hilbert subspace.
Inner products are conjugate-linear in the first entry. -/
def adjointGraphOn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Submodule ℂ H) (G : Set (H × H)) : Set (H × H) :=
  {q | q.1 ∈ S ∧ q.2 ∈ S ∧
    ∀ u v, (u, v) ∈ G → inner ℂ q.2 u = inner ℂ q.1 v}

/-- PDF p.9: self-adjointness means dense domain in the actual Hilbert space
and equality with the adjoint graph. Nondense adjoints never get a junk value. -/
def graphSelfAdjointOn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Submodule ℂ H) (G : Set (H × H)) : Prop :=
  closure (Prod.fst '' G) = (S : Set H) ∧ G = adjointGraphOn S G

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    graphSymmetric (∅ : Set (H × H)) := by
  simp [graphSymmetric]

/-- PDF p.10, Theorem 2.10: the unbounded resolvent requires an everywhere-defined
bounded inverse of A-lambda I on the ambient Hilbert subspace. The second
identity includes every point of the original graph and gives injectivity. -/
def graphResolventOn {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : Submodule ℂ H) (G : Set (H × H)) (lambda : ℂ) : Prop :=
  ∃ B : S →L[ℂ] S,
    (∀ f : S, ((B f : H), lambda • (B f : H) + (f : H)) ∈ G) ∧
    (∀ x y : S, ((x : H), (y : H)) ∈ G → B (y - lambda • x) = x)

/-- PDF p.10: the full spectrum, including continuous and residual parts. -/
def graphSpectrumOn {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : Submodule ℂ H) (G : Set (H × H)) : Set ℂ :=
  {lambda | ¬ graphResolventOn S G lambda}

example {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : Submodule ℂ H) (G : Set (H × H)) (lambda : ℂ) :
    lambda ∈ graphSpectrumOn S G ↔ ¬ graphResolventOn S G lambda := by
  rfl

/-- PDF pp.10–11: strong Schrodinger solution in the Hilbert norm.
The graph clause forces membership of the domain at every real time. -/
def strongSolution {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (G : Set (H × H)) (curve : ℝ → H) (initial : H) : Prop :=
  curve 0 = initial ∧ ∀ t : ℝ, ∃ v : H,
    HasDerivAt curve v t ∧ (curve t, Complex.I • v) ∈ G

/-- PDF p.9, Remark 2.8: maximal multiplication graph, with a.e. equality. -/
def positionGraph {E : Type*} [NormedAddCommGroup E] [MeasureSpace E] (coordinate : E → ℝ) :
    Set (Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E)) :=
  {q | ∀ᵐ x : E, q.2 x = (coordinate x : ℂ) * q.1 x}

/-- PDF p.9, Remark 2.8: the maximal L2 graph of -i times a weak directional
derivative. Pairing with a Schwartz test is complex-linear, so integration by
parts gives +i times the derivative of the test. No derivative of chi is used. -/
def momentumGraph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] (direction : E) :
    Set (Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E)) :=
  {q | ∀ phi : SchwartzMap E ℂ,
    Integrable (fun x => q.2 x * phi x) ∧
    Integrable (fun x => q.1 x * (fderiv ℝ (phi : E → ℂ) x) direction) ∧
    (∫ x, q.2 x * phi x) = Complex.I *
      ∫ x, q.1 x * (fderiv ℝ (phi : E → ℂ) x) direction}

/-- PDF pp.5–6: the double-phase symplectic form sigma_x plus sigma_p. -/
def doubleSigma {n : ℕ} (z w : DoublePhase n) : ℝ :=
  coordinateDot (z 2) (w 0) - coordinateDot (z 0) (w 2) +
    coordinateDot (z 3) (w 1) - coordinateDot (z 1) (w 3)

/-- PDF p.5, (1.9): the explicit double-phase map S. -/
def classicalS {n : ℕ} (z : DoublePhase n) : DoublePhase n :=
  ![z 0 - (1 / 2 : ℝ) • z 3, z 1 - (1 / 2 : ℝ) • z 2,
    (1 / 2 : ℝ) • z 2 + z 1, (1 / 2 : ℝ) • z 3 + z 0]

/-- PDF p.5: the dilation flow. -/
def doublePhaseDilation {n : ℕ} (s : ℝ) (z : DoublePhase n) : DoublePhase n :=
  ![Real.exp s • z 0, Real.exp s • z 1,
    Real.exp (-s) • z 2, Real.exp (-s) • z 3]

/-- PDF p.5: the simultaneous rotation of (x,xi_p) and (p,xi_x). -/
def classicalR {n : ℕ} (theta : ℝ) (z : DoublePhase n) : DoublePhase n :=
  ![Real.cos theta • z 0 - Real.sin theta • z 3,
    Real.cos theta • z 1 - Real.sin theta • z 2,
    Real.sin theta • z 1 + Real.cos theta • z 2,
    Real.sin theta • z 0 + Real.cos theta • z 3]

/-- PDF p.5, (1.10): dilation Hamiltonian. -/
def dilationHamiltonian {n : ℕ} (z : DoublePhase n) : ℝ :=
  coordinateDot (z 0) (z 2) + coordinateDot (z 1) (z 3)

/-- PDF p.5, (1.11): rotation Hamiltonian, with both minus signs. -/
def rotationHamiltonian {n : ℕ} (z : DoublePhase n) : ℝ :=
  -coordinateDot (z 2) (z 3) - coordinateDot (z 0) (z 1)

/-- PDF pp.4–5: Hamilton vector field in the paper's coordinate order. -/
def hamiltonField {n : ℕ} (H : DoublePhase n → ℝ) (z : DoublePhase n) :
    DoublePhase n :=
  ![fun j => (fderiv ℝ H z) (Pi.single 2 (Pi.single j 1)),
    fun j => (fderiv ℝ H z) (Pi.single 3 (Pi.single j 1)),
    fun j => -(fderiv ℝ H z) (Pi.single 0 (Pi.single j 1)),
    fun j => -(fderiv ℝ H z) (Pi.single 1 (Pi.single j 1))]

example {n : ℕ} : classicalS (0 : DoublePhase n) = 0 := by
  ext a j
  fin_cases a <;> simp [classicalS]

example {n : ℕ} (z : DoublePhase n) : doublePhaseDilation 0 z = z := by
  ext a j
  fin_cases a <;> simp [doublePhaseDilation]

example {n : ℕ} (z : DoublePhase n) : classicalR 0 z = z := by
  ext a j
  fin_cases a <;> simp [classicalR]

example {n : ℕ} : dilationHamiltonian (0 : DoublePhase n) = 0 := by
  simp [dilationHamiltonian, coordinateDot]

example {n : ℕ} : rotationHamiltonian (0 : DoublePhase n) = 0 := by
  simp [rotationHamiltonian, coordinateDot]

example {n : ℕ} (u : Configuration n) : coordinateDot u 0 = 0 := by
  simp [coordinateDot]

example {n : ℕ} (z : DoublePhase n) : doubleSigma z 0 = 0 := by
  simp [doubleSigma, coordinateDot]

/-- PDF p.6: the paper's unitary Fourier normalization. -/
def fourierFactor (n : ℕ) : ℂ := (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) : ℝ)

/-- PDF pp.19–21: specify a continuous L2 operator by its a.e. action.
The definition asserts no norm preservation or generator information. -/
def RealizesL2Formula {n : ℕ} (formula : PhaseL2 n → PhaseCoordinates n → ℂ)
    (V : PhaseL2 n →L[ℂ] PhaseL2 n) : Prop :=
  ∀ f, ∀ᵐ z : PhaseCoordinates n, V f z = formula f z

/-- PDF pp.19–21: the unique bounded L2 realization, if it exists, of an
explicit formula. All uses below have explicit realization conclusions. -/
def l2FormulaOperator {n : ℕ} (formula : PhaseL2 n → PhaseCoordinates n → ℂ) :
    PhaseL2 n →L[ℂ] PhaseL2 n :=
  if h : ∃ V : PhaseL2 n →L[ℂ] PhaseL2 n, RealizesL2Formula formula V
  then Classical.choose h else 0

example {n : ℕ} (formula : PhaseL2 n → PhaseCoordinates n → ℂ) : l2FormulaOperator formula 0 = 0 := by
  exact map_zero _

/-- PDF p.19, (5.3): the dilation action, independently of its generator. -/
def dilationFormula {n : ℕ} (s : ℝ) (f : PhaseL2 n) (z : PhaseCoordinates n) : ℂ :=
  (Real.exp (-(n : ℝ) * s) : ℂ) *
    f (phasePoint (Real.exp (-s) • (phasePosition z)) (Real.exp (-s) • (phaseMomentum z)))

/-- PDF p.19: bounded realization of the explicit dilation formula. -/
def dilationEvolution {n : ℕ} (s : ℝ) : PhaseL2 n →L[ℂ] PhaseL2 n :=
  l2FormulaOperator (dilationFormula s)

/-- PDF p.20: characterize partial Fourier transform on dense Schwartz inputs;
no Bochner Fourier integral is applied to an arbitrary L2 input. -/
def RealizesPartialFourier {n : ℕ} (F : PhaseL2 n →L[ℂ] PhaseL2 n) : Prop :=
  ∀ f : SchwartzMap (PhaseCoordinates n) ℂ, ∀ᵐ z : PhaseCoordinates n,
    F (f.toLp 2 (volume : Measure (PhaseCoordinates n))) z = fourierFactor n *
      ∫ p : Configuration n, Complex.exp (-Complex.I * (coordinateDot (phaseMomentum z) p : ℂ)) * f (phasePoint (phasePosition z) p)

/-- PDF p.20: the continuous L2 extension specified by the dense-domain formula.
Unitarity is a conclusion of rotation_evolution_group, not a definition. -/
def partialFourier {n : ℕ} : PhaseL2 n →L[ℂ] PhaseL2 n :=
  if h : ∃ F : PhaseL2 n →L[ℂ] PhaseL2 n, RealizesPartialFourier F
  then Classical.choose h else 0

/-- PDF p.20, (5.4): the inverse classical rotation in mixed (x,xi_p) coordinates. -/
def mixedRotation {n : ℕ} (theta : ℝ) (z : PhaseCoordinates n) : PhaseCoordinates n :=
  phasePoint (Real.cos theta • (phasePosition z) + Real.sin theta • (phaseMomentum z))
    (Real.cos theta • (phaseMomentum z) - Real.sin theta • (phasePosition z))

/-- PDF pp.20–22: L2 pullback by an explicitly given coordinate map.
Only the invertible mixed rotations and the distinguished shear are used. -/
def coordinatePullback {n : ℕ} (A : PhaseCoordinates n → PhaseCoordinates n) : PhaseL2 n →L[ℂ] PhaseL2 n :=
  l2FormulaOperator (fun f z => f (A z))

/-- PDF p.20: rotation evolution is inverse partial Fourier, mixed-coordinate
rotation pullback, then partial Fourier, with the rightmost operation first. -/
def rotationEvolution {n : ℕ} (theta : ℝ) : PhaseL2 n →L[ℂ] PhaseL2 n :=
  partialFourier.adjoint.comp ((coordinatePullback (mixedRotation theta)).comp partialFourier)

/-- PDF pp.19–21: unitarity of a bounded endomorphism on phase L2. -/
def unitaryL2 {n : ℕ} (V : PhaseL2 n →L[ℂ] PhaseL2 n) : Prop :=
  V.adjoint.comp V = 1 ∧ V.comp V.adjoint = 1

/-- PDF pp.19–21: a strongly continuous, one-parameter unitary group. -/
def strongUnitaryGroup {n : ℕ} (V : ℝ → PhaseL2 n →L[ℂ] PhaseL2 n) : Prop :=
  V 0 = 1 ∧ (∀ s t : ℝ, V (s + t) = (V s).comp (V t)) ∧
    (∀ s : ℝ, unitaryL2 (V s)) ∧ (∀ f : PhaseL2 n, Continuous (fun s => V s f))

/-- PDF pp.19–20: the full generator graph of e^(-itH), including its domain.
The derivative is a Hilbert-norm derivative at zero. -/
def generatesGraph {n : ℕ} (V : ℝ → PhaseL2 n →L[ℂ] PhaseL2 n)
    (G : Set (PhaseL2 n × PhaseL2 n)) : Prop :=
  G = {q | HasDerivAt (fun t => V t q.1) (-Complex.I • q.2) 0}

/-- PDF pp.18–20: maximal distributional L2 graph from the transposed
polynomial differential expression on Schwartz tests. Explicit integrability
prevents total Bochner integrals on bad inputs from adding graph points. -/
def weakPhaseGraph {n : ℕ} (testAction : SchwartzMap (PhaseCoordinates n) ℂ → PhaseCoordinates n → ℂ) :
    Set (PhaseL2 n × PhaseL2 n) :=
  {q | ∀ phi : SchwartzMap (PhaseCoordinates n) ℂ,
    Integrable (fun z => q.2 z * phi z) ∧
    Integrable (fun z => q.1 z * testAction phi z) ∧
    (∫ z, q.2 z * phi z) = ∫ z, q.1 z * testAction phi z}

/-- PDF p.19: transpose of -i(x dot d_x+p dot d_p+n) in the
complex-linear distribution pairing. The transpose has +i and +n. -/
def dilationTestAction {n : ℕ} (phi : SchwartzMap (PhaseCoordinates n) ℂ) (z : PhaseCoordinates n) : ℂ :=
  Complex.I * ((∑ j : Fin n,
    (((phasePosition z) j : ℂ) * (fderiv ℝ (phi : PhaseCoordinates n → ℂ) z) (phasePoint (Pi.single j 1) 0) +
    ((phaseMomentum z) j : ℂ) * (fderiv ℝ (phi : PhaseCoordinates n → ℂ) z) (phasePoint 0 (Pi.single j 1)))) +
    (n : ℂ) * phi z)

/-- PDF p.20: transpose of H_R=sum_j d_xj d_pj-x dot p;
the second derivative and multiplication terms are unchanged by transposition. -/
def rotationTestAction {n : ℕ} (phi : SchwartzMap (PhaseCoordinates n) ℂ) (z : PhaseCoordinates n) : ℂ :=
  (∑ j : Fin n, (fderiv ℝ
    (fun w : PhaseCoordinates n => (fderiv ℝ (phi : PhaseCoordinates n → ℂ) w) (phasePoint 0 (Pi.single j 1))) z)
      (phasePoint (Pi.single j 1) 0)) - (coordinateDot (phasePosition z) (phaseMomentum z) : ℂ) * phi z

example {n : ℕ} (s : ℝ) : dilationEvolution (n := n) s 0 = 0 := by
  exact map_zero _

example {n : ℕ} : partialFourier (n := n) 0 = 0 := by
  exact map_zero _

example {n : ℕ} (theta : ℝ) : rotationEvolution (n := n) theta 0 = 0 := by
  exact map_zero _

example {n : ℕ} : unitaryL2 (1 : PhaseL2 n →L[ℂ] PhaseL2 n) := by
  simp [unitaryL2, ContinuousLinearMap.adjoint_one, ContinuousLinearMap.one_def,
    ContinuousLinearMap.adjoint_id]

example {n : ℕ} (z : PhaseCoordinates n) : mixedRotation 0 z = z := by
  simpa only [mixedRotation, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero, sub_zero] using
    (show phasePoint (phasePosition z) (phaseMomentum z) = z from by
      funext j
      rcases j with ⟨j, a⟩
      fin_cases a <;> rfl)

/-- PDF p.21, (5.7): U=U_D(-log sqrt(2)) U_R(-pi/4).
The order of the two factors is essential. -/
def moyalTransform {n : ℕ} : PhaseL2 n →L[ℂ] PhaseL2 n :=
  (dilationEvolution (-Real.log (Real.sqrt 2))).comp (rotationEvolution (-Real.pi / 4))

/-- PDF p.21, (5.8): the distinguished mixed-coordinate shear. -/
def mixedShear {n : ℕ} (z : PhaseCoordinates n) : PhaseCoordinates n :=
  phasePoint ((phasePosition z) - (1 / 2 : ℝ) • (phaseMomentum z)) ((phasePosition z) + (1 / 2 : ℝ) • (phaseMomentum z))

/-- PDF p.6: the normalized configuration Fourier transform on Schwartz inputs. -/
def RealizesConfigurationFourier {n : ℕ}
    (F : ConfigurationL2 n →L[ℂ] ConfigurationL2 n) : Prop :=
  ∀ f : SchwartzMap (Configuration n) ℂ, ∀ᵐ p : Configuration n,
    F (f.toLp 2 (volume : Measure (Configuration n))) p = fourierFactor n *
      ∫ x : Configuration n, Complex.exp (-Complex.I * (coordinateDot x p : ℂ)) * f x

/-- PDF p.6: continuous configuration Fourier extension determined on Schwartz. -/
def configurationFourier {n : ℕ} : ConfigurationL2 n →L[ℂ] ConfigurationL2 n :=
  if h : ∃ F : ConfigurationL2 n →L[ℂ] ConfigurationL2 n, RealizesConfigurationFourier F
  then Classical.choose h else 0

/-- PDF pp.3,21–22: normalized cross-Wigner formula, equal to (2*pi)^(n/2)
times the conventional Wigner distribution. This is independent of U. -/
def wignerFormula {n : ℕ} (psi chi : ConfigurationL2 n) (z : PhaseCoordinates n) : ℂ :=
  fourierFactor n * ∫ y : Configuration n,
    Complex.exp (Complex.I * (coordinateDot (phaseMomentum z) y : ℂ)) *
      psi ((phasePosition z) - (1 / 2 : ℝ) • y) * star (chi ((phasePosition z) + (1 / 2 : ℝ) • y))

/-- PDF pp.21–22: the L2 class specified by the normalized Wigner integral.
The conclusion of moyal_transform_wigner asserts its realization explicitly. -/
def normalizedWigner {n : ℕ} (psi chi : ConfigurationL2 n) : PhaseL2 n :=
  if h : ∃ f : PhaseL2 n, ∀ᵐ z : PhaseCoordinates n, f z = wignerFormula psi chi z
  then Classical.choose h else 0

example {n : ℕ} : moyalTransform (n := n) 0 = 0 := by
  exact map_zero _

example {n : ℕ} : configurationFourier (n := n) 0 = 0 := by
  exact map_zero _

/-- PDF pp.22–23: transport an ambient phase operator graph by U.
This is conjugation with U^-1 when U is unitary. -/
def conjugatePhaseGraph {n : ℕ} (V : PhaseL2 n →L[ℂ] PhaseL2 n)
    (G : Set (PhaseL2 n × PhaseL2 n)) : Set (PhaseL2 n × PhaseL2 n) :=
  {q | ∃ x y, (x, y) ∈ G ∧ V x = q.1 ∧ V y = q.2}

/-- PDF pp.19,22: original maximal coordinate graphs in order X,P,Xi_x,Xi_p. -/
def originalCoordinateGraph {n : ℕ} (a : Fin 4) (j : Fin n) :
    Set (PhaseL2 n × PhaseL2 n) :=
  ![positionGraph (fun z : PhaseCoordinates n => (phasePosition z) j),
    positionGraph (fun z : PhaseCoordinates n => (phaseMomentum z) j),
    momentumGraph (phasePoint (Pi.single j 1 : Configuration n) 0),
    momentumGraph (phasePoint 0 (Pi.single j 1 : Configuration n))] a

/-- PDF p.22, (5.10): the four Bopp expressions on functions, used only
on the common invariant Schwartz core and its differentiated expressions. -/
def boppOnFunction {n : ℕ} (a : Fin 4) (j : Fin n) (f : PhaseCoordinates n → ℂ) : PhaseCoordinates n → ℂ :=
  ![fun z => ((phasePosition z) j : ℂ) * f z + Complex.I / 2 * (fderiv ℝ f z) (phasePoint 0 (Pi.single j 1)),
    fun z => ((phaseMomentum z) j : ℂ) * f z + Complex.I / 2 * (fderiv ℝ f z) (phasePoint (Pi.single j 1) 0),
    fun z => ((phaseMomentum z) j : ℂ) * f z - Complex.I / 2 * (fderiv ℝ f z) (phasePoint (Pi.single j 1) 0),
    fun z => ((phasePosition z) j : ℂ) * f z - Complex.I / 2 * (fderiv ℝ f z) (phasePoint 0 (Pi.single j 1))] a

/-- PDF p.22: the independently defined maximal weak graphs of the four
Bopp expressions; transposition reverses the first-derivative sign. -/
def boppCoordinateGraph {n : ℕ} (a : Fin 4) (j : Fin n) :
    Set (PhaseL2 n × PhaseL2 n) :=
  weakPhaseGraph (fun phi z =>
    ![((phasePosition z) j : ℂ) * phi z - Complex.I / 2 *
        (fderiv ℝ (phi : PhaseCoordinates n → ℂ) z) (phasePoint 0 (Pi.single j 1)),
      ((phaseMomentum z) j : ℂ) * phi z - Complex.I / 2 *
        (fderiv ℝ (phi : PhaseCoordinates n → ℂ) z) (phasePoint (Pi.single j 1) 0),
      ((phaseMomentum z) j : ℂ) * phi z + Complex.I / 2 *
        (fderiv ℝ (phi : PhaseCoordinates n → ℂ) z) (phasePoint (Pi.single j 1) 0),
      ((phasePosition z) j : ℂ) * phi z + Complex.I / 2 *
        (fderiv ℝ (phi : PhaseCoordinates n → ℂ) z) (phasePoint 0 (Pi.single j 1))] a)

/-- PDF pp.1,23: canonical symplectic commutator coefficients in (X,P,Xi_x,Xi_p) order. -/
def commutatorCoefficient {n : ℕ} (a b : Fin 4) (j k : Fin n) : ℂ :=
  if j = k then
    if (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 3) then 1
    else if (a = 2 ∧ b = 0) ∨ (a = 3 ∧ b = 1) then -1 else 0
  else 0

example {n : ℕ} (G : Set (PhaseL2 n × PhaseL2 n)) :
    conjugatePhaseGraph (1 : PhaseL2 n →L[ℂ] PhaseL2 n) G = G := by
  ext q
  simp [conjugatePhaseGraph]

example {n : ℕ} (j : Fin n) : commutatorCoefficient 0 2 j j = 1 := by
  simp [commutatorCoefficient]

/-- PDF p.15, (4.10): phase-space Heisenberg-Weyl displacement formula. -/
def phaseDisplacementFormula {n : ℕ} (d : PhaseCoordinates n) (f : PhaseL2 n) (z : PhaseCoordinates n) : ℂ :=
  Complex.exp (Complex.I * ((coordinateDot (phaseMomentum d) (phasePosition z) - coordinateDot (phaseMomentum d) (phasePosition d) / 2 : ℝ) : ℂ)) *
    f (phasePoint ((phasePosition z) - (phasePosition d)) (phaseMomentum z))

/-- PDF p.15: bounded realization of the explicit phase-space displacement. -/
def phaseDisplacement {n : ℕ} (d : PhaseCoordinates n) : PhaseL2 n →L[ℂ] PhaseL2 n :=
  l2FormulaOperator (phaseDisplacementFormula d)

/-- PDF p.23, Theorem 5.6: Moyal displacement is defined by conjugation,
independently of the claimed shift-and-phase formula. -/
def moyalDisplacement {n : ℕ} (d : PhaseCoordinates n) : PhaseL2 n →L[ℂ] PhaseL2 n :=
  moyalTransform.comp ((phaseDisplacement d).comp moyalTransform.adjoint)

example {n : ℕ} (d : PhaseCoordinates n) : moyalDisplacement d (0 : PhaseL2 n) = 0 := by
  exact map_zero _

end QAlgorithms.Papers.Independent.Next46.P20


