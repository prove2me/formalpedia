-- Prove2me | Definitions.Def_OAIQWCO002
-- name    : OAIQWCO002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T02:53:39.56205+00:00
-- url     : https://prove2.me/theorems/638a2913-c1a6-40f5-94c1-b2c41bbdcfd5
-- title:
--   OpenAI classical O(n) split: definitions bundle 3 (spin systems, rotations, dyadic profiles, bond representation, annuli)
-- statement:
--   The main definitions bundle of the split of OpenAI's proof of exponential decay of spin correlations in two-dimensional classical $O(n)$ models, $n \ge 3$ (`OAI.ClassicalON.main`). It holds OpenAI's Lean definitions from `lean/OAI/Probability/ClassicalON` (OpenAI, *Exponential decay in two-dimensional classical O(n) models*, OpenAI Math Release, September 23, 2026, result family 215, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies.
--
--   Among them: pinned spin systems `SpinSystem` with their Gibbs `average`, `energy` and rotation generators `axisA`, `axisB`, `axisC`; the responses `secondAxisResponse`, `complexSecondResponse`, `complexMixedResponse`, the forms `differential` and `commutatorForm`; the dyadic cutoffs `squareTheta`, `scaledSite`, `LatticeGraph.thetaEdge`, `LatticeGraph.WithinDyadicBox`, `LatticeGraph.BoundaryPins`, `LatticeGraph.spinSystem`; the bond representation `freeBondMean`, `bondConnected`, `LatticeGraph.connectionProbability`; and the annulus and coarse-grained geometry (`annulusGraph`, `coarseSite`, `siteRadius`).
--
--   The definitions of the published statement (`LatticeGraph`, `Spin`, `referenceLaw`, `correlation`, `siteDistance`, `ExponentialDecay` and the rest) are not repeated: the bundle imports them from the published bundle `Def_ClassicalON`. It imports the bundle `OAIQWCO001` of this split, and through it `OAIQWCO000`.
--
--   Modules (`Compat` is the port's compatibility block; the others are each `.lean` in `lean/OAI/Probability/ClassicalON`): `Compat`, `FiniteVolume`, `TorusFourier`, `DyadicFourier`, `SmoothProfiles`, `ProfileEstimates`, `LatticeGeometry`, `LatticeRestriction`, `LatticeRadius`, `AnnulusLabels`, `CoarseGeometry`, `CoarseCodes`, `FerromagneticMean`, `WeightedTilt`, `AmplitudePartition`, `IsingReference`, `MomentCone`, `ProductMoments`, `IsingGinibre`, `TorusDouble`, `PlanarAlgebra`, `PlanarGinibre`, `AmplitudeLaw`, `CylindricalGeometry`, `CylindricalFiber`, `CylindricalLaw`, `CylindricalConfiguration`, `UpperEndpoint`, `AmplitudeSplit`, `PinnedReference`, `PinnedCylinder`, `BondSubspace`, `BondLaw`, `BondSigns`, `BondExpansion`, `SpinBondKernel`, `JointBond`, `RawBond`, `SpinBonds`, `BondPin`, `PinnedSigns`, `BondConnectivity`, `SignedSigns`, `PinComparison`, `PinnedBonds`, `ProductGrouping`, `PinnedBlocks`, `SpinReindex`, `AnnulusBlocks`, `DyadicSine`, `DyadicModes`, `MatrixSquare`, `LatticeModes`, `ModeBounds`, `RotationWork`, `MixedWard`, `ComplexWard`, `FamilyAlgebra`, `GradientComplex`, `ObservableBounds`, `FamilyKernel`, `ModeCosts`, `ModeCommutator`, `SecondBound`, `ResponseTransfer`, `FamilyBound`, `RotationInequality`, `AnnulusResponse`, `AnnulusSmall`, `AxisRotation`, `PotentialRotation`, `AnnulusPartition`, `PoleCrossing`, `AnnulusCrossing`, `SpinCorrelation`, `SeparatedAnnuli`, `AnnulusCut`, `CoarsePaths`, `CoarseTail`, `SpinIsotropy`, `OrthogonalAverage`, `BlockGeometry`, `BlockOrbit`, `BlockKernel`.
-- source:
--   OpenAI, Exponential decay in two-dimensional classical O(n) models, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 215; Apache License 2.0); definitions carved from lean/OAI/Probability/ClassicalON at commit adc7f12

import Mathlib
import Definitions.Def_ClassicalON
import Definitions.Def_OAIQWCO001

section
-- module Solutions.OAIQW_ClassicalON.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FiniteVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF uR uS uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace ClassicalON

@[simp] theorem spin_norm {n : ℕ} (s : Spin n) : ‖s.val‖ = 1 := by
  exact mem_sphere_zero_iff_norm.mp s.property

instance sphereProbability_isProbability (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (sphereProbability n) := by
  have hs : (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere ≠ 0 :=
    Measure.toSphere_ne_zero _
  constructor
  dsimp [sphereProbability]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_eq_zero.not.mpr hs)
    (measure_ne_top _ _)

instance referenceLaw_isProbability (n : ℕ) [NeZero n] (G : LatticeGraph) :
    IsProbabilityMeasure (referenceLaw n G) := by
  unfold referenceLaw
  infer_instance

def spinRotation {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Spin n ≃ₜ Spin n :=
  R.toHomeomorph.subtype fun x => by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖R x‖ = 1
    rw [R.norm_map]

@[simp] theorem spinRotation_val {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (s : Spin n) :
    (spinRotation R s).val = R s.val := rfl

def siteReference (n : ℕ) (p : Option (Spin n)) : Measure (Spin n) :=
  match p with
  | none => sphereProbability n
  | some s => Measure.dirac s

instance siteReference_isProbability (n : ℕ) [NeZero n] (p : Option (Spin n)) :
    IsProbabilityMeasure (siteReference n p) := by
  cases p <;> dsimp [siteReference] <;> infer_instance

structure SpinSystem (n : ℕ) (V : Type uV) (E : Type uE) where
  left : E → V
  right : E → V
  strength : E → ℝ
  pin : V → Option (Spin n)

abbrev SpinOperator (n : ℕ) :=
  EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)

instance spinOperator_completeSpace (dimension : ℕ) : CompleteSpace (SpinOperator dimension) :=
  ContinuousLinearMap.instCompleteSpace

instance spinOperator_ratNormedAlgebra (n : ℕ) : NormedAlgebra ℚ (SpinOperator n) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

def rotationExp {n : ℕ} (A : SpinOperator n) (hA : A ∈ skewAdjoint (SpinOperator n)) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Unitary.linearIsometryEquiv
    ⟨NormedSpace.exp A, NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hA⟩

@[simp] theorem rotationExp_apply {n : ℕ} (A : SpinOperator n)
    (hA : A ∈ skewAdjoint (SpinOperator n)) (v : EuclideanSpace ℝ (Fin n)) :
    rotationExp A hA v = NormedSpace.exp A v := rfl

@[simp] theorem rotationExp_symm_apply {n : ℕ} (A : SpinOperator n)
    (hA : A ∈ skewAdjoint (SpinOperator n)) (v : EuclideanSpace ℝ (Fin n)) :
    (rotationExp A hA).symm v = NormedSpace.exp (-A) v := by
  change (star (NormedSpace.exp A)) v = _
  rw [NormedSpace.star_exp, skewAdjoint.mem_iff.mp hA]

namespace SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def reference (S : SpinSystem n V E) : Measure (V → Spin n) :=
  Measure.pi (fun x => siteReference n (S.pin x))

instance reference_isProbability [NeZero n] (S : SpinSystem n V E) :
    IsProbabilityMeasure S.reference := by
  unfold reference
  infer_instance

def energy (S : SpinSystem n V E) (K : E → SpinOperator n) (σ : V → Spin n) : ℝ :=
  ∑ e, S.strength e * ⟪(σ (S.left e)).val, K e (σ (S.right e)).val⟫_ℝ

def Z (S : SpinSystem n V E) (K : E → SpinOperator n) : ℝ :=
  ∫ σ, Real.exp (S.energy K σ) ∂S.reference

omit [Fintype V] in
theorem continuous_energy (S : SpinSystem n V E) (K : E → SpinOperator n) :
    Continuous (S.energy K) := by
  unfold energy
  fun_prop

def rotateConfiguration
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (V → Spin n) ≃ₜ (V → Spin n) :=
  Homeomorph.piCongrRight (fun x => spinRotation (U x))

def rotatePins (S : SpinSystem n V E)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    SpinSystem n V E :=
  { S with pin := fun x => (S.pin x).map (spinRotation (U x)) }

def gauge (S : SpinSystem n V E) (K : E → SpinOperator n)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    E → SpinOperator n :=
  fun e => (U (S.left e)).symm.toContinuousLinearEquiv.toContinuousLinearMap * K e *
    (U (S.right e)).toContinuousLinearEquiv.toContinuousLinearMap

def W (S : SpinSystem n V E) (A : E → SpinOperator n) : ℝ :=
  S.Z (fun e => NormedSpace.exp (A e)) / S.Z (fun _ => 1)

def gaugeProduct (S : SpinSystem n V E) (F : V → SpinOperator n) : E → SpinOperator n :=
  fun e => NormedSpace.exp (F (S.left e)) *
    NormedSpace.exp (F (S.right e) - F (S.left e)) *
    NormedSpace.exp (-F (S.right e))

def twistEnergy (S : SpinSystem n V E) (A : E → SpinOperator n)
    (k : ℕ) (t : ℝ) (σ : V → Spin n) : ℝ :=
  S.energy (fun e => NormedSpace.exp (t • A e) * A e ^ k) σ

def firstWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) * S.twistEnergy A 1 t σ

def secondWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) *
    (S.twistEnergy A 2 t σ + (S.twistEnergy A 1 t σ)^2)

def thirdWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) *
    (S.twistEnergy A 3 t σ + 3 * S.twistEnergy A 1 t σ * S.twistEnergy A 2 t σ +
      (S.twistEnergy A 1 t σ)^3)

def fourthWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) *
    (S.twistEnergy A 4 t σ + 4 * S.twistEnergy A 1 t σ * S.twistEnergy A 3 t σ +
      3 * (S.twistEnergy A 2 t σ)^2 +
      6 * (S.twistEnergy A 1 t σ)^2 * S.twistEnergy A 2 t σ +
      (S.twistEnergy A 1 t σ)^4)

def average (S : SpinSystem n V E) (f : (V → Spin n) → ℝ) : ℝ :=
  (∫ σ, f σ * Real.exp (S.energy (fun _ => 1) σ) ∂S.reference) / S.Z (fun _ => 1)

theorem integrable_average_integrand [NeZero n] (S : SpinSystem n V E)
    {f : (V → Spin n) → ℝ} (hf : Continuous f) :
    Integrable (fun σ => f σ * Real.exp (S.energy (fun _ => 1) σ)) S.reference :=
  (hf.mul (S.continuous_energy _).rexp).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem average_add [NeZero n] (S : SpinSystem n V E)
    {f g : (V → Spin n) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    S.average (f+g) = S.average f + S.average g := by
  unfold average
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (S.integrable_average_integrand hf)
    (S.integrable_average_integrand hg), add_div]

omit [Fintype V] [Fintype E] in

def axisGradient (S : SpinSystem n V E) (f : V → ℝ) (g : SpinOperator n) : E → SpinOperator n :=
  fun e => (f (S.right e) - f (S.left e)) • g

end SpinSystem

def fourthBell {Ω : Type uΩ} (F : ℕ → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (F 0 t ω) * (F 4 t ω + 4 * F 1 t ω * F 3 t ω + 3 * (F 2 t ω)^2 +
    6 * (F 1 t ω)^2 * F 2 t ω + (F 1 t ω)^4)

def expPower {n : ℕ} (X : SpinOperator n) (a : ℕ) (t : ℝ) : SpinOperator n :=
  NormedSpace.exp (t • X) * X^a

def tripleJet {n : ℕ} (X Y Z : SpinOperator n) : ℕ → ℕ → ℕ → ℕ → ℝ → SpinOperator n
  | 0, a, b, c, t => expPower X a t * expPower Y b t * expPower Z c t
  | k+1, a, b, c, t => tripleJet X Y Z k (a+1) b c t +
      tripleJet X Y Z k a (b+1) c t + tripleJet X Y Z k a b (c+1) t

@[simp] theorem expPower_zero {n : ℕ} (X : SpinOperator n) (a : ℕ) :
    expPower X a 0 = X^a := by
  rw [expPower, zero_smul ℝ X, NormedSpace.exp_zero, one_mul]

namespace SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def gaugeEnergy (S : SpinSystem n V E) (F : V → SpinOperator n)
    (k : ℕ) (t : ℝ) (σ : V → Spin n) : ℝ :=
  S.energy (fun e => tripleJet (F (S.left e))
    (F (S.right e)-F (S.left e)) (-F (S.right e)) k 0 0 0 t) σ

omit [Fintype V] in
@[simp] theorem energy_zero (S : SpinSystem n V E) (σ : V → Spin n) :
    S.energy 0 σ = 0 := by simp [energy]

end SpinSystem

open scoped Matrix

def matrixOperator {n : ℕ} : Matrix (Fin n) (Fin n) ℝ ≃ₐ[ℝ] SpinOperator n :=
  (Matrix.toLinAlgEquiv (PiLp.basisFun 2 ℝ (Fin n))).trans
    (Module.End.toContinuousLinearMap (EuclideanSpace ℝ (Fin n)))
theorem matrixOperator_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    matrixOperator M v = WithLp.toLp 2 (M *ᵥ v.ofLp) := by
  change (Matrix.toLin (PiLp.basisFun 2 ℝ (Fin n)) (PiLp.basisFun 2 ℝ (Fin n)) M) v = _
  rw [← Matrix.toLpLin_eq_toLin, Matrix.toLpLin_apply]

def axisMatrixA : Matrix (Fin 3) (Fin 3) ℝ := !![0,0,0; 0,0,-1; 0,1,0]
def axisMatrixB : Matrix (Fin 3) (Fin 3) ℝ := !![0,0,1; 0,0,0; -1,0,0]
def axisMatrixC : Matrix (Fin 3) (Fin 3) ℝ := !![0,-1,0; 1,0,0; 0,0,0]
def axisA : SpinOperator 3 := matrixOperator axisMatrixA
def axisB : SpinOperator 3 := matrixOperator axisMatrixB
def axisC : SpinOperator 3 := matrixOperator axisMatrixC

theorem matrixOperator_star {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    star (matrixOperator M) = matrixOperator M.transpose := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    matrixOperator_apply, matrixOperator_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem axisC_skew : axisC ∈ skewAdjoint (SpinOperator 3) := by
  rw [skewAdjoint.mem_iff, axisC, matrixOperator_star, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixC]

def tripleMoment {R : Type uR} [Ring R] (X Y Z : R) : ℕ → ℕ → ℕ → ℕ → R
  | 0, a, b, c => X^a * Y^b * Z^c
  | k+1, a, b, c => tripleMoment X Y Z k (a+1) b c +
      tripleMoment X Y Z k a (b+1) c + tripleMoment X Y Z k a b (c+1)

def plane (f g : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0,0,g; 0,0,-f; -g,f,0]
def third : Matrix (Fin 3) (Fin 3) ℝ := !![0,-1,0; 1,0,0; 0,0,0]

def moment4Plane (f g h k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  tripleMoment (plane f g) (plane h k - plane f g) (-plane h k) 4 0 0 0

/-- Block-diagonal 3×3 matrices (a 2×2 block and a scalar); products of two `plane`
matrices have this shape. -/
def blkM (p q r s t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![p,q,0; r,s,0; 0,0,t]

def planeOperator (f g : ℝ) : SpinOperator 3 := matrixOperator (plane f g)

def mixedMatrixAB : Matrix (Fin 3) (Fin 3) ℝ := !![0,1/2,0;1/2,0,0;0,0,0]
def mixedMatrixAAB : Matrix (Fin 3) (Fin 3) ℝ := (-1/3 : ℝ) • axisMatrixB
def mixedMatrixABB : Matrix (Fin 3) (Fin 3) ℝ := (-1/3 : ℝ) • axisMatrixA
def mixedMatrixAABB : Matrix (Fin 3) (Fin 3) ℝ := (-1/6 : ℝ) • (axisMatrixA^2+axisMatrixB^2)

def mixedAB : SpinOperator 3 := matrixOperator mixedMatrixAB
def mixedAAB : SpinOperator 3 := matrixOperator mixedMatrixAAB
def mixedABB : SpinOperator 3 := matrixOperator mixedMatrixABB
def mixedAABB : SpinOperator 3 := matrixOperator mixedMatrixAABB

namespace SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem average_mul_const (S : SpinSystem n V E) (r : ℝ) (f : (V → Spin n) → ℝ) :
    S.average (fun σ => r * f σ) = r * S.average f := by
  simp only [average, mul_assoc, integral_const_mul, mul_div_assoc]

def fourthPolynomial (F : ℕ → ℝ) : ℝ :=
  F 4 + 4 * F 1 * F 3 + 3 * (F 2)^2 + 6 * (F 1)^2 * F 2 + (F 1)^4

def fourthResponse (S : SpinSystem n V E) (A : E → SpinOperator n) : ℝ :=
  S.average (fun σ => fourthPolynomial (fun k => S.energy (fun e => A e ^ k) σ))

omit [Fintype V] [Fintype E] in
def crossForm (S : SpinSystem 3 V E) (f g : V → ℝ) : E → ℝ :=
  fun e => f (S.left e)*g (S.right e)-g (S.left e)*f (S.right e)

omit [Fintype V] [Fintype E] in
def planarGradient (S : SpinSystem 3 V E) (f g : V → ℝ) : E → SpinOperator 3 :=
  fun e => planeOperator (f (S.right e)) (g (S.right e)) -
    planeOperator (f (S.left e)) (g (S.left e))

def secondAxisResponse (S : SpinSystem 3 V E) (h k : E → ℝ) : ℝ :=
  S.average (fun σ => S.energy (fun e => (h e*k e) • axisC^2) σ +
    S.energy (fun e => h e • axisC) σ * S.energy (fun e => k e • axisC) σ)

end SpinSystem

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.TorusFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

noncomputable section
open scoped BigOperators ComplexConjugate

namespace ClassicalON

abbrev DiscreteTorus (L : ℕ) := ZMod L × ZMod L

def torusWave {L : ℕ} [NeZero L] (p x : DiscreteTorus L) : ℂ :=
  ZMod.stdAddChar (p.1*x.1+p.2*x.2)

variable {L : ℕ} [NeZero L]

@[simp] theorem torusWave_norm (p x : DiscreteTorus L) : ‖torusWave p x‖ = 1 :=
  AddChar.norm_apply _ _

@[simp] theorem torusWave_add (p x y : DiscreteTorus L) :
    torusWave p (x+y) = torusWave p x * torusWave p y := by
  unfold torusWave
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

@[simp] theorem torusWave_zero (p : DiscreteTorus L) : torusWave p 0 = 1 := by
  simp [torusWave]

@[simp] theorem torusWave_conj (p x : DiscreteTorus L) :
    conj (torusWave p x) = torusWave (-p) x := by
  unfold torusWave
  rw [← AddChar.map_neg_eq_conj]
  congr 1
  simp only [Prod.fst_neg, Prod.snd_neg]
  ring

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.DyadicFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

abbrev DyadicFreq (k : ℕ) := Σ j : Fin k, Fin (2^j.val) × Fin (2*2^j.val+1)

def dyadicRadius {k : ℕ} (p : DyadicFreq k) : ℕ := 2^p.1.val

def dyadicPoint {k : ℕ} (p : DyadicFreq k) : ℤ × ℤ :=
  ((dyadicRadius p : ℤ)+p.2.1.val, (p.2.2.val:ℤ)-dyadicRadius p)

def dyadicTorusPoint {k : ℕ} (p : DyadicFreq k) : DiscreteTorus (16*2^k) :=
  (((dyadicPoint p).1:ZMod (16*2^k)), ((dyadicPoint p).2:ZMod (16*2^k)))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SmoothProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped Topology ContDiff

namespace ClassicalON

def thetaBump : ContDiffBump (0 : ℝ) := ⟨4/3, 5/3, by norm_num, by norm_num⟩
def outerBump : ContDiffBump (0 : ℝ) := ⟨7/4, 15/8, by norm_num, by norm_num⟩
def innerBump : ContDiffBump (0 : ℝ) := ⟨9/8, 5/4, by norm_num, by norm_num⟩

def squareTheta (z : ℝ × ℝ) : ℝ := thetaBump z.1 * thetaBump z.2

def squareCutoff (z : ℝ × ℝ) : ℝ :=
  outerBump z.1 * outerBump z.2 * (1-innerBump z.1*innerBump z.2)

def squareGradient (m : Bool) (z : ℝ × ℝ) : ℝ :=
  if m then thetaBump z.1 * deriv thetaBump z.2 else deriv thetaBump z.1 * thetaBump z.2

def squareProfile (m sign : Bool) (z : ℝ × ℝ) : ℝ :=
  if sign then (squareCutoff z-squareGradient m z)/2 else
    (squareCutoff z+squareGradient m z)/2

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ProfileEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff BigOperators
namespace ClassicalON

def squareStep (m : Bool) (ε : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  if m then (z.1,z.2+ε) else (z.1+ε,z.2)

@[simp] theorem squareStep_distance (m : Bool) (ε : ℝ) (z : ℝ × ℝ) :
    ‖squareStep m ε z-z‖ = |ε| := by
  cases m <;> simp [squareStep, Prod.norm_def, Real.norm_eq_abs, abs_nonneg]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.LatticeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace ClassicalON

def latticeAxis (m : Bool) : Site := if m then (0,1) else (1,0)

def latticeTorus (L : ℕ) (x : Site) : DiscreteTorus L := ((x.1:ZMod L),(x.2:ZMod L))

@[simp] theorem latticeTorus_add (L : ℕ) (x y : Site) :
    latticeTorus L (x+y) = latticeTorus L x+latticeTorus L y := by
  ext <;> simp [latticeTorus]

def scaledSite (k : ℕ) (x : Site) : ℝ × ℝ :=
  ((x.1:ℝ)/(2:ℝ)^k, (x.2:ℝ)/(2:ℝ)^k)

@[simp] theorem scaledSite_add_axis (k : ℕ) (x : Site) (m : Bool) :
    scaledSite k (x+latticeAxis m) = squareStep m (1/(2:ℝ)^k) (scaledSite k x) := by
  cases m <;> ext <;> simp [scaledSite, latticeAxis, squareStep, add_div]

namespace LatticeGraph

def edgeDirection (G : LatticeGraph) (e : G.edges) : Bool :=
  decide (e.val.2.val.1 = e.val.1.val.1)

abbrev DirectionalEdges (G : LatticeGraph) (m : Bool) := {e : G.edges // G.edgeDirection e=m}

def WithinDyadicBox (G : LatticeGraph) (k : ℕ) : Prop :=
  ∀ x : G.vertices, |x.val.1| ≤ 2*(2^k:ℕ) ∧ |x.val.2| ≤ 2*(2^k:ℕ)

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.LatticeRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical
namespace ClassicalON.LatticeGraph

def restrictVertices (G : LatticeGraph) (P : Site → Prop) : Finset Site := G.vertices.filter P

def restrictVertex (G : LatticeGraph) (P : Site → Prop) (v : G.restrictVertices P) : G.vertices :=
  ⟨v.val,(Finset.mem_filter.mp v.property).1⟩

def restrict (G : LatticeGraph) (P : Site → Prop) : LatticeGraph where
  vertices := G.restrictVertices P
  edges := Finset.univ.filter (fun e : G.restrictVertices P × G.restrictVertices P =>
    (G.restrictVertex P e.1,G.restrictVertex P e.2)∈G.edges)
  nearest _e he := G.nearest _ (Finset.mem_filter.mp he).2

def restrictEdge (G : LatticeGraph) (P : Site → Prop) (e : (G.restrict P).edges) : G.edges :=
  ⟨(G.restrictVertex P e.val.1,G.restrictVertex P e.val.2),(Finset.mem_filter.mp e.property).2⟩

def restrictEdgeEquiv (G : LatticeGraph) (P : Site → Prop) :
    {e : G.edges // P e.val.1.val ∧ P e.val.2.val} ≃ (G.restrict P).edges where
  toFun e := ⟨(⟨e.val.val.1.val,Finset.mem_filter.mpr ⟨e.val.val.1.property,e.property.1⟩⟩,
    ⟨e.val.val.2.val,Finset.mem_filter.mpr ⟨e.val.val.2.property,e.property.2⟩⟩),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.val.property⟩⟩
  invFun e := ⟨G.restrictEdge P e,(Finset.mem_filter.mp e.val.1.property).2,
    (Finset.mem_filter.mp e.val.2.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def translateVertexEquiv (G : LatticeGraph) (z : Site) :
    G.vertices ≃ G.vertices.map (Equiv.addRight (-z)).toEmbedding :=
  Finset.equivMap (Equiv.addRight (-z)).toEmbedding G.vertices

def translate (G : LatticeGraph) (z : Site) : LatticeGraph where
  vertices := G.vertices.map (Equiv.addRight (-z)).toEmbedding
  edges := G.edges.map ((Equiv.prodCongr (G.translateVertexEquiv z) (G.translateVertexEquiv z)).toEmbedding)
  nearest e he := by
    obtain ⟨e',he',rfl⟩ := Finset.mem_map.mp he
    have h := G.nearest e' he'
    change PositiveNeighbor (e'.1.val+-z) (e'.2.val+-z)
    rcases h with h | h
    · left
      constructor <;> simp only [Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg]
      · omega
      · omega
    · right
      constructor <;> simp only [Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg]
      · omega
      · omega

def translateEdgeEquiv (G : LatticeGraph) (z : Site) : G.edges ≃ (G.translate z).edges :=
  Finset.equivMap ((Equiv.prodCongr (G.translateVertexEquiv z) (G.translateVertexEquiv z)).toEmbedding) G.edges

@[simp] theorem translateVertexEquiv_val (G : LatticeGraph) (z : Site) (v : G.vertices) :
    (G.translateVertexEquiv z v).val=v.val-z := rfl

@[simp] theorem translateEdgeEquiv_left (G : LatticeGraph) (z : Site) (e : G.edges) :
    (G.translateEdgeEquiv z e).val.1=G.translateVertexEquiv z e.val.1 := rfl

@[simp] theorem translateEdgeEquiv_right (G : LatticeGraph) (z : Site) (e : G.edges) :
    (G.translateEdgeEquiv z e).val.2=G.translateVertexEquiv z e.val.2 := rfl

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.LatticeRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical
namespace ClassicalON

def siteRadius (z v : Site) : ℤ := max |v.1-z.1| |v.2-z.2|

@[simp] theorem siteRadius_self (z : Site) : siteRadius z z=0 := by simp [siteRadius]

theorem siteRadius_symm (z v : Site) : siteRadius z v=siteRadius v z := by
  simp only [siteRadius,abs_sub_comm]

theorem siteRadius_triangle (x y z : Site) : siteRadius x z≤ siteRadius x y+siteRadius y z := by
  apply max_le
  · have h := abs_add_le (y.1-x.1) (z.1-y.1)
    have h1 : |y.1-x.1|≤ siteRadius x y := le_max_left _ _
    have h2 : |z.1-y.1|≤ siteRadius y z := le_max_left _ _
    have he : (y.1-x.1)+(z.1-y.1)=z.1-x.1 := by ring
    rw [he] at h
    omega
  · have h := abs_add_le (y.2-x.2) (z.2-y.2)
    have h1 : |y.2-x.2|≤ siteRadius x y := le_max_right _ _
    have h2 : |z.2-y.2|≤ siteRadius y z := le_max_right _ _
    have he : (y.2-x.2)+(z.2-y.2)=z.2-x.2 := by ring
    rw [he] at h
    omega

def annulusSites (N : ℤ) (z : Site) : Set Site := {v | N≤ siteRadius z v ∧ siteRadius z v≤2*N}

def annulusBoundary (N : ℤ) (z : Site) : Set Site := {v | siteRadius z v=N ∨ siteRadius z v=2*N}

def annulusInterior (N : ℤ) (z : Site) : Set Site := {v | N<siteRadius z v ∧ siteRadius z v<2*N}

theorem annuli_disjoint {N : ℤ} {x y : Site} (hxy : 4*N<siteRadius x y) :
    Disjoint (annulusSites N x) (annulusSites N y) := by
  apply Set.disjoint_left.mpr
  intro z hx hy
  have ht := siteRadius_triangle x z y
  rw [siteRadius_symm z y] at ht
  change N≤ siteRadius x z ∧ siteRadius x z≤2*N at hx
  change N≤ siteRadius y z ∧ siteRadius y z≤2*N at hy
  omega

namespace LatticeGraph

def annulusGraph (G : LatticeGraph) (N : ℤ) (z : Site) := G.restrict (·∈annulusSites N z)

def annulusInner (G : LatticeGraph) (N : ℤ) (z : Site) : Set (G.annulusGraph N z).vertices :=
  {v | siteRadius z v.val=N}

def annulusOuter (G : LatticeGraph) (N : ℤ) (z : Site) : Set (G.annulusGraph N z).vertices :=
  {v | siteRadius z v.val=2*N}

def annulusPins (G : LatticeGraph) (N : ℤ) (z : Site) : Set (G.annulusGraph N z).vertices :=
  G.annulusInner N z∪G.annulusOuter N z

def annulusCoupling (G : LatticeGraph) (b : G.edges → ℝ) (N : ℤ) (z : Site) :
    (G.annulusGraph N z).edges → ℝ := fun e => b (G.restrictEdge _ e)

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK

noncomputable section
open Set
open scoped Classical
namespace ClassicalON
variable {K : Type uK}

def SeparatedCenters (N : ℤ) (z : K → Site) : Prop := ∀ i j,i≠j → 4*N<siteRadius (z i) (z j)

def centerLabel (N : ℤ) (z : K → Site) (v : Site) : Option K :=
  if h : ∃ i,v∈annulusSites N (z i) then some h.choose else none

def centerPins (N : ℤ) (z : K → Site) : Set Site := {v | ∃ i,v∈annulusBoundary N (z i)}

theorem annulus_unique (N : ℤ) (z : K → Site) (hz : SeparatedCenters N z)
    (v : Site) {i j : K} (hi : v∈annulusSites N (z i)) (hj : v∈annulusSites N (z j)) : i=j := by
  by_contra h
  exact Set.disjoint_left.mp (annuli_disjoint (hz i j h)) hi hj

theorem centerLabel_some_iff (N : ℤ) (z : K → Site) (hz : SeparatedCenters N z) (v : Site) (i : K) :
    centerLabel N z v=some i ↔ v∈annulusSites N (z i) := by
  unfold centerLabel
  split_ifs with h
  · constructor
    · intro he
      have hi := Option.some.inj he
      exact hi ▸ h.choose_spec
    · intro hv
      congr 1
      exact annulus_unique N z hz v h.choose_spec hv
  · constructor
    · intro he; cases he
    · intro hv; exact False.elim (h ⟨i,hv⟩)

theorem annulusBoundary_subset (N : ℤ) (hN : 0≤N) (z : Site) :
    annulusBoundary N z⊆annulusSites N z := by
  intro v hv
  change siteRadius z v=N ∨ siteRadius z v=2*N at hv
  change N≤ siteRadius z v ∧ siteRadius z v≤2*N
  omega

theorem local_centerPins_iff (N : ℤ) (hN : 0≤N) (z : K → Site) (hz : SeparatedCenters N z)
    (v : Site) (i : K) (hi : v∈annulusSites N (z i)) :
    v∈centerPins N z ↔ v∈annulusBoundary N (z i) := by
  constructor
  · rintro ⟨j,hj⟩
    have hij := annulus_unique N z hz v hi (annulusBoundary_subset N hN _ hj)
    exact hij ▸ hj
  · exact fun h => ⟨i,h⟩

namespace LatticeGraph

def annulusVertexLabel (G : LatticeGraph) (N : ℤ) (z : K → Site) : G.vertices → Option K :=
  fun v => centerLabel N z v.val

def annulusEdgeLabel (G : LatticeGraph) (N : ℤ) (z : K → Site) (e : G.edges) : Option K :=
  if h : ∃ i,e.val.1.val∈annulusSites N (z i) ∧ e.val.2.val∈annulusSites N (z i) then some h.choose else none

def allAnnulusPins (G : LatticeGraph) (N : ℤ) (z : K → Site) : Set G.vertices :=
  {v | v.val∈centerPins N z}

theorem annulusEdgeLabel_some_iff (G : LatticeGraph) (N : ℤ) (z : K → Site)
    (hz : SeparatedCenters N z) (e : G.edges) (i : K) :
    G.annulusEdgeLabel N z e=some i ↔
      e.val.1.val∈annulusSites N (z i) ∧ e.val.2.val∈annulusSites N (z i) := by
  unfold annulusEdgeLabel
  split_ifs with h
  · constructor
    · intro he
      exact Option.some.inj he ▸ h.choose_spec
    · intro hv
      congr 1
      exact annulus_unique N z hz _ h.choose_spec.1 hv.1
  · constructor
    · intro he; cases he
    · intro hv; exact False.elim (h ⟨i,hv⟩)

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CoarseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open scoped Classical
namespace ClassicalON

def coarseSite (N : ℤ) (v : Site) : Site := (v.1/N,v.2/N)
def coarseCenter (N : ℤ) (v : Site) : Site := (N*v.1,N*v.2)

abbrev SiteColor := Fin 5 × Fin 5

def siteColor (v : Site) : SiteColor :=
  (⟨(v.1%5).toNat,by omega⟩,⟨(v.2%5).toNat,by omega⟩)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CoarseCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

abbrev CoarseDirection := Fin 3 × Fin 3
abbrev CoarseCode (L : ℕ) := Fin L → CoarseDirection

def directionVector (d : CoarseDirection) : Site := ((d.1.val:ℤ)-1,(d.2.val:ℤ)-1)
def codePosition {L : ℕ} (z : Site) (c : CoarseCode L) (i : Fin (L+1)) : Site :=
  z+Fin.partialSum (directionVector ∘ c) i

@[simp] theorem codePosition_zero {L : ℕ} (z : Site) (c : CoarseCode L) : codePosition z c 0=z := by
  simp [codePosition]

abbrev SimpleCoarseCode (z : Site) (L : ℕ) := {c : CoarseCode L // Function.Injective (codePosition z c)}

theorem codeColor_exists (t : ℕ) (z : Site) (c : CoarseCode (25*t)) :
    ∃ q : SiteColor,t≤Fintype.card {i : Fin (25*t+1) // siteColor (codePosition z c i)=q} := by
  obtain ⟨q,hq⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (fun i => siteColor (codePosition z c i)) (n := t) (by simp [SiteColor])
  exact ⟨q,by simpa only [Fintype.card_subtype] using hq⟩

def codeColor (t : ℕ) (z : Site) (c : CoarseCode (25*t)) : SiteColor :=
  (codeColor_exists t z c).choose

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FerromagneticMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} {E : Type uE} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Fintype E] (μ : Measure X) [IsProbabilityMeasure μ]
  (T : E → X → ℝ)

def edgeHamiltonian (b : E → ℝ) (x : X) : ℝ := ∑ e,b e*T e x

def edgeMean (b : E → ℝ) (f : X → ℝ) : ℝ := exponentialMean μ (edgeHamiltonian T b) f

def EdgeCovarianceNonneg : Prop := ∀ b : E → ℝ,(∀ e,0≤b e) → ∀ e f : E,
  edgeMean μ T b (T e)*edgeMean μ T b (T f)≤edgeMean μ T b (fun x => T e x*T f x)

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.WeightedTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory
namespace ClassicalON

section Product
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology X] [FirstCountableTopology Y] [LocallyCompactSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def marginalWeight (w : Y×X → ℝ) (y : Y) : ℝ := ∫ x,w (y,x) ∂μ

def conditionalMean (w f : Y×X → ℝ) (y : Y) : ℝ :=
  weightedMean μ (fun x => w (y,x)) (fun x => f (y,x))

end Product
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AmplitudePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uX

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} {V : Type uV} {E : Type uE} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Fintype E] (μ : Measure X) [IsProbabilityMeasure μ]
  (T : E → X → ℝ) (left right : E → V) (b : E → ℝ)

def amplitudeCoupling (a : V → ℝ) (e : E) : ℝ := b e*a (left e)*a (right e)

def amplitudePartition (a : V → ℝ) : ℝ :=
  ∫ x,Real.exp (edgeHamiltonian T (amplitudeCoupling left right b a) x) ∂μ

def amplitudeSlope (a d : V → ℝ) (t : ℝ) (e : E) : ℝ :=
  b e*(d (left e)*(a (right e)+t*d (right e))+(a (left e)+t*d (left e))*d (right e))

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.IsingReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ClassicalON

instance signLaw_isProbability : IsProbabilityMeasure signLaw := by
  constructor
  norm_num [signLaw,Measure.count_apply_finite]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

variable {V : Type uV} [Fintype V]

instance isingReference_isProbability : IsProbabilityMeasure (isingReference (V := V)) := by
  unfold isingReference; infer_instance

def isingU (t : Bool×Bool) : ℝ := (signValue t.1+signValue t.2)/2

def isingW (t : Bool×Bool) : ℝ := (signValue t.1-signValue t.2)/2

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.MomentCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uJ uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

def MomentCone {X : Type uX} {I : Type uI} (a : I → X → ℝ) (f : X → ℝ) : Prop :=
  ∃ (k : ℕ) (c : Fin k → ℝ) (p : Fin k → List I),
    (∀ j,0≤c j) ∧ ∀ x,f x=∑ j,c j*((p j).map (fun i => a i x)).prod

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ProductMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uV uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {I : Type uI} {X : Type uX} [Fintype V] [DecidableEq V]

def retainedIndices (v : V) (l : List (V×I)) : List I :=
  l.filterMap (fun p => if p.1=v then some p.2 else none)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.IsingGinibre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def isingDoubleVariable (i : V×Bool) (p : V → Bool×Bool) : ℝ :=
  if i.2 then isingU (p i.1) else isingW (p i.1)

def isingDoubleEnergy (left right : E → V) (e : E) (p : V → Bool×Bool) : ℝ :=
  isingU (p (left e))*isingU (p (right e))+isingW (p (left e))*isingW (p (right e))

def isingDoubleDifference (left right : E → V) (e : E) (p : V → Bool×Bool) : ℝ :=
  2*(isingU (p (left e))*isingW (p (right e))+isingW (p (left e))*isingU (p (right e)))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.TorusDouble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section
open MeasureTheory
namespace ClassicalON

abbrev PlanarAngle := UnitAddCircle

def angleLaw : Measure PlanarAngle := AddCircle.haarAddCircle

instance angleLaw_isProbability : IsProbabilityMeasure angleLaw := by
  unfold angleLaw; infer_instance
instance angleLaw_isAddHaar : angleLaw.IsAddHaarMeasure := by
  unfold angleLaw; infer_instance

variable {V : Type uV} [Fintype V]

def planarReference : Measure (V → PlanarAngle) := Measure.pi (fun _ => angleLaw)

instance planarReference_isProbability : IsProbabilityMeasure (planarReference (V := V)) := by
  unfold planarReference; infer_instance
instance planarReference_isAddHaar : (planarReference (V := V)).IsAddHaarMeasure := by
  unfold planarReference; infer_instance

def torusDouble : ((V → PlanarAngle)×(V → PlanarAngle)) →+
    ((V → PlanarAngle)×(V → PlanarAngle)) where
  toFun p := (p.1+p.2,p.1-p.2)
  map_zero' := by simp
  map_add' := by intros; ext <;> simp <;> abel

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PlanarAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
namespace ClassicalON

open scoped ComplexConjugate

def planarCharacter (t : PlanarAngle) : ℂ := AddCircle.toCircle t

def planarCos (t : PlanarAngle) : ℝ := (planarCharacter t).re

def planarSin (t : PlanarAngle) : ℝ := (planarCharacter t).im

variable {V : Type uV} {E : Type uE}

def planarEnergy (left right : E → V) (e : E) (θ : V → PlanarAngle) : ℝ :=
  planarCos (θ (left e)-θ (right e))

def planarSine (left right : E → V) (e : E) (θ : V → PlanarAngle) : ℝ :=
  planarSin (θ (left e)-θ (right e))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PlanarGinibre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def planarHamiltonian (left right : E → V) (b : E → ℝ) (θ : V → PlanarAngle) : ℝ :=
  ∑ e,b e*planarEnergy left right e θ

def planarMean (left right : E → V) (b : E → ℝ) (f : (V → PlanarAngle) → ℝ) : ℝ :=
  exponentialMean planarReference (planarHamiltonian left right b) f

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AmplitudeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
namespace ClassicalON

abbrev Amplitude := Set.Icc (0 : ℝ) 1

def transverseAmplitude (r : Amplitude) : ℝ := Real.sqrt (1-(r:ℝ)^2)

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def isingAmplitudePartition (left right : E → V) (b : E → ℝ) (r : V → Amplitude) : ℝ :=
  amplitudePartition isingReference (isingEnergy left right) left right b (fun v => (r v : ℝ))

def planarAmplitudePartition (left right : E → V) (b : E → ℝ) (r : V → Amplitude) : ℝ :=
  amplitudePartition planarReference (planarEnergy left right) left right b (fun v => transverseAmplitude (r v))

def amplitudeDensity (left right : E → V) (b : E → ℝ) (r : V → Amplitude) : ℝ :=
  isingAmplitudePartition left right b r*planarAmplitudePartition left right b r

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ClassicalON

theorem planarCos_sq_add_sin_sq (θ : PlanarAngle) : planarCos θ^2+planarSin θ^2=1 := by
  have h := Circle.normSq_coe (AddCircle.toCircle θ)
  simpa [Complex.normSq_apply,planarCos,planarSin,planarCharacter,pow_two] using h

theorem signValue_sq (τ : Bool) : signValue τ^2=1 := by cases τ <;> norm_num [signValue]

theorem transverseAmplitude_sq (r : Amplitude) : transverseAmplitude r^2=1-(r:ℝ)^2 := by
  apply Real.sq_sqrt
  have h0:=r.property.1
  have h1:=r.property.2
  nlinarith

theorem normSq_three (v : EuclideanSpace ℝ (Fin 3)) : ‖v‖^2=v 0^2+v 1^2+v 2^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ,add_assoc]

def cylindricalSpin (r : Amplitude) (τ : Bool) (θ : PlanarAngle) : Spin 3 :=
  ⟨WithLp.toLp 2 ![(r:ℝ)*signValue τ,transverseAmplitude r*planarCos θ,
    transverseAmplitude r*planarSin θ],by
    rw [mem_sphere_zero_iff_norm]
    have h := planarCos_sq_add_sin_sq θ
    have hq := transverseAmplitude_sq r
    have ht := signValue_sq τ
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    rw [normSq_three]
    change ((r:ℝ)*signValue τ)^2+(transverseAmplitude r*planarCos θ)^2+
      (transverseAmplitude r*planarSin θ)^2=1^2
    calc
      _ = (r:ℝ)^2*signValue τ^2+transverseAmplitude r^2*(planarCos θ^2+planarSin θ^2) := by ring
      _ = 1^2 := by rw [ht,h,hq]; ring⟩

def cylinderLinear (τ : Bool) (θ : PlanarAngle) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun v := WithLp.toLp 2 ![signValue τ*v 0,
    planarCos θ*v 1-planarSin θ*v 2,planarSin θ*v 1+planarCos θ*v 2]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a v := by ext i; fin_cases i <;> simp <;> ring

theorem cylinderLinear_norm (τ : Bool) (θ : PlanarAngle) (v : EuclideanSpace ℝ (Fin 3)) :
    ‖cylinderLinear τ θ v‖=‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [normSq_three,normSq_three]
  have h := planarCos_sq_add_sin_sq θ
  have ht := signValue_sq τ
  change (signValue τ*v 0)^2+(planarCos θ*v 1-planarSin θ*v 2)^2+
    (planarSin θ*v 1+planarCos θ*v 2)^2=_
  nlinarith [congrArg (fun a : ℝ => a*(v 1^2+v 2^2)) h,
    congrArg (fun a : ℝ => a*v 0^2) ht]

def cylinderRotation (τ : Bool) (θ : PlanarAngle) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearIsometryEquiv.ofSurjective
    {cylinderLinear τ θ with norm_map' := cylinderLinear_norm τ θ}
    (LinearMap.surjective_of_injective
      (show Function.Injective (cylinderLinear τ θ) from
        (show EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) from
          {cylinderLinear τ θ with norm_map' := cylinderLinear_norm τ θ}).injective))

@[simp] theorem cylinderRotation_apply (τ : Bool) (θ : PlanarAngle) (v : EuclideanSpace ℝ (Fin 3)) :
    cylinderRotation τ θ v=cylinderLinear τ θ v := rfl

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace ClassicalON

def firstAmplitude (s : Spin 3) : Amplitude := ⟨|s.val 0|,abs_nonneg _,by
  simpa only [Real.norm_eq_abs,spin_norm] using PiLp.norm_apply_le s.val 0⟩

@[simp] theorem firstAmplitude_cylindricalSpin (r : Amplitude) (τ : Bool) (θ : PlanarAngle) :
    firstAmplitude (cylindricalSpin r τ θ)=r := by
  apply Subtype.ext
  change |(r:ℝ)*signValue τ|=(r:ℝ)
  cases τ <;> simp [signValue,abs_of_nonneg r.property.1]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ClassicalON

def cylinderLaw : Measure (Bool×PlanarAngle) := signLaw.prod angleLaw
instance cylinderLaw_isProbability : IsProbabilityMeasure cylinderLaw := by
  unfold cylinderLaw; infer_instance

def sphericalAmplitudeLaw : Measure Amplitude := (sphereProbability 3).map firstAmplitude

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def freeSpinReference (n : ℕ) : Measure (V → Spin n) := Measure.pi (fun _ => sphereProbability n)
instance freeSpinReference_isProbability (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (freeSpinReference (V := V) n) := by unfold freeSpinReference; infer_instance

def freeSpinEnergy (n : ℕ) (left right : E → V) (b : E → ℝ) (s : V → Spin n) : ℝ :=
  ∑ e,b e*⟪(s (left e)).val,(s (right e)).val⟫_ℝ

def freeSpinMean (n : ℕ) (left right : E → V) (b : E → ℝ) (f : (V → Spin n) → ℝ) : ℝ :=
  weightedMean (freeSpinReference n) (fun s => Real.exp (freeSpinEnergy n left right b s)) f

def cylindricalConfiguration (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) : V → Spin 3 :=
  fun v => cylindricalSpin (r v) (τ v) (θ v)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.UpperEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology Classical
namespace ClassicalON

instance sphereProbability_isOpenPos (n : ℕ) [NeZero n] :
    (sphereProbability n).IsOpenPosMeasure := by
  unfold sphereProbability
  exact Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

variable {I : Type uI} [Fintype I]

def upperTent (δ : ℝ) (r : I → Amplitude) : ℝ := ∏ i,max 0 ((r i:ℝ)-(1-δ))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AmplitudeSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology Classical
namespace ClassicalON

variable {V : Type uV} [Fintype V]

def glueAmplitude (B : Set V) (a : B → Amplitude) (r : ↥(Bᶜ) → Amplitude) : V → Amplitude :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => Amplitude) (·∈B)).symm (a,r)

omit [Fintype V] in
@[simp] theorem glueAmplitude_in (B : Set V) (a : B → Amplitude) (r : ↥(Bᶜ) → Amplitude)
    (v : B) : glueAmplitude B a r v=a v := by
  simp [glueAmplitude,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,v.property]

omit [Fintype V] in
@[simp] theorem glueAmplitude_out (B : Set V) (a : B → Amplitude) (r : ↥(Bᶜ) → Amplitude)
    (v : ↥(Bᶜ)) : glueAmplitude B a r v=r v := by
  simp [glueAmplitude,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,show v.val∉B from v.property]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinnedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {A : Type uA} [Fintype V]

def glueFamily (B : Set V) (a : B → A) (r : ↥(Bᶜ) → A) : V → A :=
  (Equiv.piEquivPiSubtypeProd (·∈B) (fun _ : V => A)).symm (a,r)

omit [Fintype V] in
@[simp] theorem glueFamily_in (B : Set V) (a : B → A) (r : ↥(Bᶜ) → A) (v : B) :
    glueFamily B a r v=a v := by simp [glueFamily,Equiv.piEquivPiSubtypeProd,v.property]

omit [Fintype V] in
@[simp] theorem glueFamily_out (B : Set V) (a : B → A) (r : ↥(Bᶜ) → A) (v : ↥(Bᶜ)) :
    glueFamily B a r v=r v := by
  simp [glueFamily,Equiv.piEquivPiSubtypeProd,show v.val∉B from v.property]

section Measure
variable [MeasurableSpace A] [MeasurableSingletonClass A]

def pinProductMeasure (μ : Measure A) (B : Set V) (a : B → A) : Measure (V → A) :=
  Measure.pi (fun v => if h : v∈B then Measure.dirac (a ⟨v,h⟩) else μ)

instance pinProductMeasure_isProbability (μ : Measure A) [IsProbabilityMeasure μ]
    (B : Set V) (a : B → A) : IsProbabilityMeasure (pinProductMeasure μ B a) := by
  unfold pinProductMeasure
  have : ∀ v : V,IsProbabilityMeasure (if h : v∈B then Measure.dirac (a ⟨v,h⟩) else μ) := by
    intro v; split <;> infer_instance
  infer_instance

end Measure
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinnedCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def poleSpin (τ : Bool) : Spin 3 := cylindricalSpin ⊤ τ 0

def poleSystem (left right : E → V) (b : E → ℝ) (B : Set V) (t : B → Bool) : SpinSystem 3 V E :=
  ⟨left,right,b,fun v => if h : v∈B then some (poleSpin (t ⟨v,h⟩)) else none⟩

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondSubspace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators
namespace ClassicalON

abbrev SignField := ZMod 2

variable {V : Type uV} {E : Type uE}

def bondSubspace (left right : E → V) (η : E → Bool) : Submodule SignField (V → SignField) where
  carrier := {s | ∀ e,η e=true → s (left e)=s (right e)}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg e he; simp only [Pi.add_apply,hf e he,hg e he]
  smul_mem' := by intro c f hf e he; simp only [Pi.smul_apply,hf e he]

@[simp] theorem mem_bondSubspace (left right : E → V) (η : E → Bool) (s : V → SignField) :
    s∈bondSubspace left right η ↔ ∀ e,η e=true → s (left e)=s (right e) := Iff.rfl

variable [Fintype V]

def bondRank (left right : E → V) (η : E → Bool) : ℕ :=
  Module.finrank SignField (bondSubspace left right η)

def clusterWeight (left right : E → V) (η : E → Bool) : ℝ :=
  2^bondRank left right η

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uX

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def bondProduct (t : E → ℝ) (η : E → Bool) : ℝ := ∏ e,if η e then t e else 1

def bondWeight (left right : E → V) (t : E → ℝ) (η : E → Bool) : ℝ :=
  clusterWeight left right η*bondProduct t η

def finiteMean {X : Type uX} [Fintype X] (w f : X → ℝ) : ℝ := (∑ x,w x*f x)/(∑ x,w x)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

def signFieldEquiv : Bool ≃ SignField where
  toFun b := if b then 0 else 1
  invFun a := a=0
  left_inv b := by cases b <;> decide
  right_inv a := by
    have ha : a=0 ∨ a=1 := by fin_cases a <;> [exact Or.inl rfl; exact Or.inr rfl]
    rcases ha with rfl | rfl <;> simp

@[simp] theorem signFieldEquiv_true : signFieldEquiv true=0 := rfl
@[simp] theorem signFieldEquiv_false : signFieldEquiv false=1 := rfl

def fieldSign (a : SignField) : ℝ := if a=0 then 1 else -1

@[simp] theorem fieldSign_zero : fieldSign 0=1 := by simp [fieldSign]
@[simp] theorem fieldSign_one : fieldSign 1= -1 := by simp [fieldSign]

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def compatibleSigns (left right : E → V) (η : E → Bool) : Set (V → Bool) :=
  {s | ∀ e,η e=true → s (left e)=s (right e)}

def compatibleSignsEquiv (left right : E → V) (η : E → Bool) :
    compatibleSigns left right η ≃ bondSubspace left right η :=
  (Equiv.piCongrRight (fun _ : V => signFieldEquiv)).subtypeEquiv (by
    intro s
    change (∀ e,η e=true → s (left e)=s (right e)) ↔
      ∀ e,η e=true → signFieldEquiv (s (left e))=signFieldEquiv (s (right e))
    simp only [Equiv.apply_eq_iff_eq])

omit [Fintype V] [Fintype E] in
def bondConnected (left right : E → V) (η : E → Bool) (x y : V) : Prop :=
  ∀ s∈bondSubspace left right η,s x=s y

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def bondSignProduct (left right : E → V) (t : E → ℝ) (η : E → Bool) (s : V → Bool) : ℝ :=
  ∏ e,if η e then (if s (left e)=s (right e) then t e else 0) else 1

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinBondKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def spinBondParameter (left right : E → V) (b : E → ℝ) (s : V → Spin 3) (e : E) : ℝ :=
  1-Real.exp (-2*b e*max ((s (left e)).val 0*(s (right e)).val 0) 0)

def spinBondWeight (left right : E → V) (b : E → ℝ) (s : V → Spin 3) (η : E → Bool) : ℝ :=
  ∏ e,if η e then spinBondParameter left right b s e else 1-spinBondParameter left right b s e

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.JointBond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def amplitudeBondParam (left right : E → V) (b : E → ℝ) (r : V → Amplitude) (e : E) : ℝ :=
  Real.exp (2*b e*(r (left e):ℝ)*(r (right e):ℝ))-1

def bondConditionalMean (left right : E → V) (b : E → ℝ)
    (f : (V → Amplitude) → (E → Bool) → ℝ) (r : V → Amplitude) : ℝ :=
  finiteMean (bondWeight left right (amplitudeBondParam left right b r)) (f r)

def jointBondMean (μ : Measure Amplitude) (left right : E → V) (b : E → ℝ)
    (f : (V → Amplitude) → (E → Bool) → ℝ) : ℝ :=
  weightedMean (Measure.pi (fun _ : V => μ)) (amplitudeDensity left right b)
    (bondConditionalMean left right b f)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.RawBond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def amplitudeBondPrefactor (left right : E → V) (b : E → ℝ) (r : V → Amplitude) : ℝ :=
  (2:ℝ)⁻¹^Fintype.card V*Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
    planarAmplitudePartition left right b r

def amplitudeBondWeight (left right : E → V) (b : E → ℝ) (r : V → Amplitude) (η : E → Bool) : ℝ :=
  amplitudeBondPrefactor left right b r*bondWeight left right (amplitudeBondParam left right b r) η

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinBonds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def freeBondMean (left right : E → V) (b : E → ℝ) (f : (E → Bool) → ℝ) : ℝ :=
  freeSpinMean 3 left right b (fun s => ∑ η,spinBondWeight left right b s η*f η)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondPin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V]

def pinRestriction (B : Set V) : (V → SignField) →ₗ[SignField] (B → SignField) where
  toFun s := fun v => s v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def bondPinRank (left right : E → V) (B : Set V) (η : E → Bool) : ℕ :=
  Module.finrank SignField ((bondSubspace left right η).map (pinRestriction B))

def bondPinFactor (left right : E → V) (B : Set V) (η : E → Bool) : ℝ :=
  (2^bondPinRank left right B η)⁻¹

def pinnedBondSubspace (left right : E → V) (B : Set V) (η : E → Bool) :
    Submodule SignField (V → SignField) :=
  bondSubspace left right η⊓LinearMap.ker (pinRestriction B)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinnedSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V]

def positiveCompatibleSigns (left right : E → V) (B : Set V) (η : E → Bool) : Set (V → Bool) :=
  {s | s∈compatibleSigns left right η ∧ ∀ v∈B,s v=true}

def positiveCompatibleSignsEquiv (left right : E → V) (B : Set V) (η : E → Bool) :
    positiveCompatibleSigns left right B η ≃ pinnedBondSubspace left right B η :=
  (Equiv.piCongrRight (fun _ : V => signFieldEquiv)).subtypeEquiv (by
    intro s
    change ((∀ e,η e=true → s (left e)=s (right e)) ∧ ∀ v∈B,s v=true) ↔
      ((∀ e,η e=true → signFieldEquiv (s (left e))=signFieldEquiv (s (right e))) ∧
        (fun v : B => signFieldEquiv (s v))=0)
    simp only [Equiv.apply_eq_iff_eq,funext_iff,Pi.zero_apply,Subtype.forall,
      ← signFieldEquiv_true,Equiv.apply_eq_iff_eq])

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondConnectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE}

def bondGraph (left right : E → V) (η : E → Bool) : SimpleGraph V where
  Adj x y := x≠y ∧ ∃ e,η e=true ∧
    ((left e=x ∧ right e=y) ∨ (left e=y ∧ right e=x))
  symm := ⟨by
    intro x y ⟨h,e,he,hor⟩
    exact ⟨h.symm,e,he,hor.elim (fun ⟨a,b⟩ => Or.inr ⟨a,b⟩) (fun ⟨a,b⟩ => Or.inl ⟨a,b⟩)⟩⟩
  loopless := ⟨by intro x; simp⟩

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SignedSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE}

def prescribedCompatibleSigns (left right : E → V) (B : Set V) (p : V → Bool) (η : E → Bool) : Set (V → Bool) :=
  {s | s∈compatibleSigns left right η ∧ ∀ v∈B,s v=p v}

def signTranslate (t : V → Bool) : (V → Bool) ≃ (V → Bool) where
  toFun s v := s v==t v
  invFun s v := s v==t v
  left_inv s := by funext v; change ((s v==t v)==t v)=s v; cases s v <;> cases t v <;> rfl
  right_inv s := by funext v; change ((s v==t v)==t v)=s v; cases s v <;> cases t v <;> rfl

theorem signTranslate_compatible (left right : E → V) (η : E → Bool) (t : V → Bool)
    (ht : t∈compatibleSigns left right η) (s : V → Bool) :
    signTranslate t s∈compatibleSigns left right η ↔ s∈compatibleSigns left right η := by
  change (∀ e,η e=true → (s (left e)==t (left e))=(s (right e)==t (right e))) ↔ _
  constructor
  · intro h e he
    have h' := h e he
    rw [ht e he] at h'
    have hc (a b c : Bool) : (a==c)=(b==c) ↔ a=b := by
      cases a <;> cases b <;> cases c <;> decide
    exact (hc _ _ _).mp h'
  · intro h e he
    rw [h e he,ht e he]

def prescribedCompatibleSignsEquiv (left right : E → V) (B : Set V) (p : V → Bool) (η : E → Bool)
    (t : prescribedCompatibleSigns left right B p η) :
    positiveCompatibleSigns left right B η ≃ prescribedCompatibleSigns left right B p η :=
  (signTranslate t.val).subtypeEquiv (by
    intro s
    change (s∈compatibleSigns left right η ∧ ∀ v∈B,s v=true) ↔
      (signTranslate t.val s∈compatibleSigns left right η ∧ ∀ v∈B,(s v==t.val v)=p v)
    rw [signTranslate_compatible left right η t.val t.property.1]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro v
    apply forall_congr'
    intro hv
    rw [← t.property.2 v hv]
    cases s v <;> cases t.val v <;> decide)

variable [Fintype V]

def bondCrossing (left right : E → V) (I O : Set V) (η : E → Bool) : Prop :=
  ∃ x∈I,∃ y∈O,bondConnected left right η x y

def layerSigns (I : Set V) (v : V) : Bool := if v∈I then false else true

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def pinnedBondNumerator (μ : Measure Amplitude) (left right : E → V) (b : E → ℝ)
    (B : Set V) (f : (E → Bool) → ℝ) : ℝ :=
  ∫ r,∑ η,amplitudeBondWeight left right b (glueAmplitude B ⊤ r) η*
    bondPinFactor left right B η*f η ∂Measure.pi (fun _ : ↥(Bᶜ) => μ)

def pinnedBondMean (μ : Measure Amplitude) (left right : E → V) (b : E → ℝ)
    (B : Set V) (f : (E → Bool) → ℝ) : ℝ :=
  pinnedBondNumerator μ left right b B f/pinnedBondNumerator μ left right b B (fun _ => 1)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinnedBonds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def pinNormalization (B : Set V) : ℝ :=
  (2:ℝ)⁻¹^Fintype.card ↥(Bᶜ)/((2:ℝ)⁻¹^Fintype.card V)

def poleBondMean (left right : E → V) (b : E → ℝ) (B : Set V) (p : B → Bool)
    (f : (E → Bool) → ℝ) : ℝ :=
  weightedMean (poleSystem left right b B p).reference (fun s => Real.exp (freeSpinEnergy 3 left right b s))
    (fun s => ∑ η,spinBondWeight left right b s η*f η)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ProductGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uC uD uK uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {K : Type uK} [Fintype V] [Fintype K]
variable (A : V → Type uA) (label : V → K)

abbrev GroupedFamily := (k : K) → (v : {v // label v=k}) → A v.val

def groupedEquiv : GroupedFamily A label ≃ ((v : V) → A v) where
  toFun s v := s (label v) ⟨v,rfl⟩
  invFun s k v := s v.val
  left_inv s := by
    funext k v
    rcases v with ⟨v,h⟩
    subst k
    rfl
  right_inv _ := rfl

variable [∀ v,MeasurableSpace (A v)]

def groupedMeasurableEquiv : GroupedFamily A label ≃ᵐ ((v : V) → A v) where
  toEquiv := groupedEquiv A label
  measurable_toFun := Measurable.of_eval (fun v => (measurable_pi_apply (⟨v,rfl⟩ : {w // label w=label v})).comp (measurable_pi_apply (label v)))
  measurable_invFun := Measurable.of_eval (fun _ => Measurable.of_eval (fun v => measurable_pi_apply v.val))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinnedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} {K : Type uK} [Fintype V] [Fintype E] [Fintype K]

abbrev BlockVertex (B : Set V) (label : V → K) (k : K) := {v : ↥(Bᶜ) // label v.val=k}

def blockSpin (B : Set V) (label : V → K) (k : K) (s : BlockVertex B label k → Spin 3) : V → Spin 3 :=
  fun v => if hv : v∈B then poleSpin true else
    if hk : label v=k then s ⟨⟨v,hv⟩,hk⟩ else poleSpin true

def blockEnergy (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (k : K) (s : BlockVertex B label k → Spin 3) : ℝ :=
  freeSpinEnergy 3 (fun e : {e // elabel e=k} => left e.val) (fun e => right e.val)
    (fun e => b e.val) (blockSpin B label k s)

def blockBondWeight (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (k : K) (s : BlockVertex B label k → Spin 3)
    (η : {e // elabel e=k} → Bool) : ℝ :=
  spinBondWeight (fun e : {e // elabel e=k} => left e.val) (fun e => right e.val)
    (fun e => b e.val) (blockSpin B label k s) η

def blockBondMean (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (k : K) (f : ({e // elabel e=k} → Bool) → ℝ) : ℝ :=
  weightedMean (Measure.pi (fun _ : BlockVertex B label k => sphereProbability 3))
    (fun s => Real.exp (blockEnergy left right b B label elabel k s))
    (fun s => ∑ η,blockBondWeight left right b B label elabel k s η*f η)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uE uF uV uW

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {W : Type uW} {E : Type uE} {F : Type uF} {A : Type uA} [Fintype V] [Fintype W] [Fintype E] [Fintype F]

def arrowEquiv (e : E ≃ F) : (E → A) ≃ (F → A) where
  toFun η := fun f => η (e.symm f)
  invFun η := fun f => η (e f)
  left_inv η := by funext f; simp
  right_inv η := by funext f; simp

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK

noncomputable section
open Set
open scoped Classical
namespace ClassicalON.LatticeGraph
variable {K : Type uK}

def annulusFreeEquiv (G : LatticeGraph) (N : ℤ) (hN : 0≤N) (z : K → Site)
    (hz : SeparatedCenters N z) (i : K) :
    BlockVertex (G.allAnnulusPins N z) (G.annulusVertexLabel N z) (some i) ≃
      ↥((G.annulusPins N (z i))ᶜ) where
  toFun v := ⟨⟨v.val.val.val,Finset.mem_filter.mpr ⟨v.val.val.property,
    (centerLabel_some_iff N z hz _ i).mp v.property⟩⟩,
    fun hp => v.val.property ⟨i,hp⟩⟩
  invFun v := ⟨⟨G.restrictVertex _ v.val,fun hp => v.property
    ((local_centerPins_iff N hN z hz _ i (Finset.mem_filter.mp v.val.property).2).mp hp)⟩,
    (centerLabel_some_iff N z hz _ i).mpr (Finset.mem_filter.mp v.val.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def annulusEdgesEquiv (G : LatticeGraph) (N : ℤ) (z : K → Site)
    (hz : SeparatedCenters N z) (i : K) :
    {e : G.edges // G.annulusEdgeLabel N z e=some i} ≃ (G.annulusGraph N (z i)).edges :=
  (Equiv.subtypeEquivRight (fun e => G.annulusEdgeLabel_some_iff N z hz e i)).trans
    (G.restrictEdgeEquiv (·∈annulusSites N (z i)))

@[simp] theorem annulusEdgesEquiv_restrictEdge (G : LatticeGraph) (N : ℤ) (z : K → Site)
    (hz : SeparatedCenters N z) (i : K) (e : {e : G.edges // G.annulusEdgeLabel N z e=some i}) :
    G.restrictEdge _ (G.annulusEdgesEquiv N z hz i e)=e.val := rfl

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.DyadicSine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace ClassicalON

def dyadicAngle (k : ℕ) (t : ℝ) : ℝ := 2*Real.pi*t/(16*(2:ℝ)^k)

def dyadicLambda (k : ℕ) : ℝ :=
  (2:ℝ)^k * ∑ p : DyadicFreq k,
    (1/(dyadicRadius p:ℝ))^3 * Real.sin (dyadicAngle k (dyadicPoint p).1)

@[simp] theorem dyadicAngle_neg (k : ℕ) (t : ℝ) : dyadicAngle k (-t) = -dyadicAngle k t := by
  unfold dyadicAngle; ring

def dyadicReflect {k : ℕ} (p : DyadicFreq k) : DyadicFreq k :=
  ⟨p.1, p.2.1, p.2.2.rev⟩

@[simp] theorem dyadicReflect_radius {k : ℕ} (p : DyadicFreq k) :
    dyadicRadius (dyadicReflect p) = dyadicRadius p := rfl

@[simp] theorem dyadicReflect_point {k : ℕ} (p : DyadicFreq k) :
    (dyadicPoint (dyadicReflect p)).2 = -(dyadicPoint p).2 := by
  simp only [dyadicPoint, dyadicReflect, dyadicRadius, Fin.val_rev]
  have h := p.2.2.isLt
  omega

@[simp] theorem dyadicReflect_involution {k : ℕ} (p : DyadicFreq k) :
    dyadicReflect (dyadicReflect p) = p := by
  simp [dyadicReflect]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.DyadicModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

variable {k : ℕ}

def groupedPoint (m s : Bool) (p : DyadicFreq k) : ℤ × ℤ :=
  let q := if m then (dyadicPoint p).swap else dyadicPoint p
  if s then -q else q

def groupedTorusPoint (m s : Bool) (p : DyadicFreq k) : DiscreteTorus (16*2^k) :=
  (((groupedPoint m s p).1:ZMod (16*2^k)), ((groupedPoint m s p).2:ZMod (16*2^k)))

instance dyadicModulus_neZero (k : ℕ) : NeZero (16*2^k) := ⟨by positivity⟩

def dyadicWeight (p : DyadicFreq k) : ℝ :=
  1/((dyadicRadius p:ℝ)*Real.sqrt (dyadicRadius p:ℝ))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.MatrixSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uX

noncomputable section
open scoped BigOperators ComplexConjugate

namespace ClassicalON

def SquareBound {X : Type uX} {P : Type uP} [Fintype X] [Fintype P]
    (U : X → P → ℂ) (a : ℝ) : Prop :=
  ∀ v : P → ℂ, (∑ x, ‖∑ p, U x p*v p‖^2) ≤ a^2*∑ p, ‖v p‖^2

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.LatticeModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

variable {k : ℕ}

def latticeMode (m s : Bool) (p : DyadicFreq k) (x : Site) : ℂ :=
  (dyadicWeight p:ℂ) * (squareProfile m s (scaledSite k x):ℂ) *
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) x)

namespace LatticeGraph

def modeGradient (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  latticeMode m s p e.val.2.val-latticeMode m s p e.val.1.val

def scaledModeGradient (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  (Real.sqrt (dyadicRadius p:ℝ):ℂ)*G.modeGradient m s p e

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ModeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON
namespace LatticeGraph
variable {k : ℕ}

def modeBlockConstant (C : ℝ) : ℝ := Real.sqrt (512*(C^2+C^2*(Real.pi/4)^2))

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.RotationWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
noncomputable section
open scoped BigOperators
namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]

def weighted (J u : E → K) : K := ∑ e, J e * u e

@[simp] theorem weighted_add (J u v : E → K) :
    weighted J (u+v) = weighted J u + weighted J v := by
  simp [weighted, mul_add, Finset.sum_add_distrib]

@[simp] theorem weighted_neg (J u : E → K) : weighted J (-u) = -weighted J u := by
  simp [weighted]

structure Coeffs (E : Type uE) (K : Type uK) where
  a : E → K
  b : E → K
  aa : E → K
  ab : E → K
  bb : E → K
  aab : E → K
  abb : E → K
  aabb : E → K

def four (J : Coeffs E K) (u v w z : E → K) : K :=
  weighted J.a u * weighted J.b v * weighted J.a w * weighted J.b z +
  weighted J.ab (u*v) * weighted J.a w * weighted J.b z +
  weighted J.aa (u*w) * weighted J.b v * weighted J.b z +
  weighted J.ab (u*z) * weighted J.b v * weighted J.a w +
  weighted J.ab (v*w) * weighted J.a u * weighted J.b z +
  weighted J.bb (v*z) * weighted J.a u * weighted J.a w +
  weighted J.ab (w*z) * weighted J.a u * weighted J.b v +
  weighted J.ab (u*v) * weighted J.ab (w*z) +
  weighted J.aa (u*w) * weighted J.bb (v*z) +
  weighted J.ab (u*z) * weighted J.ab (v*w) +
  weighted J.aab (u*v*w) * weighted J.b z +
  weighted J.abb (u*v*z) * weighted J.a w +
  weighted J.aab (u*w*z) * weighted J.b v +
  weighted J.abb (v*w*z) * weighted J.a u +
  weighted J.aabb (u*v*w*z)

theorem four_add_first (J : Coeffs E K) (u u' v w z : E → K) :
    four J (u+u') v w z = four J u v w z + four J u' v w z := by
  simp only [four, add_mul, weighted_add]
  ring

theorem four_add_second (J : Coeffs E K) (u v v' w z : E → K) :
    four J u (v+v') w z = four J u v w z + four J u v' w z := by
  simp only [four, add_mul, mul_add, weighted_add]
  ring

theorem four_swap_first_third (J : Coeffs E K) (u v w z : E → K) :
    four J u v w z = four J w v u z := by
  unfold four
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring

theorem four_swap_second_fourth (J : Coeffs E K) (u v w z : E → K) :
    four J u v w z = four J u z w v := by
  unfold four
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring

end MixedAlgebra

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]

theorem four_add_third (J : Coeffs E K) (u v w w' z : E → K) :
    four J u v (w+w') z = four J u v w z + four J u v w' z := by
  rw [four_swap_first_third, four_add_first, four_swap_first_third J w,
    four_swap_first_third J w']

theorem four_add_fourth (J : Coeffs E K) (u v w z z' : E → K) :
    four J u v w (z+z') = four J u v w z + four J u v w z' := by
  rw [four_swap_second_fourth, four_add_second, four_swap_second_fourth J u z,
    four_swap_second_fourth J u z']

end MixedAlgebra

def bell4 (x y z w : ℝ) : ℝ := w+4*x*z+3*y^2+6*x^2*y+x^4

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

variable {n : ℕ}

def localCoefficient (S : SpinSystem n V E) (M : SpinOperator n)
    (σ : V → Spin n) (e : E) : ℝ :=
  S.strength e * ⟪(σ (S.left e)).val, M (σ (S.right e)).val⟫_ℝ

omit [Fintype V] in
theorem energy_weighted (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℝ) (σ : V → Spin n) :
    S.energy (fun e => u e • M) σ = MixedAlgebra.weighted (S.localCoefficient M σ) u := by
  unfold energy MixedAlgebra.weighted localCoefficient
  apply Finset.sum_congr rfl
  intro e _
  simp only [smul_apply, real_inner_smul_right]
  ring

def mixedCoefficients (S : SpinSystem 3 V E) (σ : V → Spin 3) : MixedAlgebra.Coeffs E ℝ where
  a := S.localCoefficient axisA σ
  b := S.localCoefficient axisB σ
  aa := S.localCoefficient (axisA^2) σ
  ab := S.localCoefficient mixedAB σ
  bb := S.localCoefficient (axisB^2) σ
  aab := S.localCoefficient mixedAAB σ
  abb := S.localCoefficient mixedABB σ
  aabb := S.localCoefficient mixedAABB σ

omit [Fintype V] in
def differential (S : SpinSystem n V E) {K : Type uK} [Sub K] (f : V → K) : E → K :=
  fun e => f (S.right e) - f (S.left e)

end ClassicalON.SpinSystem

end
end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.MixedWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]
theorem weighted_const_mul (J u : E → K) (r : K) :
    weighted J (fun e => r * u e) = r * weighted J u := by
  simp only [weighted, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring
end MixedAlgebra

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

variable {n : ℕ}

def averageLinear [NeZero n] (S : SpinSystem n V E) : C((V → Spin n), ℝ) →ₗ[ℝ] ℝ where
  toFun f := S.average f
  map_add' f g := S.average_add f.continuous g.continuous
  map_smul' r f := S.average_mul_const r f

@[simp] theorem averageLinear_apply [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℝ)) : S.averageLinear f = S.average f := rfl

attribute [local fun_prop] continuous_energy

omit [Fintype V] in
theorem continuous_fourthPolynomial (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (fun σ => fourthPolynomial (fun k => S.energy (fun e => A e^k) σ)) := by
  unfold fourthPolynomial
  fun_prop

def fourthObservable (S : SpinSystem n V E) (A : E → SpinOperator n) : C((V → Spin n), ℝ) :=
  ⟨_, S.continuous_fourthPolynomial A⟩

@[simp] theorem average_fourthObservable [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) : S.averageLinear (S.fourthObservable A) = S.fourthResponse A := rfl

omit [Fintype V] in
@[fun_prop] theorem continuous_weighted_coefficient (S : SpinSystem n V E)
    (M : SpinOperator n) (u : E → ℝ) :
    Continuous (fun σ => MixedAlgebra.weighted (S.localCoefficient M σ) u) := by
  have he : (fun σ => MixedAlgebra.weighted (S.localCoefficient M σ) u) =
      S.energy (fun e => u e • M) := by
    funext σ
    exact (S.energy_weighted M u σ).symm
  rw [he]
  exact S.continuous_energy _

omit [Fintype V] in
@[fun_prop] theorem continuous_mixedPolynomial (S : SpinSystem 3 V E)
    (u v w z : E → ℝ) :
    Continuous (fun σ => MixedAlgebra.four (S.mixedCoefficients σ) u v w z) := by
  simp only [MixedAlgebra.four, mixedCoefficients]
  fun_prop

def mixedObservable (S : SpinSystem 3 V E) (u v w z : E → ℝ) : C((V → Spin 3), ℝ) :=
  ⟨_, S.continuous_mixedPolynomial u v w z⟩

def mixedResponse (S : SpinSystem 3 V E) (u v w z : E → ℝ) : ℝ :=
  S.averageLinear (S.mixedObservable u v w z)

omit [Fintype V] in
@[fun_prop] theorem continuous_secondPolynomial (S : SpinSystem 3 V E) (h k : E → ℝ) :
    Continuous (fun σ => S.energy (fun e => (h e*k e) • axisC^2) σ +
      S.energy (fun e => h e • axisC) σ * S.energy (fun e => k e • axisC) σ) := by
  fun_prop

def secondObservable (S : SpinSystem 3 V E) (h k : E → ℝ) : C((V → Spin 3), ℝ) :=
  ⟨_, S.continuous_secondPolynomial h k⟩

@[simp] theorem secondObservable_average (S : SpinSystem 3 V E) (h k : E → ℝ) :
    S.averageLinear (S.secondObservable h k) = S.secondAxisResponse h k := rfl

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ComplexWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uE uK uL uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

structure ComplexFourForm (A : Type uA) [AddCommMonoid A] [Module ℂ A] where
  toFun : A → A → A → A → ℂ
  add_first : ∀ u u' v w z, toFun (u+u') v w z = toFun u v w z + toFun u' v w z
  add_second : ∀ u v v' w z, toFun u (v+v') w z = toFun u v w z + toFun u v' w z
  add_third : ∀ u v w w' z, toFun u v (w+w') z = toFun u v w z + toFun u v w' z
  add_fourth : ∀ u v w z z', toFun u v w (z+z') = toFun u v w z + toFun u v w z'
  smul_first : ∀ r u v w z, toFun (r • u) v w z = r * toFun u v w z
  smul_second : ∀ r u v w z, toFun u (r • v) w z = r * toFun u v w z
  smul_third : ∀ r u v w z, toFun u v (r • w) z = r * toFun u v w z
  smul_fourth : ∀ r u v w z, toFun u v w (r • z) = r * toFun u v w z

instance instCoeFunComplexFourFormForallForallForallForallComplex {A : Type uA} [AddCommMonoid A] [Module ℂ A] :
    CoeFun (ComplexFourForm A) (fun _ => A → A → A → A → ℂ) := ⟨ComplexFourForm.toFun⟩

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} {L : Type uL} [Fintype E] [CommRing K] [CommRing L]

def Coeffs.map (φ : K →+* L) (J : Coeffs E K) : Coeffs E L where
  a := φ ∘ J.a
  b := φ ∘ J.b
  aa := φ ∘ J.aa
  ab := φ ∘ J.ab
  bb := φ ∘ J.bb
  aab := φ ∘ J.aab
  abb := φ ∘ J.abb
  aabb := φ ∘ J.aabb

theorem weighted_smul (J u : E → K) (r : K) :
    weighted J (r • u) = r * weighted J u := by
  exact weighted_const_mul J u r

theorem four_smul_first (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J (r • u) v w z = r * four J u v w z := by
  simp only [four, smul_mul_assoc, weighted_smul]
  ring

theorem four_smul_second (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J u (r • v) w z = r * four J u v w z := by
  simp only [four, mul_smul_comm, smul_mul_assoc, weighted_smul]
  ring

theorem four_smul_third (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J u v (r • w) z = r * four J u v w z := by
  rw [four_swap_first_third, four_smul_first, four_swap_first_third J w]

theorem four_smul_fourth (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J u v w (r • z) = r * four J u v w z := by
  rw [four_swap_second_fourth, four_smul_second, four_swap_second_fourth J u z]

end MixedAlgebra

namespace ClassicalON.SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem integrable_complex_integrand [NeZero n] (S : SpinSystem n V E)
    {f : (V → Spin n) → ℂ} (hf : Continuous f) :
    Integrable (fun σ => f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ)) S.reference :=
  (hf.mul (Complex.continuous_ofReal.comp (S.continuous_energy _).rexp)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def averageComplexLinear [NeZero n] (S : SpinSystem n V E) : C((V → Spin n), ℂ) →ₗ[ℂ] ℂ where
  toFun f := (∫ σ, f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ)
  map_add' f g := by
    simp only [ContinuousMap.add_apply, add_mul]
    rw [integral_add (S.integrable_complex_integrand f.continuous)
      (S.integrable_complex_integrand g.continuous), add_div]
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc,
      integral_const_mul, RingHom.id_apply, mul_div_assoc]

def ofRealObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℝ)) : C(Ω, ℂ) :=
  ⟨fun σ => (f σ : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] theorem averageComplex_ofReal [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℝ)) :
    S.averageComplexLinear (ofRealObservable f) = (S.averageLinear f : ℂ) := by
  change (∫ σ, (f σ : ℂ) * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ) = _
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, ← Complex.ofReal_div]
  rfl

def complexCoefficients (S : SpinSystem 3 V E) (σ : V → Spin 3) : MixedAlgebra.Coeffs E ℂ :=
  (S.mixedCoefficients σ).map Complex.ofRealHom

omit [Fintype V] in
@[fun_prop] theorem continuous_complexWeighted (S : SpinSystem n V E)
    (M : SpinOperator n) (u : E → ℂ) :
    Continuous (fun σ => MixedAlgebra.weighted
      (fun e => (S.localCoefficient M σ e : ℂ)) u) := by
  unfold MixedAlgebra.weighted localCoefficient
  fun_prop

omit [Fintype V] in
@[fun_prop] theorem continuous_complexMixedPolynomial (S : SpinSystem 3 V E)
    (u v w z : E → ℂ) :
    Continuous (fun σ => MixedAlgebra.four (S.complexCoefficients σ) u v w z) := by
  simp only [MixedAlgebra.four, complexCoefficients, MixedAlgebra.Coeffs.map,
    mixedCoefficients, Function.comp_def, Complex.ofRealHom_eq_coe]
  fun_prop

def complexMixedObservable (S : SpinSystem 3 V E) (u v w z : E → ℂ) : C((V → Spin 3), ℂ) :=
  ⟨_, S.continuous_complexMixedPolynomial u v w z⟩

def complexMixedResponse (S : SpinSystem 3 V E) (u v w z : E → ℂ) : ℂ :=
  S.averageComplexLinear (S.complexMixedObservable u v w z)

theorem complexMixedResponse_add_first (S : SpinSystem 3 V E) (u v w z u' : E → ℂ) :
    S.complexMixedResponse (u+u') v w z = S.complexMixedResponse u v w z + S.complexMixedResponse u' v w z := by
  have hp : S.complexMixedObservable (u+u') v w z = S.complexMixedObservable u v w z +
      S.complexMixedObservable u' v w z := by
    ext σ
    exact MixedAlgebra.four_add_first (S.complexCoefficients σ) u u' v w z
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_first (S : SpinSystem 3 V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse (r • u) v w z = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable (r • u) v w z = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_first (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexMixedResponse_add_second (S : SpinSystem 3 V E) (u v w z v' : E → ℂ) :
    S.complexMixedResponse u (v+v') w z = S.complexMixedResponse u v w z + S.complexMixedResponse u v' w z := by
  have hp : S.complexMixedObservable u (v+v') w z = S.complexMixedObservable u v w z +
      S.complexMixedObservable u v' w z := by
    ext σ
    exact MixedAlgebra.four_add_second (S.complexCoefficients σ) u v v' w z
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_second (S : SpinSystem 3 V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse u (r • v) w z = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable u (r • v) w z = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_second (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexMixedResponse_add_third (S : SpinSystem 3 V E) (u v w z w' : E → ℂ) :
    S.complexMixedResponse u v (w+w') z = S.complexMixedResponse u v w z + S.complexMixedResponse u v w' z := by
  have hp : S.complexMixedObservable u v (w+w') z = S.complexMixedObservable u v w z +
      S.complexMixedObservable u v w' z := by
    ext σ
    exact MixedAlgebra.four_add_third (S.complexCoefficients σ) u v w w' z
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_third (S : SpinSystem 3 V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse u v (r • w) z = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable u v (r • w) z = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_third (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexMixedResponse_add_fourth (S : SpinSystem 3 V E) (u v w z z' : E → ℂ) :
    S.complexMixedResponse u v w (z+z') = S.complexMixedResponse u v w z + S.complexMixedResponse u v w z' := by
  have hp : S.complexMixedObservable u v w (z+z') = S.complexMixedObservable u v w z +
      S.complexMixedObservable u v w z' := by
    ext σ
    exact MixedAlgebra.four_add_fourth (S.complexCoefficients σ) u v w z z'
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_fourth (S : SpinSystem 3 V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse u v w (r • z) = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable u v w (r • z) = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_fourth (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

def complexEnergy (S : SpinSystem n V E) (M : SpinOperator n) (u : E → ℂ)
    (σ : V → Spin n) : ℂ := MixedAlgebra.weighted
      (fun e => (S.localCoefficient M σ e : ℂ)) u

omit [Fintype V] in
@[fun_prop] theorem continuous_complexEnergy (S : SpinSystem n V E)
    (M : SpinOperator n) (u : E → ℂ) : Continuous (S.complexEnergy M u) :=
  S.continuous_complexWeighted M u

omit [Fintype V] in
@[simp] theorem complexEnergy_add (S : SpinSystem n V E) (M : SpinOperator n)
    (u v : E → ℂ) (σ : V → Spin n) :
    S.complexEnergy M (u+v) σ = S.complexEnergy M u σ + S.complexEnergy M v σ :=
  MixedAlgebra.weighted_add _ u v

omit [Fintype V] in
@[simp] theorem complexEnergy_smul (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℂ) (r : ℂ) (σ : V → Spin n) :
    S.complexEnergy M (r • u) σ = r * S.complexEnergy M u σ :=
  MixedAlgebra.weighted_smul _ u r

omit [Fintype V] in
@[fun_prop] theorem continuous_complexSecondPolynomial (S : SpinSystem 3 V E)
    (u v : E → ℂ) : Continuous (fun σ => S.complexEnergy (axisC^2) (u*v) σ +
      S.complexEnergy axisC u σ * S.complexEnergy axisC v σ) := by
  fun_prop

def complexSecondObservable (S : SpinSystem 3 V E) (u v : E → ℂ) : C((V → Spin 3), ℂ) :=
  ⟨_, S.continuous_complexSecondPolynomial u v⟩

def complexSecondResponse (S : SpinSystem 3 V E) (u v : E → ℂ) : ℂ :=
  S.averageComplexLinear (S.complexSecondObservable u v)

theorem complexSecondResponse_add_left (S : SpinSystem 3 V E) (u v w : E → ℂ) :
    S.complexSecondResponse (u+v) w = S.complexSecondResponse u w + S.complexSecondResponse v w := by
  have hp : S.complexSecondObservable (u+v) w =
      S.complexSecondObservable u w + S.complexSecondObservable v w := by
    ext σ
    change S.complexEnergy (axisC^2) ((u+v)*w) σ +
      S.complexEnergy axisC (u+v) σ * S.complexEnergy axisC w σ =
      (S.complexEnergy (axisC^2) (u*w) σ +
        S.complexEnergy axisC u σ * S.complexEnergy axisC w σ) +
      (S.complexEnergy (axisC^2) (v*w) σ +
        S.complexEnergy axisC v σ * S.complexEnergy axisC w σ)
    rw [add_mul, complexEnergy_add, complexEnergy_add]
    ring
  unfold complexSecondResponse
  rw [hp, map_add]

theorem complexSecondResponse_symm (S : SpinSystem 3 V E) (u v : E → ℂ) :
    S.complexSecondResponse u v = S.complexSecondResponse v u := by
  have hp : S.complexSecondObservable u v = S.complexSecondObservable v u := by
    ext σ
    change S.complexEnergy (axisC^2) (u*v) σ +
      S.complexEnergy axisC u σ * S.complexEnergy axisC v σ =
      S.complexEnergy (axisC^2) (v*u) σ +
        S.complexEnergy axisC v σ * S.complexEnergy axisC u σ
    rw [mul_comm u v, mul_comm (S.complexEnergy axisC u σ)]
  exact congrArg S.averageComplexLinear hp

theorem complexSecondResponse_add_right (S : SpinSystem 3 V E) (u v w : E → ℂ) :
    S.complexSecondResponse u (v+w) = S.complexSecondResponse u v + S.complexSecondResponse u w := by
  rw [S.complexSecondResponse_symm, S.complexSecondResponse_add_left,
    S.complexSecondResponse_symm v, S.complexSecondResponse_symm w]

theorem complexSecondResponse_smul_left (S : SpinSystem 3 V E) (u v : E → ℂ) (r : ℂ) :
    S.complexSecondResponse (r • u) v = r * S.complexSecondResponse u v := by
  have hp : S.complexSecondObservable (r • u) v = r • S.complexSecondObservable u v := by
    ext σ
    change S.complexEnergy (axisC^2) ((r • u)*v) σ +
      S.complexEnergy axisC (r • u) σ * S.complexEnergy axisC v σ =
      r * (S.complexEnergy (axisC^2) (u*v) σ +
        S.complexEnergy axisC u σ * S.complexEnergy axisC v σ)
    rw [smul_mul_assoc, complexEnergy_smul, complexEnergy_smul]
    ring
  unfold complexSecondResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexSecondResponse_smul_right (S : SpinSystem 3 V E) (u v : E → ℂ) (r : ℂ) :
    S.complexSecondResponse u (r • v) = r * S.complexSecondResponse u v := by
  rw [S.complexSecondResponse_symm, S.complexSecondResponse_smul_left,
    S.complexSecondResponse_symm v]

omit [Fintype V] [Fintype E] in
def complexCross (S : SpinSystem 3 V E) (f g : V → ℂ) : E → ℂ :=
  fun e => f (S.left e)*g (S.right e) - g (S.left e)*f (S.right e)

omit [Fintype V] [Fintype E] in
theorem complexCross_add_left (S : SpinSystem 3 V E) (f g h : V → ℂ) :
    S.complexCross (f+h) g = S.complexCross f g + S.complexCross h g := by
  ext e
  simp only [complexCross, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem complexCross_smul_left (S : SpinSystem 3 V E) (f g : V → ℂ) (r : ℂ) :
    S.complexCross (r • f) g = r • S.complexCross f g := by
  ext e
  simp only [complexCross, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype V] [Fintype E] in
theorem complexCross_add_right (S : SpinSystem 3 V E) (f g h : V → ℂ) :
    S.complexCross f (g+h) = S.complexCross f g + S.complexCross f h := by
  ext e
  simp only [complexCross, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem complexCross_smul_right (S : SpinSystem 3 V E) (f g : V → ℂ) (r : ℂ) :
    S.complexCross f (r • g) = r • S.complexCross f g := by
  ext e
  simp only [complexCross, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype V] [Fintype E] in
theorem complexDifferential_add (S : SpinSystem n V E) (f g : V → ℂ) :
    S.differential (f+g) = S.differential f + S.differential g := by
  ext e
  simp only [differential, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem complexDifferential_smul (S : SpinSystem n V E) (f : V → ℂ) (r : ℂ) :
    S.differential (r • f) = r • S.differential f := by
  ext e
  simp only [differential, Pi.smul_apply, smul_eq_mul]
  ring

def complexWardDefect (S : SpinSystem 3 V E) : ComplexFourForm (V → ℂ) where
  toFun f g h k := 4 * S.complexMixedResponse (S.differential f) (S.differential g)
    (S.differential h) (S.differential k) -
    (S.complexSecondResponse (S.complexCross f g) (S.complexCross h k) +
      S.complexSecondResponse (S.complexCross f k) (S.complexCross h g))
  add_first := by
    intro f f' g h k
    simp only [complexDifferential_add, complexMixedResponse_add_first,
      complexCross_add_left, complexSecondResponse_add_left]
    ring
  add_second := by
    intro f g g' h k
    simp only [complexDifferential_add, complexMixedResponse_add_second,
      complexCross_add_right, complexSecondResponse_add_left, complexSecondResponse_add_right]
    ring
  add_third := by
    intro f g h h' k
    simp only [complexDifferential_add, complexMixedResponse_add_third,
      complexCross_add_left, complexSecondResponse_add_right]
    ring
  add_fourth := by
    intro f g h k k'
    simp only [complexDifferential_add, complexMixedResponse_add_fourth,
      complexCross_add_right, complexSecondResponse_add_left, complexSecondResponse_add_right]
    ring
  smul_first := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_first,
      complexCross_smul_left, complexSecondResponse_smul_left]
    ring
  smul_second := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_second,
      complexCross_smul_right, complexSecondResponse_smul_left, complexSecondResponse_smul_right]
    ring
  smul_third := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_third,
      complexCross_smul_left, complexSecondResponse_smul_right]
    ring
  smul_fourth := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_fourth,
      complexCross_smul_right, complexSecondResponse_smul_left, complexSecondResponse_smul_right]
    ring

end ClassicalON.SpinSystem

end
end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FamilyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uK

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MixedAlgebra
variable {I : Type uI} {J : Type uJ} {E : Type uE} {K : Type uK} [Fintype I] [Fintype J] [Fintype E] [CommRing K]

omit [Fintype J] in
def paired (C : Coeffs E K) (p q : I → E → K) : K :=
  ∑ i, (weighted C.a (p i) * weighted C.b (q i) + weighted C.ab (p i*q i))

omit [Fintype J] in
def kernel (p q : I → E → K) (e l : E) : K := ∑ i, p i e*q i l

end MixedAlgebra

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.GradientComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def normObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℂ)) : C(Ω, ℝ) :=
  ⟨fun σ => ‖f σ‖, f.continuous.norm⟩

def reObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℂ)) : C(Ω, ℝ) :=
  ⟨fun σ => (f σ).re, Complex.continuous_re.comp f.continuous⟩

omit [Fintype V] in
@[simp] theorem complexEnergy_re (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℂ) (σ : V → Spin n) :
    (S.complexEnergy M u σ).re = S.energy (fun e => (u e).re • M) σ := by
  rw [S.energy_weighted]
  simp [complexEnergy, MixedAlgebra.weighted, Complex.mul_re]

omit [Fintype V] in
@[simp] theorem complexEnergy_im (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℂ) (σ : V → Spin n) :
    (S.complexEnergy M u σ).im = S.energy (fun e => (u e).im • M) σ := by
  rw [S.energy_weighted]
  simp [complexEnergy, MixedAlgebra.weighted, Complex.mul_im]

omit [Fintype V] in
@[simp] theorem complexEnergy_conj (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℂ) (σ : V → Spin n) :
    S.complexEnergy M (fun e => conj (u e)) σ = conj (S.complexEnergy M u σ) := by
  simp [complexEnergy, MixedAlgebra.weighted]

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ObservableBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [NeZero n]

@[simp] theorem normObservable_mul {Ω : Type uΩ} [TopologicalSpace Ω] (f g : C(Ω, ℂ)) :
    normObservable (f*g) = normObservable f * normObservable g := by
  ext x
  exact norm_mul (f x) (g x)

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FamilyKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON
variable {I : Type uI} {E : Type uE} [Fintype I] [Fintype E]

def familyKernel (u : I → E → ℂ) (e l : E) : ℂ := ∑ i, u i e * conj (u i l)

def rowSquare (u : I → E → ℂ) (e : E) : ℝ := ∑ l, ‖familyKernel u e l‖^2

def familyHSSquare (u : I → E → ℂ) : ℝ := ∑ e, rowSquare u e

omit [Fintype E] in
@[simp] theorem familyKernel_conj (u : I → E → ℂ) (e l : E) :
    familyKernel (fun i e => conj (u i e)) e l = conj (familyKernel u e l) := by
  simp [familyKernel]

namespace SpinSystem
variable {n : ℕ} {V : Type uV} [Fintype V]

omit [Fintype V] [Fintype I] in
def coefficientObservable (S : SpinSystem n V E) (M : SpinOperator n) (e : E) :
    C((V → Spin n), ℂ) := ⟨fun σ => (S.localCoefficient M σ e : ℂ), by
  unfold localCoefficient
  fun_prop⟩

omit [Fintype V] [Fintype I] in
def currentObservable (S : SpinSystem n V E) (M : SpinOperator n) (u : E → ℂ) :
    C((V → Spin n), ℂ) := ⟨_, S.continuous_complexEnergy M u⟩

omit [Fintype V] [Fintype I] [Fintype E] in
def conjugateObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℂ)) : C(Ω, ℂ) :=
  ⟨fun σ => conj (f σ), Complex.continuous_conj.comp f.continuous⟩

omit [Fintype V] [Fintype I] [Fintype E] in
@[simp] theorem conjugateObservable_apply {Ω : Type uΩ} [TopologicalSpace Ω]
    (f : C(Ω, ℂ)) (σ : Ω) : conjugateObservable f σ = conj (f σ) := rfl

omit [Fintype V] [Fintype I] [Fintype E] in
@[simp] theorem normObservable_conjugate {Ω : Type uΩ} [TopologicalSpace Ω]
    (f : C(Ω, ℂ)) : normObservable (conjugateObservable f) = normObservable f := by
  ext σ
  exact Complex.norm_conj (f σ)

omit [Fintype V] [Fintype I] in
@[simp] theorem currentObservable_conj (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℂ) : S.currentObservable M (fun e => conj (u e)) =
      conjugateObservable (S.currentObservable M u) := by
  ext σ
  exact S.complexEnergy_conj M u σ

omit [Fintype V] [Fintype I] [Fintype E] in
@[simp] theorem coefficientObservable_conj (S : SpinSystem n V E) (M : SpinOperator n)
    (e : E) : conjugateObservable (S.coefficientObservable M e) =
      S.coefficientObservable M e := by
  ext σ
  exact Complex.conj_ofReal _

end SpinSystem
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ModeCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON
namespace LatticeGraph
variable {k : ℕ}

abbrev ModeIndex (k : ℕ) := (Bool × Bool) × DyadicFreq k

def modes (G : LatticeGraph) (i : ModeIndex k) (x : G.vertices) : ℂ :=
  latticeMode i.1.1 i.1.2 i.2 x.val

def modeDifferences (G : LatticeGraph) (i : ModeIndex k) (e : G.edges) : ℂ :=
  G.modeGradient i.1.1 i.1.2 i.2 e

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ModeCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON
variable {k : ℕ}

namespace LatticeGraph

def modeCommutator (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  (latticeMode m s p e.val.1.val*conj (latticeMode m s p e.val.2.val)-
    conj (latticeMode m s p e.val.1.val)*latticeMode m s p e.val.2.val)/2

def profileEdge (G : LatticeGraph) (k : ℕ) (e : G.edges) : ℝ :=
  (1/(2:ℝ)^k)*(squareProfile (G.edgeDirection e) false (scaledSite k e.val.1.val)*
    squareProfile (G.edgeDirection e) false (scaledSite k e.val.2.val)-
    squareProfile (G.edgeDirection e) true (scaledSite k e.val.1.val)*
    squareProfile (G.edgeDirection e) true (scaledSite k e.val.2.val))

def thetaEdge (G : LatticeGraph) (k : ℕ) (e : G.edges) : ℝ :=
  squareTheta (scaledSite k e.val.2.val)-squareTheta (scaledSite k e.val.1.val)

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SecondBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in

def commutatorForm (S : SpinSystem 3 V E) (f g : V → ℂ) : E → ℂ :=
  (1/2 : ℂ) • S.complexCross f g

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ResponseTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
@[simp] theorem complexEnergy_sub (S : SpinSystem 3 V E) (M : SpinOperator 3)
    (u v : E → ℂ) (σ : V → Spin 3) :
    S.complexEnergy M (u-v) σ = S.complexEnergy M u σ - S.complexEnergy M v σ := by
  simp only [complexEnergy, MixedAlgebra.weighted, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

def quadraticObservable (S : SpinSystem 3 V E) (u : E → ℂ) : C((V → Spin 3), ℝ) :=
  reObservable (S.currentObservable (axisC^2) (u*(fun e => conj (u e))))

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FamilyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

def familyPaired (S : SpinSystem 3 V E) (u : I → E → ℂ) : C((V → Spin 3), ℂ) :=
  ∑ i, (S.currentObservable axisA (u i) *
    S.currentObservable axisB (fun e => conj (u i e)) +
    S.currentObservable mixedAB (fun e => u i e * conj (u i e)))

def familyRemainder (S : SpinSystem 3 V E) (u : I → E → ℂ) : C((V → Spin 3), ℂ) :=
  let T := familyKernel u
  let X := fun M e => S.currentObservable M (T e)
  let C := S.coefficientObservable
  let bar := conjugateObservable
  let k := fun z => ContinuousMap.const (V → Spin 3) z
  (∑ e, C (axisA^2) e * X axisB e * bar (X axisB e)) +
  (∑ e, C mixedAB e * X axisB e * X axisA e) +
  (∑ e, C mixedAB e * bar (X axisA e) * bar (X axisB e)) +
  (∑ e, C (axisB^2) e * bar (X axisA e) * X axisA e) +
  (∑ e, ∑ l, C (axisA^2) e * C (axisB^2) l * k (T e l * conj (T e l))) +
  (∑ e, ∑ l, C mixedAB e * C mixedAB l * k (T e l ^ 2)) +
  (∑ e, C mixedAAB e * k (T e e) * bar (X axisB e)) +
  (∑ e, C mixedABB e * k (T e e) * X axisA e) +
  (∑ e, C mixedAAB e * k (conj (T e e)) * X axisB e) +
  (∑ e, C mixedABB e * k (conj (T e e)) * bar (X axisA e)) +
  (∑ e, C mixedAABB e * k (T e e * conj (T e e)))

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.RotationInequality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

omit [Fintype I] in
def complexSecondBilin (S : SpinSystem 3 V E) : (E → ℂ) →ₗ[ℂ] (E → ℂ) →ₗ[ℂ] ℂ where
  toFun u := {
    toFun := S.complexSecondResponse u
    map_add' := S.complexSecondResponse_add_right u
    map_smul' := fun r v => by simpa only [smul_eq_mul, RingHom.id_apply] using S.complexSecondResponse_smul_right u v r }
  map_add' u v := by ext w; exact S.complexSecondResponse_add_left u v w
  map_smul' r u := by
    ext v
    change S.complexSecondResponse (r • u) v = r * S.complexSecondResponse u v
    exact S.complexSecondResponse_smul_left u v r

omit [Fintype I] in
@[simp] theorem complexSecondResponse_neg_neg (S : SpinSystem 3 V E) (u v : E → ℂ) :
    S.complexSecondResponse (-u) (-v) = S.complexSecondResponse u v := by
  change S.complexSecondBilin (-u) (-v) = S.complexSecondBilin u v
  simp

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

namespace LatticeGraph

def spinSystem (G : LatticeGraph) (n : ℕ) (b : G.edges → ℝ) (P : G.vertices → Option (Spin n)) :
    SpinSystem n G.vertices G.edges := ⟨fun e => e.val.1,fun e => e.val.2,b,P⟩

def BoundaryPins (G : LatticeGraph) (k n : ℕ) (P : G.vertices → Option (Spin n)) : Prop :=
  ∀ x s, P x=some s →
    (|(scaledSite k x.val).1| ≤ 1 ∧ |(scaledSite k x.val).2| ≤ 1) ∨
    (2 ≤ |(scaledSite k x.val).1| ∨ 2 ≤ |(scaledSite k x.val).2|)

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
namespace ClassicalON
namespace LatticeGraph

def rotationCostConstant (β C : ℝ) : ℝ :=
  4*((6*β^2+4*β*Real.sqrt β+β)*(48*(2*modeBlockConstant C)^4)+
        β*(576*C^2*(2*modeBlockConstant C)^2))

def transferCostConstant (β L D : ℝ) : ℝ :=
  β*(512*D*(2*L+D))+2*(β*512*D)*Real.sqrt (β*(512*L^2))+(β*512*D)^2

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AxisRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Real
namespace ClassicalON

def axisPolynomial (t : ℝ) : SpinOperator 3 :=
  1 + (Real.sin t) • axisC + (1-Real.cos t) • axisC^2

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PotentialRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
namespace ClassicalON
namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def potentialRotation (f : V → ℝ) (t : ℝ) (x : V) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  rotationExp ((t*f x) • axisC) (skewAdjoint.smul_mem _ axisC_skew)

def rotatePotential (S : SpinSystem 3 V E) (f : V → ℝ) (t : ℝ) : SpinSystem 3 V E :=
  S.rotatePins (potentialRotation f t)

def potentialOperators (S : SpinSystem 3 V E) (f : V → ℝ) : E → SpinOperator 3 :=
  fun e => S.differential f e • axisC

end SpinSystem
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ClassicalON.LatticeGraph

def thetaPotential (G : LatticeGraph) (k : ℕ) (x : G.vertices) : ℝ :=
  squareTheta (scaledSite k x.val)

def rotatedBoundaryPins (G : LatticeGraph) (k : ℕ) (P : G.vertices → Option (Spin 3))
    (t : ℝ) : G.vertices → Option (Spin 3) :=
  fun x => (P x).map (spinRotation (SpinSystem.potentialRotation (G.thetaPotential k) t x))

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PoleCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def crossingIndicator (left right : E → V) (I O : Set V) (η : E → Bool) : ℝ :=
  if bondCrossing left right I O η then 1 else 0

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON.LatticeGraph

def innerSet (G : LatticeGraph) (k : ℕ) : Set G.vertices :=
  {x | |(scaledSite k x.val).1|≤1 ∧ |(scaledSite k x.val).2|≤1}

def outerSet (G : LatticeGraph) (k : ℕ) : Set G.vertices :=
  {x | 2≤|(scaledSite k x.val).1| ∨ 2≤|(scaledSite k x.val).2|}

def positiveLayerPins (G : LatticeGraph) (I O : Set G.vertices) : G.vertices → Option (Spin 3) :=
  (poleSystem (fun e : G.edges => e.val.1) (fun e => e.val.2) (fun _ => 0) (I∪O) (fun _ => true)).pin

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def firstSpinProduct (x y : V) (s : V → Spin 3) : ℝ := (s x).val 0*(s y).val 0

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SeparatedAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK

noncomputable section
open Set
open scoped BigOperators Classical
namespace ClassicalON.LatticeGraph
variable {K : Type uK} [Fintype K]

def annulusIndicator (G : LatticeGraph) (N : ℤ) (z : Site) (η : G.edges → Bool) : ℝ :=
  crossingIndicator (fun e : (G.annulusGraph N z).edges => e.val.1) (fun e => e.val.2)
    (G.annulusInner N z) (G.annulusOuter N z) (fun e => η (G.restrictEdge _ e))

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical
namespace ClassicalON.LatticeGraph

def extendAnnulusSign (G : LatticeGraph) (N : ℤ) (z : Site)
    (s : (G.annulusGraph N z).vertices → Bool) (v : G.vertices) : Bool :=
  if h : v.val∈annulusSites N z then
    s ⟨v.val,Finset.mem_filter.mpr ⟨v.property,h⟩⟩ else decide (2*N<siteRadius z v.val)

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CoarsePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace ClassicalON.LatticeGraph

def cellVisited (G : LatticeGraph) (η : G.edges → Bool) (x : G.vertices) (N : ℤ) (z : Site) : Prop :=
  ∃ v : G.vertices,bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x v ∧ coarseSite N v.val=z

def coarseCluster (G : LatticeGraph) (η : G.edges → Bool) (x : G.vertices) (N : ℤ) : SimpleGraph Site where
  Adj z w := z≠w ∧ siteRadius z w≤1 ∧ G.cellVisited η x N z ∧ G.cellVisited η x N w
  symm := ⟨by intro z w ⟨h,hd,hz,hw⟩; exact ⟨h.symm,by simpa only [siteRadius_symm] using hd,hw,hz⟩⟩
  loopless := ⟨by intro z; simp⟩

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CoarseTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON.LatticeGraph

def codeEvent (G : LatticeGraph) (N : ℤ) (t : ℕ) (z : Site) (c : CoarseCode (25*t))
    (η : G.edges → Bool) : ℝ :=
  ∏ i : {i : Fin (25*t+1) // siteColor (codePosition z c i)=codeColor t z c},
    G.annulusIndicator N (coarseCenter N (codePosition z c i.val)) η

def connectionProbability (G : LatticeGraph) (b : G.edges → ℝ) (x y : G.vertices) : ℝ :=
  freeBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b
    (fun η => if bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x y then 1 else 0)

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinIsotropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def coordinateRotation (n : ℕ) (i j : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

def coordinateSpinProduct (n : ℕ) (i : Fin n) (x y : V) (s : V → Spin n) : ℝ :=
  (s x).val i*(s y).val i

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.OrthogonalAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ClassicalON

instance spinOperator_continuousStar (n : ℕ) : ContinuousStar (SpinOperator n) :=
  ⟨ContinuousLinearMap.adjoint.continuous⟩

abbrev SpinOrthogonal (n : ℕ) := unitary (SpinOperator n)

instance spinOrthogonal_compact (n : ℕ) [NeZero n] : CompactSpace (SpinOrthogonal n) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : SpinOperator n) 1).of_isClosed_subset isClosed_unitary
  intro Q hQ
  simpa only [Metric.mem_closedBall,dist_zero_right,CStarRing.norm_coe_unitary ⟨Q,hQ⟩] using (le_rfl : (1:ℝ) ≤ 1)

instance spinOrthogonal_measurableSpace (n : ℕ) : MeasurableSpace (SpinOrthogonal n) := borel _
instance spinOrthogonal_borelSpace (n : ℕ) : BorelSpace (SpinOrthogonal n) := ⟨rfl⟩

def orthogonalLaw (n : ℕ) [NeZero n] : Measure (SpinOrthogonal n) :=
  ((Measure.haar : Measure (SpinOrthogonal n)) Set.univ)⁻¹ • Measure.haar

instance orthogonalLaw_isProbability (n : ℕ) [NeZero n] : IsProbabilityMeasure (orthogonalLaw n) := by
  constructor
  unfold orthogonalLaw
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (isOpen_univ.measure_pos Measure.haar Set.univ_nonempty)) (measure_ne_top _ _)

instance orthogonalLaw_isHaar (n : ℕ) [NeZero n] : (orthogonalLaw n).IsHaarMeasure := by
  unfold orthogonalLaw
  exact Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (ne_of_gt (isOpen_univ.measure_pos Measure.haar Set.univ_nonempty)))

instance orthogonalLaw_isRightInvariant (n : ℕ) [NeZero n] :
    (orthogonalLaw n).IsMulRightInvariant := by
  constructor
  intro R
  have hm : Measurable (fun Q : SpinOrthogonal n => Q*R) := (continuous_id.mul continuous_const).measurable
  have : IsProbabilityMeasure ((orthogonalLaw n).map (·*R)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have he := Measure.isMulInvariant_eq_smul_of_compactSpace
    ((orthogonalLaw n).map (·*R)) (orthogonalLaw n)
  have hmass := congrArg (fun μ : Measure (SpinOrthogonal n) => μ Set.univ) he
  simp only [measure_univ,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,mul_one] at hmass
  have hc : Measure.haarScalarFactor ((orthogonalLaw n).map (·*R)) (orthogonalLaw n)=1 := by
    exact_mod_cast hmass.symm
  rw [hc,one_smul] at he
  exact he

def orthogonalSpin {n : ℕ} (Q : SpinOrthogonal n) (s : Spin n) : Spin n :=
  spinRotation (Unitary.linearIsometryEquiv Q) s

@[simp] theorem orthogonalSpin_mul {n : ℕ} (Q R : SpinOrthogonal n) (s : Spin n) :
    orthogonalSpin (Q*R) s=orthogonalSpin Q (orthogonalSpin R s) := by
  rfl

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BlockGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Classical
namespace ClassicalON

abbrev ThreeBlock (k : ℕ) := WithLp 2 (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin k))

def splitThree (k : ℕ) : EuclideanSpace ℝ (Fin (3+k)) ≃ₗᵢ[ℝ] ThreeBlock k :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSumFinEquiv.symm : Fin (3+k) ≃ Fin 3 ⊕ Fin k)).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin 3 ⊕ Fin k => ℝ))

def blockHead (k : ℕ) (s : Spin (3+k)) : EuclideanSpace ℝ (Fin 3) := (splitThree k s.val).fst
def blockTail (k : ℕ) (s : Spin (3+k)) : EuclideanSpace ℝ (Fin k) := (splitThree k s.val).snd
def blockRadius (k : ℕ) (s : Spin (3+k)) : ℝ := ‖blockHead k s‖

theorem blockRadius_nonneg (k : ℕ) (s : Spin (3+k)) : 0≤blockRadius k s := norm_nonneg _

theorem block_norm_sq (k : ℕ) (s : Spin (3+k)) : blockRadius k s^2+‖blockTail k s‖^2=1 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (splitThree k s.val)
  simpa only [blockRadius,blockHead,blockTail,LinearIsometryEquiv.norm_map,spin_norm,one_pow] using h.symm

def blockDirection (k : ℕ) (s : Spin (3+k)) : Spin 3 :=
  if h : blockHead k s=0 then cylindricalSpin ⊤ true 0 else
  ⟨(blockRadius k s)⁻¹ • blockHead k s,by
    rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (blockRadius_nonneg k s))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)⟩

def blockFiber (k : ℕ) (s : Spin (3+k)) (t : Spin 3) : Spin (3+k) :=
  ⟨(splitThree k).symm (WithLp.toLp 2 (blockRadius k s • t.val,blockTail k s)),by
    rw [Metric.mem_sphere,dist_zero_right,LinearIsometryEquiv.norm_map]
    have he := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (blockRadius k s • t.val,blockTail k s))
    have hn := block_norm_sq k s
    simp only [WithLp.fst,WithLp.snd,norm_smul,Real.norm_of_nonneg (blockRadius_nonneg k s),spin_norm,mul_one] at he
    nlinarith [norm_nonneg (WithLp.toLp 2 (blockRadius k s • t.val,blockTail k s))]⟩

@[simp] theorem blockHead_fiber (k : ℕ) (s : Spin (3+k)) (t : Spin 3) :
    blockHead k (blockFiber k s t)=blockRadius k s • t.val := by
  simp [blockHead,blockFiber]
@[simp] theorem blockTail_fiber (k : ℕ) (s : Spin (3+k)) (t : Spin 3) :
    blockTail k (blockFiber k s t)=blockTail k s := by
  simp [blockTail,blockFiber]

def blockRotation (k : ℕ) (Q : SpinOrthogonal 3) :
    EuclideanSpace ℝ (Fin (3+k)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (3+k)) :=
  ((splitThree k).trans (LinearIsometryEquiv.withLpProdCongr 2 (Unitary.linearIsometryEquiv Q) (.refl ℝ _))).trans (splitThree k).symm

def blockRotateSpin (k : ℕ) (Q : SpinOrthogonal 3) (s : Spin (3+k)) : Spin (3+k) :=
  spinRotation (blockRotation k Q) s

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BlockOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Classical
namespace ClassicalON

variable {V : Type uV} [Fintype V]

def blockFiberConfiguration (k : ℕ) (s : V → Spin (3+k)) (t : V → Spin 3) : V → Spin (3+k) :=
  fun v => blockFiber k (s v) (t v)

def blockRotateConfiguration (k : ℕ) (Q : V → SpinOrthogonal 3) :
    (V → Spin (3+k)) ≃ₜ (V → Spin (3+k)) :=
  SpinSystem.rotateConfiguration (fun v => blockRotation k (Q v))

def orthogonalConfigurationLaw : Measure (V → SpinOrthogonal 3) := Measure.pi (fun _ => orthogonalLaw 3)
instance orthogonalConfigurationLaw_isProbability : IsProbabilityMeasure (orthogonalConfigurationLaw (V := V)) := by
  unfold orthogonalConfigurationLaw
  infer_instance

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BlockKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def blockCoupling (k : ℕ) (left right : E → V) (b : E → ℝ) (s : V → Spin (3+k)) : E → ℝ :=
  fun e => b e*blockRadius k (s (left e))*blockRadius k (s (right e))

def blockTailEnergy (k : ℕ) (left right : E → V) (b : E → ℝ) (s : V → Spin (3+k)) : ℝ :=
  ∑ e,b e*⟪blockTail k (s (left e)),blockTail k (s (right e))⟫_ℝ

def freeSpinPartition (n : ℕ) (left right : E → V) (b : E → ℝ) : ℝ :=
  ∫ s,Real.exp (freeSpinEnergy n left right b s) ∂freeSpinReference n

end ClassicalON

end

end OAI
end


