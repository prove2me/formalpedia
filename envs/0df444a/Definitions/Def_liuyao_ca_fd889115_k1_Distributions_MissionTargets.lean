-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_MissionTargets
-- name    : liuyao_ca_fd889115_k1_Distributions_MissionTargets
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:37:47.855277+00:00
-- url     : https://prove2.me/theorems/6173d93c-9ee5-4df7-8ba9-df16672f49cc
-- title:
--   Computable analysis · MissionTargets · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/MissionTargets.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_BoxQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_CubeAverage
import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_WaveTargets
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ExpProofs
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteNBallVolume
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_MonotoneLogarithm

set_option autoImplicit true

/-! Contributor targets for the whole-space distribution mission. The
distribution definition is independent of the quadratures used to state
particular kernel formulas. -/

open ComputableAnalysis

namespace ComputableDistributions

/-- All three operators use the same test module in a given ambient
dimension. Support in a box remains a proposition about a test. -/
abbrev TestModuleFamily := ∀ dimension : Nat, TestFunctionSpace dimension

/-- The descent argument needs compact cutoffs equal to one on an interval. -/
def HasPlateauCutoffs : Prop :=
  ∀ radius : Rat, 0 < radius → ∃ χ : TestFunction 1,
    ∀ x : Rat, -radius ≤ x → x ≤ radius →
      (χ.value (fun _ => x)).Equiv (RealCompute.ofRat 1)

/-- Construct the common test modules and actual smooth tests for the
source and descent arguments. -/
def TestModulesExist : Prop :=
  Nonempty TestModuleFamily ∧
    (∀ dimension, HasLocalizedOriginTests dimension) ∧ HasPlateauCutoffs

/-- Agreement of represented values determines all the derivative
certificates of a test. -/
def TestDerivativeUniquenessTarget : Prop :=
  ∀ dimension (φ ψ : TestFunction dimension),
    (∀ x, (φ.value x).Equiv (ψ.value x)) → φ.Equivalent ψ

/-- Compact support of a test in any box is inherited by its partials,
even when the stored support certificate uses a different box. -/
def TestDerivativeSupportTarget : Prop :=
  ∀ dimension (φ : TestFunction dimension) (B : RationalBox dimension),
    φ.SupportedInBox B → ∀ i, (φ.coordinatePartial i).SupportedInBox B

/-- Construct distributional derivatives as continuous linear functionals.
The sign is the one in the formal transpose of a coordinate derivative. -/
def DistributionalDerivativeTarget : Prop :=
  ∀ dimension (tests : TestFunctionSpace dimension) (T : Distribution tests) i,
    ∃ D : Distribution tests, ∀ φ,
      (D.action φ).Equiv (RealCompute.neg (T.action (φ.coordinatePartial i)))

/-- An ordinary kernel formula with an improper boundary. For each box
containing the test's support, each fixed truncation has a box integral.
Those represented integrals converge to the proposed action as the cutoff
tends to zero. Quadrature refinement is independent of the cutoff. -/
def HasTruncatedKernelAction {dimension : Nat} (density : Rat → QPoint dimension → RealCompute)
    (action : TestFunction dimension → RealCompute) : Prop :=
  ∀ φ (B : RationalBox dimension), φ.SupportedInBox B →
    ∃ integral : Nat → RealCompute,
      (∀ k, HasBoxIntegral B
        (fun x => RealCompute.mul (density (RawLimit.allowance k) x) (φ.value x)) (integral k)) ∧
      RawLimit.TendsTo integral (action φ)

/-- A fixed locally integrable density, with no improper cutoff needed. -/
def HasRegularKernelAction {dimension : Nat} (density : QPoint dimension → RealCompute)
    (action : TestFunction dimension → RealCompute) : Prop :=
  ∀ φ (B : RationalBox dimension), φ.SupportedInBox B →
    HasBoxIntegral B (fun x => RealCompute.mul (density x) (φ.value x)) (action φ)

private def rawPow (x : RealCompute) : Nat → RealCompute
  | 0 => RealCompute.ofRat 1
  | n + 1 => RealCompute.mul (rawPow x n) x

private def root (q : Rat) (hq : 0 ≤ q) : RealCompute :=
  sqrtRaw q (by change ¬ q < 0; grind only)

private def normSquared {dimension : Nat} (x : QPoint dimension) : Rat :=
  sumRat dimension (fun i => (x i) ^ 2)

/-- The unit sphere area is dimension times the unit ball volume. This
fixes the constant in the Laplace formula by the rational ball recurrence. -/
def unitSphereArea (dimension : Nat) : RealCompute :=
  RealCompute.scaleRat ((dimension : Rat) * nBallCoeff dimension)
    (rawPow GeometricTrig.pi (nBallPiExponent dimension))

private def centeredBox (dimension : Nat) (radius : Rat) (hr : 0 ≤ radius) :
    RationalBox dimension :=
  ⟨fun _ => -radius, fun _ => radius, fun _ => by grind only⟩

/-- Identify the iterated one-coordinate integral with the tagged cube
integral. The factor restores volume to the normalized cube average. -/
def IteratedCubeAgreementTarget : Prop :=
  ∀ dimension (f : JointLipschitzSampler dimension),
    HasBoxIntegral (centeredBox dimension 1 (by decide))
      (fun x => (f.value x).real.preferred)
      (RealCompute.scaleRat ((2 : Rat) ^ dimension) f.cubeAverage.real.preferred)

/-- Laplace density with the dimension-dependent normalizing factor
cleared. The logarithm uses one half of the logarithm of the squared radius. -/
def laplaceScaledTruncation (dimension : Nat) (cutoff : Rat)
    (x : QPoint dimension) : RealCompute :=
  let s := normSquared x
  if h : 0 < s ∧ cutoff ^ 2 ≤ s then
    match dimension with
    | 0 => RealCompute.ofRat 0
    | 1 => RealCompute.scaleRat (1 / 2) (root s (Rat.le_of_lt h.1))
    | 2 => RealCompute.scaleRat (1 / 2) (MonotoneLogarithm.sample s h.1)
    | n + 3 =>
      RealCompute.neg (rawPow (root s⁻¹ (Rat.le_of_lt (Rat.inv_pos.mpr h.1))) (n + 1))
  else RealCompute.ofRat 0

def laplaceNormalization : Nat → RealCompute
  | 0 | 1 => RealCompute.ofRat 1
  | 2 => unitSphereArea 2
  | n + 3 => RealCompute.scaleRat ((n + 1 : Nat) : Rat) (unitSphereArea (n + 3))

/-- The explicit Newtonian kernel, in the sign convention with source
`Delta E = delta`. -/
def HasLaplaceKernelFormula {dimension : Nat} {tests : TestFunctionSpace dimension}
    (E : Distribution tests) : Prop :=
  HasTruncatedKernelAction (laplaceScaledTruncation dimension)
    (fun φ => RealCompute.mul (laplaceNormalization dimension) (E.action φ))

/-- A represented positive square root of pi, for the heat normalization
in odd as well as even dimensions. -/
structure HeatNormalization where
  rootPi : RealCompute
  valid : rootPi.Valid
  positive : rootPi.Pos
  square : (RealCompute.mul rootPi rootPi).Equiv GeometricTrig.pi

/-- Heat density with the factor pi to the power minus half the dimension
cleared. The truncation removes the strip next to the initial-time slice. -/
def heatScaledSlice (dimension : Nat) (t : Rat) (ht : 0 < t) (x : QPoint dimension) : RealCompute :=
  let q := 4 * t
  have hq : 0 < q := Rat.mul_pos (by decide) ht
  RealCompute.mul (rawPow (root q⁻¹ (Rat.le_of_lt (Rat.inv_pos.mpr hq))) dimension)
    (expPowerSeries (-(normSquared x) / q))

def heatScaledTruncation (dimension : Nat) (cutoff : Rat)
    (p : QPoint (dimension + 1)) : RealCompute :=
  let t := p (timeCoordinate dimension)
  if h : 0 < t ∧ cutoff ≤ t then
    heatScaledSlice dimension t h.1 (fun i => p (spatialCoordinate i))
  else RealCompute.ofRat 0

def HasHeatKernelFormula {dimension : Nat} {tests : TestFunctionSpace (dimension + 1)}
    (N : HeatNormalization) (H : Distribution tests) : Prop :=
  HasTruncatedKernelAction (heatScaledTruncation dimension)
    (fun φ => RealCompute.mul (rawPow N.rootPi dimension) (H.action φ))

/-- Integrate one fixed spatial integrand over an exhaustion by boxes. -/
def HasWholeSpaceIntegral {dimension : Nat} (f : QPoint dimension → RealCompute)
    (value : RealCompute) : Prop :=
  ∃ integrals : Nat → RealCompute,
    (∀ k, HasBoxIntegral (centeredBox dimension ((k + 1 : Nat) : Rat) Rat.natCast_nonneg)
      f (integrals k)) ∧ RawLimit.TendsTo integrals value

/-- At every positive rational time the heat kernel has unit spatial mass. -/
def HeatUnitMassTarget (N : HeatNormalization) : Prop :=
  ∀ dimension, 0 < dimension → ∀ t : Rat, ∀ ht : 0 < t,
    HasWholeSpaceIntegral (heatScaledSlice dimension t ht) (rawPow N.rootPi dimension)

/-- Test the initial trace with the test evaluated at the same positive
time as the heat density. Both sides have the heat normalization cleared. -/
def HeatInitialTraceTarget (N : HeatNormalization) : Prop :=
  ∀ dimension, 0 < dimension → ∀ φ : TestFunction (dimension + 1),
    ∃ trace : Nat → RealCompute,
      (∀ k, HasWholeSpaceIntegral (fun x =>
        let t := RawLimit.allowance k
        RealCompute.mul (heatScaledSlice dimension t (RawLimit.allowance_pos k) x)
          (φ.value (Fin.cases t x))) (trace k)) ∧
      RawLimit.TendsTo trace (RealCompute.mul (rawPow N.rootPi dimension) φ.atOrigin)

def waveOneDensity (p : QPoint 2) : RealCompute :=
  RealCompute.ofRat (if qabs (p (spatialCoordinate (0 : Fin 1))) < p (timeCoordinate 1)
    then 1 / 2 else 0)

/-- Two-dimensional wave density with its factor of pi cleared.
The cutoff removes points too close to the conical boundary. -/
def waveTwoScaledTruncation (cutoff : Rat) (p : QPoint 3) : RealCompute :=
  let t := p (timeCoordinate 2)
  let gap := t ^ 2 - spatialRadiusSquared p
  if h : 0 < t ∧ 0 < gap ∧ cutoff ≤ gap then
    RealCompute.scaleRat (1 / 2) (root gap⁻¹ (Rat.le_of_lt (Rat.inv_pos.mpr h.2.1)))
  else RealCompute.ofRat 0

/-- The base cases use the exact density or spherical-action formulas. -/
def WaveBaseFormulasTarget {tests : ∀ n, 0 < n → TestFunctionSpace (n + 1)}
    (kernels : ∀ n (h : 0 < n), Distribution (tests n h)) : Prop :=
  HasRegularKernelAction waveOneDensity (kernels 1 (by decide)).action ∧
  HasTruncatedKernelAction waveTwoScaledTruncation
    (fun φ => RealCompute.mul GeometricTrig.pi ((kernels 2 (by decide)).action φ)) ∧
  HasThreeDimensionalConeAction (kernels 3 (by decide))

private def hemispherePoint {chartDimension : Nat} (upper : Bool)
    (u : QPoint chartDimension) : QPoint (chartDimension + 1) :=
  let s := normSquared u
  Fin.lastCases ((if upper then 1 - s else s - 1) / (1 + s))
    (fun i => 2 * u i / (1 + s))

/-- The integral of an angular function, using two stereographic charts
on the unit ball in one dimension less. -/
def HasSphereIntegral {chartDimension : Nat} (f : QPoint (chartDimension + 1) → RealCompute)
    (value : RealCompute) : Prop :=
  HasBoxIntegral (centeredBox chartDimension 1 (by decide)) (fun u =>
    let s := normSquared u
    if s ≤ 1 then
      RealCompute.scaleRat ((2 / (1 + s)) ^ chartDimension)
        (RealCompute.add (f (hemispherePoint true u)) (f (hemispherePoint false u)))
    else RealCompute.ofRat 0) value

/-- The chart integral of one agrees with the sphere area used in the
Newtonian normalization and the radial wave recurrence. -/
def SphereAreaNormalizationTarget : Prop :=
  ∀ chartDimension, HasSphereIntegral (chartDimension := chartDimension)
    (fun _ => RealCompute.ofRat 1) (unitSphereArea (chartDimension + 1))

private def radialProbe (dimension : Nat) (t r : Rat) : QPoint (dimension + 1) :=
  Fin.cases t (fun i => if i.val = 0 then r else 0)

private def radialEulerValue {dimension : Nat} (φ : TestFunction (dimension + 1))
    (p : QPoint (dimension + 1)) : RealCompute :=
  sumRaw dimension (fun i => RealCompute.scaleRat (p (spatialCoordinate i))
    ((φ.coordinatePartial (spatialCoordinate i)).value p))

/-- Weak form of raising the spatial dimension by two. The lower-dimensional
test is the spherical mean of the higher test plus one over the lower
dimension times its spatial Euler derivative. This expression includes the
axis, since it uses no division by the radius. -/
def IsWaveRadialTransfer {dimension : Nat} (φ : TestFunction (dimension + 3))
    (ψ : TestFunction (dimension + 1)) : Prop :=
  (∀ p q, p (timeCoordinate dimension) = q (timeCoordinate dimension) →
    spatialRadiusSquared p = spatialRadiusSquared q → (ψ.value p).Equiv (ψ.value q)) ∧
  ∀ t r : Rat, 0 ≤ r →
    HasSphereIntegral (chartDimension := dimension + 1) (fun direction =>
      let p := Fin.cases t (fun i => r * direction i)
      RealCompute.add (φ.value p) (RealCompute.scaleRat (1 / (dimension : Rat)) (radialEulerValue φ p)))
      (RealCompute.mul (unitSphereArea (dimension + 2)) (ψ.value (radialProbe dimension t r)))

/-- Construct the radial transfer for every higher-dimensional test and
prove the exact action identity for every such transfer. -/
def WaveRadialRaisingTarget {tests : ∀ n, 0 < n → TestFunctionSpace (n + 1)}
    (kernels : ∀ n (h : 0 < n), Distribution (tests n h)) : Prop :=
  ∀ n (hn : 0 < n) (φ : TestFunction (n + 3)),
    (∃ ψ, IsWaveRadialTransfer φ ψ) ∧
    ∀ ψ, IsWaveRadialTransfer φ ψ →
      ((kernels (n + 2) (Nat.zero_lt_succ _)).action φ).Equiv ((kernels n hn).action ψ)

/-- Laplace milestone on the common test modules. -/
def LaplaceKernelMission (tests : TestModuleFamily) : Prop :=
  ∃ kernels : ∀ dimension, 0 < dimension → Distribution (tests dimension),
    ∀ dimension (h : 0 < dimension),
      IsLaplaceFundamentalSolution (kernels dimension h) ∧
        HasLaplaceKernelFormula (kernels dimension h)

/-- Heat milestone on the common test modules. -/
def HeatKernelMission (tests : TestModuleFamily) : Prop :=
  ∃ N : HeatNormalization, HeatUnitMassTarget N ∧ HeatInitialTraceTarget N ∧
    ∃ kernels : ∀ dimension, 0 < dimension → Distribution (tests (dimension + 1)),
      ∀ dimension (h : 0 < dimension),
        IsRetardedHeatFundamentalSolution (kernels dimension h) ∧
          IsSupportedIn (kernels dimension h) (fun p => 0 ≤ p (timeCoordinate dimension)) ∧
          HasHeatKernelFormula N (kernels dimension h)

/-- Wave milestone with all-dimensional source and support identities,
explicit base cases, and consistent descent. -/
def WaveKernelMission (tests : TestModuleFamily) : Prop :=
  ∃ kernels : ∀ dimension, 0 < dimension → Distribution (tests (dimension + 1)),
    WaveAllDimensionsTarget (fun n _ => tests (n + 1)) kernels ∧
    WaveBaseFormulasTarget kernels ∧ WaveRadialRaisingTarget kernels ∧ WaveKernelsDescend kernels

/-- The full mission. Witnesses for the PDEs all use a single family of
test modules. The foundational proof obligations are stated separately
so contributors can work on them independently. -/
def SchwartzFundamentalSolutionsMission : Prop :=
  ∃ tests : TestModuleFamily,
    (∀ dimension, HasLocalizedOriginTests dimension) ∧ HasPlateauCutoffs ∧
    TestDerivativeUniquenessTarget ∧ TestDerivativeSupportTarget ∧
    DistributionalDerivativeTarget ∧ BoxIntegralLawsTarget ∧ IteratedCubeAgreementTarget ∧
    SphereAreaNormalizationTarget ∧
    LaplaceKernelMission tests ∧ HeatKernelMission tests ∧ WaveKernelMission tests

theorem schwartzMission_implies_fundamentalSolutions
    (h : SchwartzFundamentalSolutionsMission) : AllThreeFundamentalSolutionsExist := by
  obtain ⟨tests, originTests, _, _, _, _, _, _, _, hE, hH, hW⟩ := h
  obtain ⟨E, hE⟩ := hE
  obtain ⟨_, _, _, H, hH⟩ := hH
  obtain ⟨W, hW, _, _, _⟩ := hW
  exact ⟨⟨fun n _ => tests n, E, fun n hn => (hE n hn).1⟩,
    ⟨fun n _ => tests (n + 1), H, fun n hn => (hH n hn).1⟩,
    ⟨fun n _ => tests (n + 1), W, fun n _ => originTests (n + 1), hW⟩⟩

end ComputableDistributions


