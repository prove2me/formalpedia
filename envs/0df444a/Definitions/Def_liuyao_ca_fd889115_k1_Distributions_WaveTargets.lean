-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_WaveTargets
-- name    : liuyao_ca_fd889115_k1_Distributions_WaveTargets
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:34:28.62468+00:00
-- url     : https://prove2.me/theorems/f6b5bfe4-08bc-4211-a537-53eab358e96e
-- title:
--   Computable analysis · WaveTargets · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/WaveTargets.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_CoordinateIntegration
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricSinCos

set_option autoImplicit true

/-! Explicit spherical normalization and uniqueness targets for the wave
equation. The target action is a limit of rational quadratures on the cone,
independent of the ordinary spacetime functions used to present it. -/

open ComputableAnalysis

namespace ComputableDistributions

private def midpointTag {cells : Nat} (a b : Rat) (i : Fin cells) : Rat :=
  a + (b - a) * (((2 * i.val + 1 : Nat) : Rat) / ((2 * cells : Nat) : Rat))

private theorem midpointTag_nonnegative {cells : Nat} (b : Rat) (i : Fin cells)
    (hb : 0 ≤ b) : 0 ≤ midpointTag 0 b i := by
  unfold midpointTag
  rw [Rat.zero_add, show b - 0 = b by grind only, Rat.div_def]
  have hd : 0 < (((2 * cells : Nat) : Rat)) :=
    Rat.natCast_pos.mpr (Nat.mul_pos (by decide) (Nat.zero_lt_of_lt i.isLt))
  exact Rat.mul_nonneg hb (Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hd)))

private theorem squareNonnegative (q : Rat) : 0 ≤ q ^ 2 := by
  rw [Rat.pow_succ, Rat.pow_one]
  by_cases hq : 0 ≤ q
  · exact Rat.mul_nonneg hq hq
  · have hneg : 0 ≤ -q := by grind only
    have hsquare : (-q) * (-q) = q * q := by grind only
    rw [← hsquare]
    exact Rat.mul_nonneg hneg hneg

/-- Two rational stereographic charts on the closed unit disk map to the
upper and lower hemispheres. Scaling the direction by the time gives a
point on the forward cone. -/
def sphericalConePoint (upper : Bool) (t u v : Rat) : QPoint 4 :=
  let radiusSquared := u ^ 2 + v ^ 2
  let denominator := 1 + radiusSquared
  Fin.cases t fun i =>
    t * (if i = 0 then 2 * u / denominator
      else if i = 1 then 2 * v / denominator
      else (if upper then 1 - radiusSquared else radiusSquared - 1) / denominator)

theorem sphericalConePoint_onForwardLightCone (upper : Bool) (t u v : Rat)
    (ht : 0 ≤ t) :
    OnForwardLightCone (spatialDimension := 3) (sphericalConePoint upper t u v) := by
  refine ⟨ht, ?_⟩
  let d : Rat := 1 + (u ^ 2 + v ^ 2)
  have hd : d ≠ 0 := by
    have hu := squareNonnegative u
    have hv := squareNonnegative v
    dsimp [d]
    grind only
  have hcancel := Rat.mul_inv_cancel d hd
  have hfactor : (t * d⁻¹) ^ 2 * d ^ 2 = t ^ 2 := by
    calc
      _ = (t * (d * d⁻¹)) ^ 2 := by grind [Rat.pow_succ]
      _ = _ := by rw [hcancel, Rat.mul_one]
  cases upper
  · change 0 + (t * (2 * u / d)) ^ 2 + (t * (2 * v / d)) ^ 2 +
      (t * ((u ^ 2 + v ^ 2 - 1) / d)) ^ 2 = t ^ 2
    calc
      _ = (t * d⁻¹) ^ 2 * d ^ 2 := by
        dsimp only [d]
        grind [Rat.div_def, Rat.pow_succ]
      _ = _ := hfactor
  · change 0 + (t * (2 * u / d)) ^ 2 + (t * (2 * v / d)) ^ 2 +
      (t * ((1 - (u ^ 2 + v ^ 2)) / d)) ^ 2 = t ^ 2
    calc
      _ = (t * d⁻¹) ^ 2 * d ^ 2 := by
        dsimp only [d]
        grind [Rat.div_def, Rat.pow_succ]
      _ = _ := hfactor

/-! The chart Jacobian is 4 / (1 + u^2 + v^2)^2. The two disks
cover the unit sphere and the factor four cancels the one in 4 pi. -/

structure ConeQuadraturePoint where
  point : QPoint 4
  weight : Rat
  nonnegative : 0 ≤ weight

/-- The weighted samples of the cone quadrature up to a rational time. -/
def coneQuadraturePoints (cutoff : Rat) (level : Nat) : List ConeQuadraturePoint :=
  let cells : Nat := 2 ^ level
  let timeStep := max 0 cutoff / (cells : Rat)
  let chartStep := 2 / (cells : Rat)
  (List.ofFn fun ti : Fin cells => ti).flatMap fun ti =>
    let t := midpointTag 0 (max 0 cutoff) ti
    have ht := midpointTag_nonnegative (max 0 cutoff) ti (by grind)
    (List.ofFn fun (ui : Fin cells) => midpointTag (-1) 1 ui).flatMap fun u =>
      (List.ofFn fun (vi : Fin cells) => midpointTag (-1) 1 vi).flatMap fun v =>
        let r := u ^ 2 + v ^ 2
        if r ≤ 1 then
          let w := timeStep * chartStep ^ 2 * (t / (1 + r) ^ 2)
          have hstep : 0 ≤ timeStep := by
            have hc : 0 < (cells : Rat) := Rat.natCast_pos.mpr (Nat.pow_pos (by decide))
            change 0 ≤ max 0 cutoff / (cells : Rat)
            rw [Rat.div_def]
            exact Rat.mul_nonneg (by grind) (Rat.le_of_lt (Rat.inv_pos.mpr hc))
          have hdiv : 0 ≤ t / (1 + r) ^ 2 := by
            have hr : 0 ≤ r := Rat.add_nonneg (squareNonnegative u) (squareNonnegative v)
            have hd : 0 < 1 + r := by grind only
            rw [Rat.div_def]
            exact Rat.mul_nonneg ht (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.pow_pos hd)))
          [true, false].map fun upper =>
            ⟨sphericalConePoint upper t u v, w,
              Rat.mul_nonneg (Rat.mul_nonneg hstep (squareNonnegative chartStep)) hdiv⟩
        else []

/-- Every atom used to form the boxes is a point on the forward light cone. -/
theorem coneQuadraturePoints_onForwardLightCone {cutoff : Rat} {level : Nat}
    {a : ConeQuadraturePoint} (ha : a ∈ coneQuadraturePoints cutoff level) :
    OnForwardLightCone (spatialDimension := 3) a.point := by
  unfold coneQuadraturePoints at ha
  obtain ⟨ti, _, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨u, _, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨v, _, ha⟩ := List.mem_flatMap.mp ha
  dsimp only at ha
  split at ha
  · obtain ⟨upper, _, rfl⟩ := List.mem_map.mp ha
    exact sphericalConePoint_onForwardLightCone upper _ u v
      (midpointTag_nonnegative (max 0 cutoff) ti (by grind))
  · simp at ha

open ComputableCoefficient RealApproximationOrder

/-- Apply a finite weighted quadrature to represented values. -/
def coneWeightedSum (f : ConeQuadraturePoint → Value) : List ConeQuadraturePoint → Value
  | [] => Value.rational 0
  | a :: rest => Value.add (scale a.weight (f a)) (coneWeightedSum f rest)

/-- Midpoint approximation of the spherical action multiplied by pi. -/
def threeDimensionalConeApproximation (φ : TestFunction 4) (level : Nat) : RealCompute :=
  (coneWeightedSum (fun a => parameter (φ.value a.point) (φ.value_valid a.point))
    (coneQuadraturePoints (φ.support.upper (timeCoordinate 3)) level)).real.preferred

theorem threeDimensionalConeApproximation_valid (φ : TestFunction 4) (level : Nat) :
    (threeDimensionalConeApproximation φ level).Valid :=
  (coneWeightedSum _ _).real.valid

/-- Exact three-dimensional target: the kernel has the action
∫₀∞ (t / (4 pi)) ∫_{S²} φ(t, t ω) dσ(ω) dt. Stating the comparison
after multiplication by the foundation's pi avoids a division at the
level of raw values. -/
def HasThreeDimensionalConeAction {tests : TestFunctionSpace 4}
    (W : Distribution tests) : Prop :=
  ∀ φ, RawLimit.TendsTo (threeDimensionalConeApproximation φ)
    (RealCompute.mul GeometricTrig.pi (W.action φ))

/-- Identify the dimension-three member of the all-dimensional family with
the explicit spherical action. -/
def WaveAllDimensionsWithConeFormulaExist : Prop :=
  ∃ G : WaveAllDimensionsGoal, HasThreeDimensionalConeAction (G.kernels 3 (by decide))

theorem waveAllDimensionsWithConeFormula_impliesExist
    (h : WaveAllDimensionsWithConeFormulaExist) : RetardedWaveFundamentalSolutionsExist := by
  obtain ⟨G, _⟩ := h
  exact ⟨G.testSpaces, G.kernels, G.originTests, G.satisfies⟩

/-- Lift a lower-dimensional spacetime test by multiplying in the added
spatial coordinate by a compact cutoff. The cutoff equals one throughout
the part of the added axis that the forward cone can reach during the
test's time interval, with a positive margin. -/
def IsWaveDescentLift {spatialDimension : Nat}
    (φ : TestFunction (spatialDimension + 1))
    (ψ : TestFunction (spatialDimension + 2)) : Prop :=
  ∃ cutoff : TestFunction 1,
    let radius := max 0 (φ.support.upper (timeCoordinate spatialDimension)) + 1
    (∀ r : Rat, -radius ≤ r → r ≤ radius →
      (cutoff.value (fun _ => r)).Equiv (RealCompute.ofRat 1)) ∧
    ∀ p r, (ψ.value (appendLast p r)).Equiv
      (RealCompute.mul (φ.value p) (cutoff.value (fun _ => r)))

/-- Adjacent dimensions agree under integration of one spatial coordinate.
The target asks both for compact test lifts and for independence of their
cutoffs. -/
def WaveKernelsDescend {tests : ∀ n, 0 < n → TestFunctionSpace (n + 1)}
    (kernels : ∀ n (h : 0 < n), Distribution (tests n h)) : Prop :=
  ∀ spatialDimension (h : 0 < spatialDimension)
    (φ : TestFunction (spatialDimension + 1)),
    (∃ ψ, IsWaveDescentLift φ ψ) ∧
    ∀ ψ, IsWaveDescentLift φ ψ →
      ((kernels (spatialDimension + 1) (Nat.zero_lt_succ _)).action ψ).Equiv
        ((kernels spatialDimension h).action φ)

def WaveDimensionDescentTarget (G : WaveAllDimensionsGoal) : Prop :=
  WaveKernelsDescend G.kernels

/-- Uniqueness of the retarded wave action on a fixed test module. The
conclusion identifies the actions on all tests, so regularizations may
differ. -/
def RetardedWaveUniquenessTarget : Prop :=
  ∀ spatialDimension, 0 < spatialDimension →
    ∀ (tests : TestFunctionSpace (spatialDimension + 1))
      (W V : Distribution tests),
      IsRetardedWaveFundamentalSolution W → IsRetardedWaveFundamentalSolution V →
      Distribution.Equivalent W V

end ComputableDistributions


