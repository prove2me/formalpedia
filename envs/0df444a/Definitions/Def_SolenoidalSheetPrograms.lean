-- Prove2me | Definitions.Def_SolenoidalSheetPrograms
-- name    : SolenoidalSheetPrograms
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:24.197396+00:00
-- url     : https://prove2.me/theorems/2f42d8f4-113a-4dee-93ac-1e4ab4b11df3
-- statement:
--   Inside namespace Solenoidal, this block sets up the geometric and analytic vocabulary for programs built from solenoidal sheets, taking place on the three-dimensional torus with period 10 in each coordinate. Plane is ℝ², Space is ℝ³, SpaceTime is ℝ×ℝ³, a Field is a time-dependent vector field ℝ→ℝ³→ℝ³, a Pressure is a time-dependent scalar function, toTorus reduces a point mod 10, and sheet(y) lifts a plane point y to the point (y₀, y₁, 2) in space. A Rectangle is a closed axis-parallel box in the plane with rational lower and upper corners satisfying lower<upper in each coordinate; it has a carrier set, a center and half-widths, and lies in the coding square if every coordinate interval is contained in [2,3]. A family of N rectangles is SeparatelySeparated if distinct members are at positive distance from each other. diagonalMap(P,Q,r) sends y to Q's center plus r_j(y_j−P's center_j) coordinatewise. SheetData(N) packages N source and target rectangles, both inside the coding square and each family separated, with positive rational ratios such that the diagonal map from each source to its target with that ratio maps the source carrier exactly onto the target carrier. Next come torus-flavored field notions: deck(k) is the translation by 10k for integer vector k, SpatiallyPeriodic means invariance under all such translations, the fundamental cell is [0,10)³, and spatial partials, the time partial (a one-sided derivative on t≥0), divergence, Laplacian, advection (u·∇)u and pressure gradient are defined. Properties of a field include DivergenceFree, MeanZero over the cell at each time, Smooth as a C^∞ function of space-time, OnePeriodic in time with period 1, and IntegerCollars, meaning it vanishes identically in some time neighborhood of every integer. ClassicalSolution(ν,f,u,p) is a Prop-valued structure asserting that u and p are spatially periodic, have the stated continuity and differentiability (u to second order in space and first order in time, p to first order in space) on time cylinders [0,T]×ℝ³, p has mean zero, u is divergence-free and vanishes at time 0, and the forced Navier–Stokes equation ∂ₜu+(u·∇)u=−∇p+νΔu+f holds for t≥0. MaterialFlow(u,X) says X starts at the identity, is continuous for t≥0 and follows trajectories with velocity u. Finally, mixedDerivative takes arbitrary iterated space-time partial derivatives indexed by lists over four directions, and computability notions are defined using Mathlib partial recursive codes: a code names a real r if it yields rational approximations within 2⁻ⁿ, ComputableReal means some code names r, and NamesPoint does the same for space-time points. Effective(u) says one code computes, from any name of a point, any derivative multi-index and rational ε>0, a rational vector within ε of that derivative, and EffectiveBounds(u) says one code produces, for each multi-index, a nonnegative rational uniform bound on that derivative's norm.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SolenoidalSheetPrograms.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SolenoidalSheetPrograms.lean; bytes 16..6448
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Solenoidal

abbrev Plane := Fin 2 → ℝ
abbrev Space := Fin 3 → ℝ
abbrev SpaceTime := ℝ × Space
abbrev Field := ℝ → Space → Space
abbrev Pressure := ℝ → Space → ℝ
abbrev Torus := Fin 3 → AddCircle (10 : ℝ)

def toTorus (x : Space) : Torus := fun i => (x i : AddCircle (10 : ℝ))

def sheet (y : Plane) : Space := ![y 0, y 1, 2]

structure Rectangle where
  lower : Fin 2 → ℚ
  upper : Fin 2 → ℚ
  positive : ∀ j, lower j < upper j

namespace Rectangle

def carrier (R : Rectangle) : Set Plane :=
  {y | ∀ j, (R.lower j : ℝ) ≤ y j ∧ y j ≤ (R.upper j : ℝ)}

def center (R : Rectangle) : Plane :=
  fun j => ((R.lower j : ℝ) + (R.upper j : ℝ)) / 2

def halfWidth (R : Rectangle) : Plane :=
  fun j => ((R.upper j : ℝ) - (R.lower j : ℝ)) / 2

def inCodingSquare (R : Rectangle) : Prop :=
  ∀ j, 2 ≤ R.lower j ∧ R.upper j ≤ 3

end Rectangle

def SeparatelySeparated {N : ℕ} (R : Fin N → Rectangle) : Prop :=
  ∀ i j, i ≠ j → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ (R i).carrier, ∀ y ∈ (R j).carrier, δ ≤ ‖x - y‖

def diagonalMap (P Q : Rectangle) (r : Fin 2 → ℚ) (y : Plane) : Plane :=
  fun j => Q.center j + (r j : ℝ) * (y j - P.center j)

structure SheetData (N : ℕ) where
  source : Fin N → Rectangle
  target : Fin N → Rectangle
  source_inside : ∀ i, (source i).inCodingSquare
  target_inside : ∀ i, (target i).inCodingSquare
  source_separated : SeparatelySeparated source
  target_separated : SeparatelySeparated target
  ratio : Fin N → Fin 2 → ℚ
  ratio_positive : ∀ i j, 0 < ratio i j
  image_eq : ∀ i,
    diagonalMap (source i) (target i) (ratio i) '' (source i).carrier =
      (target i).carrier

def deck (k : Fin 3 → ℤ) : Space := fun j => 10 * (k j : ℝ)

def SpatiallyPeriodic {E : Type*} (g : ℝ → Space → E) : Prop :=
  ∀ t x k, g t (x + deck k) = g t x

def fundamentalCell : Set Space :=
  Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 10)

def basis (j : Fin 3) : Space := Pi.single j 1

def spatialPartial (u : Field) (j : Fin 3) : Field :=
  fun t x => fderiv ℝ (u t) x (basis j)

def timePartial (u : Field) : Field :=
  fun t x => derivWithin (fun s => u s x) (Set.Ici 0) t

def divergence (u : Field) (t : ℝ) (x : Space) : ℝ :=
  ∑ j : Fin 3, spatialPartial u j t x j

def laplacian (u : Field) : Field :=
  fun t x => ∑ j : Fin 3, spatialPartial (spatialPartial u j) j t x

def advection (u : Field) : Field :=
  fun t x => fderiv ℝ (u t) x (u t x)

def gradient (p : Pressure) : Field :=
  fun t x j => fderiv ℝ (p t) x (basis j)

def DivergenceFree (u : Field) : Prop := ∀ t x, divergence u t x = 0

def MeanZero (u : Field) : Prop :=
  ∀ t, (∫ x in fundamentalCell, u t x) = 0

def Smooth (u : Field) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun z : SpaceTime => u z.1 z.2)

def OnePeriodic (u : Field) : Prop := ∀ t x, u (t + 1) x = u t x

def IntegerCollars (u : Field) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℤ, ∀ t x, |t - (n : ℝ)| < ε → u t x = 0

def cylinder (T : ℝ) : Set SpaceTime := Set.Icc 0 T ×ˢ Set.univ

structure ClassicalSolution (ν : ℝ) (f u : Field) (p : Pressure) : Prop where
  spatial_periodic_u : SpatiallyPeriodic u
  spatial_periodic_p : SpatiallyPeriodic p
  continuous_u : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => u z.1 z.2) (cylinder T)
  differentiable_t : ∀ t, 0 ≤ t → ∀ x,
    DifferentiableWithinAt ℝ (fun s => u s x) (Set.Ici 0) t
  continuous_t : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => timePartial u z.1 z.2) (cylinder T)
  differentiable_x : ∀ t, 0 ≤ t → Differentiable ℝ (u t)
  continuous_x : ∀ T, 0 ≤ T → ∀ j,
    ContinuousOn (fun z : SpaceTime => spatialPartial u j z.1 z.2) (cylinder T)
  differentiable_xx : ∀ t, 0 ≤ t → ∀ j,
    Differentiable ℝ (spatialPartial u j t)
  continuous_xx : ∀ T, 0 ≤ T → ∀ i j,
    ContinuousOn (fun z : SpaceTime => spatialPartial (spatialPartial u i) j z.1 z.2)
      (cylinder T)
  continuous_p : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => p z.1 z.2) (cylinder T)
  differentiable_p : ∀ t, 0 ≤ t → Differentiable ℝ (p t)
  continuous_px : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => gradient p z.1 z.2) (cylinder T)
  pressure_mean_zero : ∀ t, 0 ≤ t → (∫ x in fundamentalCell, p t x) = 0
  incompressible : ∀ t, 0 ≤ t → ∀ x, divergence u t x = 0
  initial : ∀ x, u 0 x = 0
  equation : ∀ t, 0 ≤ t → ∀ x,
    timePartial u t x + advection u t x =
      -gradient p t x + ν • laplacian u t x + f t x

def MaterialFlow (u : Field) (X : ℝ → Space → Space) : Prop :=
  (∀ a, X 0 a = a) ∧
  (∀ a, ContinuousOn (fun t => X t a) (Set.Ici 0)) ∧
  (∀ a t, 0 ≤ t →
    HasDerivWithinAt (fun s => X s a) (u t (X t a)) (Set.Ici 0) t)

def spacetimeBasis : Fin 4 → SpaceTime :=
  ![(1, 0), (0, basis 0), (0, basis 1), (0, basis 2)]

def mixedDerivative (u : Field) : List (Fin 4) → SpaceTime → Space
  | [] => fun z => u z.1 z.2
  | j :: α => fun z => fderiv ℝ (mixedDerivative u α) z (spacetimeBasis j)

def flatten (z : SpaceTime) : Fin 4 → ℝ := ![z.1, z.2 0, z.2 1, z.2 2]

def NamesReal (c : Nat.Partrec.Code) (r : ℝ) : Prop :=
  ∀ n : ℕ, ∃ q : ℚ, Encodable.encode q ∈ c.eval n ∧
    |(q : ℝ) - r| ≤ (1 / 2 : ℝ) ^ n

def ComputableReal (r : ℝ) : Prop := ∃ c, NamesReal c r

def NamesPoint (c : Nat.Partrec.Code) (z : SpaceTime) : Prop :=
  ∀ n : ℕ, ∃ q : Fin 4 → ℚ,
    @Encodable.encode (Fin 4 → ℚ) Encodable.finArrow q ∈ c.eval n ∧
    ‖(fun j => (q j : ℝ)) - flatten z‖ ≤ (1 / 2 : ℝ) ^ n

def Effective (u : Field) : Prop :=
  ∃ e : Nat.Partrec.Code, ∀ α : List (Fin 4), ∀ c : Nat.Partrec.Code,
    ∀ z : SpaceTime, NamesPoint c z → ∀ ε : ℚ, 0 < ε →
      ∃ q : Fin 3 → ℚ,
        @Encodable.encode (Fin 3 → ℚ) Encodable.finArrow q ∈
          e.eval (Encodable.encode (α, c, ε)) ∧
          ‖(fun j => (q j : ℝ)) - mixedDerivative u α z‖ < (ε : ℝ)

def EffectiveBounds (u : Field) : Prop :=
  ∃ e : Nat.Partrec.Code, ∀ α : List (Fin 4), ∃ B : ℚ,
    Encodable.encode B ∈ e.eval (Encodable.encode α) ∧ 0 ≤ B ∧
      ∀ z : SpaceTime, ‖mixedDerivative u α z‖ ≤ (B : ℝ)



end Solenoidal
end
end OAI


