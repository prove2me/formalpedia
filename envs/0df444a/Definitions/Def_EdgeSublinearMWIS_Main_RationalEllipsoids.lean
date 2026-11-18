-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_RationalEllipsoids
-- name    : EdgeSublinearMWIS_Main_RationalEllipsoids
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:24:28.068074+00:00
-- url     : https://prove2.me/theorems/371d85c3-ccdb-4d68-ae3c-ae674656188c
-- title:
--   Stored rational ellipsoids and their geometric and encoding invariants
-- statement:
--   This module defines the rounded rational ellipsoid sequence used in exact feasibility.
--
--   For dimension $n$, the initial shape is the identity matrix. At step $k$, a rational central-cut update is rounded to the grid with denominator
--   $$D_k=2^{2k+3n+9}.$$
--   A diagonal error allowance and the fixed relative enlargement $\eta=2^{-(2n+4)}$ compensate for rounding the shape and center. Square roots are approximated from above using integer square roots, so every stored entry is rational.
--
--   The predicate `RoundedEllipsoidEstimates` records positive definiteness, quadratic-form bounds, retention of points satisfying the central cuts, determinant contraction, and numerator/denominator bounds for these specific iterates. Its fields are specifications to be proved; they impose no assumptions on the finite program.
--
--   These definitions provide the common interface between rational ellipsoid geometry and its verified arithmetic implementation.
-- source:
--   Edouard Bonnet, Linear-programming foundations, immutable source https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs, EllipsoidSequence.lean (shapes_invariant, preserves_points_up_to, shapes_below_threshold), EllipsoidStateSize.lean (centers_magnitude, shapes_entry_magnitude and denominator bounds); dyadic height corollaries for the same stored iterates. Supporting the exact-feasibility step in Bonnet--Chang, Theorem 2, Section 5.

import Mathlib
set_option autoImplicit false

-- Solutions.GLSRationalRounding
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RationalRounding.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
Computable rational rounding primitives with real error guarantees and grid
encoding bounds. These do not yet supply a RAM implementation.
-/

namespace EdgeSublinearMWIS.Main.GLS.RationalRounding

/-- Round to the grid with denominator `D`, towards minus infinity. -/
def roundDown (q : ℚ) (D : ℕ) : ℚ := (Int.floor (q * D) : ℚ) / D

/-- A rational upper approximation to a square root using integer square root. -/
def sqrtUpper (q : ℚ) (D : ℕ) : ℚ :=
  ((Nat.sqrt (Nat.ceil (q * (D : ℚ) ^ 2)) + 1 : ℕ) : ℚ) / D

end EdgeSublinearMWIS.Main.GLS.RationalRounding
end


-- Solutions.GLSCast
noncomputable section

namespace EdgeSublinearMWIS.Main.GLS.Cast
def realVector {n : ℕ} (x : Fin n → ℚ) : Fin n → ℝ := fun i => (x i:ℝ)
end EdgeSublinearMWIS.Main.GLS.Cast
end


-- Solutions.GLSDeterminantBounds
noncomputable section
-- Adapted from EdouardBonnet/lax-109476, commit0a042604c7ae1ef4cd9a4c7d82eb902f313d4864.
-- Apache-2.0; original license retained in external-lp/LICENSE.

open scoped BigOperators Matrix

namespace EdgeSublinearMWIS.Main.GLS.DeterminantBounds

end EdgeSublinearMWIS.Main.GLS.DeterminantBounds
end


-- Solutions.GLSEllipsoidStep
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidStep.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
Internal lemmas for the ellipsoid algorithm. These establish the normalized
central-cut matrix update, containment, and determinant shrink factor. They do not yet
establish a rounded rational algorithm or a RAM runtime bound.
-/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStep

/-- The updated ellipsoid's quadratic form in coordinates parallel and
perpendicular to a unit cut normal. -/
noncomputable def centralCutForm (n r t : ℝ) : ℝ :=
  (n + 1) ^ 2 / n ^ 2 * (t + 1 / (n + 1)) ^ 2 +
    (n ^ 2 - 1) / n ^ 2 * (r - t ^ 2)

/-- The determinant factor for the normalized central-cut shape update. -/
noncomputable def determinantFactor (n : ℕ) : ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ (n - 1) *
    ((n : ℝ) / ((n : ℝ) + 1)) ^ 2

open Matrix

/-- The shape matrix for a central cut of the unit ball with normal `u`. -/
noncomputable def centralCutShape (n : ℕ) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (1 - (2 / ((n : ℝ) + 1)) • Matrix.vecMulVec u u)

end EdgeSublinearMWIS.Main.GLS.EllipsoidStep
end


-- Solutions.GLSEllipsoidRounding
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidRounding.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
Internal shape-rounding lemmas. Entrywise rounding needs a diagonal enlargement:
entrywise inequalities alone do not imply containment of ellipsoids.
-/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidRounding

open Matrix

/-- Round every rational entry down, then add a diagonal error allowance. -/
def roundedShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (D : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  (of fun i j => RationalRounding.roundDown (A i j) D) + ((n : ℚ) / D) • 1

/-- Cast a rational shape entrywise to the real numbers. -/
def realShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => (A i j : ℝ)

end EdgeSublinearMWIS.Main.GLS.EllipsoidRounding
end


-- Solutions.GLSEllipsoidBounds
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidBounds.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Internal conditioning and precision bounds for general central-cut shapes. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidBounds

open Matrix EllipsoidRounding

/-- The general central-cut shape uses only rational operations on its data. -/
def cutShape (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  ((n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1)) •
    (A - (2 / (((n : ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

/-- The corresponding real-valued update, used for the conditioning proof. -/
noncomputable def realCutShape (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (A - (2 / (((n : ℝ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

end EdgeSublinearMWIS.Main.GLS.EllipsoidBounds
end


-- Solutions.GLSEllipsoidCenter
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidCenter.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Computable center updates and their error in the new ellipsoid's metric. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidCenter

open Matrix EllipsoidRounding EllipsoidBounds
open EdgeSublinearMWIS.Main.GLS.Cast

/-- Before grid rounding, the new center uses a rational upper square root. -/
def approximateCenter (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) (D : ℕ) : Fin n → ℚ :=
  c - (1 / (((n : ℚ) + 1) * RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D)) •
    (A *ᵥ a)

/-- The stored center is rounded onto the same rational grid as the shape. -/
def roundedCenter (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) (D : ℕ) : Fin n → ℚ :=
  fun i => RationalRounding.roundDown (approximateCenter n A a c D i) D

/-- The exact real center, used only in the correctness argument. -/
noncomputable def exactCenter (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) : Fin n → ℝ :=
  realVector c -
    (1 / (((n : ℝ) + 1) * Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
      (realShape A *ᵥ realVector a)

/-- The stored rational shape also includes the allowance for center displacement. -/
def roundedStepShape (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) (D : ℕ) (η : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  ((1 + η) ^ 2) • roundedShape (cutShape n A a) D

end EdgeSublinearMWIS.Main.GLS.EllipsoidCenter
end


-- Solutions.GLSEllipsoidPrecision
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidPrecision.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! A uniform dyadic grid for both parts of the rational center update. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidPrecision

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter
open EdgeSublinearMWIS.Main.GLS.Cast

/-- This denominator has a linear bit length in the conditioning and accuracy exponents. -/
def gridDenominator (l s n : ℕ) : ℕ := 2 ^ (l + s + n + 3)

end EdgeSublinearMWIS.Main.GLS.EllipsoidPrecision
end


-- Solutions.GLSEllipsoidDeterminant
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidDeterminant.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Determinant bounds from quadratic-form comparison, used for rounded updates. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidDeterminant

open Matrix EllipsoidRounding

end EdgeSublinearMWIS.Main.GLS.EllipsoidDeterminant
end


-- Solutions.GLSEllipsoidIteration
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidIteration.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Conditioning and determinant shrinkage of the same rational stored update. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidIteration

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision
open EllipsoidDeterminant EdgeSublinearMWIS.Main.GLS.Cast

/-- The per-step enlargement used by the uniform precision schedule. -/
def stepAccuracy (n : ℕ) : ℚ := 1 / (2 : ℚ) ^ (2 * n + 4)

end EdgeSublinearMWIS.Main.GLS.EllipsoidIteration
end


-- Solutions.GLSEllipsoidSequence
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidSequence.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
A concrete sequence of rational stored ellipsoids. The cut normals are supplied
externally; no LP separation, stopping rule, certificate recovery, or RAM execution
is asserted here.
-/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidSequence

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision EllipsoidIteration
open EdgeSublinearMWIS.Main.GLS.Cast

/-- The shape sequence uses the precision justified by the previous iteration's lower bound. -/
def shapes (n : ℕ) (a : ℕ → Fin n → ℚ) : ℕ → Matrix (Fin n) (Fin n) ℚ
  | 0 => 1
  | k + 1 => roundedStepShape n (shapes n a k) (a k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)

/-- The center sequence performs the matching computable rational update. -/
def centers (n : ℕ) (a : ℕ → Fin n → ℚ) (c₀ : Fin n → ℚ) : ℕ → Fin n → ℚ
  | 0 => c₀
  | k + 1 => roundedCenter n (shapes n a k) (a k) (centers n a c₀ k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n)

/-- A polynomial number of steps suffices for a prescribed dyadic determinant threshold. -/
def thresholdSteps (n B : ℕ) : ℕ := 4 * (n + 1) * (B * n + 1)

end EdgeSublinearMWIS.Main.GLS.EllipsoidSequence
end


-- Solutions.GLSEllipsoidBall
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidBall.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

open scoped BigOperators Matrix

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidBall

open Matrix EllipsoidRounding EllipsoidDeterminant

variable {ι : Type} [Fintype ι] [DecidableEq ι]

end EdgeSublinearMWIS.Main.GLS.EllipsoidBall
end


-- Solutions.GLSEllipsoidStateBounds
noncomputable section
-- Adapted from EdouardBonnet/lax-109476, commit 0a042604c7ae1ef4cd9a4c7d82eb902f313d4864.
-- Apache-2.0; original license retained in external-lp/LICENSE.

open scoped BigOperators

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize

open Matrix EllipsoidBounds EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence RationalRounding
open EdgeSublinearMWIS.Main.GLS.Cast

def shapeGrid (n k : ℕ) : ℕ :=
  gridDenominator (2 * k + 2) (2 * n + 4) n * (2 ^ (2 * n + 4)) ^ 2

end EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
end


-- Solutions.EllipsoidSequenceHeight
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
open EllipsoidSequence EllipsoidRounding EllipsoidPrecision Cast

 def stateHeight (n k : ℕ) : ℕ := 10*(k+n+4)

end EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
end

namespace EdgeSublinearMWIS.Main
open Matrix GLS.Cast GLS.EllipsoidRounding GLS.EllipsoidSequence GLS.EllipsoidStateSize

/-- Geometric and encoding invariants of the stored rational ellipsoid sequence. -/
structure RoundedEllipsoidEstimates (n : ℕ) (a : ℕ → Fin n → ℚ) : Prop where
  conditioned : ∀ k : ℕ,
    (realShape (shapes n a k)).PosDef ∧
    ∀ x : Fin n → ℝ,
      ((2 : ℝ) ^ (2*k))⁻¹ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (realShape (shapes n a k) *ᵥ x) ∧
      x ⬝ᵥ (realShape (shapes n a k) *ᵥ x) ≤ (4 : ℝ)^k * (x ⬝ᵥ x)
  retained : ∀ (c₀ : Fin n → ℚ) (x : Fin n → ℝ),
    (x-realVector c₀) ⬝ᵥ (x-realVector c₀) ≤ 1 → ∀ k : ℕ,
    (∀ j < k,realVector (a j) ⬝ᵥ (x-realVector (centers n a c₀ j)) ≤ 0) →
    (x-realVector (centers n a c₀ k)) ⬝ᵥ
      ((realShape (shapes n a k))⁻¹ *ᵥ (x-realVector (centers n a c₀ k))) ≤ 1
  determinant : ∀ B : ℕ,
    Real.sqrt (realShape (shapes n a (thresholdSteps n B))).det < (((2 : ℝ)^B)⁻¹)^n
  shapeHeight : ∀ (k : ℕ) (i j : Fin n),
    (shapes n a k i j).num.natAbs ≤ 2^stateHeight n k ∧ (shapes n a k i j).den ≤ 2^stateHeight n k
  centerHeight : ∀ (k : ℕ) (i : Fin n),
    (centers n a 0 k i).num.natAbs ≤ 2^stateHeight n k ∧ (centers n a 0 k i).den ≤ 2^stateHeight n k
  centerMagnitude : ∀ (k : ℕ) (i : Fin n), |(centers n a 0 k i : ℝ)| ≤ (2 : ℝ)^(k+2)
  shapeMagnitude : ∀ (k : ℕ) (i j : Fin n), |(shapes n a k i j : ℝ)| ≤ (4 : ℝ)^k

end EdgeSublinearMWIS.Main


