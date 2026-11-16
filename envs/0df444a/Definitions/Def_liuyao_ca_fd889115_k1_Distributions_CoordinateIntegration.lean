-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_CoordinateIntegration
-- name    : liuyao_ca_fd889115_k1_Distributions_CoordinateIntegration
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:13:58.190256+00:00
-- url     : https://prove2.me/theorems/7869d370-df0c-4bab-9cd7-13ae56386593
-- title:
--   Computable analysis · CoordinateIntegration · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/CoordinateIntegration.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_Goals
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_LipschitzQuadrature

set_option autoImplicit true

/-! Fixing a coordinate preserves the compact test certificates. Integrating
one coordinate uses the foundation's one-variable integral with explicit
slice bounds. -/

open ComputableAnalysis

namespace ComputableDistributions

export ComputableAnalysis (appendLast)

end ComputableDistributions

namespace ComputableAnalysis.RationalBox

/-- The box on the coordinates that remain after fixing the last one. -/
def dropLast {dimension : Nat} (B : RationalBox (dimension + 1)) :
    RationalBox dimension where
  lower i := B.lower i.castSucc
  upper i := B.upper i.castSucc
  ordered i := B.ordered i.castSucc

theorem contains_appendLast {dimension : Nat} (B : RationalBox (dimension + 1))
    (x : QPoint dimension) (t : Rat) :
    B.Contains (appendLast x t) ↔
      B.dropLast.Contains x ∧ B.lower (Fin.last dimension) ≤ t ∧
        t ≤ B.upper (Fin.last dimension) := by
  constructor
  · intro h
    exact ⟨fun i => by simpa [appendLast, dropLast] using h i.castSucc,
      by simpa [appendLast] using h (Fin.last dimension)⟩
  · rintro ⟨hx, ht⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [appendLast] using ht
    · simpa [appendLast, dropLast] using hx j

end ComputableAnalysis.RationalBox

namespace ComputableDistributions

private theorem last_ne_castSucc {dimension : Nat} (i : Fin dimension) :
    Fin.last dimension ≠ i.castSucc := by
  intro h
  have he : dimension = i.val := congrArg Fin.val h
  exact (Nat.ne_of_gt i.isLt) he

private theorem appendLast_incrementIndex {dimension : Nat}
    (alpha : MultiIndex dimension) (i : Fin dimension) :
    appendLast (incrementIndex alpha i) 0 =
      incrementIndex (appendLast alpha 0) i.castSucc := by
  funext j
  refine Fin.lastCases ?_ (fun l => ?_) j
  · simp [appendLast, incrementIndex, last_ne_castSucc]
  · simp [appendLast, incrementIndex, Fin.castSucc_inj]

private theorem appendLast_replaceCoordinate {dimension : Nat}
    (x : QPoint dimension) (i : Fin dimension) (r t : Rat) :
    appendLast (replaceCoordinate x i r) t =
      replaceCoordinate (appendLast x t) i.castSucc r := by
  funext j
  refine Fin.lastCases ?_ (fun l => ?_) j
  · simp [appendLast, replaceCoordinate, last_ne_castSucc]
  · simp [appendLast, replaceCoordinate, Fin.castSucc_inj]

namespace TestFunction

/-- Fix the last input of a compactly supported test at a rational value. -/
def sliceLast {dimension : Nat} (φ : TestFunction (dimension + 1))
    (t : Rat) : TestFunction dimension where
  derivative alpha x := φ.derivative (appendLast alpha 0) (appendLast x t)
  derivative_valid alpha x := φ.derivative_valid _ _
  support := φ.support.dropLast
  derivative_vanishes_off_support alpha x hx :=
    φ.derivative_vanishes_off_support _ _
      (fun h => hx ((φ.support.contains_appendLast x t).mp h).1)
  derivativeLipschitz alpha := φ.derivativeLipschitz (appendLast alpha 0)
  derivativeLipschitz_nonneg alpha := φ.derivativeLipschitz_nonneg (appendLast alpha 0)
  derivative_control alpha x y δ hδ hxy := by
    apply φ.derivative_control _ _ _ _ hδ
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [appendLast, Fin.lastCases_last]
      constructor <;> grind only
    · simpa [appendLast] using hxy j
  partialDerivative alpha i x := by
    simp only [appendLast_incrementIndex, appendLast_replaceCoordinate]
    simpa [appendLast] using
      φ.partialDerivative (appendLast alpha 0) i.castSucc (appendLast x t)

/-- The one-variable sampler obtained by fixing all but the last input. -/
def lastCoordinateIntegrand {dimension : Nat} (φ : TestFunction (dimension + 1))
    (x : QPoint dimension) (t : Rat) : ComputableCoefficient.Value :=
  RealApproximationOrder.parameter (φ.value (appendLast x t)) (φ.value_valid _)

/-- The test's joint bound certifies its last-coordinate integral at each
fixed rational point, with one constant for all parallel slices. -/
def lastCoordinateBounds {dimension : Nat} (φ : TestFunction (dimension + 1))
    (x : QPoint dimension) :
    LipschitzQuadrature.Data (φ.lastCoordinateIntegrand x)
      (φ.support.lower (Fin.last dimension)) (φ.support.upper (Fin.last dimension)) where
  ordered := φ.support.ordered (Fin.last dimension)
  constant := φ.derivativeLipschitz (zeroIndex (dimension + 1))
  nonnegative := φ.derivativeLipschitz_nonneg (zeroIndex (dimension + 1))
  lipschitz := by
    intro u v _ huv _
    apply φ.derivative_control _ _ _ (v - u) (by grind only)
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [appendLast, Fin.lastCases_last]
      constructor <;> grind only
    · simp only [appendLast, Fin.lastCases_castSucc]
      constructor <;> grind only

/-- Integrate over the last interval of the support box, given a justified
one-variable Lipschitz bound on this slice. -/
def integrateLast {dimension : Nat} (φ : TestFunction (dimension + 1))
    (x : QPoint dimension)
    (bounds : LipschitzQuadrature.Data (φ.lastCoordinateIntegrand x)
      (φ.support.lower (Fin.last dimension)) (φ.support.upper (Fin.last dimension))) :
    RealCompute :=
  bounds.integral

theorem integrateLast_hasIntegral {dimension : Nat} (φ : TestFunction (dimension + 1))
    (x : QPoint dimension)
    (bounds : LipschitzQuadrature.Data (φ.lastCoordinateIntegrand x)
      (φ.support.lower (Fin.last dimension)) (φ.support.upper (Fin.last dimension))) :
    Integral.HasIntegral
      (LipschitzIntegralBounds.onInterval (φ.lastCoordinateIntegrand x)
        (φ.support.lower (Fin.last dimension)) (φ.support.upper (Fin.last dimension)))
      (φ.integrateLast x bounds) :=
  bounds.hasIntegral

theorem integrateLast_agrees {dimension : Nat} (φ : TestFunction (dimension + 1))
    (x : QPoint dimension)
    (bounds₁ bounds₂ : LipschitzQuadrature.Data (φ.lastCoordinateIntegrand x)
      (φ.support.lower (Fin.last dimension)) (φ.support.upper (Fin.last dimension))) :
    (φ.integrateLast x bounds₁).Equiv (φ.integrateLast x bounds₂) :=
  (φ.integrateLast_hasIntegral x bounds₁).unique (φ.integrateLast_hasIntegral x bounds₂)

theorem integrateLast_zero_off_projected_support {dimension : Nat}
    (φ : TestFunction (dimension + 1)) (x : QPoint dimension)
    (bounds : LipschitzQuadrature.Data (φ.lastCoordinateIntegrand x)
      (φ.support.lower (Fin.last dimension)) (φ.support.upper (Fin.last dimension)))
    (hx : ¬ φ.support.dropLast.Contains x) :
    (φ.integrateLast x bounds).Equiv (RealCompute.ofRat 0) := by
  let a := φ.support.lower (Fin.last dimension)
  let b := φ.support.upper (Fin.last dimension)
  have hzero : Integral.HasIntegral
      (LipschitzIntegralBounds.onInterval (φ.lastCoordinateIntegrand x) a b)
      (RealCompute.ofRat 0) := by
    simpa only [Rat.mul_zero] using
      (Integral.exactRat_constant_hasIntegral 0 a b
        (φ.support.ordered (Fin.last dimension))).congrFunction
        (G := LipschitzIntegralBounds.onInterval (φ.lastCoordinateIntegrand x) a b)
        ⟨rfl, rfl, fun t _ _ => RealCompute.equiv_symm
          (φ.derivative_vanishes_off_support _ (appendLast x t)
            (fun h => hx ((φ.support.contains_appendLast x t).mp h).1))⟩
  exact (φ.integrateLast_hasIntegral x bounds).unique hzero

end TestFunction

end ComputableDistributions


