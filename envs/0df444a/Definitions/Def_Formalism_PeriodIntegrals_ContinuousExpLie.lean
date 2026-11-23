-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ContinuousExpLie
-- name    : Formalism_PeriodIntegrals_ContinuousExpLie
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:37.669141+00:00
-- url     : https://prove2.me/theorems/dd22dfd1-359c-4ba8-8c9f-eee167e1419b
-- title:
--   Continuous Exp Lie
-- statement:
--   Definitions and structural lemmas for Continuous Exp Lie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContinuousExpLie.lean

import Definitions.Def_Formalism_PeriodIntegrals_HaarDefs
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
noncomputable section
namespace PI
open Formalism.QuantumDeterminants
abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
def InLieHpk (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0
section ExpD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def mulL (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)
def mulR (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ a)
end ExpD
section Grp
variable {k r : ℕ}
end Grp
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
def InA (k r : ℕ) (X : Mx k r) : Prop :=
  (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → X i (eI k r a) = 0) ∧
    ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val → X i j = 0
def InLieN (k r : ℕ) (X : Mx k r) : Prop := InLieHpk k r X ∧ InA k r X
theorem unrealify_add (x y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]
theorem unrealify_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]
def unrealL (k r : ℕ) : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) →ₗ[ℝ] Mx k r where
  toFun := unrealify
  map_add' := unrealify_add
  map_smul' := by
    intro c x
    rw [unrealify_smul]
    exact Complex.coe_smul c _
instance (S : Set (Mx k r)) (κ : ENNReal) : SFinite (haarLie S κ) := by
  unfold haarLie
  infer_instance
end PI


