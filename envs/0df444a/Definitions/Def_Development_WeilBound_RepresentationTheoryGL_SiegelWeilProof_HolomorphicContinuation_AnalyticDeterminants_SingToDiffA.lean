-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffA
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:48.949626+00:00
-- url     : https://prove2.me/theorems/681044ba-c260-4481-8c2a-b5af48587429
-- title:
--   Sing To Diff A
-- statement:
--   Definitions and structural lemmas for Sing To Diff A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiffA.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
namespace STD
variable {n : ℕ}
abbrev Vr (n : ℕ) := Fin n → Fin n → ℝ
def hermLin (n : ℕ) : Vr n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := herm
  map_add' x y := by
    ext i j
    simp only [herm, Pi.add_apply, Matrix.add_apply]
    push_cast
    ring
  map_smul' c x := by
    ext i j
    simp only [herm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring
def hermL (n : ℕ) : Vr n →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap (hermLin n)
def v1 (r c : Fin n) : Vr n := fun i j =>
  ((if i = r ∧ j = c then 1 else 0) + (if i = c ∧ j = r then 1 else 0)) / 2
def v2 (r c : Fin n) : Vr n := fun i j =>
  ((if i = c ∧ j = r then 1 else 0) - (if i = r ∧ j = c then 1 else 0)) / 2
def dc (a : Fin n × Fin n) (f : Vr n → ℂ) : Vr n → ℂ :=
  fun x => fderiv ℝ f x (v1 a.1 a.2) + Complex.I * fderiv ℝ f x (v2 a.1 a.2)
def dList : List (Fin n × Fin n) → (Vr n → ℂ) → Vr n → ℂ
  | [], f => f
  | a :: l, f => dc a (dList l f)
end STD
end PositivityTheory.Rg.Sw.LVs


