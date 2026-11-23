-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:45.107944+00:00
-- url     : https://prove2.me/theorems/5d16d122-37c6-443a-9f7a-a38d43200617
-- title:
--   Nstatement Hyps Consistent
-- statement:
--   Definitions and structural lemmas for Nstatement Hyps Consistent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/NstatementHypsConsistent.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 NumberField Complex
noncomputable section
abbrev E4 : Type := CyclotomicField 4 ℚ
instance : NumberField E4 := inferInstanceAs (NumberField (CyclotomicField 4 ℚ))
instance : IsCyclotomicExtension {4} ℚ E4 := by
  have h : @IsCyclotomicExtension {4} ℚ E4 _ _ (CyclotomicField.algebra 4 ℚ) := inferInstance
  convert h
  exact Subsingleton.elim _ _
instance : IsCMField E4 := IsCyclotomicExtension.Rat.isCMField E4 (S := {4}) ⟨4, rfl, by norm_num⟩
def dim0 : (E4 →+* ℂ) → ℕ := fun _ => 0
instance : IsEmpty (Idx dim0) := ⟨fun i => i.2.elim0⟩
instance : Subsingleton (Vsp dim0) := ⟨fun x y => PiLp.ext fun i => isEmptyElim i⟩
instance : IsEmpty (Fin (2 * Fintype.card (Idx dim0))) :=
  ⟨fun i => absurd i.2 (by simp)⟩
theorem Hf0 (x y : Vsp dim0) : Hf x y = 0 := by
  simp [Hf]
def X0 : PT E4 where
  dim := dim0
  r := 0
  dim_conj := fun _ => rfl
  b := Module.Basis.empty _
  stable := fun α x _ => by rw [Subsingleton.elim (act α x) 0]; exact zero_mem _
  integral := fun _ _ _ _ => ⟨0, by simp [Hf0]⟩
  perfect := fun φ => ⟨0, zero_mem _, fun y => by
    have hy : y = 0 := Subtype.ext (Subsingleton.elim _ _)
    rw [hy, map_zero]; simp [Hf0]⟩
  eps := fun _ => 1
  eps_pm := fun _ _ => Or.inl rfl
  eps_add := fun _ _ _ _ => by simp [Hf0]
  eps_iso := fun _ _ _ => rfl
instance : IsEmpty (Idx X0.dim) := inferInstanceAs (IsEmpty (Idx dim0))
instance : Subsingleton (Vsp X0.dim) := inferInstanceAs (Subsingleton (Vsp dim0))
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries


