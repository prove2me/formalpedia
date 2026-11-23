-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:08.680329+00:00
-- url     : https://prove2.me/theorems/95c96b78-0391-474c-b94e-a3140d02c0b1
-- title:
--   Unipotent Radical Basic
-- statement:
--   Definitions and structural lemmas for Unipotent Radical Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
namespace GlobalTheory.RootEx.Radical
section
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
def Uni (b : ι → ℕ) (M : Matrix ι ι k) : Prop :=
  ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s
omit [Fintype ι] in
theorem Uni.blockTri {b : ι → ℕ} {M : Matrix ι ι k} (h : Uni b M) : M.BlockTriangular b := by
  intro r s hrs
  rw [h r s hrs.le, Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hrs
theorem Uni.det {b : ι → ℕ} {M : Matrix ι ι k} (h : Uni b M) : M.det = 1 := by
  rw [h.blockTri.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [h r s (by rw [hr, hs])]
    simp [Matrix.one_apply]
  rw [this, Matrix.det_one]
end
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
end GlobalTheory.RootEx.Radical


