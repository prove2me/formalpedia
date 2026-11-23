-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
-- name    : ReciprocityTheory_SemistableReduction_SemiDegI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:05.985542+00:00
-- url     : https://prove2.me/theorems/1c008e6a-4798-4f1b-b354-a87b58793004
-- title:
--   Semi Deg I
-- statement:
--   Definitions and structural lemmas for Semi Deg I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegI.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
def hypG {K : Type} [Field K] {r : ℕ} (j p : Fin r) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun a b => (if a = j ∧ b = p then 1 else 0) + (if a = p ∧ b = j then 1 else 0)
def hypForm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (j p : Fin r) :
    HermForm K r where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := hypG j p
  G_herm a b := by
    simp only [hypG, Matrix.of_apply, map_add, apply_ite S.c, map_one, map_zero]
    rw [add_comm]
    congr 1 <;> simp only [and_comm]
end ReciprocityTheory.MultiplicativeHeights.SemiPt


