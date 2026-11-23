-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:47.850799+00:00
-- url     : https://prove2.me/theorems/4983226a-3ad0-4179-9b5f-7f0ee1711c19
-- title:
--   Irreducible XSq Add One
-- statement:
--   Definitions and structural lemmas for Irreducible XSq Add One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleXSqAddOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
namespace GlobalTheory.GaussExt
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : F[X]) := by
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!
  refine (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hdeg]) (by rw [hdeg]; norm_num)).2 ?_
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [mem_roots (Monic.ne_zero (by monicity!)), IsRoot, eval_add, eval_pow, eval_X, eval_one] at hr
  obtain ⟨τ⟩ : Nonempty (F →+* ℝ) := by
    obtain ⟨φ⟩ := (inferInstance : Nonempty (F →+* ℂ))
    exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩
  have := congrArg τ hr
  simp at this
  nlinarith [sq_nonneg (τ r)]
instance : Fact (Irreducible (X ^ 2 + 1 : F[X])) := ⟨irreducible_X_sq_add_one F⟩
abbrev Ext : Type := AdjoinRoot (X ^ 2 + 1 : F[X])
instance : Module.Finite F (Ext F) :=
  (AdjoinRoot.powerBasis (Monic.ne_zero (by monicity!) : (X ^ 2 + 1 : F[X]) ≠ 0)).finite
instance : NumberField (Ext F) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap F (Ext F)).injective
  to_finiteDimensional := Module.Finite.trans F (Ext F)
def ii : Ext F := AdjoinRoot.root _
def gEmb (p : F × F) : Ext F := algebraMap F (Ext F) p.1 + algebraMap F (Ext F) p.2 * ii F
end GlobalTheory.GaussExt


