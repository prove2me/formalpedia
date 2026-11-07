-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
-- name    : QEC_Coding_ExpanderCodes_LocalStarExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:35:29.750564+00:00
-- url     : https://prove2.me/theorems/cf839b1e-dbd0-4184-ad8b-4e2751445147
-- title:
--   Local Star Expansion
-- statement:
--   Definitions and structural lemmas for Local Star Expansion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
def IsCosetLeader (h : Matrix R W F) (y : R → F) (x : Word F W) : Prop :=
  h.mulVec x = y ∧
    ∀ z : Word F W, h.mulVec z = y → HammingWeight x ≤ HammingWeight z
omit [Fintype F] [DecidableEq W] [Fintype R] [Fintype R'] in
/-- Every nonempty syndrome fiber has a coset leader. -/
theorem exists_cosetLeader
    (h : Matrix R W F) (y : R → F) (x₀ : Word F W)
    (hx₀ : h.mulVec x₀ = y) :
    ∃ x : Word F W, IsCosetLeader h y x := by
  let S : Set (Word F W) := {x | h.mulVec x = y}
  have hS : S.Nonempty := ⟨x₀, hx₀⟩
  let x := Function.argminOn HammingWeight S hS
  refine ⟨x, Function.argminOn_mem HammingWeight S hS, ?_⟩
  intro z hz
  exact Function.argminOn_le HammingWeight S hz
omit [Fintype F] [DecidableEq F] [DecidableEq W] [Fintype R'] in
/-- A parity-check matrix of maximal row rank realizes every syndrome. -/
theorem mulVec_surjective_of_rank_eq_card_rows
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R) :
    Function.Surjective h.mulVec := by
  have hRange : LinearMap.range h.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using hRank
  intro y
  obtain ⟨x, hx⟩ := (LinearMap.range_eq_top.mp hRange) y
  exact ⟨x, hx⟩
omit [Fintype F] [DecidableEq F] [DecidableEq W] [Fintype R'] in
/-- A chosen preimage of one syndrome under a maximal-row-rank check. -/
noncomputable def fullRowRankPreimage
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (y : Word F R) : Word F W :=
  Classical.choose (mulVec_surjective_of_rank_eq_card_rows h hRank y)
omit [Fintype F] [DecidableEq F] [DecidableEq W] [Fintype R'] in
@[simp] theorem fullRowRankPreimage_syndrome
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (y : Word F R) :
    h.mulVec (fullRowRankPreimage h hRank y) = y :=
  Classical.choose_spec (mulVec_surjective_of_rank_eq_card_rows h hRank y)
noncomputable def cosetLeaderMatrix
    (h : Matrix R W F) (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (row x₀ i) = z i) : Matrix W W F :=
  fun i => Classical.choose (exists_cosetLeader h (z i) (row x₀ i) (hx₀ i))
noncomputable def fullRowRankCosetLeaderMatrix
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (z : Matrix W R F) : Matrix W W F :=
  cosetLeaderMatrix h z
    (fun i => fullRowRankPreimage h hRank (z i))
    (fun i => fullRowRankPreimage_syndrome h hRank (z i))
end QEC.Coding.ProductExpansion


