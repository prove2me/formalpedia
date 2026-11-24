-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:07.42031+00:00
-- url     : https://prove2.me/theorems/326f30b8-b00a-4e24-9884-31cd03d29693
-- title:
--   Theta Recognition Matched Parts Dim Eq
-- statement:
--   Definitions and structural lemmas for Theta Recognition Matched Parts Dim Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionMatchedPartsDimEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_equivalence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
namespace GlobalTheory.MatchParts
section Gen
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}
theorem qrefl {k : ℕ} (p : N.QT k) : N.QEq p p := (N.qEq_equivalence k).refl p
theorem r_right (μ : Match N N' n) {k : ℕ} {p : N.QT k} {p' q' : N'.QT k} (h : μ.r k p p') :
    μ.r k p q' ↔ N'.QEq p' q' := μ.eqv k p p p' q' h (qrefl p)
noncomputable def flip (μ : Match N N' n) : Match N' N n where
  r k p' p := μ.r k p p'
  tot := μ.cotot
  cotot := μ.tot
  mul k p q p' q' h h' := μ.mul k _ _ _ _ h h'
  eqv k p' q' p q h e :=
    ⟨fun h' => μ.inj k p q q' ((r_right μ h).2 e) h', fun e' => (μ.eqv k p q p' q' h e').2 e⟩
  inj k p' q' p h h' := (r_right μ h).1 h'
  incl k k' p' p q' q hk a b c d := μ.incl k k' p p' q q' hk c d a b
  wp k p' q' p q h h' := (μ.wp k p q p' q' h h').symm
  c₀ := μ.c₀⁻¹
  c₀_ne := inv_ne_zero μ.c₀_ne
  tx j p' p h := by rw [μ.tx j p p' h, ← mul_assoc, inv_mul_cancel₀ μ.c₀_ne, one_mul]
def ofG {k : ℕ} (x : N.Gt) (hx : x ^ k = 1) : N.QT k := ⟨(1, x), by rw [N.mem_QT]; exact hx.trans N.io_zero.symm⟩
end Gen
section Main
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
  {N N' : NumD C} {q : QuadraticMap ℤ N.X ℝ} {q' : QuadraticMap ℤ N'.X ℝ} {n g g' : ℕ}
end Main
end GlobalTheory.MatchParts


