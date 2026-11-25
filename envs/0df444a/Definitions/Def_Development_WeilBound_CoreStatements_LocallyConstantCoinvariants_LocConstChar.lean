-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
-- name    : Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:08.652394+00:00
-- url     : https://prove2.me/theorems/60968d9e-96af-4fd6-8cbc-99bd186f0a1c
-- title:
--   Loc Const Char
-- statement:
--   Definitions and structural lemmas for Loc Const Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/LocConstChar.lean

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_gl_eq_mul_of_rank
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.KCo
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank Matrix Topology
  MeasureTheory
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a : Type} [Fintype a] [DecidableEq a] {κ : ℕ}
def toRank (hκ : κ = Fintype.card a) (g : GL a k) : RankIn k a a {κ} :=
  ⟨g.val, (Matrix.rank_unit g).trans hκ.symm⟩
theorem toRank_surj (hκ : κ = Fintype.card a) : Function.Surjective (toRank (k := k) hκ) := fun x => by
  obtain ⟨g, hg⟩ := exists_gl_eq_mul_of_rank k a a (1 : Matrix a a k) x.1 (by simp) (x.2.trans hκ)
  exact ⟨g, Subtype.ext (by rw [hg, Matrix.one_mul]; rfl)⟩
def rankHomeo (hκ : κ = Fintype.card a) : GL a k ≃ₜ RankIn k a a {κ} :=
  IsEmbedding.toHomeomorphOfSurjective (f := toRank hκ)
    ((IsEmbedding.subtypeVal.of_comp_iff (f := toRank hκ)).1 (GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := a))) (toRank_surj hκ)
end PositivityTheory.KCo


