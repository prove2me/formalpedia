-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:38.871512+00:00
-- url     : https://prove2.me/theorems/0c5f4872-f905-4cf7-93a9-d5aac642fa9b
-- title:
--   Bot Mul Vec Ext
-- statement:
--   Definitions and structural lemmas for Bot Mul Vec Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/BotMulVecExt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
def en {n : ℕ} (v : Fin n → ℂ) : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖
section Blocks
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def top (w : Fin r → ℂ) : Fin X.p0 → ℂ := fun a => w (Fin.castLE X.p0_le a)
def bot (w : Fin r → ℂ) : Fin (r - X.p0) → ℂ := fun m => w (nI X m)
def ext (d : Fin X.p0 → ℂ) : Fin r → ℂ := fun i => if h : (i : ℕ) < X.p0 then d ⟨i, h⟩ else 0
def blkA (K : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  Matrix.of fun a b => K (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le b)
def blkB (K : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
  Matrix.of fun m b => K (nI X m) (Fin.castLE X.p0_le b)
end Blocks
section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
end Frames
end
end UnipMove.GraphH
namespace UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
end UnipMove


