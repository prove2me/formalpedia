-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:38.801253+00:00
-- url     : https://prove2.me/theorems/b47dd527-d6ca-4012-8fd6-9675cdb3f1b6
-- title:
--   PPlucker Cover
-- statement:
--   Definitions and structural lemmas for PPlucker Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace PluckerAffineCover
section Wedge
variable {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E]
end Wedge
section Chart
variable {Ω : Type} [Field Ω] {ι : Type} (x : ι → Ω) (i : ι)
variable {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
end Chart
section Bundle
variable {D : ℕ} (S : ProjectiveLineBundle D)
abbrev wt : (Σ k, S.YIdx k) → (T.YBlk → ℕ) := fun q => Pi.single q.1 1
abbrev yyc : (Σ k, S.YIdx k) → S.Φ := T.yyCoord S.x S.δ S.e S.φ (S.a 0)
def blk0 : T.YBlk → T.WBlk
  | .base => .base
  | .det => .det
  | .line => .line0
def Good (r : MRing S.YIdx) : Prop :=
  ∃ b : T.YBlk → ℕ, IsMultiHomog r b ∧ b .line = 0 ∧ rename (T.yyEmb 0) r ∈ S.WW
end Bundle
section Local
variable {D : ℕ} (S : ProjectiveLineBundle D)
end Local
end PluckerAffineCover
end
end GroundTheory.Heights₂.Heights.Inter


