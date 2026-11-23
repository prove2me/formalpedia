-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_RankEqRankOfPermAndZero
-- name    : ReciprocityTheory_DualLattices_RankEqRankOfPermAndZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:57.317579+00:00
-- url     : https://prove2.me/theorems/5728ac44-15e3-4f9e-a8a0-a7fe7683b229
-- title:
--   Rank Eq Rank Of Perm And Zero
-- statement:
--   Definitions and structural lemmas for Rank Eq Rank Of Perm And Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RankEqRankOfPermAndZero.lean

import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroupStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_RankMapLeRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section Rank
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
section Local
variable [IsLocalRing R]
end Local
end Rank
end ReciprocityTheory.PGsh.Up


