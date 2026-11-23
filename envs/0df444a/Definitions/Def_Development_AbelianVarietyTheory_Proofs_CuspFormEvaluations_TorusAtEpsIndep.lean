-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:51.385883+00:00
-- url     : https://prove2.me/theorems/981a7210-a611-47bf-b8d2-8624f0614ba3
-- title:
--   Torus At Eps Indep
-- statement:
--   Definitions and structural lemmas for Torus At Eps Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TorusAtEpsIndep.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
namespace GlobalTheory.SemicharIndep
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
noncomputable def B (X : Data E r) (u v : Fin r → E) : ℚ :=
  Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v)
def Par (X : Data E r) (w : 𝓞 E) : Prop :=
  ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, B X u (((w : E) - cc (w : E)) • v) - B X u v = 2 * k
end GlobalTheory.SemicharIndep
namespace GlobalTheory
end GlobalTheory


