-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:34:36.454859+00:00
-- url     : https://prove2.me/theorems/da517657-cbe6-5cb8-bc61-cfc5e0c4d39c
-- title:
--   Tate Basis Matrix
-- statement:
--   Definitions and structural lemmas for Tate Basis Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TateBasisMatrix.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
section
variable {p : ℕ} [hp : Fact p.Prime] {κ Γ : Type} [Fintype κ] [AddCommGroup Γ] {τ : κ → ℕ → Γ}
end
end GlobalTheory


