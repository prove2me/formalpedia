-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqOneOfSameClass
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqOneOfSameClass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:50.377659+00:00
-- url     : https://prove2.me/theorems/30a25812-9b5f-4596-9cce-8d758c590e9b
-- title:
--   Eq One Of Same Class
-- statement:
--   Definitions and structural lemmas for Eq One Of Same Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EqOneOfSameClass.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitaryRigid
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
def hf (v w : Fin n → E) : E := ∑ j, IsCMField.complexConj E (v j) * w j
def qf (v : Fin n → E) : ℝ := ∑ σ : E →ₐ[ℚ] ℂ, ∑ j, ‖σ (v j)‖ ^ 2
end GlobalTheory.UnitaryRigid


