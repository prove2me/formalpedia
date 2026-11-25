-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ArcLineFunctions_ValLine
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ArcLineFunctions_ValLine
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:18:49.514409+00:00
-- url     : https://prove2.me/theorems/ec8b839b-736a-4fb0-af47-dc545786dae8
-- title:
--   Val Line
-- statement:
--   Definitions and structural lemmas for Val Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/ArcLineFunctions/ValLine.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Pj.QAt
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
def lineVal (n : ℕ) (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (μ : ArcLt Dw →₀ ℕ) : ℤ :=
  -((n : ℤ) * vth) - ∑ x ∈ μ.support, (μ x : ℤ) * vη x.1 x.2.2
end Formalism.L2.Pj.QAt


