-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:54.950806+00:00
-- url     : https://prove2.me/theorems/92f25993-15ae-46d1-93ea-9659c3f72dcc
-- title:
--   Fn Trdeg Of
-- statement:
--   Definitions and structural lemmas for Fn Trdeg Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FnTrdegOf.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
def KapFG : Prop := ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (kap Z)).FG
def KapTrdeg (d : ℕ) : Prop := ∀ Z : Comp Xo c, Algebra.trdeg c.F (kap Z) = d
end Formalism.L2.Pj
end


