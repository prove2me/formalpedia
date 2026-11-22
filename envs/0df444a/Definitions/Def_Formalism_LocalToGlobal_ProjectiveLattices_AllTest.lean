-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_AllTest
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:52:35.301199+00:00
-- url     : https://prove2.me/theorems/10adef71-8f1c-4c79-80aa-16ae90c630ae
-- title:
--   All Test
-- statement:
--   Definitions and structural lemmas for All Test, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AllTest.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
def AllTest : Prop :=
  ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
end Formalism.L2.Pj


