-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:59.982456+00:00
-- url     : https://prove2.me/theorems/b6becfaf-d437-4b07-9d44-bbc51b54b730
-- title:
--   Unit Indep Of Charts
-- statement:
--   Definitions and structural lemmas for Unit Indep Of Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnitIndepOfCharts.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD
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
section Clauses
variable (Xo : Moduli Dw l) (c : Coeff l)
def FrChartF : Prop :=
  FrChart (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
def BorChartF : Prop :=
  BorChart (K := c.F) (ι := Ix Dw) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
end Clauses
section Proofs
variable {Xo : Moduli Dw l} {c : Coeff l}
end Proofs
end Formalism.L2.Pj


