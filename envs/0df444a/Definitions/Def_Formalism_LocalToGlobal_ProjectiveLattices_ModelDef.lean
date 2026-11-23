-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ModelDef
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ModelDef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:44.13283+00:00
-- url     : https://prove2.me/theorems/662b3652-ced2-4113-a0cc-ef6f454369f7
-- title:
--   Model Def
-- statement:
--   Definitions and structural lemmas for Model Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ModelDef.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
def AbelianAtQZero (D : Datum H) : Prop :=
  D.q = 0 → ∀ (Xo : ∀ l : Level H, Moduli D l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W),
    N2 Y → ∀ i : Idx H p, abLocus (Y i).t.G = Set.univ
end Formalism.L2.Pj


