-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:05.225898+00:00
-- url     : https://prove2.me/theorems/0c6da0f5-3f78-4e15-a3f4-0c526a9df3c8
-- title:
--   Real Pt Geo
-- statement:
--   Definitions and structural lemmas for Real Pt Geo, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RealPtGeo.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExtPtUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
def ModelAtSt (Xo : Moduli Dw l) (c : Coeff l) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L ∧
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
      ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β
end Formalism.L2.Pj


