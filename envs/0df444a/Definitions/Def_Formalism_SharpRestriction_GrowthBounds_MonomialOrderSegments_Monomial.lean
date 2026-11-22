-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:42:58.857841+00:00
-- url     : https://prove2.me/theorems/80c2ccee-a277-46e9-8d33-6001ee09c171
-- title:
--   Monomial
-- statement:
--   Definitions and structural lemmas for Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/Monomial.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
namespace TwistData
variable {K : Type} [Field K] (D : TwistData K)
def varE (p : ℕ) (x : D.ML × Fin D.r) : D.EA :=
  Sum.elim (fun b => Finsupp.single (Sum.inl b, x.2) 1)
    (Sum.elim (fun t => Finsupp.single (Sum.inr t, x.2) 1)
      (Sum.elim (fun t => Finsupp.single (Sum.inr t, x.2) (D.P p t))
        (fun t => Finsupp.single (Sum.inr t, x.2) 1))) x.1
end TwistData
end Formalism.MainNotions.PlaneGram


