-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
-- name    : Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:26.655275+00:00
-- url     : https://prove2.me/theorems/900d62df-5e48-4477-aa91-3704cb3fbc38
-- title:
--   Data Form
-- statement:
--   Definitions and structural lemmas for Data Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
section Weyl
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
end Weyl
section Lat
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
end Lat
section Form
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (C : Level P)
variable (h0 : ∀ v, P.lam0 v = fun _ _ => 0)
open Classical in

def oneFn : P.Tup → P.Xsp := fun L => if P.IsLatTup L then 1 else 0
end Form
section Ex
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
end Ex
end Formalism.MainNotions.G.Inhab
end


