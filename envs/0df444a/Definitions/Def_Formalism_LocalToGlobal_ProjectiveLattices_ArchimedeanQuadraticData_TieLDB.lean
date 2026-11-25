-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:16:53.228861+00:00
-- url     : https://prove2.me/theorems/b7591677-2c4f-4521-a32a-25ca702b2214
-- title:
--   Tie LDB
-- statement:
--   Definitions and structural lemmas for Tie LDB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/TieLDB.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Pj.QAt.TieLDB
open Module
variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]
variable (H G : Submodule A V)
def inc : H →ₗ[A] Submodule.span (Localization.AtPrime p) (H : Set V) where
  toFun h := ⟨h, Submodule.subset_span h.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def locMap :
    H ⧸ G.comap H.subtype →ₗ[A] ↥(Submodule.span (Localization.AtPrime p) (H : Set V)) ⧸
      (Submodule.span (Localization.AtPrime p) (G : Set V)).comap
        (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype :=
  (G.comap H.subtype).liftQ
    (((((Submodule.span (Localization.AtPrime p) (G : Set V)).comap
      (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype).mkQ).restrictScalars A) ∘ₗ
        inc p H) (by
      intro h hh
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span hh)
end Formalism.L2.Pj.QAt.TieLDB


