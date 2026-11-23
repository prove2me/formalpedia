-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IdentityComponentOpen_d12b41cbe53351ef
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IdentityComponentOpen_d12b41cbe53351ef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:27.493453+00:00
-- url     : https://prove2.me/theorems/6c6de640-f5a7-49ba-bf30-ea2ccca116b5
-- title:
--   Identity Component Open
-- statement:
--   Definitions and structural lemmas for Identity Component Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IdentityComponentOpen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
namespace GlobalTheory.Published
def IdentityComponentOpen : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom →
    ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧
      ∀ x : G.left, x ∈ Set.range j.left ↔
        x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))
end GlobalTheory.Published


