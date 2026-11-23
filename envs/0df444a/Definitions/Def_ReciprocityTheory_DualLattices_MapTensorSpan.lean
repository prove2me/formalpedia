-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan
-- name    : ReciprocityTheory_DualLattices_MapTensorSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:16.84832+00:00
-- url     : https://prove2.me/theorems/d0a7105f-9c6b-4702-868f-502c8c469353
-- title:
--   Map Tensor Span
-- statement:
--   Definitions and structural lemmas for Map Tensor Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MapTensorSpan.lean

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
def slice2 {X : Type} (E : (X → C) →ₗ[C] (X → C)) : (X × X → C) →ₗ[C] (X × X → C) where
  toFun F p := E (fun a => E (fun b => F (a, b)) p.2) p.1
  map_add' F G := by
    funext p
    have h2 : (fun a => E (fun b => (F + G) (a, b)) p.2) =
        (fun a => E (fun b => F (a, b)) p.2) + (fun a => E (fun b => G (a, b)) p.2) := by
      funext a
      rw [show (fun b => (F + G) (a, b)) = (fun b => F (a, b)) + (fun b => G (a, b)) from rfl,
        map_add]
      rfl
    show E (fun a => E (fun b => (F + G) (a, b)) p.2) p.1 =
      E (fun a => E (fun b => F (a, b)) p.2) p.1 + E (fun a => E (fun b => G (a, b)) p.2) p.1
    rw [h2, map_add]
    rfl
  map_smul' c F := by
    funext p
    have h2 : (fun a => E (fun b => (c • F) (a, b)) p.2) =
        c • (fun a => E (fun b => F (a, b)) p.2) := by
      funext a
      rw [show (fun b => (c • F) (a, b)) = c • (fun b => F (a, b)) from rfl, map_smul]
      rfl
    show E (fun a => E (fun b => (c • F) (a, b)) p.2) p.1 =
      c • E (fun a => E (fun b => F (a, b)) p.2) p.1
    rw [h2, map_smul]
    rfl
end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice


