-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
-- name    : GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:48.6578+00:00
-- url     : https://prove2.me/theorems/c5ea000a-9715-4bf7-b7bb-b65b6d90f4c8
-- title:
--   Modules Pullback
-- statement:
--   Definitions and structural lemmas for Modules Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/ModulesPullback.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
variable {T U W : Scheme.{u}}
noncomputable def pullbackSection (g : T ⟶ U) (N : U.Modules) :
    Γ(N, ⊤) →+ Γ((Scheme.Modules.pullback g).obj N, ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app ⊤).hom
end GroundTheory.Arith.Etale


