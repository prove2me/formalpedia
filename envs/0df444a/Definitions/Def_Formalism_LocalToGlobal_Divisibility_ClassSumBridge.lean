-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
-- name    : Formalism_LocalToGlobal_Divisibility_ClassSumBridge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:47.55788+00:00
-- url     : https://prove2.me/theorems/dc3ab3f4-a79d-452a-a915-3776fba5eb98
-- title:
--   Class Sum Bridge
-- statement:
--   Definitions and structural lemmas for Class Sum Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumBridge.lean

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
def pairOne (K : Type) [Field K] [StarRing K] : K →ₗ⋆[K] K →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
    (by intro x y z; simp [add_mul]) (by intro a x y; simp [mul_assoc, starRingEnd_apply])
    (by intro x y z; simp [mul_add]) (by intro a x y; simp [mul_left_comm])
def one (K : Type) [Field K] [NumberField K] [StarRing K] : CSD K where
  Cl := Unit
  V := K
  ιV := Unit
  bV := Basis.singleton Unit K
  pair := pairOne K
  Gam := fun _ => Unit
  grpGam := fun _ => inferInstance
  ρ := fun _ => 1
  Nab := fun _ => 1
  Del := fun _ => 1
end Formalism.L2.DIV.CSD


