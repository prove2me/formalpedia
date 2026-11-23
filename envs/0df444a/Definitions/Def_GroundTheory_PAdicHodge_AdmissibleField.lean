-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField
-- name    : GroundTheory_PAdicHodge_AdmissibleField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:58.917409+00:00
-- url     : https://prove2.me/theorems/0cef60a7-b84c-487d-af08-c2ee09bf7fe0
-- title:
--   Admissible Field
-- statement:
--   Definitions and structural lemmas for Admissible Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open TensorProduct Module
section Field
variable (G F B : Type*) [Group G] [Field F] [Field B] [Algebra F B] [MulSemiringAction G B]
end Field
section Coeff
variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
def DBK : Submodule K (B ⊗[F] V) where
  carrier := {x | ∀ g : G, baseChangeRep B ρ g x = x}
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  zero_mem' g := map_zero _
  smul_mem' k x hx g := by
    change baseChangeRep B ρ g (k • x) = k • x
    rw [← algebraMap_smul B k x, baseChangeRep_smul, hx g, smul_algebraMap]
def toInvariantRing : K →+* invariantRing G F B where
  toFun k := ⟨algebraMap K B k, fun g => smul_algebraMap g k⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)
variable {G F K B}
variable [IsDomain B]
end Coeff
end GroundTheory.PAdicHodge


