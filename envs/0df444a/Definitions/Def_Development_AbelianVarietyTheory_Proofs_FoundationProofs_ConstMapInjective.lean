-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:24.698828+00:00
-- url     : https://prove2.me/theorems/88a6232d-5a04-4851-9290-d0eddd57fb97
-- title:
--   Const Map Injective
-- statement:
--   Definitions and structural lemmas for Const Map Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open Formalism.MainNotions.G MvPolynomial
noncomputable section
namespace GlobalTheory.PrescribedRank
variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
def noPlaces : Places p O Kf where
  w := 0
  nV := 0
  n' := fun _ => 0
  W := fun _ => O
  Qq := fun _ => Kf
  ι := fun _ => RingHom.id Kf
  σ := fun _ => RingEquiv.refl Kf
  j := fun _ => RingHom.id O
  setting := fun v => v.elim0
  m := 0
  r := 0
  lam0 := fun _ _ _ => 0
  dom := fun v => v.elim0
instance : IsEmpty (Fin (noPlaces p O Kf).nV) := inferInstanceAs (IsEmpty (Fin 0))
def trivLevel : Level (noPlaces p O Kf) where
  Γ := PUnit
  act := fun _ => 1
  χ := 1
def gat (d : ℕ) : GAtP p where
  O := O
  Kf := Kf
  P := noPlaces p O Kf
  comp := Fin d
  lev := fun _ => trivLevel p O Kf
  e := 0
def constMap (d : ℕ) : (Fin d → O) →ₗ[O] (Fin d → (noPlaces p O Kf).Tup → (noPlaces p O Kf).Xsp) where
  toFun c := fun i _ => c i • (1 : (noPlaces p O Kf).Xsp)
  map_add' a b := by
    funext i L
    simp [add_smul]
  map_smul' a b := by
    funext i L
    simp [mul_smul]
end GlobalTheory.PrescribedRank


