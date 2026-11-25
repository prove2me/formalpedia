-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLattice
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLattice
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:55:02.839813+00:00
-- url     : https://prove2.me/theorems/697016e2-bdfd-4bd2-ac2c-2eddbfafe904
-- title:
--   Quasi Reflection Stabilizes Lattice
-- statement:
--   Definitions and structural lemmas for Quasi Reflection Stabilizes Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/QuasiReflectionStabilizesLattice.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.QRefl
section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
def conjLin (c : (Fin n → E) →+ (Fin n → E)) (hs : ∀ t v, c (t • v) = L.cj t • c v)
    (hc : ∀ v, c (c v) = v) (h : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    (Fin n → E) ≃ₗ[E] (Fin n → E) where
  toFun v := c (h (c v))
  invFun v := c (h.symm (c v))
  map_add' u v := by simp only [map_add]
  map_smul' t v := by simp only [hs, map_smul, L.cj_cj, RingHom.id_apply]
  left_inv v := by simp only [hc, LinearEquiv.symm_apply_apply]
  right_inv v := by simp only [hc, LinearEquiv.apply_symm_apply]
def conjAut (c : (Fin n → E) →+ (Fin n → E)) (hs : ∀ t v, c (t • v) = L.cj t • c v)
    (hc : ∀ v, c (c v) = v) :
    ((Fin n → E) ≃ₗ[E] (Fin n → E)) ≃* ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  toFun := conjLin L c hs hc
  invFun := conjLin L c hs hc
  left_inv h := by
    ext1 v
    show c (c (h (c (c v)))) = h v
    rw [hc, hc]
  right_inv h := by
    ext1 v
    show c (c (h (c (c v)))) = h v
    rw [hc, hc]
  map_mul' h k := by
    ext1 v
    show c (h (k (c v))) = c (h (c (c (k (c v)))))
    rw [hc]
end
end GlobalTheory.QRefl


