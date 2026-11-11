-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T04:49:28.682244+00:00
-- url     : https://prove2.me/theorems/d2665dec-c3ef-436f-af42-526fa148ce4e
-- title:
--   Keyed Geometric Legacy
-- statement:
--   Definitions and structural lemmas for Keyed Geometric Legacy, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricLegacy.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleKey_injective
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
namespace QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
theorem legacy_eligible_iff (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (s : Finset (Triangle P)) :
    KeyEligible P (triangleKey P) (triangleKey_injective P) J r s ↔ Eligible P J r s := Iff.rfl
def legacyEventEquiv (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ) :
    KeyEvent P (triangleKey P) (triangleKey_injective P) J r ≃ Event P J r where
  toFun e := ⟨e.val,(legacy_eligible_iff P J r e.val).mp e.property⟩
  invFun e := ⟨e.val,(legacy_eligible_iff P J r e.val).mpr e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
def legacySupportEquiv (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    keySupport P (triangleKey P) (triangleKey_injective P) J r e ≃
      eventSupport P J r (legacyEventEquiv P J r e) where
  toFun v := ⟨v.val,v.property⟩
  invFun v := ⟨v.val,v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
def legacyAssignmentEquiv (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    (keySupport P (triangleKey P) (triangleKey_injective P) J r e → Space) ≃
      (eventSupport P J r (legacyEventEquiv P J r e) → Space) where
  toFun w v := w ((legacySupportEquiv P J r e).symm v)
  invFun w v := w (legacySupportEquiv P J r e v)
  left_inv w := by funext v; rfl
  right_inv w := by funext v; rfl
end QEC.Coding.BDL26KeyedGeometric


