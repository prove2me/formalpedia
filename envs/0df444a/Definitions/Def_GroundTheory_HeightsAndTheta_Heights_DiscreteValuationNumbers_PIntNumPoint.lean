-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:17.603192+00:00
-- url     : https://prove2.me/theorems/2d9b3c24-653d-4069-9618-83658f410c02
-- title:
--   PInt Num Point
-- statement:
--   Definitions and structural lemmas for PInt Num Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
def chartMonomial (i : ∀ k, ι k) (e : K → ℕ) : MRing ι F :=
  ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ e k
def chartUnitIdeal (i : ∀ k, ι k) : Ideal (MRing ι F) :=
  Ideal.span (Set.range fun k => (X ⟨k, i k⟩ : MRing ι F) - 1)
section Dehom
variable (V : Ideal (MRing ι F)) [V.IsPrime]
def xc (p : Σ k, ι k) : FractionRing (MRing ι F ⧸ V) :=
  algebraMap (MRing ι F ⧸ V) _ (Ideal.Quotient.mk V (X p))
def cls : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ V) :=
  (IsScalarTower.toAlgHom F (MRing ι F ⧸ V) _).comp (Ideal.Quotient.mkₐ F V)
def dehom (i : ∀ k, ι k) : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ V) :=
  aeval fun p => xc V p / xc V ⟨p.1, i p.1⟩
variable {V}
variable (i : ∀ k, ι k) (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
include hi
end Dehom
end IntNumPoint
end
end GroundTheory.Heights₂.Heights.NumbersDVR


