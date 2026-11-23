-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:59.073563+00:00
-- url     : https://prove2.me/theorems/bcee954d-a855-4c65-80b6-2333da5c69a8
-- title:
--   Commute Row Op Right Mixed Op
-- statement:
--   Definitions and structural lemmas for Commute Row Op Right Mixed Op, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
noncomputable def polar (K : Type*) [CommRing K] (u v : σ) : Module.End K (MvPolynomial σ K) :=
  (LinearMap.mulLeft K (X u : MvPolynomial σ K)) ∘ₗ (pderiv v).toLinearMap
section Ops
variable {I J I' J' : Type*}
noncomputable def colOp (K : Type*) [CommRing K] [Fintype I] (z : I × J → σ) (k l : J) :
    Module.End K (MvPolynomial σ K) :=
  ∑ a, polar K (z (a, k)) (z (a, l))
noncomputable def rowOp (K : Type*) [CommRing K] [Fintype J] (z : I × J → σ) (a b : I) :
    Module.End K (MvPolynomial σ K) :=
  ∑ k, polar K (z (a, k)) (z (b, k))
noncomputable def mixedOp (K : Type*) [CommRing K] [Fintype I] [Fintype I'] (z : I × J → σ)
    (y : I' × J → σ) (k l : J) : Module.End K (MvPolynomial σ K) :=
  colOp K z k l - colOp K y l k
end Ops
end GlobalTheory.Capelli
namespace GlobalTheory
open Capelli
namespace Capelli
variable {K σ : Type*} [CommRing K] {p q n : ℕ}
end Capelli
end GlobalTheory


