-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_JTransMA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_JTransMA
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:06:10.732547+00:00
-- url     : https://prove2.me/theorems/2b6c8c06-9d3c-5505-8926-dc9de00f8a26
-- title:
--   JTrans MA
-- statement:
--   Definitions and structural lemmas for JTrans MA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/JTransMA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_TransposeUnitary
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Mult1
namespace TransM
variable {S : Type} [Fintype S] [DecidableEq S]
def cE (S : Type) [Fintype S] : EuclideanSpace ℂ S ≃ₗᵢ⋆[ℂ] EuclideanSpace ℂ S where
  toFun v := WithLp.toLp 2 (fun i => conj (v.ofLp i))
  invFun v := WithLp.toLp 2 (fun i => conj (v.ofLp i))
  map_add' u v := by ext i; simp
  map_smul' a v := by ext i; simp
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp
  norm_map' v := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
abbrev TE (S : Type) [Fintype S] [DecidableEq S] :
    Matrix S S ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :=
  Matrix.toEuclideanCLM (n := S) (𝕜 := ℂ)
end TransM
end ReciprocityTheory.ChartRestriction.DS.Mult1


