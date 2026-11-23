-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_HermLinApply
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_HermLinApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:26.732433+00:00
-- url     : https://prove2.me/theorems/794beee5-b9e8-4082-bf48-338d70bbdc09
-- title:
--   Herm Lin Apply
-- statement:
--   Definitions and structural lemmas for Herm Lin Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/HermLinApply.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace DeltaValuation
def linF {r : ℕ} (c : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ a, v a * c a
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k v := by simp [Finset.mul_sum, mul_assoc]
def hermLin {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (K : ℂ) (w : Fin r → ℂ) :
    (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := K * hermC τ G v w
  map_add' u v := by rw [hermC_add_left]; ring
  map_smul' k v := by rw [hermC_smul_left]; simp only [smul_eq_mul, RingHom.id_apply]; ring
end DeltaValuation
end
end UnipMove


