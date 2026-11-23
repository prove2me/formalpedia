-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:04.357492+00:00
-- url     : https://prove2.me/theorems/b6dcec40-e7b2-479c-84ad-650bd71674b4
-- title:
--   Perp Basis Existence
-- statement:
--   Definitions and structural lemmas for Perp Basis Existence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpBasisExistence.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalComplementLines
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_smul_mem__5cba0dccb7e4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_integer_smul_eq_coe_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def hxi (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : (Fin r → E) →ₗ[E] E where
  toFun x := herm G x ξ
  map_add' x y := HermitianTraceFormVanishing.herm_add_left G x y ξ
  map_smul' a x := HermitianTraceFormVanishing.herm_smul_left G a x ξ
variable (X : DataX E r)
def LBsub {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {c | ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L'}
  add_mem' := by
    rintro c c' ⟨e, he⟩ ⟨e', he'⟩
    refine ⟨e + e', ?_⟩
    have h : ∑ k, (c + c') k • β k + (e + e') • ξ =
        (∑ k, c k • β k + e • ξ) + (∑ k, c' k • β k + e' • ξ) := by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      abel
    rw [h]
    exact X.L'.add_mem he he'
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a c ⟨e, he⟩
    refine ⟨(a : E) * e, ?_⟩
    have h : ∑ k, (a • c) k • β k + ((a : E) * e) • ξ = a • (∑ k, c k • β k + e • ξ) := by
      rw [integer_smul_eq_coe_smul a c, integer_smul_eq_coe_smul a (∑ k, c k • β k + e • ξ)]
      simp only [Pi.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum, mul_smul]
    rw [h]
    exact X.L'.smul_mem a he
end
end ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence


