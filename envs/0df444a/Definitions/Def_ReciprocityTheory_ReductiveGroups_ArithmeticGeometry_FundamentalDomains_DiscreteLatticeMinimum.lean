-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:02:31.380914+00:00
-- url     : https://prove2.me/theorems/30e3d60b-fd45-4bf3-a597-fa01c461ab1b
-- title:
--   Discrete Lattice Minimum
-- statement:
--   Definitions and structural lemmas for Discrete Lattice Minimum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscreteLatticeMinimum.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_Bop_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_Bop_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_Bop_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_gI_Bop_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_VT_val_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_inner_eq
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
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace DiscreteLatticeMinimum
open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Y : DataX E r}
  (z : Frame Y.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ Y.dom)]
noncomputable def Bmap : VT (X := Y.toData) z ξ →ₗ[ℝ] VT (X := Y.toData) z ξ where
  toFun u := VT.mk (MajorantOperators.Bop z u.val) (MajorantOperators.Bop_mem hz.out u.val_mem)
  map_add' u v := VT.ext (by simp [MajorantOperators.Bop_add])
  map_smul' c u := VT.ext (by simp [MajorantOperators.Bop_smul])
theorem Bmap_val (u : VT (X := Y.toData) z ξ) : (Bmap z ξ u).val = MajorantOperators.Bop z u.val := rfl
theorem norm_Bmap (u : VT (X := Y.toData) z ξ) : ‖Bmap z ξ u‖ = Y.k0 * ‖u‖ := by
  have h : ‖Bmap z ξ u‖ ^ 2 = (Y.k0 * ‖u‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, mul_pow, ← real_inner_self_eq_norm_sq, inner_eq, inner_eq,
      Bmap_val, MajorantOperators.gI_Bop_self hz.out]
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg Y.minWeight_pos.le (norm_nonneg _))
    two_ne_zero).1 h
theorem Bmap_injective : Function.Injective (Bmap z ξ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h := norm_Bmap z ξ u
  rw [hu, norm_zero] at h
  have h2 : ‖u‖ = 0 := by
    rcases mul_eq_zero.1 h.symm with h3 | h3
    · exact absurd h3 Y.minWeight_pos.ne'
    · exact h3
  exact norm_eq_zero.1 h2
noncomputable def Bequiv : VT (X := Y.toData) z ξ ≃ₗ[ℝ] VT (X := Y.toData) z ξ :=
  LinearEquiv.ofBijective (Bmap z ξ) ⟨Bmap_injective z ξ,
    LinearMap.surjective_of_injective (Bmap_injective z ξ)⟩
variable {ξ} (hξ : Y.IsIso ξ)
section lattice
variable (ep0 : ℝ) (hns : ∀ x ∈ Y.L', herm Y.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : Y.Ψ, ep0 ≤ Y.maj z τ (Y.ucomp z ξ (Y.embV x) τ))
end lattice
end DiscreteLatticeMinimum
end ReciprocityTheory.ChartRestriction.G.FD


