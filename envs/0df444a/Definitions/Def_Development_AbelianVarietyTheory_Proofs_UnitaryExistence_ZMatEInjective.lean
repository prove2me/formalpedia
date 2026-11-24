-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZMatEInjective
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZMatEInjective
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T19:22:53.719011+00:00
-- url     : https://prove2.me/theorems/eb78e7e2-6c65-419d-852a-d2ad2db946b0
-- title:
--   ZMat EInjective
-- statement:
--   Definitions and structural lemmas for ZMat EInjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ZMatEInjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q


set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
namespace GlobalTheory.CuspCentre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
theorem cc_add' (x y : E) : cc (x + y) = cc x + cc y := by simp [cc]
theorem cc_neg' (x : E) : cc (-x) = -cc x := by simp [cc]
theorem cc_zero' : cc (0 : E) = 0 := by simp [cc]
theorem herm_add_l (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]
theorem herm_comb_l (G : Matrix (Fin r) (Fin r) E) (c : Fin ρ → E) (e : Fin ρ → Fin r → E)
    (y : Fin r → E) : herm G (∑ a, c a • e a) y = ∑ a, c a * herm G (e a) y := by
  simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring
theorem zMatE_mulVec (X : Data E r) (e : Fin ρ → Fin r → E) (β : Matrix (Fin ρ) (Fin ρ) E)
    (v : Fin r → E) :
    FJ.zMatE X e β *ᵥ v = v + ∑ a, (∑ b, β a b * herm X.Gm v (e b)) • e a := by
  funext k
  simp only [FJ.zMatE, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun m _ => ?_
  ring
theorem zMatE_zero (X : Data E r) (e : Fin ρ → Fin r → E) : FJ.zMatE X e 0 = 1 := by
  ext k l
  simp [FJ.zMatE, Matrix.one_apply]
theorem zMatE_add (X : Data E r) (cu : FJ.CuspFD X ρ) (β β' : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.zMatE X cu.e (β + β') = FJ.zMatE X cu.e β * FJ.zMatE X cu.e β' := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec]
  simp only [zMatE_mulVec, herm_add_l, herm_comb_l, cu.iso, mul_zero, Finset.sum_const_zero,
    add_zero, Matrix.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
  abel
def zGamSub (X : Data E r) (cu : FJ.CuspFD X ρ) : AddSubgroup (Matrix (Fin ρ) (Fin ρ) E) where
  carrier := FJ.zGam X cu
  zero_mem' := ⟨fun a b => by simp [cc_zero'], 1, X.Γ.one_mem, by simp [zMatE_zero]⟩
  add_mem' := by
    rintro β β' ⟨h, γ, hγ, e⟩ ⟨h', γ', hγ', e'⟩
    refine ⟨fun a b => ?_, γ * γ', X.Γ.mul_mem hγ hγ', ?_⟩
    · rw [Matrix.add_apply, Matrix.add_apply, cc_add', h, h']; ring
    · rw [zMatE_add, ← e, ← e', Units.val_mul]
  neg_mem' := by
    rintro β ⟨h, γ, hγ, e⟩
    refine ⟨fun a b => ?_, γ⁻¹, X.Γ.inv_mem hγ, ?_⟩
    · rw [Matrix.neg_apply, Matrix.neg_apply, cc_neg', h]
    · refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [e, ← zMatE_add, add_neg_cancel, zMatE_zero]
end GlobalTheory.CuspCentre


