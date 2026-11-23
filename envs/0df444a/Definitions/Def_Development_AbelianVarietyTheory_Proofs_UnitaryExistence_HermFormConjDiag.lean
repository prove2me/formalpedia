-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:51.761997+00:00
-- url     : https://prove2.me/theorems/5e49a95c-3014-4774-aea1-aca5d8901742
-- title:
--   Herm Form Conj Diag
-- statement:
--   Definitions and structural lemmas for Herm Form Conj Diag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply


set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def locPer (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) :
    (Fin r → ℂ) →ₗ[ℝ] (Fin r → ℂ) where
  toFun u a := if (a : ℕ) < q then FD.hermC τ Gm (FD.col M a) u else (M⁻¹ *ᵥ u) a
  map_add' u w := by
    funext a
    simp only [Pi.add_apply, FD.hermC_add_right, mulVec_add]
    split_ifs <;> rfl
  map_smul' t u := by
    funext a
    have : t • u = (t : ℂ) • u := by funext k; simp
    rw [this]
    simp only [FD.hermC_smul_right, mulVec_smul, Pi.smul_apply, RingHom.id_apply, Complex.conj_ofReal,
      smul_eq_mul, Complex.real_smul]
    split_ifs <;> rfl
def allPer {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (x : FD.Frame Ψ r) {g : ℕ}
    (idx : Fin g ≃ Ψ × Fin r) : (Ψ → Fin r → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun y k := locPer (idx k).1.1 Gm q (FD.mat x (idx k).1) (y (idx k).1) (idx k).2
  map_add' u w := by funext k; simp
  map_smul' t u := by funext k; simp
end
end GlobalTheory.FramePeriod


