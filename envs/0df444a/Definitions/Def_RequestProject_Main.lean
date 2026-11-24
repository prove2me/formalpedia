-- Prove2me | Definitions.Def_RequestProject_Main
-- name    : RequestProject_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T23:51:56.465364+00:00
-- url     : https://prove2.me/theorems/03474dfd-e1cc-497b-b8cd-98b2eaaa9a97
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Main.lean

import Definitions.Def_RequestProject_Aqt_Algebra
import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_ThetaDescent
import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
import Theorems.Thm_DyckAlgebra_DyckRepU_sStar_acts_as_0
import Theorems.Thm_DyckAlgebra_DyckRepU_thetaDOneWord_eq_series
import Theorems.Thm_DyckAlgebra_DyckRepU_thetaE1Word_eq
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_Q2
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_preserve_I1_via_sStar
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_preserve_I2_qpow_via_sStar
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_y1_dps
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_z1_dp

set_option autoImplicit true
namespace DyckAlgebra
example (𝕜 : Type*) [Field 𝕜] (q cQ2 : 𝕜) : Type _ := Aqt q cQ2
example {𝕜 : Type*} [Field 𝕜] {q t : 𝕜} (ρ : AqtAction 𝕜 q t) :
    Aqt q t →ₐ[𝕜] Module.End 𝕜 ρ.carrier := ρ.act
example {𝕜 C : Type*} [Field 𝕜] [Ring C] [Algebra 𝕜 C] {q t : 𝕜}
    (f : Gen → C)
    (hf : ∀ ⦃a b : Pre 𝕜⦄, Rel q t a b → thetaPre f a = thetaPre f b) :
    Aqt q t →ₐ[𝕜] C := thetaDescent f hf
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2) :
    ρ.Θz1 * ρ.Θdp = cQ2 • (ρ.Θy1 * ρ.Θdps) := ρ.theta_Q2
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2) :
    ρ.Θz1 * ρ.Θdp = ρ.w 1 * ρ.zz 1 * ρ.dp ∧
      ρ.Θy1 * ρ.Θdps = ρ.w 1 * ρ.yy 1 * ρ.dps :=
  ⟨ρ.theta_z1_dp, ρ.theta_y1_dps⟩
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2) :
    ρ.thetaDOneWord = ρ.dPositiveSeries :=
  ρ.thetaDOneWord_eq_series
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
    (hlevel : ρ.level = 0) :
    ρ.thetaE1Word = ρ.e1Word + (ρ.dPositiveSeries - ρ.dOneWord) :=
  ρ.thetaE1Word_eq hlevel
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
    (k : ℕ) (hk : 1 ≤ k) (e0 : ρ.carrier) (hq : q ≠ 0)
    (hI2 : ρ.yy 1 * ρ.dps ^ k * e0 =
      (-(q ^ k)⁻¹) • (ρ.dp * ρ.dps ^ (k - 1) * e0))
    (hQ2 : ρ.zz 1 * (ρ.dp * ρ.dps ^ (k - 1) * e0) =
      (-(q ^ k)) • (ρ.yy 1 * ρ.dps ^ k * e0)) :
    ρ.sStarElt * ρ.dps ^ k * e0 = 0 :=
  ρ.sStar_acts_as_0 k hk e0 hq hI2 hQ2
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2) (k : ℕ)
    (e0 : ρ.carrier)
    (hs : ∀ j, 1 ≤ j → ρ.sStarElt * ρ.dps ^ j * e0 = 0)
    (hI1 : (ρ.dm * ρ.dps - 1) * ρ.dps ^ k * e0 = 0) :
    (ρ.dm * ρ.Θdps - 1) * ρ.Θdps ^ k * e0 = 0 :=
  ρ.theta_preserve_I1_via_sStar k e0 hs hI1
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2) (k : ℕ)
    (e0 : ρ.carrier) (hcQ2 : cQ2 = -(q ^ k))
    (hs : ∀ j, 1 ≤ j → ρ.sStarElt * ρ.dps ^ j * e0 = 0)
    (hI2 : (ρ.dp + (q ^ k) • (ρ.yy 1 * ρ.dps)) * ρ.dps ^ k * e0 = 0) :
    (ρ.Θdp + (q ^ k) • (ρ.Θy1 * ρ.Θdps)) * ρ.Θdps ^ k * e0 = 0 :=
  ρ.theta_preserve_I2_qpow_via_sStar k e0 hcQ2 hs hI2
end DyckAlgebra


