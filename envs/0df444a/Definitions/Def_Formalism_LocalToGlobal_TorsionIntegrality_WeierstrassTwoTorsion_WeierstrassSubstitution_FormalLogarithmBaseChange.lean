-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalLogarithmBaseChange
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalLogarithmBaseChange
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:33:49.168478+00:00
-- url     : https://prove2.me/theorems/93710d27-fb45-48fd-95e2-a60634082cc4
-- title:
--   Formal Logarithm Base Change
-- statement:
--   Definitions and structural lemmas for Formal Logarithm Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalLogarithmBaseChange.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv
import Theorems.Thm_Formalism_ELL_WeierstrassSubstitution_mvsubst_psubst
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_cThree_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_L
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_WK
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_eq
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_univ
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_uThird_L
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_uThird_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wThird_eq
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Univ_map_eq
import Theorems.Thm_Formalism_L2_Th1_A_Univ_mv_map_injective
import Theorems.Thm_Formalism_L2_Th1_A_chartFlowNegation
import Theorems.Thm_Formalism_L2_Th1_A_composition_inverse_spec
import Theorems.Thm_Formalism_L2_Th1_A_expSpec_of
import Theorems.Thm_Formalism_L2_Th1_A_flowThirdPoint
import Theorems.Thm_Formalism_L2_Th1_A_formal_group_chord
import Theorems.Thm_Formalism_L2_Th1_A_iSerSpec_of
import Theorems.Thm_Formalism_L2_Th1_A_integration_spec
import Theorems.Thm_Formalism_L2_Th1_A_invariant_differential_units
import Theorems.Thm_Formalism_L2_Th1_A_logSpec_of
import Theorems.Thm_Formalism_L2_Th1_A_series_map
import Theorems.Thm_Formalism_L2_Th1_A_unit_flow
import Theorems.Thm_Formalism_L2_Th1_A_w_series_factorization
import Theorems.Thm_Formalism_L2_Th1_A_w_series_spec
import Theorems.Thm_P2M_Formalism_L2_Th1_A_Univ___injective_04fee711be81
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply


set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
namespace Formalism.L2.Th1.A
namespace Fgl2
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
section Subst
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
abbrev curveM : WeierstrassCurve (MvPowerSeries (Fin 2) R) :=
  W.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin 2) R)
theorem fw_subst {s : MvPowerSeries (Fin 2) R} (hs : cc s = 0) :
    (fw W).subst s = fwAt (curveM W) s ((wSer W).subst s) := by
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have hC : ∀ a : R, (PowerSeries.C a).subst s = MvPowerSeries.C a := fun a => by
    rw [← PowerSeries.coe_substAlgHom hs']
    exact (PowerSeries.substAlgHom hs').commutes a
  rw [← PowerSeries.coe_substAlgHom hs']
  simp only [fw, fu, fwAt, fuAt, map_sub, map_mul, map_add, map_pow, map_ofNat, map_one]
  rw [PowerSeries.coe_substAlgHom hs']
  simp only [hC, PowerSeries.subst_X hs', WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  try ring
theorem fu_subst {s : MvPowerSeries (Fin 2) R} (hs : cc s = 0) :
    (fu W).subst s = fuAt (curveM W) s ((wSer W).subst s) := by
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have hC : ∀ a : R, (PowerSeries.C a).subst s = MvPowerSeries.C a := fun a => by
    rw [← PowerSeries.coe_substAlgHom hs']
    exact (PowerSeries.substAlgHom hs').commutes a
  rw [← PowerSeries.coe_substAlgHom hs']
  simp only [fw, fu, fwAt, fuAt, map_sub, map_mul, map_add, map_pow, map_ofNat, map_one]
  rw [PowerSeries.coe_substAlgHom hs']
  simp only [hC, PowerSeries.subst_X hs', WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  try ring
theorem weq_subst {s : MvPowerSeries (Fin 2) R} (hs : cc s = 0) :
    WEq (curveM W) s ((wSer W).subst s) := by
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have hC : ∀ a : R, (PowerSeries.C a).subst s = MvPowerSeries.C a := fun a => by
    rw [← PowerSeries.coe_substAlgHom hs']
    exact (PowerSeries.substAlgHom hs').commutes a
  have h := (unit_flow R W).2.2.1.1
  unfold WEq at h ⊢
  have h2 := congrArg (PowerSeries.substAlgHom (R := R) hs') h
  simp only [map_sub, map_mul, map_add, map_pow, map_ofNat, map_one] at h2
  rw [PowerSeries.coe_substAlgHom hs'] at h2
  simp only [hC, PowerSeries.subst_X hs', WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h2 ⊢
  exact h2
def Dm (i : Fin 2) (a : MvPowerSeries (Fin 2) R) : MvPowerSeries (Fin 2) R :=
  (fw W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) * MvPowerSeries.pderiv R i a
theorem isDer_Dm (i : Fin 2) : IsDer (Dm W i) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · unfold Dm
    rw [map_add, mul_add]
  · unfold Dm
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
theorem const_Dm (i : Fin 2) : ConstCurve (Dm W i) (curveM W) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold Dm
    simp [MvPowerSeries.pderiv_C]
theorem Dm_subst (i : Fin 2) {s : MvPowerSeries (Fin 2) R} (hs : cc s = 0) (f : R⟦X⟧) :
    Dm W i (f.subst s) = (derivative R f).subst s * Dm W i s := by
  unfold Dm
  rw [Formalism.G.LogCR.pderiv_psubst hs]
  ring
theorem flow_Dm (i : Fin 2) : IsFlowUW (curveM W) (Dm W i) (MvPowerSeries.X i) (Fgl1.Wi W i) := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) = 0 :=
    MvPowerSeries.constantCoeff_X i
  have hF := unit_flow R W
  have hDX : Dm W i (MvPowerSeries.X i) = (fw W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) := by
    unfold Dm
    rw [MvPowerSeries.pderiv_X_self, mul_one]
  refine ⟨weq_subst W hX, ?_, ?_⟩
  · rw [hDX, fw_subst W hX]
  · rw [Dm_subst W i hX, ← fu_subst W hX, hDX]
    have h3 : fw W * derivative R (wSer W) = fu W := by
      have h4 := hF.2.2.1.2.2
      rw [hF.2.2.2.2.1] at h4
      simpa only [D, Derivation.smul_apply, smul_eq_mul] using h4
    have hs' := PowerSeries.HasSubst.of_constantCoeff_zero hX
    rw [← h3, ← PowerSeries.coe_substAlgHom (R := R) hs', map_mul, mul_comm]
theorem Dm_X_of_ne {i j : Fin 2} (h : j ≠ i) : Dm W i (MvPowerSeries.X j) = 0 := by
  unfold Dm
  rw [MvPowerSeries.pderiv_X_of_ne h, mul_zero]
theorem lam_mul' (i j : Fin 2) :
    lam W * (MvPowerSeries.X i - MvPowerSeries.X j) = Fgl1.Wi W i - Fgl1.Wi W j := by
  have h : lam W * (MvPowerSeries.X 1 - MvPowerSeries.X 0) = Fgl1.Wi W 1 - Fgl1.Wi W 0 :=
    (formal_group_chord R W).1
  fin_cases i <;> fin_cases j
  · simp
  · show lam W * (MvPowerSeries.X 0 - MvPowerSeries.X 1) = Fgl1.Wi W 0 - Fgl1.Wi W 1
    rw [← neg_sub, mul_neg, h, neg_sub]
  · exact h
  · simp
theorem nu_eq (i : Fin 2) : nu W = Fgl1.Wi W i - lam W * MvPowerSeries.X i := by
  have h : lam W * (MvPowerSeries.X 1 - MvPowerSeries.X 0) = Fgl1.Wi W 1 - Fgl1.Wi W 0 :=
    (formal_group_chord R W).1
  fin_cases i
  · rfl
  · show nu W = Fgl1.Wi W 1 - lam W * MvPowerSeries.X 1
    unfold nu
    linear_combination h
theorem third_rel (i j : Fin 2) (hij : i ≠ j) :
    cThree W * (MvPowerSeries.X i + MvPowerSeries.X j + uThird W) + cTwo W = 0 := by
  have hinv : cThree W * MvPowerSeries.invOfUnit (cThree W) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by simp [Fgl1.cThree_cc])
  have hsum : (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) + MvPowerSeries.X j =
      MvPowerSeries.X 0 + MvPowerSeries.X 1 := by
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | rfl | exact add_comm _ _
  rw [hsum, uThird]
  linear_combination (-(cTwo W)) * hinv
theorem Dm_uThird [IsDomain R] (i : Fin 2) : Dm W i (uThird W) = -(fw W).subst (uThird W) := by
  obtain ⟨j, hji⟩ : ∃ j : Fin 2, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
  have hXj : MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 2) R) = 0 :=
    MvPowerSeries.constantCoeff_X j
  have hD2 : Dm W i (Fgl1.Wi W j) = 0 := by
    rw [Dm_subst W i hXj, Dm_X_of_ne W hji, mul_zero]
  have hne12 : (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ≠ MvPowerSeries.X j := fun h =>
    hji (MvPowerSeries.X_inj.mp h).symm
  have hcoef : ∀ k l : Fin 2, MvPowerSeries.coeff (Finsupp.single k 1)
      (MvPowerSeries.X l : MvPowerSeries (Fin 2) R) = if k = l then 1 else 0 := by
    intro k l
    rw [MvPowerSeries.coeff_X]
    by_cases h : k = l
    · simp [h]
    · simp [h, Finsupp.single_left_inj one_ne_zero]
  have hne31 : uThird W ≠ MvPowerSeries.X i := fun h => by
    have h1 := Fgl1.uThird_L (W := W) j
    rw [h, hcoef, if_neg hji] at h1
    exact one_ne_zero (neg_eq_zero.mp h1.symm)
  have hne32 : uThird W ≠ MvPowerSeries.X j := fun h => by
    have h1 := Fgl1.uThird_L (W := W) i
    rw [h, hcoef, if_neg (Ne.symm hji)] at h1
    exact one_ne_zero (neg_eq_zero.mp h1.symm)
  have hC3 : (1 + (curveM W).a₂ * lam W + (curveM W).a₄ * lam W ^ 2 + (curveM W).a₆ * lam W ^ 3) ≠ 0 := by
    intro h
    have h1 := congrArg MvPowerSeries.constantCoeff (show cThree W = 0 from h)
    rw [Fgl1.cThree_cc, map_zero] at h1
    exact one_ne_zero h1
  have h9 : (1 + (curveM W).a₂ * lam W + (curveM W).a₄ * lam W ^ 2 + (curveM W).a₆ * lam W ^ 3) *
      (MvPowerSeries.X i + MvPowerSeries.X j + uThird W) + ((curveM W).a₁ * lam W + (curveM W).a₂ * nu W +
        (curveM W).a₃ * lam W ^ 2 + 2 * (curveM W).a₄ * lam W * nu W + 3 * (curveM W).a₆ * lam W ^ 2 * nu W) = 0 :=
    third_rel W i j (Ne.symm hji)
  haveI : IsDomain (MvPowerSeries (Fin 2) R) := NoZeroDivisors.to_isDomain _
  have hT := flowThirdPoint (MvPowerSeries (Fin 2) R) (curveM W) (Dm W i) (MvPowerSeries.X i) (Fgl1.Wi W i)
    (MvPowerSeries.X j) (Fgl1.Wi W j) (lam W) (nu W) (uThird W) (isDer_Dm W i) (const_Dm W i) (flow_Dm W i)
    (weq_subst W hXj) (Dm_X_of_ne W hji) hD2 (lam_mul' W i j) (nu_eq W i) h9 hC3 hne12 hne31 hne32
  rw [hT.2.1, fw_subst W (Fgl1.uThird_cc (W := W)), ← Fgl1.wThird_eq (W := W)]
  rfl
theorem formal_inverse_spec : ISerSpec.{u} := iSerSpec_of w_series_spec w_series_factorization invariant_differential_units unit_flow chartFlowNegation
theorem Dm_fgl [IsDomain R] (i : Fin 2) : Dm W i (fgl W) = (fw W).subst (fgl W) := by
  have hu : MvPowerSeries.constantCoeff (uThird W) = 0 := (formal_group_chord R W).2.1
  have hu' := PowerSeries.HasSubst.of_constantCoeff_zero hu
  have hS := formal_inverse_spec R W
  have hI : PowerSeries.HasSubst (iSer W) := PowerSeries.HasSubst.of_constantCoeff_zero hS.1
  have hD : derivative R (iSer W) * fw W = -(fw W).subst (iSer W) := by
    have h := hS.2.2.2.2.2.2.1
    simp only [D, Derivation.smul_apply, smul_eq_mul] at h
    rw [mul_comm]
    exact h
  have hmul : ∀ f g : R⟦X⟧, (f * g).subst (uThird W) = f.subst (uThird W) * g.subst (uThird W) :=
    fun f g => by rw [← PowerSeries.coe_substAlgHom (R := R) hu', map_mul]
  have hneg : ∀ f : R⟦X⟧, (-f).subst (uThird W) = -(f.subst (uThird W)) :=
    fun f => by rw [← PowerSeries.coe_substAlgHom (R := R) hu', map_neg]
  rw [Fgl1.fgl_eq, Dm_subst W i hu, Dm_uThird W i, ← PowerSeries.subst_comp_subst_apply hI hu', mul_neg,
    ← hmul, hD, hneg, neg_neg]
end Subst
section Transfer
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
theorem map_pderiv (φ : R →+* S) (i : Fin 2) (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv R i f)
      = MvPowerSeries.pderiv S i (MvPowerSeries.map φ f) := by
  ext n
  simp [MvPowerSeries.coeff_pderiv]
theorem map_Dm (φ : R →+* S) (W : WeierstrassCurve R) (i : Fin 2) (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.map φ (Dm W i f) = Dm (W.map φ) i (MvPowerSeries.map φ f) := by
  unfold Dm
  rw [map_mul, map_pderiv,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)),
    (series_map R S φ W).2.2.2.2.1, MvPowerSeries.map_X]
theorem Dm_fgl' (W : WeierstrassCurve R) (i : Fin 2) : Dm W i (fgl W) = (fw W).subst (fgl W) := by
  have hcc : PowerSeries.HasSubst (fgl Univ.W₀) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (Fgl1.fgl_cc Univ.W₀)
  have h1 := congrArg (MvPowerSeries.map (Univ.φ_of W)) (Dm_fgl Univ.W₀ i)
  rw [map_Dm, Univ.map_eq, ← Fgl1.fgl_univ, PowerSeries.map_subst hcc,
    (series_map _ _ (Univ.φ_of W) Univ.W₀).2.2.2.2.1, Univ.map_eq, ← Fgl1.fgl_univ] at h1
  exact h1
theorem fw_mul_om_subst (W : WeierstrassCurve R) {s : MvPowerSeries (Fin 2) R} (hs : cc s = 0) :
    (fw W).subst s * (om W).subst s = 1 := by
  have h1 : fw W * om W = 1 := by
    have h := (unit_flow R W).2.2.2.2.2 X
    simp only [D, Derivation.smul_apply, PowerSeries.derivative_X, smul_eq_mul, mul_one] at h
    rw [mul_comm]
    exact h
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero hs
  rw [← PowerSeries.coe_substAlgHom (R := R) hs', ← map_mul, h1, map_one]
theorem om_fgl (W : WeierstrassCurve R) (i : Fin 2) :
    (om W).subst (fgl W) * MvPowerSeries.pderiv R i (fgl W)
      = (om W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) := by
  have h := Dm_fgl' W i
  unfold Dm at h
  have hF : MvPowerSeries.constantCoeff (fgl W) = 0 := Fgl1.fgl_cc W
  have h1 := fw_mul_om_subst W hF
  have h2 := fw_mul_om_subst W (MvPowerSeries.constantCoeff_X i)
  linear_combination ((om W).subst (fgl W) * (om W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)) * h +
    (om W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) * h1 -
    ((om W).subst (fgl W) * MvPowerSeries.pderiv R i (fgl W)) * h2
theorem mvsubst_psubst {σ τ : Type*} {a : MvPowerSeries σ R} (ha : PowerSeries.HasSubst a)
    {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) (f : R⟦X⟧) :
    MvPowerSeries.subst b (f.subst a) = f.subst (MvPowerSeries.subst b a) := by
  unfold PowerSeries.subst
  exact MvPowerSeries.subst_comp_subst_apply ha.const hb f
end Transfer
section Log
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
theorem formal_logarithm_spec : LogSpec.{u} := logSpec_of integration_spec invariant_differential_units
theorem formal_exponential_spec : ExpSpec.{u} := expSpec_of integration_spec composition_inverse_spec invariant_differential_units
theorem eq_zero_of_pderiv_zero_of_pderiv_one_eq_zero {h : MvPowerSeries (Fin 2) K}
    (h0 : MvPowerSeries.pderiv K 0 h = 0) (h1 : MvPowerSeries.pderiv K 1 h = 0)
    (hc : MvPowerSeries.constantCoeff h = 0) : h = 0 := by
  ext n
  rw [map_zero]
  by_cases hn : n = 0
  · subst hn
    simpa using hc
  · obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hn (Finsupp.ext hne)
    have hD : MvPowerSeries.pderiv K i h = 0 := by
      fin_cases i
      · exact h0
      · exact h1
    have h2 := congrArg (MvPowerSeries.coeff (n - Finsupp.single i 1)) hD
    rw [MvPowerSeries.coeff_pderiv, map_zero] at h2
    have hsum : n - Finsupp.single i 1 + Finsupp.single i 1 = n := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
        omega
      · simp [Finsupp.single_apply, Ne.symm hj]
    rw [hsum] at h2
    exact (mul_eq_zero.mp h2).resolve_right (Nat.cast_add_one_ne_zero _)
theorem log_fgl : (logSer W).subst (fgl W) = (logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
    + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K) := by
  have hL := formal_logarithm_spec K W
  have hF : MvPowerSeries.constantCoeff (fgl W) = 0 := Fgl1.fgl_cc W
  rw [← sub_eq_zero]
  apply eq_zero_of_pderiv_zero_of_pderiv_one_eq_zero
  · rw [map_sub, map_add, Formalism.G.LogCR.pderiv_psubst hF, Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X 0),
      Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X 1), hL.2.2.1, om_fgl W 0,
      MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (by decide), mul_zero, mul_one, add_zero, sub_self]
  · rw [map_sub, map_add, Formalism.G.LogCR.pderiv_psubst hF, Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X 0),
      Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X 1), hL.2.2.1, om_fgl W 1,
      MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (by decide), mul_zero, mul_one, zero_add, sub_self]
  · have hc : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 →
        MvPowerSeries.constantCoeff ((logSer W).subst a) = 0 := fun a ha => by
      rw [PowerSeries.subst, Formalism.G.LogP.constantCoeff_subst_of_zero _ (fun _ => ha)]
      exact hL.1
    rw [map_sub, map_add, hc _ hF, hc _ (MvPowerSeries.constantCoeff_X 0), hc _ (MvPowerSeries.constantCoeff_X 1)]
    simp
end Log
section Group
open MvPowerSeries in
theorem cons_map {τ : Type*} {A : Type*} {B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (g₁ g₂ : MvPowerSeries τ A) :
    (fun i => (![g₁, g₂] i).map f) = ![g₁.map f, g₂.map f] := by
  funext i
  fin_cases i <;> rfl
theorem exists_FK : ∃ F : FormalGroup Univ.K₀, F.toPowerSeries = fgl Univ.WK := by
  have hGc : MvPowerSeries.constantCoeff (fgl Univ.WK) = 0 := Fgl1.fgl_cc _
  have hlog := log_fgl Univ.WK
  have hE := formal_exponential_spec Univ.K₀ Univ.WK
  have hLs : PowerSeries.HasSubst (logSer Univ.WK) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (formal_logarithm_spec Univ.K₀ Univ.WK).1
  have hhs : ∀ a b : MvPowerSeries (Fin 3) Univ.K₀, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → MvPowerSeries.HasSubst ![a, b] := fun a b ha hb =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      fin_cases i
      · exact ha
      · exact hb
  have hadd : ∀ a b : MvPowerSeries (Fin 3) Univ.K₀, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 →
      (logSer Univ.WK).subst (MvPowerSeries.subst ![a, b] (fgl Univ.WK)) =
        (logSer Univ.WK).subst a + (logSer Univ.WK).subst b := by
    intro a b ha hb
    have hab := hhs a b ha hb
    have h := congrArg (MvPowerSeries.subst ![a, b]) hlog
    rw [mvsubst_psubst (PowerSeries.HasSubst.of_constantCoeff_zero hGc) hab, ← MvPowerSeries.coe_substAlgHom hab,
      map_add, MvPowerSeries.coe_substAlgHom hab,
      mvsubst_psubst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)) hab,
      mvsubst_psubst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)) hab,
      MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab] at h
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h
  have hcs : ∀ a b : MvPowerSeries (Fin 3) Univ.K₀, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst ![a, b] (fgl Univ.WK)) = 0 := fun a b ha hb => by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero _ (fun i => by
      fin_cases i
      · exact ha
      · exact hb)]
    exact hGc
  have hinj : ∀ u v : MvPowerSeries (Fin 3) Univ.K₀, MvPowerSeries.constantCoeff u = 0 →
      MvPowerSeries.constantCoeff v = 0 → (logSer Univ.WK).subst u = (logSer Univ.WK).subst v → u = v := by
    intro u v hu hv huv
    have hu' := PowerSeries.HasSubst.of_constantCoeff_zero hu
    have hv' := PowerSeries.HasSubst.of_constantCoeff_zero hv
    calc u = PowerSeries.subst u (X : Univ.K₀⟦X⟧) := (PowerSeries.subst_X hu').symm
      _ = PowerSeries.subst u (PowerSeries.subst (logSer Univ.WK) (expSer Univ.WK)) := by rw [hE.2.2.2.1]
      _ = PowerSeries.subst (PowerSeries.subst u (logSer Univ.WK)) (expSer Univ.WK) :=
          PowerSeries.subst_comp_subst_apply hLs hu' _
      _ = PowerSeries.subst (PowerSeries.subst v (logSer Univ.WK)) (expSer Univ.WK) := by
          rw [show PowerSeries.subst u (logSer Univ.WK) = PowerSeries.subst v (logSer Univ.WK) from huv]
      _ = PowerSeries.subst v (PowerSeries.subst (logSer Univ.WK) (expSer Univ.WK)) :=
          (PowerSeries.subst_comp_subst_apply hLs hv' _).symm
      _ = v := by rw [hE.2.2.2.1, PowerSeries.subst_X hv']
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) Univ.K₀) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) Univ.K₀) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have c2 : MvPowerSeries.constantCoeff (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) Univ.K₀) = 0 :=
    MvPowerSeries.constantCoeff_X _
  refine ⟨{
    toPowerSeries := fgl Univ.WK
    zero_constantCoeff := hGc
    lin_coeff_X := Fgl1.fgl_L _ 0
    lin_coeff_Y := Fgl1.fgl_L _ 1
    assoc := ?_ }, rfl⟩
  apply hinj _ _ (hcs _ _ (hcs _ _ c0 c1) c2) (hcs _ _ c0 (hcs _ _ c1 c2))
  rw [hadd _ _ (hcs _ _ c0 c1) c2, hadd _ _ c0 c1, hadd _ _ c0 (hcs _ _ c1 c2), hadd _ _ c1 c2, add_assoc]
def FZ : FormalGroup Univ.Z where
  toPowerSeries := fgl Univ.W₀
  zero_constantCoeff := Fgl1.fgl_cc _
  lin_coeff_X := Fgl1.fgl_L _ 0
  lin_coeff_Y := Fgl1.fgl_L _ 1
  assoc := by
    obtain ⟨F, hF⟩ := exists_FK
    apply Univ.mv_map_injective Univ.ι Univ.ι_injective
    have h := F.assoc
    rw [hF, ← Fgl1.fgl_WK] at h
    rw [MvPowerSeries.map_subst
        (MvPowerSeries.HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 (Fgl1.fgl_cc _)),
      MvPowerSeries.map_subst
        (MvPowerSeries.HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 (Fgl1.fgl_cc _)),
      cons_map, cons_map, MvPowerSeries.map_subst MvPowerSeries.HasSubst.X_X,
      MvPowerSeries.map_subst MvPowerSeries.HasSubst.X_X, cons_map, cons_map]
    simp only [MvPowerSeries.map_X]
    exact h
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
end Group
section Inv
end Inv
end Fgl2
end Formalism.L2.Th1.A


