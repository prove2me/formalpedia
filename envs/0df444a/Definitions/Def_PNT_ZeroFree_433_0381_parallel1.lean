-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0381_parallel1
-- name    : PNT_ZeroFree_433_0381_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:24:15.294807+00:00
-- url     : https://prove2.me/theorems/f834b5a7-30b3-4a7e-844d-19c14f22f7a5
-- title:
--   Zero-free region foundations: Hecke.InverseAmplificationBudget, Hecke.InverseAmplificationPowers [0381_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationBudget
--   - OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationPowers
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationBudget.lean#L9-L98
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationPowers.lean#L8-L50

import Definitions.Def_PNT_ZeroFree_433_0150
import Definitions.Def_PNT_ZeroFree_433_0292_parallel1
import Definitions.Def_PNT_ZeroFree_433_0293_parallel1
import Definitions.Def_PNT_ZeroFree_433_0294_parallel1
import Definitions.Def_PNT_ZeroFree_433_0306_parallel1
import Definitions.Def_PNT_ZeroFree_433_0326_parallel1
import Definitions.Def_PNT_ZeroFree_433_0339_parallel1
import Definitions.Def_PNT_ZeroFree_433_0366_parallel1
import Definitions.Def_PNT_ZeroFree_433_0369_parallel1
import Definitions.Def_PNT_ZeroFree_433_0391_parallel1
import Definitions.Def_PNT_ZeroFree_433_0439_parallel1
import Definitions.Def_PNT_ZeroFree_433_0464_parallel1
import Definitions.Def_PNT_ZeroFree_433_0480_parallel1
import Definitions.Def_PNT_ZeroFree_433_0600_parallel1
import Definitions.Def_PNT_ZeroFree_433_0616_parallel1
import Definitions.Def_PNT_ZeroFree_433_0623_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationBudget.lean#L9-L98
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationPowers.lean#L8-L50
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationBudget
section
namespace OAI

noncomputable section
open Filter
namespace SevenEighths.HeckeInverseAmplification

def amplificationPower (c r : ℝ) : ℝ := max 0 (((1+c)*r-1)/6)
def sourceExponent (r : ℝ) : ℝ := max 1 ((1+5*r)/6)

theorem amplificationPower_nonneg (c r : ℝ) : 0≤amplificationPower c r := le_max_left _ _

theorem amplificationPower_upper (c r R : ℝ) (hc : c≤1) (hr : 0≤r)
    (hrR : r≤R) : amplificationPower c r≤R/3 := by
  apply max_le (by linarith)
  have hh := mul_le_mul_of_nonneg_right hc hr
  nlinarith

theorem amplified_exponent (c r : ℝ) :
    1+5*amplificationPower c r=max 1 ((1+5*(1+c)*r)/6) := by
  unfold amplificationPower
  by_cases h : 0≤((1+c)*r-1)/6
  · rw [max_eq_right h,max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_left (by linarith)]
    ring

theorem amplified_exponent_le (c r R : ℝ) (hc : 0≤c) (hrR : r≤R)
    (hR : 0≤R) : 1+5*amplificationPower c r≤sourceExponent r+5*c*R/6 := by
  rw [amplified_exponent]
  apply max_le
  · have hh := le_max_left 1 ((1+5*r)/6)
    unfold sourceExponent
    nlinarith [mul_nonneg hc hR]
  · have hh := le_max_right 1 ((1+5*r)/6)
    have hh' := mul_le_mul_of_nonneg_left hrR hc
    unfold sourceExponent
    nlinarith

theorem exists_amplification_budget (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧
      ∀ r : ℝ, 0≤r → r≤R →
      1+5*amplificationPower c r+κ*(1+6*amplificationPower c r+r)≤
        sourceExponent r+ε/2 := by
  let c := min 1 (ε/(4*(R+1)))
  let κ := ε/(4*(1+3*R))
  have hc : 0<c := lt_min zero_lt_one (div_pos hε (by positivity))
  have hκ : 0<κ := div_pos hε (by positivity)
  have hc1 : c≤1 := min_le_left _ _
  have hcb : c*(4*(R+1))≤ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hκb : κ*(4*(1+3*R))=ε := by dsimp [κ]; field_simp
  refine ⟨c,κ,hc,hc1,hκ,?_⟩
  intro r hr hrR
  have hp := amplificationPower_upper c r R hc1 hr hrR
  have he := amplified_exponent_le c r R hc.le hrR hR
  have hraw : κ*(1+6*amplificationPower c r+r)≤κ*(1+3*R) := by
    apply mul_le_mul_of_nonneg_left _ hκ.le
    linarith
  nlinarith

theorem logarithmic_cost_eventually (A b P η : ℝ) (hA : 1≤A)
    (hbA : 1≤b*A) (hP : 0≤P) (hη : 0<η) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ U : ℝ in atTop, ∀ p : ℝ, 0≤p → p≤P →
      (1+2*Real.log (b*(A*U^p)))*Real.log (A*U^p)≤K*U^η := by
  let K := (1+2*Real.log (b*A)+2*P)*(Real.log A+P)
  have hLA : 0≤Real.log A := Real.log_nonneg hA
  have hLB : 0≤Real.log (b*A) := Real.log_nonneg hbA
  have hK : 0≤K := mul_nonneg (by positivity) (by positivity)
  have hlog := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hη).bound (by norm_num : (0 : ℝ)<1)
  refine ⟨K,hK,?_⟩
  filter_upwards [hlog,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with U hlog hLU hU
  intro p hp hpP
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hpow : 0<U^p := Real.rpow_pos_of_pos hUp _
  have hx : 1≤A*U^p := one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hU hp)
  have hlogx : Real.log (A*U^p)=Real.log A+p*Real.log U := by
    rw [Real.log_mul (ne_of_gt (zero_lt_one.trans_le hA)) hpow.ne',Real.log_rpow hUp]
  have hlogbx : Real.log (b*(A*U^p))=Real.log (b*A)+p*Real.log U := by
    rw [show b*(A*U^p)=b*A*U^p by ring,
      Real.log_mul (ne_of_gt (zero_lt_one.trans_le hbA)) hpow.ne',Real.log_rpow hUp]
  have hfirst : 1+2*Real.log (b*(A*U^p))≤(1+2*Real.log (b*A)+2*P)*Real.log U := by
    rw [hlogbx]
    nlinarith [mul_le_mul_of_nonneg_right hpP (by linarith : 0≤Real.log U),
      mul_le_mul_of_nonneg_left hLU hLB]
  have hsecond : Real.log (A*U^p)≤(Real.log A+P)*Real.log U := by
    rw [hlogx]
    nlinarith [mul_le_mul_of_nonneg_right hpP (by linarith : 0≤Real.log U),
      mul_le_mul_of_nonneg_left hLU hLA]
  have hsq : (Real.log U)^2≤U^η := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log U)),
      abs_of_nonneg (Real.rpow_nonneg hUp.le _),one_mul] using hlog
  calc
    _ ≤ ((1+2*Real.log (b*A)+2*P)*Real.log U)*((Real.log A+P)*Real.log U) :=
      mul_le_mul hfirst hsecond (Real.log_nonneg hx) (by positivity)
    _ = K*(Real.log U)^2 := by dsimp [K]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hK

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationPowers
section
namespace OAI

noncomputable section
namespace SevenEighths.HeckeInverseAmplification

theorem amplified_norm_power (U A b p : ℝ) (hU : 0<U) :
    U*(b*(A*U^p))^6=(b*A)^6*U^(1+6*p) := by
  have h6 : (U^p)^6=U^(6*p) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
    congr 1
    norm_num
    ring
  calc
    _ = (b*A)^6*(U^(1 : ℝ)*U^(6*p)) := by
      rw [show b*(A*U^p)=(b*A)*U^p by ring,mul_pow,h6,Real.rpow_one]
      ring
    _ = _ := by rw [←Real.rpow_add hU]

theorem amplified_energy_power (U A b p r κ : ℝ) (hU : 0<U) :
    (U*(b*(A*U^p))^6)*((U*(b*(A*U^p))^6)*U^r)^κ/(A*U^p)=
      ((b*A)^6*((b*A)^6)^κ/A)*U^(1+5*p+κ*(1+6*p+r)) := by
  rw [amplified_norm_power U A b p hU]
  have hHD : ((b*A)^6*U^(1+6*p))*U^r=(b*A)^6*U^(1+6*p+r) := by
    rw [mul_assoc,←Real.rpow_add hU]
  rw [hHD,Real.mul_rpow (by positivity) (Real.rpow_nonneg hU.le _),
    ←Real.rpow_mul hU.le]
  calc
    _ = ((b*A)^6*((b*A)^6)^κ/A)*
        ((U^(1+6*p)*U^((1+6*p+r)*κ))/U^p) := by ring
    _ = ((b*A)^6*((b*A)^6)^κ/A)*U^((1+6*p)+(1+6*p+r)*κ-p) := by
      rw [←Real.rpow_add hU,←Real.rpow_sub hU]
    _ = _ := by congr 2; ring

theorem fixed_multiplier_lower (U A p : ℝ) (hU : 1≤U) (hA : 0≤A) (hp : 0≤p) :
    A≤A*U^p := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_rpow hU hp) hA

theorem amplified_norm_dominates (U A b c r : ℝ) (hU : 1≤U) (hbA : 1≤b*A) :
    (U^r)^(1+c)≤U*(b*(A*U^(amplificationPower c r)))^6 := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  rw [amplified_norm_power U A b _ hUp,←Real.rpow_mul hUp.le]
  have he : r*(1+c)≤1+6*amplificationPower c r := by
    have hh := le_max_right 0 (((1+c)*r-1)/6)
    unfold amplificationPower
    nlinarith
  have hp := Real.rpow_le_rpow_of_exponent_le hU he
  have hconst : (1 : ℝ)≤(b*A)^6 := one_le_pow₀ hbA
  exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg hUp.le _) hconst)

end SevenEighths.HeckeInverseAmplification

end

end OAI

end


