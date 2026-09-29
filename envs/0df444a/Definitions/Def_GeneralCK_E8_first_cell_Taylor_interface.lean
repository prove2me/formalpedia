-- Prove2me | Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface
-- name    : GeneralCK_E8_first_cell_Taylor_interface
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T00:42:05.734929+00:00
-- url     : https://prove2.me/theorems/325ce718-3c31-4834-ae1a-ee6bf0a59dda
-- title:
--   Exact E8 analytic, Taylor replay and first-cell geometry definitions
-- statement:
--   These original definitions describe the analytic inverse germ used by the regularized E8 determinant derivative, its directional derivatives, fourth-order Taylor replay data, and exact first-cell geometry. The rectangle uses the original rational lower endpoints, upper bounds $s\le3/40$ and $t\le1/50$, and center $(57/800,3/200)$. The bundle preserves the short source lemmas needed to construct these analytic definitions, including the nonzero derivative witnesses for local inverses. Separate theorem nodes establish the Taylor remainder estimate and strict first-cell positivity; no positivity assumption is introduced.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/tree/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_first_cell_inputs
import Definitions.Def_GeneralCK_E8_first_cell_jet_graphs
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_mixed_polynomial_interface
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

namespace GeneralCK.Reflection.ComplexFixedPoint
end GeneralCK.Reflection.ComplexFixedPoint

namespace GeneralCK.Certificates.E8PositiveAxisGermJet
end GeneralCK.Certificates.E8PositiveAxisGermJet

namespace GeneralCK.Certificates.E8TAxisBivariateTaylor
end GeneralCK.Certificates.E8TAxisBivariateTaylor

section
namespace GeneralCK.Certificates



namespace Jet5









def add (a b : Jet5) : Jet5 :=
  ⟨fun t => a.d0 t + b.d0 t, fun t => a.d1 t + b.d1 t,
   fun t => a.d2 t + b.d2 t, fun t => a.d3 t + b.d3 t,
   fun t => a.d4 t + b.d4 t, fun t => a.d5 t + b.d5 t⟩

def neg (a : Jet5) : Jet5 :=
  ⟨fun t => -a.d0 t, fun t => -a.d1 t, fun t => -a.d2 t,
   fun t => -a.d3 t, fun t => -a.d4 t, fun t => -a.d5 t⟩

/-- Raw-derivative Leibniz propagation through order five. -/
def mul (a b : Jet5) : Jet5 :=
  ⟨fun t => a.d0 t * b.d0 t,
   fun t => a.d1 t * b.d0 t + a.d0 t * b.d1 t,
   fun t => a.d2 t * b.d0 t + 2*a.d1 t*b.d1 t + a.d0 t*b.d2 t,
   fun t => a.d3 t*b.d0 t + 3*a.d2 t*b.d1 t + 3*a.d1 t*b.d2 t + a.d0 t*b.d3 t,
   fun t => a.d4 t*b.d0 t + 4*a.d3 t*b.d1 t + 6*a.d2 t*b.d2 t +
     4*a.d1 t*b.d3 t + a.d0 t*b.d4 t,
   fun t => a.d5 t*b.d0 t + 5*a.d4 t*b.d1 t + 10*a.d3 t*b.d2 t +
     10*a.d2 t*b.d3 t + 5*a.d1 t*b.d4 t + a.d0 t*b.d5 t⟩




















end Jet5
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.E8TAxisOneCellArithmetic

open DyadicInterval

def precision : ℕ := 160





def ds : DyadicInterval precision := ⟨-5480631139990885943263818122686061323709747037, 5480631139990885943263818122686061323709747037⟩
def dt : DyadicInterval precision := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩




































end GeneralCK.Certificates.E8TAxisOneCellArithmetic
end

section
namespace GeneralCK.Certificates.E8TAxisCenteredReplaySoundness

open DyadicInterval E8TAxisOneCellArithmetic Set





noncomputable def centeredValue (c r : ℕ → ℕ → ℝ) (x y : ℝ) : ℝ :=
  c 0 1 + c 0 2 * x ^ 0 * y ^ 1 / 1 + c 1 1 * x ^ 1 * y ^ 0 / 1 + c 0 3 * x ^ 0 * y ^ 2 / 2 + c 1 2 * x ^ 1 * y ^ 1 / 1 + c 2 1 * x ^ 2 * y ^ 0 / 2 + c 0 4 * x ^ 0 * y ^ 3 / 6 + c 1 3 * x ^ 1 * y ^ 2 / 2 + c 2 2 * x ^ 2 * y ^ 1 / 2 + c 3 1 * x ^ 3 * y ^ 0 / 6 + r 0 5 * x ^ 0 * y ^ 4 / 24 + r 1 4 * x ^ 1 * y ^ 3 / 6 + r 2 3 * x ^ 2 * y ^ 2 / 4 + r 3 2 * x ^ 3 * y ^ 1 / 6 + r 4 1 * x ^ 4 * y ^ 0 / 24
















end GeneralCK.Certificates.E8TAxisCenteredReplaySoundness
end

section
namespace GeneralCK











/-- Cross-multiplied form of the manuscript's equation-(8) difference. -/
noncomputable def e8Delta (Q : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (Q (2 * s + t) - Q s) * (Q (s + t) - Q t) -
    (Q (2 * s + t) - Q (s + t)) * (Q s + Q t)





















end GeneralCK
end

section
namespace GeneralCK.Reflection.ComplexEntropy

open Set

/-- Natural binary entropy, written in the bias coordinate and extended to
the complex unit disc by the principal logarithm. -/
noncomputable def entropyExt (c : ℂ) : ℂ :=
  (Real.log 2 : ℂ) -
    ((1 + c) * Complex.log (1 + c) + (1 - c) * Complex.log (1 - c)) / 2

/-- The logarithmic derivative of `entropyExt`. -/
noncomputable def entropyDeriv (c : ℂ) : ℂ :=
  (Complex.log (1 - c) - Complex.log (1 + c)) / 2

private lemma one_add_mem_slitPlane {c : ℂ} (hc : ‖c‖ < 1) :
    1 + c ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_of_norm_lt_one hc

private lemma one_sub_mem_slitPlane {c : ℂ} (hc : ‖c‖ < 1) :
    1 - c ∈ Complex.slitPlane := by
  simpa only [sub_eq_add_neg, norm_neg] using
    (Complex.mem_slitPlane_of_norm_lt_one (z := -c) (by simpa using hc))

/-- Exact complex derivative throughout the open unit disc. -/
theorem hasDerivAt_entropyExt {c : ℂ} (hc : ‖c‖ < 1) :
    @HasDerivAt ℂ _ ℂ _
      (((NormedAlgebra.toNormedSpace ℂ) : NormedSpace ℂ ℂ).toModule) _ _
      entropyExt (entropyDeriv c) c := by
  have hp : HasDerivAt (fun z : ℂ => Complex.log (1 + z)) (1 + c)⁻¹ c := by
    simpa only [one_div] using
      (Complex.hasDerivAt_log (one_add_mem_slitPlane hc)).comp_const_add 1 c
  have hm := (Complex.hasDerivAt_log (one_sub_mem_slitPlane hc)).comp c
    ((hasDerivAt_id c).const_sub 1)
  have hpMul := ((hasDerivAt_id c).const_add 1).mul hp
  have hmMul := ((hasDerivAt_id c).const_sub 1).mul hm
  have hraw := ((hpMul.add hmMul).div_const 2).const_sub (Real.log 2 : ℂ)
  have hraw' := hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => by
    simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, id_eq]
    rfl))
  apply hraw'.congr_deriv
  unfold entropyDeriv
  simp only [Function.comp_apply, id_eq, one_mul, neg_one_mul, mul_neg, mul_one]
  field_simp [show (1 + c : ℂ) ≠ 0 from Complex.slitPlane_ne_zero (one_add_mem_slitPlane hc),
    show (1 - c : ℂ) ≠ 0 from Complex.slitPlane_ne_zero (one_sub_mem_slitPlane hc)]
  ring



























end GeneralCK.Reflection.ComplexEntropy
end

section
namespace GeneralCK.Reflection.ComplexContactGerm

open Set Filter Function
open scoped Topology
open ComplexEntropy ComplexFixedPoint

/-- The principal-log entropy is analytic at every point of the open unit
disc. -/
theorem analyticAt_entropyExt {c : ℂ} (hc : ‖c‖ < 1) :
    AnalyticAt ℂ entropyExt c := by
  have hp : AnalyticAt ℂ (fun z : ℂ => 1 + z) c :=
    analyticAt_const.add analyticAt_id
  have hm : AnalyticAt ℂ (fun z : ℂ => 1 - z) c :=
    analyticAt_const.sub analyticAt_id
  have hpSlit : 1 + c ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_of_norm_lt_one hc
  have hmSlit : 1 - c ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg, norm_neg] using
      (Complex.mem_slitPlane_of_norm_lt_one (z := -c) (by simpa using hc))
  unfold entropyExt
  exact analyticAt_const.sub
    (((hp.mul (hp.clog hpSlit)).add (hm.mul (hm.clog hmSlit))).div
      analyticAt_const (by norm_num))

@[simp] theorem entropyExt_zero : entropyExt 0 = (Real.log 2 : ℂ) := by
  simp [entropyExt]

private theorem entropyExt_zero_ne : entropyExt 0 ≠ 0 := by
  rw [entropyExt_zero]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

/-- The analytic map whose local inverse is the contact point. -/
noncomputable def slopeMap (c : ℂ) : ℂ := c / entropyExt c

@[simp] theorem slopeMap_zero : slopeMap 0 = 0 := by simp [slopeMap]

theorem analyticAt_slopeMap : AnalyticAt ℂ slopeMap 0 := by
  unfold slopeMap
  exact analyticAt_id.div (analyticAt_entropyExt (by norm_num)) entropyExt_zero_ne

/-- Exact derivative of the reciprocal-slope map at the origin. -/
theorem hasDerivAt_slopeMap_zero :
    HasDerivAt slopeMap (Real.log 2 : ℂ)⁻¹ 0 := by
  have h := (hasDerivAt_id (𝕜 := ℂ) 0).div
    (hasDerivAt_entropyExt (by norm_num)) entropyExt_zero_ne
  have h' : (Real.log 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  have hcoef :
      ((1 : ℂ) * entropyExt 0 - 0 * entropyDeriv 0) / entropyExt 0 ^ 2 =
        (Real.log 2 : ℂ)⁻¹ := by
    rw [entropyExt_zero]
    simp only [one_mul, zero_mul, sub_zero]
    field_simp [h']
  rw [show slopeMap = id / entropyExt by rfl, ← hcoef]
  simpa only [id_eq] using h

private theorem deriv_slopeMap_zero : deriv slopeMap 0 = (Real.log 2 : ℂ)⁻¹ :=
  hasDerivAt_slopeMap_zero.deriv

private theorem deriv_slopeMap_ne : deriv slopeMap 0 ≠ 0 := by
  rw [deriv_slopeMap_zero]
  exact inv_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num))))

/-- The holomorphic contact germ at `tau = 0`, obtained as the local inverse
of `c ↦ c / entropyExt c`. -/
noncomputable def contactGerm : ℂ → ℂ :=
  analyticAt_slopeMap.hasStrictDerivAt.localInverse slopeMap
    (deriv slopeMap 0) 0 deriv_slopeMap_ne

@[simp] theorem contactGerm_zero : contactGerm 0 = 0 := by
  have h := analyticAt_slopeMap.hasStrictDerivAt.eventually_left_inverse
    deriv_slopeMap_ne
  simpa [contactGerm] using h.self_of_nhds













end GeneralCK.Reflection.ComplexContactGerm
end

section
namespace GeneralCK.E8AnalyticGerm

open Set Filter Function
open Reflection.ComplexEntropy

abbrev CDeriv (f : ℂ → ℂ) (f' x : ℂ) : Prop :=
  @HasDerivAt ℂ _ ℂ _
    (((NormedAlgebra.toNormedSpace ℂ) : NormedSpace ℂ ℂ).toModule) _ _ f f' x

noncomputable def atanhExt (c : ℂ) : ℂ :=
  (Complex.log (1 + c) - Complex.log (1 - c)) / 2

noncomputable def biasBExt (c : ℂ) : ℂ :=
  (Real.log 2 : ℂ) - Complex.log (1 - c ^ 2) / 2

/-- The manuscript's `Theta_*(α)` expressed through `c = tanh α`. -/
noncomputable def thetaParam (c : ℂ) : ℂ :=
  (2 / (Real.log 2 : ℂ)) *
    (atanhExt c + c * entropyExt c / ((1 - c ^ 2) * biasBExt c))

/-- The manuscript's `X(α)` in the same coordinate. -/
noncomputable def xParam (c : ℂ) : ℂ :=
  (Real.log 2 : ℂ) * c / (2 * entropyExt c)

@[simp] theorem atanhExt_zero : atanhExt 0 = 0 := by simp [atanhExt]
@[simp] theorem biasBExt_zero : biasBExt 0 = (Real.log 2 : ℂ) := by simp [biasBExt]
@[simp] theorem thetaParam_zero : thetaParam 0 = 0 := by simp [thetaParam]
@[simp] theorem xParam_zero : xParam 0 = 0 := by simp [xParam]









private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))



theorem analyticAt_atanhExt : AnalyticAt ℂ atanhExt 0 := by
  unfold atanhExt
  have hp : AnalyticAt ℂ (fun z : ℂ => 1 + z) 0 := analyticAt_const.add analyticAt_id
  have hm : AnalyticAt ℂ (fun z : ℂ => 1 - z) 0 := analyticAt_const.sub analyticAt_id
  exact ((hp.clog (by simpa using one_mem_slit)).sub
    (hm.clog (by simpa using one_mem_slit))).div analyticAt_const (by norm_num)

theorem analyticAt_biasBExt : AnalyticAt ℂ biasBExt 0 := by
  unfold biasBExt
  have harg : AnalyticAt ℂ (fun z : ℂ => 1 - z ^ 2) 0 :=
    analyticAt_const.sub (analyticAt_id.pow 2)
  have hslit : (1 - (0 : ℂ) ^ 2) ∈ Complex.slitPlane := by simpa using one_mem_slit
  exact analyticAt_const.sub ((harg.clog hslit).div analyticAt_const (by norm_num))

theorem analyticAt_thetaParam : AnalyticAt ℂ thetaParam 0 := by
  unfold thetaParam
  have hE := Reflection.ComplexContactGerm.analyticAt_entropyExt (c := (0 : ℂ)) (by norm_num)
  have hden : (1 - (0 : ℂ) ^ 2) * biasBExt 0 ≠ 0 := by
    simpa only [biasBExt_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero, one_mul] using logTwo_ne
  exact analyticAt_const.mul (analyticAt_atanhExt.add
    ((analyticAt_id.mul hE).div
      ((analyticAt_const.sub (analyticAt_id.pow 2)).mul analyticAt_biasBExt) hden))





theorem hasDerivAt_thetaParam_zero :
    CDeriv thetaParam (4 / (Real.log 2 : ℂ)) 0 := by
  have hp : CDeriv (fun z : ℂ => Complex.log (1 + z)) 1 0 := by
    have hi : CDeriv (fun z : ℂ => 1 + z) 1 0 := by
      convert (hasDerivAt_id (𝕜 := ℂ) 0).const_add 1 using 1 <;> simp [add_comm]
    have hc := (Complex.hasDerivAt_log (show 1 + (0 : ℂ) ∈ Complex.slitPlane by
      simpa using one_mem_slit)).comp (0 : ℂ) hi
    convert hc using 1
    · rfl
    · norm_num
  have hm : CDeriv (fun z : ℂ => Complex.log (1 - z)) (-1) 0 := by
    have hi := (hasDerivAt_id (𝕜 := ℂ) 0).const_sub 1
    have hc := (Complex.hasDerivAt_log (show 1 - (0 : ℂ) ∈ Complex.slitPlane by
      simpa using one_mem_slit)).comp (0 : ℂ) hi
    convert hc using 1
    · rfl
    · norm_num
  have hA : CDeriv atanhExt 1 0 := by
    convert! (hp.sub hm).div_const 2 using 1 <;> simp [atanhExt]
  have hE : CDeriv entropyExt 0 0 := by
    simpa [entropyDeriv] using hasDerivAt_entropyExt (c := (0 : ℂ)) (by norm_num)
  have hB : CDeriv biasBExt 0 0 := by
    have hs := ((hasDerivAt_id (𝕜 := ℂ) 0).pow 2).const_sub 1
    have hl := (Complex.hasDerivAt_log
      (show 1 - ((id : ℂ → ℂ) ^ 2) 0 ∈ Complex.slitPlane by
        simpa [id_eq] using one_mem_slit)).comp (0 : ℂ) hs
    convert! (hl.div_const 2).const_sub (Real.log 2 : ℂ) using 1 <;>
      simp [biasBExt]
  have hden := (((hasDerivAt_id (𝕜 := ℂ) 0).pow 2).const_sub 1).mul hB
  have hden0 : (1 - (0 : ℂ) ^ 2) * biasBExt 0 ≠ 0 := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero,
      one_mul, biasBExt_zero] using logTwo_ne
  have hfrac := ((hasDerivAt_id (𝕜 := ℂ) 0).mul hE).div hden (by
    simpa only [Pi.mul_apply, Pi.pow_apply, id_eq] using hden0)
  have h := (hA.add hfrac).const_mul (2 / (Real.log 2 : ℂ))
  convert! h using 1
  · simp only [Reflection.ComplexContactGerm.entropyExt_zero, biasBExt_zero,
      id_eq, zero_mul, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, one_mul, Pi.mul_apply, Pi.pow_apply]
    have hk : (Real.log 2 : ℂ) * (Real.log 2 : ℂ) /
        (Real.log 2 : ℂ) ^ 2 = 1 := by
      calc
        _ = (Real.log 2 : ℂ) / (Real.log 2 : ℂ) := by
          field_simp [logTwo_ne]
        _ = 1 := div_self logTwo_ne
    rw [hk]
    ring

private theorem deriv_thetaParam_zero :
    deriv thetaParam 0 = 4 / (Real.log 2 : ℂ) :=
  hasDerivAt_thetaParam_zero.deriv

private theorem deriv_thetaParam_ne : deriv thetaParam 0 ≠ 0 := by
  rw [deriv_thetaParam_zero]
  exact div_ne_zero (by norm_num) logTwo_ne

/-- Bias-coordinate inverse germ for the E8 slope parametrization. -/
noncomputable def biasGerm : ℂ → ℂ :=
  analyticAt_thetaParam.hasStrictDerivAt.localInverse thetaParam
    (deriv thetaParam 0) 0 deriv_thetaParam_ne

/-- The analytic inverse `Q` germ, still separate from the zero-filled `e8Q`. -/
noncomputable def qGerm (y : ℂ) : ℂ := xParam (biasGerm y)

@[simp] theorem biasGerm_zero : biasGerm 0 = 0 := by
  have h := analyticAt_thetaParam.hasStrictDerivAt.eventually_left_inverse deriv_thetaParam_ne
  simpa [biasGerm] using h.self_of_nhds

@[simp] theorem qGerm_zero : qGerm 0 = 0 := by simp [qGerm]









/-- Factorial-normalized Taylor coefficient convention used by the finite
inverse-jet checker. -/
noncomputable def qTaylorCoeff (n : ℕ) : ℂ :=
  iteratedDeriv n qGerm 0 / n.factorial

@[simp] theorem qTaylorCoeff_zero : qTaylorCoeff 0 = 0 := by
  simp [qTaylorCoeff, iteratedDeriv_zero]











end GeneralCK.E8AnalyticGerm
end

section
namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology

/-- Signed smooth extension of the contact in the regular radius/entropy coordinate.
Unlike `biasContact (1/τ)`, its value at zero is the physical limit zero. -/
noncomputable def regularContact (τ : ℝ) : ℝ :=
  if τ=0 then 0 else if 0<τ then biasContact τ⁻¹ else -biasContact (-τ)⁻¹

@[simp] theorem regularContact_zero : regularContact 0=0 := by simp [regularContact]

































noncomputable def regularContactFirst (τ : ℝ) : ℝ :=
  (biasE (regularContact τ))^2/biasB (regularContact τ)

noncomputable def regularContactSecond (τ : ℝ) : ℝ :=
  let c := regularContact τ;
  -2*(biasE c)^3*SmallMean.A c/(biasB c)^2 -
    (biasE c)^4*c/((1-c^2)*(biasB c)^3)





@[simp] theorem regularContactFirst_zero : regularContactFirst 0=Real.log 2 := by
  simp only [regularContactFirst,regularContact_zero,biasE,biasB]
  norm_num
  field_simp

@[simp] theorem regularContactSecond_zero : regularContactSecond 0=0 := by
  simp [regularContactSecond,SmallMean.A]





end GeneralCK.Reflection
end

section
namespace GeneralCK.E8AnalyticGerm

open Set Filter Function
open Reflection Certificates.Reflection

noncomputable def thetaParamReal (c : ℝ) : ℝ :=
  (2 / Real.log 2) *
    (SmallMean.A c + c * biasE c / ((1 - c ^ 2) * biasB c))

noncomputable def xParamReal (c : ℝ) : ℝ :=
  Real.log 2 * c / (2 * biasE c)















end GeneralCK.E8AnalyticGerm
end

section
namespace GeneralCK









/-- Exact first `t`-derivative used by axis and compact certificate rules. -/
noncomputable def e8DeltaDerivT (Q : ℝ → ℝ) (s t : ℝ) : ℝ :=
  deriv Q (2 * s + t) * (Q (s + t) - Q t) +
    (Q (2 * s + t) - Q s) * (deriv Q (s + t) - deriv Q t) -
    (deriv Q (2 * s + t) - deriv Q (s + t)) * (Q s + Q t) -
    (Q (2 * s + t) - Q (s + t)) * deriv Q t







/-- Membership conditions needed to evaluate all four inverse arguments in
the range-restricted E8 statement. -/
def E8Admissible (s t : ℝ) : Prop :=
  0 < s ∧ 0 < t ∧
    s ∈ e8SlopeRange ∧ t ∈ e8SlopeRange ∧
    s + t ∈ e8SlopeRange ∧ 2 * s + t ∈ e8SlopeRange











end GeneralCK
end

section
namespace GeneralCK

open Set Filter
open Certificates Certificates.E8PositiveAxisGermJet
open Certificates.E8InverseJet5Bridge E8AnalyticGerm

/-- The positive inverse, continued through zero by its proved analytic germ. -/
noncomputable def e8RegularQ (y : ℝ) : ℝ :=
  if 0 < y then e8Q y else (qGerm (y : ℂ)).re



@[simp] theorem e8RegularQ_zero : e8RegularQ 0 = 0 := by
  simp [e8RegularQ]























end GeneralCK
end

section
namespace GeneralCK

open Set





noncomputable def e8RegularDeltaT (s t : ℝ) : ℝ :=
  deriv (fun v => e8Delta e8RegularQ s v) t













@[simp] theorem e8RegularDelta_zero_left (t : ℝ) :
    e8Delta e8RegularQ 0 t = 0 := by
  unfold e8Delta
  rw [e8RegularQ_zero]
  simp only [zero_add]
  ring

@[simp] theorem e8RegularDelta_zero_right (s : ℝ) :
    e8Delta e8RegularQ s 0 = 0 := by
  unfold e8Delta
  rw [e8RegularQ_zero]
  simp only [add_zero]
  ring

































end GeneralCK
end

section
namespace GeneralCK.Certificates.E8TAxisDeltaDirectionalJet

open GeneralCK Set
open E8InverseJet5Bridge

/-- Four derivative links; no derivative of the fourth component is asserted. -/
def Sound4At (j : Jet5) (u : ℝ) : Prop :=
  HasDerivAt j.d0 (j.d1 u) u ∧ HasDerivAt j.d1 (j.d2 u) u ∧
    HasDerivAt j.d2 (j.d3 u) u ∧ HasDerivAt j.d3 (j.d4 u) u

def Sound4On (j : Jet5) (S : Set ℝ) : Prop := ∀ u ∈ S, Sound4At j u









def sub (a b : Jet5) : Jet5 := a.add b.neg





/-- Raw derivatives under the affine change of variable `c + m*u`. -/
def affine (j : Jet5) (c m : ℝ) : Jet5 :=
  ⟨fun u => j.d0 (c + m * u),
   fun u => j.d1 (c + m * u) * m,
   fun u => j.d2 (c + m * u) * m ^ 2,
   fun u => j.d3 (c + m * u) * m ^ 3,
   fun u => j.d4 (c + m * u) * m ^ 4,
   fun u => j.d5 (c + m * u) * m ^ 5⟩



/-- The first derivative of an order-five jet, truncated after order four. -/
def shift (j : Jet5) : Jet5 :=
  ⟨j.d1, j.d2, j.d3, j.d4, j.d5, fun _ => 0⟩



noncomputable def qJet : Jet5 := e8QJet5 e8ThetaCanonicalJet5

noncomputable def qPrimeJet : Jet5 := shift qJet







@[simp] theorem qJet_d0 (y : ℝ) : qJet.d0 y = e8Q y := rfl





/-- Product-rule graph for the first t derivative of the E8 determinant.
The inputs are `Q(A),Q(B),Q(C),Q(D),Q'(A),Q'(B),Q'(C)`. -/
def deltaTGraph (a b c d ap bp cp : Jet5) : Jet5 :=
  (((bp.mul (sub c a)).add ((sub b d).mul (sub cp ap))).add
    (((sub bp cp).mul (d.add a)).neg)).add (((sub b c).mul ap).neg)



/-- All four inverse arguments belong to the positive slope range. -/
def InputsInRange (s t : ℝ) : Prop :=
  t ∈ e8SlopeRange ∧ 2 * s + t ∈ e8SlopeRange ∧
    s + t ∈ e8SlopeRange ∧ s ∈ e8SlopeRange

/-- The order-four jet along `(s,t)=(s0+ds*u,t0+dt*u)`. -/
noncomputable def deltaTJet (s0 t0 ds dt : ℝ) : Jet5 :=
  deltaTGraph
    (affine qJet t0 dt)
    (affine qJet (2 * s0 + t0) (2 * ds + dt))
    (affine qJet (s0 + t0) (ds + dt))
    (affine qJet s0 ds)
    (affine qPrimeJet t0 dt)
    (affine qPrimeJet (2 * s0 + t0) (2 * ds + dt))
    (affine qPrimeJet (s0 + t0) (ds + dt))










end GeneralCK.Certificates.E8TAxisDeltaDirectionalJet
end

section
namespace GeneralCK.Certificates.E8TAxisStableScalar

open GeneralCK.Reflection GeneralCK.Certificates.Reflection
open GeneralCK.E8AnalyticGerm







noncomputable def X (a : ℝ) : ℝ := Real.log 2 * r a / (2 * h a)


















































end GeneralCK.Certificates.E8TAxisStableScalar
end

section
namespace GeneralCK.Certificates.E8TAxisOneCellGeometry

open GeneralCK DyadicInterval E8TAxisOneCellArithmetic E8TAxisDeltaDirectionalJet Set








def InFirstCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ 3 / 40 ∧ tLower ≤ t ∧ t ≤ 1 / 50
















end GeneralCK.Certificates.E8TAxisOneCellGeometry
end

section
namespace GeneralCK.Certificates.E8TAxisFirstCellBridge

open GeneralCK E8TAxisOneCellGeometry E8TAxisMixedCoefficients
open E8TAxisDeltaDirectionalJet E8TAxisCenteredReplaySoundness
open E8TAxisOneCellArithmetic DyadicInterval







/-- Four raw inverse-jet boxes, ordered by the actual inverse arguments. -/
structure InverseBoxes (p : ℕ) where
  a : DyadicJet5Enclosure p
  b : DyadicJet5Enclosure p
  c : DyadicJet5Enclosure p
  d : DyadicJet5Enclosure p

def InverseBoxes.ContainsAt {p : ℕ} (b : InverseBoxes p) (s t : ℝ) : Prop :=
  b.a.Contains qJet t ∧ b.b.Contains qJet (2*s+t) ∧
    b.c.Contains qJet (s+t) ∧ b.d.Contains qJet s

def InverseBoxes.coeff {p : ℕ} (b : InverseBoxes p) (i j : ℕ) : DyadicInterval p :=
  mixedBox b.a b.b b.c b.d i j



















end GeneralCK.Certificates.E8TAxisFirstCellBridge
end

section
namespace GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor

open GeneralCK Set DyadicInterval
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisCenteredReplaySoundness E8TAxisBivariateTaylor
open E8TAxisOneCellGeometry

structure Data (p : ℕ) where
  ds : DyadicInterval p
  dt : DyadicInterval p
  coeff : ℕ → ℕ → DyadicInterval p

namespace Data

def term {p : ℕ} (b : Data p) (i j : ℕ) : DyadicInterval p :=
  (((b.coeff i (j + 1)).mul (E8TAxisReparamInterval.powI b.ds i)).mul
    (E8TAxisReparamInterval.powI b.dt j)).mul
      (ofInt p (i.factorial * j.factorial : ℕ)).recip

def replay {p : ℕ} (b : Data p) : DyadicInterval p :=
  ((((((((((((((b.coeff 0 1).add (b.term 0 1)).add (b.term 1 0)).add
    (b.term 0 2)).add (b.term 1 1)).add (b.term 2 0)).add
    (b.term 0 3)).add (b.term 1 2)).add (b.term 2 1)).add (b.term 3 0)).add
    (b.term 0 4)).add (b.term 1 3)).add (b.term 2 2)).add (b.term 3 1)).add (b.term 4 0)

def CenterEnclosed {p : ℕ} (b : Data p) (c : ℕ → ℕ → ℝ) : Prop :=
  (b.coeff 0 1).Contains (c 0 1) ∧
  (b.coeff 0 2).Contains (c 0 2) ∧
  (b.coeff 1 1).Contains (c 1 1) ∧
  (b.coeff 0 3).Contains (c 0 3) ∧
  (b.coeff 1 2).Contains (c 1 2) ∧
  (b.coeff 2 1).Contains (c 2 1) ∧
  (b.coeff 0 4).Contains (c 0 4) ∧
  (b.coeff 1 3).Contains (c 1 3) ∧
  (b.coeff 2 2).Contains (c 2 2) ∧
  (b.coeff 3 1).Contains (c 3 1)

def RemainderEnclosed {p : ℕ} (b : Data p) (r : ℕ → ℕ → ℝ) : Prop :=
  (b.coeff 0 5).Contains (r 0 5) ∧
  (b.coeff 1 4).Contains (r 1 4) ∧
  (b.coeff 2 3).Contains (r 2 3) ∧
  (b.coeff 3 2).Contains (r 3 2) ∧
  (b.coeff 4 1).Contains (r 4 1)





end Data



namespace Data







end Data





end GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor
end

section
namespace GeneralCK.Certificates.E8TAxisFirstCellCertifiedArithmetic
open DyadicInterval E8TAxisFirstCellBridge E8TAxisGeneralCenteredTaylor
open E8TAxisMixedCoefficients E8TAxisDeltaDirectionalJet
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev precision := E8TAxisOneCellArithmetic.precision

def centerBoxes : InverseBoxes precision :=
  ⟨E8TAxisFirstCellGraphCenterA.qJetBox,
   E8TAxisFirstCellGraphCenterB.qJetBox,
   E8TAxisFirstCellGraphCenterC.qJetBox,
   E8TAxisFirstCellGraphCenterD.qJetBox⟩

def wholeBoxes : InverseBoxes precision :=
  ⟨E8TAxisFirstCellGraphWholeA.qJetBox,
   E8TAxisFirstCellGraphWholeB.qJetBox,
   E8TAxisFirstCellGraphWholeC.qJetBox,
   E8TAxisFirstCellGraphWholeD.qJetBox⟩

def coeff : ℕ → ℕ → DyadicInterval precision
  | 0, 1 => ⟨96479987514856367516858254791171850106, 96479987514856367516858255460322082807⟩
  | 0, 2 => ⟨4519210457057521137229765139953619817928, 4519210457057521137229765142754871024084⟩
  | 1, 1 => ⟨5825744588294595774549217802970136549585, 5825744588294595774549217806423767163599⟩
  | 0, 3 => ⟨118582717436939698908153654194265207673308, 118582717436939698908153654197939640291448⟩
  | 1, 2 => ⟨229186523496188191082139692014847477648867, 229186523496188191082139692018822376660177⟩
  | 2, 1 => ⟨279368631586065225204327724262437028885490, 279368631586065225204327724267032203070671⟩
  | 0, 4 => ⟨1392332258135485598173151523468405107985501, 1392332258135485598173151523480329691160081⟩
  | 1, 3 => ⟨4720977068780883704213191717648165547815933, 4720977068780883704213191717660922554753666⟩
  | 2, 2 => ⟨8688810967106778156071161810391014491554469, 8688810967106778156071161810406505821818591⟩
  | 3, 1 => ⟨9973899596571059047491509856328455544911152, 9973899596571059047491509856351161025073887⟩
  | 0, 5 => ⟨-74457952780821296581695184168200523788038143009, 74439410165405833350584184507752176190924299801⟩
  | 1, 4 => ⟨-95583919609723943566368389130934515085249097355, 95286713356500406361469781387161486528407717914⟩
  | 2, 3 => ⟨-139821872536797064973641233530513361810108281260, 139281527327397602758618716250103032158006792900⟩
  | 3, 2 => ⟨-217913758159767110484324985942297847377869727958, 217201332945325891221317223286676926810141359572⟩
  | 4, 1 => ⟨-335941581950737157449126701072858963739140896963, 335500890137050531761979692516751135702897986125⟩
  | _, _ => ofInt precision 0

def data : Data precision :=
  ⟨E8TAxisOneCellArithmetic.ds, E8TAxisOneCellArithmetic.dt, coeff⟩











































end GeneralCK.Certificates.E8TAxisFirstCellCertifiedArithmetic
end

section
namespace GeneralCK.Certificates.E8TAxisPartitionKernel

open GeneralCK

structure Rect where
  s0 : ℝ
  s1 : ℝ
  t0 : ℝ
  t1 : ℝ

def Rect.Covers (r : Rect) (s t : ℝ) : Prop :=
  r.s0 ≤ s ∧ s ≤ r.s1 ∧ r.t0 ≤ t ∧ t ≤ r.t1

inductive Tree where
  | leaf
  | splitS (x : ℚ) (left right : Tree)
  | splitT (x : ℚ) (lower upper : Tree)












def CellPositive (r : Rect) : Prop :=
  ∀ s t : ℝ, E8Admissible s t → r.Covers s t → 0 < e8RegularDeltaT s t








end GeneralCK.Certificates.E8TAxisPartitionKernel
end

section
namespace GeneralCK.Certificates.E8TAxisFirstCellCertified
open GeneralCK Set E8TAxisOneCellGeometry E8TAxisFirstCellCertifiedArithmetic
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor





/-- Ten center and five whole-cell mixed derivative bounds, with no assumptions. -/
def MixedBounds : Prop :=
  data.CenterEnclosed (mixed qJet centerS centerT) ∧
    ∀ s t, InFirstCell s t → data.RemainderEnclosed (mixed qJet s t)







noncomputable def rectangle : E8TAxisPartitionKernel.Rect :=
  ⟨sLower, 3 / 40, tLower, 1 / 50⟩









end GeneralCK.Certificates.E8TAxisFirstCellCertified
end

section
namespace GeneralCK.Certificates.E8TAxisGeneratedGeometry

open E8TAxisPartitionKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

structure RatRect where
  s0 : ℚ
  s1 : ℚ
  t0 : ℚ
  t1 : ℚ
  deriving DecidableEq, Repr





noncomputable def RatRect.real (r : RatRect) : Rect :=
  { s0 := r.s0, s1 := r.s1, t0 := r.t0, t1 := r.t1 }







def certifiedFirstCell : RatRect := { s0 := (13500000000000000000000000000000000000000000000000000000000637236764453 / 200000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), s1 := (3 / 40 : ℚ), t0 := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), t1 := (1 / 50 : ℚ) }









end GeneralCK.Certificates.E8TAxisGeneratedGeometry
end


