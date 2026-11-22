-- Prove2me | Definitions.Def_NoHair_TwoCentreStandardEnd
-- name    : NoHair_TwoCentreStandardEnd
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T23:49:20.726433+00:00
-- url     : https://prove2.me/theorems/e589ae54-6876-4baf-82ad-26c5ea5f73a0
-- title:
--   The canonical asymptotically flat end of the two-centre spacetime
-- statement:
--   The canonical asymptotically flat end of the equal-mass, two-centre Majumdar–Papapetrou model as an element of the no-hair mission's `AsymptoticallyFlatEnd` type. Its explicit chart is the map from isotropic coordinates to the advanced spacetime, its cutoff radius is 2, and its decay constant is 64. The metric, its first coordinate derivatives and the Faraday tensor satisfy the corresponding decay estimates. The construction proves the required pullback identities and equivariance of the chart under time translation. The four projection identities give direct access to the end's region, chart, radius and decay constant.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696. Coordinate pullbacks and decay estimates verified in https://prove2.me/theorems/88e17b35-990e-49b3-afed-000cfea2f033 and https://prove2.me/theorems/4f53689b-31b8-4da5-8988-3877b29b410b.

import Definitions.Def_NoHair_TwoCentreAdvanced
import Definitions.Def_NoHair_TwoCentreSpacetime
import Definitions.Def_NoHair_spacetime
import Definitions.Def_NoHair_TwoCentreIsotropic
import Definitions.Def_NoHair_TwoCentreBlackHole
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
/-! Canonical two-centre asymptotically flat end, its explicit radius, chart and decay constant. The construction contains the coordinate computations that yield its defining fields. -/
set_option linter.all false
namespace TwoCentreEndCollar

open Set Filter Topology
open scoped ContDiff

namespace NoHair.TwoCentre.Advanced
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Advanced

noncomputable section

theorem collar_positive {p : ℝ × ℝ} (hr : |p.1| < 1 / 4)
    (hc : |p.2| ≤ 1) :
    0 < 4 + p.1 ^ 2 - 4 * p.1 * p.2 ∧ 1 < distanceToOther p ∧ 0 < H p := by
  have hprod : |p.1 * p.2| < 1 / 4 := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg p.1)]
  have hsq : (1 : ℝ) ^ 2 < 4 + p.1 ^ 2 - 4 * p.1 * p.2 := by
    nlinarith [(abs_lt.mp hprod).2, sq_nonneg p.1]
  have hd : 1 < distanceToOther p := (Real.lt_sqrt (by norm_num)).2 hsq
  have hi : 0 < 1 / distanceToOther p := one_div_pos.mpr (by linarith)
  have hi' : 1 / distanceToOther p < 1 := (div_lt_one (by linarith)).2 hd
  refine ⟨by linarith, hd, ?_⟩
  unfold H
  nlinarith [mul_nonneg (show 0 ≤ p.1 + 1 / 4 by linarith [(abs_lt.mp hr).1])
    (show 0 ≤ 1 + 1 / distanceToOther p by linarith)]

end
end NoHair.TwoCentre.Advanced

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Advanced
open NoHair.TwoCentre.Advanced


end TwoCentreEndCollar
namespace TwoCentreEndCoordinates

open _root_.NoHair _root_.NoHair.TwoCentre
open NoHair NoHair.TwoCentre Set Topology
open scoped ContDiff Manifold

namespace NoHair.TwoCentre.Cartesian
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian

theorem coordinates_time (t : ℝ) (x : E3) : coordinates t x 0 = t := rfl
theorem coordinates_spatial (t : ℝ) (x : E3) : spatial (coordinates t x) = x := by
  ext i
  simp [spatial, coordinates, Fin.cons_succ]

theorem coordinates_recover (z : E4) : coordinates (z 0) (spatial z) = z := by
  ext i
  refine Fin.cases rfl (fun j => ?_) i
  simp [spatial, coordinates, Fin.cons_succ]

theorem spatial_smooth : ContDiff ℝ ∞ spatial :=
  contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))

theorem coordinates_smooth : ContDiff ℝ ∞ (fun p : ℝ × E3 => coordinates p.1 p.2) := by
  apply contDiff_euclidean.2
  intro i
  refine Fin.cases (by exact contDiff_fst) (fun j => ?_) i
  simp only [coordinates, WithLp.ofLp_toLp, Fin.cons_succ]
  fun_prop

theorem unit_norm : ‖unitAxis‖ = 1 := by simp [unitAxis]

theorem norm_squared (c : ℝ) (y : E4) :
    ‖spatial y - c • unitAxis‖ ^ 2 = squaredDistance c y := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [spatial, unitAxis, squaredDistance, PiLp.sub_apply, PiLp.smul_apply]

theorem exterior_iff (y : E4) :
    y ∈ exterior ↔ spatial y + unitAxis ≠ 0 ∧ spatial y + unitAxis ≠ (2 : ℝ) • unitAxis := by
  change 0 < squaredDistance (-1) y ∧ 0 < squaredDistance 1 y ↔ _
  rw [← norm_squared, ← norm_squared]
  simp only [neg_smul, one_smul, sub_neg_eq_add, sq_pos_iff, norm_ne_zero_iff,
    sub_ne_zero, two_smul]
  constructor
  · rintro ⟨hn, hh⟩
    exact ⟨hn, fun he => hh (add_right_cancel he)⟩
  · rintro ⟨hn, hh⟩
    exact ⟨hn, fun he => hh (congrArg (· + unitAxis) he)⟩

theorem expanded_norm {a : E3} (ha : a ≠ 0) : ‖expandRadius a‖ = ‖a‖ + 1 := by
  have h := norm_pos_iff.mpr ha
  rw [expandRadius, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

theorem contracted_norm {a : E3} (ha : 1 < ‖a‖) : ‖contractRadius a‖ = ‖a‖ - 1 := by
  have hn : 0 < ‖a‖ := by linarith
  have hinv : ‖a‖⁻¹ < 1 := by simpa [one_div] using (div_lt_one hn).2 ha
  rw [contractRadius, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hinv)]
  field_simp

theorem contract_expand {a : E3} (ha : a ≠ 0) : contractRadius (expandRadius a) = a := by
  have hn := norm_pos_iff.mpr ha
  rw [contractRadius, expanded_norm ha, expandRadius, smul_smul]
  rw [show (1 - (‖a‖ + 1)⁻¹) * (1 + ‖a‖⁻¹) = 1 by
    field_simp [hn.ne', show ‖a‖ + 1 ≠ 0 by linarith]; ring, one_smul]

theorem expand_contract {a : E3} (ha : 1 < ‖a‖) : expandRadius (contractRadius a) = a := by
  have hn : 0 < ‖a‖ := by linarith
  rw [expandRadius, contracted_norm ha, contractRadius, smul_smul]
  rw [show (1 + (‖a‖ - 1)⁻¹) * (1 - ‖a‖⁻¹) = 1 by
    field_simp [hn.ne', (sub_pos.mpr ha).ne']; ring, one_smul]

theorem pole_contract : contractRadius ((3 : ℝ) • unitAxis) = (2 : ℝ) • unitAxis := by
  simp only [contractRadius, norm_smul, Real.norm_eq_abs, unit_norm, mul_one, smul_smul]
  norm_num

theorem pole_expand : expandRadius ((2 : ℝ) • unitAxis) = (3 : ℝ) • unitAxis := by
  simp only [expandRadius, norm_smul, Real.norm_eq_abs, unit_norm, mul_one, smul_smul]
  norm_num

theorem shift_smooth {s : ℝ} (hs : s ≠ 0) : ContDiffAt ℝ ∞ timeShift s := by
  unfold timeShift
  fun_prop (disch := assumption)

theorem toAdvanced_smooth {y : E4} (hy : y ∈ exterior) : ContDiffAt ℝ ∞ toAdvanced y := by
  let a := fun z => spatial z + unitAxis
  have ha : a y ≠ 0 := ((exterior_iff y).mp hy).1
  have hs : ContDiffAt ℝ ∞ a y := spatial_smooth.contDiffAt.add contDiffAt_const
  have hn : ContDiffAt ℝ ∞ (fun z => ‖a z‖) y := hs.norm ℝ ha
  change ContDiffAt ℝ ∞ ((fun p : ℝ × E3 => coordinates p.1 p.2) ∘
    (fun z => (z 0 + timeShift ‖a z‖, expandRadius (a z)))) y
  apply coordinates_smooth.contDiffAt.comp y
  exact ((contDiffAt_piLp_apply (p := 2) (i := (0 : Fin 4))).add
    ((shift_smooth (norm_ne_zero_iff.mpr ha)).comp y hn)).prodMk
    ((contDiffAt_const.add (hn.inv (norm_ne_zero_iff.mpr ha))).smul hs)

theorem toIsotropic_smooth {z : E4} (hz : z ∈ outerRegion) : ContDiffAt ℝ ∞ toIsotropic z := by
  have h := hz.1
  have hz' : 0 < ‖spatial z‖ := by linarith
  have hs : ContDiffAt ℝ ∞ spatial z := spatial_smooth.contDiffAt
  have hn : ContDiffAt ℝ ∞ (fun y => ‖spatial y‖) z := hs.norm ℝ (norm_pos_iff.mp hz')
  change ContDiffAt ℝ ∞ ((fun p : ℝ × E3 => coordinates p.1 p.2) ∘
    (fun y => (y 0 - timeShift (‖spatial y‖ - 1), contractRadius (spatial y) - unitAxis))) z
  apply coordinates_smooth.contDiffAt.comp z
  exact ((contDiffAt_piLp_apply (p := 2) (i := (0 : Fin 4))).sub
    ((shift_smooth (sub_pos.mpr h).ne').comp z (hn.sub contDiffAt_const))).prodMk
    (((contDiffAt_const.sub (hn.inv hz'.ne')).smul hs).sub contDiffAt_const)

theorem global_chart : IsDiffeoOnto toAdvanced exterior outerRegion := by
  refine ⟨toIsotropic, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨hn, hp⟩ := (exterior_iff y).mp hy
    change 1 < ‖spatial (toAdvanced y)‖ ∧ spatial (toAdvanced y) ≠ _
    simp only [toAdvanced, coordinates_spatial, expanded_norm hn]
    refine ⟨by linarith [norm_pos_iff.mpr hn], ?_⟩
    intro hh
    apply hp
    simpa only [contract_expand hn, pole_contract] using congrArg contractRadius hh
  · intro z hz
    apply (exterior_iff _).mpr
    simp only [toIsotropic, coordinates_spatial, sub_add_cancel]
    refine ⟨norm_pos_iff.mp (by rw [contracted_norm hz.1]; exact sub_pos.mpr hz.1), ?_⟩
    intro hh
    apply hz.2
    simpa only [expand_contract hz.1, pole_expand] using congrArg expandRadius hh
  · intro y hy
    have h := ((exterior_iff y).mp hy).1
    simp only [toIsotropic, toAdvanced, coordinates_time, coordinates_spatial, expanded_norm h,
      add_sub_cancel_right, contract_expand h, coordinates_recover]
  · intro z hz
    simp only [toAdvanced, toIsotropic, coordinates_time, coordinates_spatial, sub_add_cancel,
      contracted_norm hz.1, expand_contract hz.1, coordinates_recover]
  · exact fun y hy => (toAdvanced_smooth hy).contMDiffAt.contMDiffWithinAt
  · exact fun z hz => (toIsotropic_smooth hz).contMDiffAt.contMDiffWithinAt

end NoHair.TwoCentre.Cartesian

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian
open NoHair.TwoCentre.Cartesian


end TwoCentreEndCoordinates
namespace TwoCentreEndTensorPullbacks

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace NoHair.TwoCentre.Model.Curves
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model

noncomputable section

def radialSpeed (z : E4) (w : E4) : ℝ := ⟪angularDirection z, spatial w⟫

theorem spatial_inner (w v : E4) :
    ⟪spatial w, spatial v⟫ = w 1 * v 1 + w 2 * v 2 + w 3 * v 3 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, spatial]
  ring

theorem radialSpeed_coords (z w : E4) :
    radialSpeed z w = dr z 1 * w 1 + dr z 2 * w 2 + dr z 3 * w 3 := by
  unfold radialSpeed
  rw [← Model.spatial_coordinates 0 (angularDirection z), spatial_inner]
  rfl

theorem metric_eval (z : manifold) (v w : E4) :
    metric z v w =
    Advanced.gvv (parameters z) * v 0 * w 0
    + Advanced.gvr (parameters z) * (v 0 * radialSpeed z w + radialSpeed z v * w 0)
    + Advanced.grr (parameters z) * radialSpeed z v * radialSpeed z w
    + Advanced.angularScale (parameters z) / ‖spatial z‖ ^ 2 *
      (⟪spatial v, spatial w⟫ - radialSpeed z v * radialSpeed z w) := by
  change Matrix.toLinearMap₂' ℝ (metricCoeffs z) (WithLp.ofLp v) (WithLp.ofLp w) = _
  rw [Matrix.toLinearMap₂'_apply (R := ℝ) (metricCoeffs z : Matrix (Fin 4) (Fin 4) ℝ) (WithLp.ofLp v) (WithLp.ofLp w), spatial_inner]
  simp only [radialSpeed_coords, Fin.sum_univ_four, smul_eq_mul, metricCoeffs]
  have hd : dr z 0 = 0 := rfl
  simp (config := {decide := true}) [dt, spatialDelta, hd]
  ring

end
end NoHair.TwoCentre.Model.Curves

namespace NoHair.TwoCentre.Advanced
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Advanced
noncomputable section
theorem gap_factor {p : ℝ × ℝ} (harg : 0 < 4 + p.1 ^ 2 - 4 * p.1 * p.2) :
    H p - H₀ p = p.1 ^ 2 * gapCoeff p := by
  have hd : 0 < distanceToOther p := Real.sqrt_pos.2 harg
  have hd2 : distanceToOther p ^ 2 = 4 + p.1 ^ 2 - 4 * p.1 * p.2 :=
    Real.sq_sqrt harg.le
  unfold H H₀ gapCoeff
  field_simp [hd.ne', show 2 + distanceToOther p ≠ 0 by linarith]
  linear_combination -p.1 * hd2

theorem coefficient_analytic {p : ℝ × ℝ}
    (harg : 0 < 4 + p.1 ^ 2 - 4 * p.1 * p.2) (hH : 0 < H p) :
    ∀ f ∈ [gvv, gvr, grr, angularScale, potentialV, potentialR], AnalyticAt ℝ f p := by
  have hd : 0 < distanceToOther p := Real.sqrt_pos.2 harg
  have hd' : 0 < 2 + distanceToOther p := by linarith
  have ds : ContDiffAt ℝ ω distanceToOther p := by
    unfold distanceToOther
    exact (show ContDiffAt ℝ ω (fun q : ℝ × ℝ => 4 + q.1 ^ 2 - 4 * q.1 * q.2) p
      by fun_prop).sqrt harg.ne'
  have hs : ContDiffAt ℝ ω H p := by unfold H; fun_prop (disch := positivity)
  have h0s : ContDiffAt ℝ ω H₀ p := by unfold H₀; fun_prop
  have cs : ContDiffAt ℝ ω gapCoeff p := by unfold gapCoeff; fun_prop (disch := positivity)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> apply ContDiffAt.analyticAt <;>
    first | unfold gvv | unfold gvr | unfold grr | unfold angularScale | unfold potentialV |
      unfold potentialR
  all_goals fun_prop (disch := positivity)

theorem match_exterior {p : ℝ × ℝ} (hr : p.1 ≠ 0) (hH : H p ≠ 0)
    (hgap : H p - H₀ p = p.1 ^ 2 * gapCoeff p) :
    grr p = (H p ^ 4 - H₀ p ^ 4) / (p.1 ^ 2 * H p ^ 2) ∧
      potentialR p = -(H₀ p ^ 2 / (p.1 * H p)) + H₀ p / p.1 := by
  constructor
  · unfold grr
    field_simp [hr, hH]
    linear_combination -(H p + H₀ p) * (H p ^ 2 + H₀ p ^ 2) * hgap
  · unfold potentialR
    field_simp [hr, hH]
    linear_combination -H₀ p * hgap


end
end NoHair.TwoCentre.Advanced

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

abbrev AM (f : E4 → ℝ) (z : E4) := ContDiffAt ℝ ω f z
theorem spatial_an : ContDiff ℝ ω spatial :=
  contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))
theorem coordinate_an : ContDiff ℝ ω (fun p : ℝ × E3 => coordinates p.1 p.2) := by
  apply contDiff_euclidean.2
  intro i
  refine Fin.cases (by exact contDiff_fst) (fun j => ?_) i
  simp only [coordinates, WithLp.ofLp_toLp, Fin.cons_succ]
  fun_prop

theorem partial_an {f : E4 → ℝ} {z : E4} (hf : AM f z) (i : Fin 4) : AM (coordPartial f i) z :=
  (hf.fderiv_right (m := ω) (by simp)).clm_apply contDiffAt_const

theorem unit_inner (x : E3) : ⟪x,unitAxis⟫ = x 0 := by
  simp [unitAxis,PiLp.inner_apply]

theorem param_norm {z : E4} (hp : 0 < ‖spatial z‖) :
    ‖angularDirection z‖ = 1 := by
  rw [angularDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']

theorem radius_data (z : manifold) :
    0 < ‖spatial z‖ ∧
    0 < 4 + (parameters z).1^2 - 4*(parameters z).1*(parameters z).2 ∧
    0 < Advanced.H (parameters z) ∧ 0 < Advanced.H₀ (parameters z) := by
  let p := parameters z
  let n := angularDirection z
  let r := p.1
  have hsize : (3 : ℝ)/4 < ‖spatial z‖ := z.property.1
  have hp : 0 < ‖spatial z‖ := by linarith
  have hn : ‖n‖ = 1 := param_norm hp
  have hc : |p.2| ≤ 1 := by
    change |n 0| ≤ 1
    simpa only [Real.norm_eq_abs, hn] using PiLp.norm_apply_le n 0
  have hela : (4 + p.1^2 - 4*p.1*p.2) = ‖r • n - (2:ℝ) • unitAxis‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, unit_inner,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hn]
    have he : n 0 = p.2 := rfl
    rw [he]
    simp [unitAxis,sq_abs,r]
    ring
  have har : 0 < 4 + p.1 ^ 2 - 4*p.1*p.2 := by
    rw [hela,sq_pos_iff,norm_ne_zero_iff,sub_ne_zero]
    intro h
    have hs := congrArg norm h
    simp [norm_smul,Real.norm_eq_abs,hn,unitAxis] at hs
    have hr : r=2 := by
      have hrg : -(1/4:ℝ) < r := by dsimp [r,p,parameters];linarith
      rcases le_or_gt 0 r with hpos | hneg
      · rwa [abs_of_nonneg hpos] at hs
      · rw [abs_of_neg hneg] at hs; linarith
    rw [hr] at h
    have hdir : n = unitAxis := (smul_right_injective (M := E3) (by norm_num : (2:ℝ) ≠ 0)) h
    have hre : ‖spatial z‖ = 3 := by change ‖spatial z‖ - 1 = 2 at hr; linarith
    apply z.property.2
    calc spatial z = ‖spatial z‖ • n := by simp [n,angularDirection,smul_smul,hp.ne']
         _ = (3:ℝ) • unitAxis := by rw [hre,hdir]
  have hH : 0 < Advanced.H p := by
    by_cases hnon : 0 < p.1
    · unfold Advanced.H
      have hd : 0 < Advanced.distanceToOther p := Real.sqrt_pos.2 har
      positivity
    · have hr : |p.1| < 1/4 := by apply abs_lt.mpr; change - (1/4:ℝ) < ‖spatial z‖ - 1 ∧ _; constructor <;> linarith
      exact (_root_.TwoCentreEndCollar.NoHair.TwoCentre.Advanced.collar_positive hr hc).2.2
  exact ⟨hp,har,hH,by unfold Advanced.H₀; change 0 < 1 + 3/2 * (‖spatial z‖ - 1);linarith⟩

theorem reg_data (z : manifold) :
    (∀ i j, AM (fun x => metricCoeffs x i j) z) ∧ (∀ i, AM (potential i) z) ∧
    (∀ i j, AM (fun x => faradayCoeffs x i j) z) ∧
    (ContDiffAt ℝ ω (fun x : E4 => coordinates 1
      (-(Advanced.gvr (parameters x) / (1+Advanced.grr (parameters x)^2)) • angularDirection x)) (z:E4)) := by
  obtain ⟨hp,harg,hH,_⟩ := radius_data z
  have hnorm := spatial_an.contDiffAt.norm ℝ (norm_pos_iff.mp hp)
  have hdire : ContDiffAt ℝ ω angularDirection (z:E4) :=
    (hnorm.inv hp.ne').smul spatial_an.contDiffAt
  have hparams : ContDiffAt ℝ ω parameters (z:E4) :=
    (hnorm.sub contDiffAt_const).prodMk ((contDiffAt_piLp_apply (p := 2) (i := (0 : Fin 3))).comp (z:E4) hdire)
  have hfn (f : ℝ × ℝ → ℝ) (hf : f ∈ [Advanced.gvv, Advanced.gvr, Advanced.grr, Advanced.angularScale,
        Advanced.potentialV, Advanced.potentialR]) : AM (fun x => f (parameters x)) z :=
    ((Advanced.coefficient_analytic harg hH f hf).contDiffAt).comp (z:E4) hparams
  have hvv := hfn _ (by simp : Advanced.gvv ∈ _)
  have hvr := hfn _ (by simp : Advanced.gvr ∈ _)
  have hrr := hfn _ (by simp : Advanced.grr ∈ _)
  have ha := hfn _ (by simp : Advanced.angularScale ∈ _)
  have hv := hfn _ (by simp : Advanced.potentialV ∈ _)
  have hav := hfn _ (by simp : Advanced.potentialR ∈ _)
  have hdr (i : Fin 4) : AM (fun x => dr x i) z := by
    refine Fin.cases (by exact contDiffAt_const) (fun j => ?_) i
    exact (contDiffAt_piLp_apply (p := 2) (i := j)).comp (z:E4) hdire
  have hpot (i : Fin 4) : AM (potential i) z :=
    (hv.mul contDiffAt_const).add (hav.mul (hdr i))
  refine ⟨?_, hpot, fun i j => (partial_an (hpot j) i).sub (partial_an (hpot i) j), ?_⟩
  · intro i j
    exact (((hvv.mul contDiffAt_const).mul contDiffAt_const).add
      (hvr.mul ((contDiffAt_const.mul (hdr j)).add ((hdr i).mul contDiffAt_const))) |>.add
      ((hrr.mul (hdr i)).mul (hdr j))).add
      ((ha.div (hnorm.pow 2) (pow_ne_zero 2 hp.ne')).mul (contDiffAt_const.sub ((hdr i).mul (hdr j))))
  · have hspace := ((hvr.div ((contDiffAt_const (c := (1:ℝ))).add (hrr.pow 2)) (by positivity)).neg.smul hdire)
    exact coordinate_an.contDiffAt.comp (z:E4) ((contDiffAt_const (c := (1:ℝ))).prodMk hspace)

end
end NoHair.TwoCentre.Model.Geo

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators

namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

end
end NoHair.TwoCentre.Model.Geo

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

theorem val_diff (z : manifold) : HasMFDerivAt 𝓘(ℝ,E4) 𝓘(ℝ,E4) (Subtype.val : manifold → E4) z
    (ContinuousLinearMap.id ℝ E4) := by
  have hd : MDifferentiableAt 𝓘(ℝ,E4) 𝓘(ℝ,E4) (Subtype.val : manifold → E4) z :=
    contMDiff_subtype_val.mdifferentiableAt (n := (1:ℕ∞ω)) one_ne_zero
  have he : mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) (Subtype.val : manifold → E4) z =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := 𝓘(ℝ,E4)) (x := z)
  exact he ▸ hd.hasMFDerivAt

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem line_deriv (y v : E4) : HasDerivAt (fun t : ℝ => y+t • v) v 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y

def spatialL : E4 →L[ℝ] E3 := LinearMap.toContinuousLinearMap {
  toFun := spatial, map_add' := fun _ _ => by ext; rfl, map_smul' := fun _ _ => by ext; rfl }

theorem norm_der {f : ℝ → E3} {v : E3} {t : ℝ} (h : HasDerivAt f v t) (hn : 0 < ‖f t‖) :
    HasDerivAt (fun s => ‖f s‖) ⟪‖f t‖⁻¹ • f t,v⟫ t := by
  have hs := h.norm_sq.sqrt (pow_ne_zero 2 hn.ne')
  simp only [Real.sqrt_sq (norm_nonneg _)] at hs
  convert! hs using 1
  rw [real_inner_smul_left]
  field_simp
  <;> ring

theorem shift_der {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt timeShift ((1+(3/2:ℝ)*r)^2/r^2) r := by
  have h : HasDerivAt timeShift (9 * 1 / 4 + 3 * r⁻¹ - (0 * r - 1 * 1)/r^2) r := by
    unfold timeShift
    exact ((((hasDerivAt_id r).const_mul 9).div_const 4).add ((Real.hasDerivAt_log hr).const_mul 3)).sub
      ((hasDerivAt_const r (1:ℝ)).div (hasDerivAt_id r) hr)
  convert h using 1
  field_simp
  <;> ring

theorem partial_from_line {f : E4 → ℝ} {z v : E4} {k : ℝ}
    (hd : DifferentiableAt ℝ f z) (h : HasDerivAt (fun t : ℝ => f (z+t • v)) k 0) :
    fderiv ℝ f z v = k := by
  have hd' : HasFDerivAt f (fderiv ℝ f z) (z+(0:ℝ) • v) := by simpa using hd.hasFDerivAt
  exact (hd'.comp_hasDerivAt 0 (line_deriv z v)).unique h

theorem second_symm {f : E4 → ℝ} {z : E4} (hf : AM f z) (i j : Fin 4) :
    coordPartial (coordPartial f i) j z = coordPartial (coordPartial f j) i z := by
  have hd := (hf.fderiv_right (m := ω) (by simp)).differentiableAt (by simp)
  have ev (k l : Fin 4) : coordPartial (coordPartial f k) l z =
      fderiv ℝ (fderiv ℝ f) z (coordBasis l) (coordBasis k) := by
    unfold coordPartial
    let A := ContinuousLinearMap.apply ℝ ℝ (coordBasis k)
    have h := A.hasFDerivAt.comp z hd.hasFDerivAt
    exact DFunLike.congr_fun h.fderiv (coordBasis l)
  rw [ev,ev]
  exact hf.isSymmSndFDerivAt_of_omega _ _

end
end NoHair.TwoCentre.Model.Geo

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

def sourceA (y : E4) := spatial y + unitAxis
def sourceR (y : E4) := ‖sourceA y‖
def sourceN (y : E4) := (sourceR y)⁻¹ • sourceA y
def sourceSpeed (y v : E4) := ⟪sourceN y,spatial v⟫

theorem dist_squared (c : ℝ) (y : E4) :
    ‖spatial y - c • unitAxis‖^2 = squaredDistance c y := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [spatial, unitAxis, squaredDistance, PiLp.sub_apply, PiLp.smul_apply]

theorem exterior_open : IsOpen exterior := by
  have h (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance;fun_prop
  exact (isOpen_lt continuous_const (h (-1))).inter (isOpen_lt continuous_const (h 1))

theorem left_pos {y : E4} (hy : y ∈ exterior) : 0 < sourceR y := by
  have h : 0 < squaredDistance (-1) y := hy.1
  rw [← dist_squared, neg_one_smul, sub_neg_eq_add] at h
  exact lt_of_le_of_ne (norm_nonneg _) (fun he => by
    change 0 = ‖spatial y+unitAxis‖ at he; rw [← he] at h; norm_num at h)

theorem source_unit {y : E4} (hy : y ∈ exterior) : ‖sourceN y‖=1 := by
  have h := left_pos hy
  change ‖(sourceR y)⁻¹ • sourceA y‖=1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr h)]
  exact inv_mul_cancel₀ h.ne'

theorem adv_spatial {y : E4} (hy : y ∈ exterior) :
    spatial (toAdvanced y) = (1+sourceR y) • sourceN y := by
  change spatial (coordinates _ _) = _
  rw [spatial_coordinates]
  change (1+(sourceR y)⁻¹) • sourceA y = (1+sourceR y) • ((sourceR y)⁻¹ • sourceA y)
  rw [smul_smul]
  congr 1
  field_simp [(left_pos hy).ne']
  <;> ring

theorem adv_norm {y : E4} (hy : y ∈ exterior) : ‖spatial (toAdvanced y)‖=1+sourceR y := by
  rw [adv_spatial hy,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith [left_pos hy]),source_unit hy,mul_one]

theorem adv_direction {y : E4} (hy : y ∈ exterior) : angularDirection (toAdvanced y)=sourceN y := by
  rw [angularDirection,adv_norm hy,adv_spatial hy,smul_smul,inv_mul_cancel₀ (by linarith [left_pos hy]),one_smul]

theorem adv_params {y : E4} (hy : y ∈ exterior) : parameters (toAdvanced y)=(sourceR y,sourceN y 0) := by
  simp [parameters,adv_norm hy,adv_direction hy]

theorem source_recover {y : E4} (hy : y ∈ exterior) : sourceR y • sourceN y = sourceA y := by
  rw [sourceN,smul_smul,mul_inv_cancel₀ (left_pos hy).ne',one_smul]

theorem adv_H {y : E4} (hy : y ∈ exterior) :
    Advanced.H (parameters (toAdvanced y)) = sourceR y*harmonicPotential y := by
  let r := sourceR y
  let n := sourceN y
  have hn : ‖n‖=1 := source_unit hy
  have hd : 4 + r ^ 2 - 4*r*n 0 = squaredDistance 1 y := by
    have he : ‖r • n - (2:ℝ) • unitAxis‖^2 = 4+r^2-4*r*n 0 := by
      rw [norm_sub_sq_real,real_inner_smul_left,real_inner_smul_right,unit_inner,norm_smul,norm_smul,hn]
      simp [unitAxis,sq_abs]; ring
    rw [← he,source_recover hy,← dist_squared]
    congr 2
    simp [sourceA,two_smul]
  have hdL : Real.sqrt (squaredDistance (-1) y)=r := by
    rw [← dist_squared,Real.sqrt_sq (norm_nonneg _)]
    simp [r,sourceR,sourceA]
  have hdR : Advanced.distanceToOther (r,n 0)=Real.sqrt (squaredDistance 1 y) := congrArg Real.sqrt hd
  rw [adv_params hy]
  change 1+r*(1+1/Advanced.distanceToOther (r,n 0)) = r*(1+1/Real.sqrt (squaredDistance (-1) y)+1/Real.sqrt (squaredDistance 1 y))
  rw [hdR,hdL]
  field_simp [(left_pos hy).ne',show r ≠ 0 from (left_pos hy).ne',
    (Real.sqrt_pos.mpr (show 0<squaredDistance 1 y from hy.2)).ne']
  <;> ring

theorem adv_mem {y : E4} (hy : y ∈ exterior) : toAdvanced y ∈ manifold := by
  obtain ⟨_,hm,_⟩ := _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian.global_chart
  obtain ⟨hr,hn⟩ := hm hy
  exact ⟨lt_trans (by norm_num) hr,hn⟩

theorem chart_coe {y : E4} (hy : y ∈ exterior) : (Model.chart y:E4) = toAdvanced y := by
  have : toAdvanced y ∈ spacetime := adv_mem hy
  simp [Model.chart,this]

theorem r_an {y : E4} (hy : y ∈ exterior) : AM sourceR y :=
  (spatial_an.contDiffAt.add (contDiffAt_const (c := unitAxis))).norm ℝ (norm_pos_iff.mp (left_pos hy))

theorem adv_an {y : E4} (hy : y ∈ exterior) : ContDiffAt ℝ ω toAdvanced y := by
  have ha : ContDiffAt ℝ ω sourceA y := spatial_an.contDiffAt.add contDiffAt_const
  have hr := r_an hy
  have hs : ContDiffAt ℝ ω timeShift (sourceR y) := by
    have hn := (left_pos hy).ne'
    unfold timeShift
    fun_prop (disch := assumption)
  have ht := (contDiffAt_piLp_apply (p := 2) (i := (0:Fin 4)) (𝕜 := ℝ) (n := ω) (y := y)).add (hs.comp y hr)
  have hx := ((contDiffAt_const (c := (1:ℝ))).add (hr.inv (left_pos hy).ne')).smul ha
  exact coordinate_an.contDiffAt.comp y (ht.prodMk hx)

set_option backward.isDefEq.respectTransparency false in
theorem chart_der {y : E4} (hy : y ∈ exterior) :
    (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) Model.chart y : E4 →L[ℝ] E4) = fderiv ℝ toAdvanced y := by
  have he : (Subtype.val ∘ Model.chart : E4 → E4) =ᶠ[𝓝 y] toAdvanced :=
    Filter.mem_of_superset (exterior_open.mem_nhds hy) (fun _ h => chart_coe h)
  have cont := (ContMDiffAt.subtypeVal_comp_iff manifold Model.chart y).mp
    (((adv_an hy).of_le (show (∞:ℕ∞ω) ≤ ω by simp)).contMDiffAt.congr_of_eventuallyEq he)
  have hd := (val_diff (Model.chart y)).comp y (cont.mdifferentiableAt (by simp)).hasMFDerivAt
  have hh := (hasMFDerivAt_iff_hasFDerivAt.mp hd).fderiv
  exact hh.symm.trans he.fderiv_eq

def packL : (ℝ × E3) →L[ℝ] E4 := LinearMap.toContinuousLinearMap {
  toFun := fun p => coordinates p.1 p.2
  map_add' := fun _ _ => by ext i; exact Fin.cases rfl (fun _ => rfl) i
  map_smul' := fun _ _ => by ext i; exact Fin.cases rfl (fun _ => rfl) i }

theorem r_line {y : E4} (hy : y ∈ exterior) (v:E4) :
    HasDerivAt (fun t : ℝ => sourceR (y+t • v)) (sourceSpeed y v) 0 := by
  have hx := (spatialL.hasFDerivAt.comp_hasDerivAt 0 (line_deriv y v)).add_const unitAxis
  have hh : 0 < ‖sourceA (y+(0:ℝ) • v)‖ := by rw [zero_smul,add_zero];exact left_pos hy
  have hs := norm_der (f := fun t => sourceA (y+t • v)) (v := spatial v) hx hh
  change HasDerivAt (fun t : ℝ => ‖sourceA (y+t • v)‖) ⟪‖sourceA y‖⁻¹ • sourceA y,spatial v⟫ 0
  simpa only [zero_smul,add_zero] using hs

theorem adv_der {y : E4} (hy : y ∈ exterior) (v : E4) :
    fderiv ℝ toAdvanced y v =
      coordinates (v 0 + ((1+3/2 * sourceR y)^2/sourceR y^2) * sourceSpeed y v)
        (((1+sourceR y)/sourceR y) • spatial v - (sourceSpeed y v / sourceR y) • sourceN y) := by
  let r := sourceR y
  let n := sourceN y
  let d := sourceSpeed y v
  let x := fun t : ℝ => y+t • v
  have hx := line_deriv y v
  have h0 : x 0=y := by simp [x]
  have hr := r_line hy v
  have hs := (shift_der (r := sourceR (x 0)) (by rw [h0];exact (left_pos hy).ne')).comp 0 hr
  have ht := (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) 0).hasFDerivAt.comp_hasDerivAt 0 hx
  have hu := (spatialL.hasFDerivAt.comp_hasDerivAt 0 hx).add_const unitAxis
  have hi := hr.inv (by change sourceR (x 0) ≠ 0;rw [h0];exact (left_pos hy).ne')
  have hd := ((hi.const_add 1).smul hu)
  have hpair := (ht.add hs).prodMk hd
  have hp := packL.hasFDerivAt.comp_hasDerivAt 0 hpair
  have hf := (adv_an hy).differentiableAt (by simp)
  have hf' : HasFDerivAt toAdvanced (fderiv ℝ toAdvanced y) (x 0) := by rw [h0];exact hf.hasFDerivAt
  have eq := (hf'.comp_hasDerivAt 0 hx).unique hp
  rw [eq]
  change coordinates (v 0 + (1+3/2*sourceR (x 0))^2/sourceR (x 0)^2*d)
    ((1+(sourceR (x 0))⁻¹) • spatial v+(-d/sourceR (x 0)^2) • sourceA (x 0)) = _
  rw [h0]
  congr 1
  rw [← source_recover hy,smul_smul]
  have hh : sourceR y ≠ 0 := (left_pos hy).ne'
  have eb : 1+(sourceR y)⁻¹=(1+sourceR y)/sourceR y := by field_simp;ring
  rw [eb,sub_eq_add_neg,← neg_smul]
  congr 2
  field_simp
  <;> ring


def J (y v : E4) := fderiv ℝ toAdvanced y v

theorem velocity_data {y : E4} (hy : y ∈ exterior) (v : E4) :
    J y v 0 = v 0 + (1+3/2 *sourceR y)^2/sourceR y^2 * sourceSpeed y v ∧
    spatial (J y v) = ((1+sourceR y)/sourceR y) • spatial v - (sourceSpeed y v/sourceR y) • sourceN y ∧
    Curves.radialSpeed (toAdvanced y) (J y v) = sourceSpeed y v := by
  have hv := adv_der hy v
  change J y v = _ at hv
  have hx := congrArg spatial hv
  rw [spatial_coordinates] at hx
  refine ⟨congrArg (fun x : E4 => x 0) hv,hx,?_⟩
  change ⟪angularDirection (toAdvanced y), spatial (J y v)⟫ = _
  rw [adv_direction hy,hx,inner_sub_right,real_inner_smul_right,real_inner_smul_right,real_inner_self_eq_norm_sq,source_unit hy]
  change (1+sourceR y)/sourceR y * sourceSpeed y v-sourceSpeed y v/sourceR y*1^2=sourceSpeed y v
  field_simp [(left_pos hy).ne']
  <;> ring

theorem tangential_pull {y : E4} (hy : y ∈ exterior) (v w : E4) :
    ⟪spatial (J y v),spatial (J y w)⟫ - sourceSpeed y v * sourceSpeed y w =
    (((1+sourceR y)/sourceR y)^2)*(⟪spatial v,spatial w⟫-sourceSpeed y v*sourceSpeed y w) := by
  rw [(velocity_data hy v).2.1,(velocity_data hy w).2.1]
  have hnn : ⟪sourceN y,sourceN y⟫ = 1 := by rw [real_inner_self_eq_norm_sq,source_unit hy];norm_num
  have hn (u:E4) : ⟪sourceN y,spatial u⟫ = sourceSpeed y u := rfl
  have hn' (u:E4) : ⟪spatial u,sourceN y⟫ = sourceSpeed y u := real_inner_comm _ _
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hnn,hn,hn']
  field_simp [(left_pos hy).ne']
  <;> ring

theorem model_metric_pull {y : E4} (hy : y ∈ exterior) (v w : E4) :
    metric (Model.chart y) (J y v) (J y w) =
      -(v 0*w 0)/harmonicPotential y^2 + harmonicPotential y^2*⟪spatial v,spatial w⟫ := by
  let p := parameters (toAdvanced y)
  let r := sourceR y
  let U := harmonicPotential y
  let H := Advanced.H p
  let h := Advanced.H₀ p
  have hR : 0 < r := left_pos hy
  have hp : p.1 = r := congrArg Prod.fst (adv_params hy)
  have hH : H = r*U := adv_H hy
  obtain ⟨_,harg,hhpos,_⟩ := radius_data (Model.chart y)
  rw [chart_coe hy] at harg hhpos
  have hpos : 0<H := hhpos
  have hU : U ≠ 0 := fun hU => hpos.ne' (by simp [hH,hU])
  have hmatch := (Advanced.match_exterior (hp.trans_ne hR.ne') hpos.ne' (Advanced.gap_factor harg)).1
  have hh : (1+3/2*sourceR y) = h := by change _ = 1+3/2*p.1;rw [hp]
  rw [Curves.metric_eval,chart_coe hy,(velocity_data hy v).2.2,(velocity_data hy w).2.2,
    (velocity_data hy v).1,(velocity_data hy w).1,tangential_pull hy,adv_norm hy,hh]
  change Advanced.gvv p*(v 0+h^2/r^2*sourceSpeed y v)*(w 0+h^2/r^2*sourceSpeed y w) +
    Advanced.gvr p*((v 0+h^2/r^2*sourceSpeed y v)*sourceSpeed y w+
      sourceSpeed y v*(w 0+h^2/r^2*sourceSpeed y w)) +
    Advanced.grr p*sourceSpeed y v*sourceSpeed y w+
    (H^2/(1+r)^2)*(((1+r)/r)^2*(⟪spatial v,spatial w⟫-sourceSpeed y v*sourceSpeed y w)) = _
  rw [hmatch]
  change -(p.1^2)/H^2 * _ * _ + h^2/H^2 * _ + ((H^4-h^4)/(p.1^2*H^2))*_*_ + _ = -(v 0*w 0)/U^2+U^2*_
  rw [hp,hH]
  field_simp [hR.ne',hU,show 1+r≠0 by linarith]
  <;> ring

theorem metric_chart {y : E4} (hy : y ∈ exterior) :
    pullbackCoeffs metric Model.chart y = isotropicMetric y := by
  funext i j
  unfold pullbackCoeffs
  rw [chart_der hy]
  change metric (Model.chart y) (J y (coordBasis i)) (J y (coordBasis j)) = _
  rw [model_metric_pull hy,Curves.spatial_inner]
  fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [coordBasis,isotropicMetric,Matrix.diagonal]
  <;> ring

def gauge (y : E4) := Real.log (sourceR y) + (3/2:ℝ)*sourceR y

theorem gauge_an {y : E4} (hy : y ∈ exterior) : AM gauge y := by
  have h := r_an hy
  exact (h.log (left_pos hy).ne').add (contDiffAt_const.mul h)

theorem gauge_partial {y : E4} (hy : y ∈ exterior) (i : Fin 4) :
    coordPartial gauge i y = (1+3/2*sourceR y)/sourceR y*sourceSpeed y (coordBasis i) := by
  apply partial_from_line ((gauge_an hy).differentiableAt (by simp))
  let v := coordBasis i
  have hr := r_line hy v
  have hd := (hr.log (by simpa using (left_pos hy).ne')).add (hr.const_mul (3/2:ℝ))
  convert! hd using 1
  simp only [zero_smul,add_zero]
  field_simp [(left_pos hy).ne']
  <;> ring

theorem potential_eval (z v : E4) :
    ∑ i, potential i z*v i = Advanced.potentialV (parameters z)*v 0 + Advanced.potentialR (parameters z)*Curves.radialSpeed z v := by
  have hr := Curves.spatial_inner (coordinates 0 (angularDirection z)) v
  rw [spatial_coordinates] at hr
  unfold Curves.radialSpeed
  rw [hr]
  have hz : coordinates 0 (angularDirection z) 0 = 0 := rfl
  simp (config := {decide := true}) [Fin.sum_univ_four,potential,dt,dr,hz]
  ring

theorem potential_chart {y : E4} (hy : y ∈ exterior) (i : Fin 4) :
    ∑ k, potential k (toAdvanced y)*(J y (coordBasis i) k) =
    electricPotential y*dt i + coordPartial gauge i y := by
  let p := parameters (toAdvanced y)
  let r := sourceR y
  let U := harmonicPotential y
  let H := Advanced.H p
  let h := Advanced.H₀ p
  let v := coordBasis i
  have hR : 0<r := left_pos hy
  have hp : p.1=r := congrArg Prod.fst (adv_params hy)
  have hH : H=r*U := adv_H hy
  obtain ⟨_,harg,hpos,_⟩ := radius_data (Model.chart y)
  rw [chart_coe hy] at harg hpos
  have hHp : 0<H := hpos
  have hU : U≠0 := fun hU => hHp.ne' (by simp [hH,hU])
  have hmatch := (Advanced.match_exterior (hp.trans_ne hR.ne') hHp.ne' (Advanced.gap_factor harg)).2
  have ht : v 0 = dt i := by fin_cases i <;> simp (config := {decide := true}) [v,dt,coordBasis]
  have hh : 1+3/2*sourceR y = h := by change _=1+3/2*p.1;rw [hp]
  rw [potential_eval,(velocity_data hy v).1,(velocity_data hy v).2.2,gauge_partial hy,hh]
  change (p.1/H)*(v 0+h^2/r^2*sourceSpeed y v)+Advanced.potentialR p*sourceSpeed y v =
    1/U*dt i + h/r*sourceSpeed y v
  rw [hmatch,ht]
  change (p.1/H)*_+(-(h^2/(p.1*H))+h/p.1)*_ = _
  rw [hp,hH]
  field_simp [hR.ne',hU]
  <;> ring

end
end NoHair.TwoCentre.Model.Geo

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Calc
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

abbrev AM := Geo.AM
def jac (f : E4 → E4) (j k : Fin 4) (z : E4) := coordPartial (fun w => f w k) j z
def pull (f : E4 → E4) (A : Fin 4 → E4 → ℝ) (j : Fin 4) (z : E4) :=
  ∑ k, A k (f z) * jac f j k z
def curl (A : Fin 4 → E4 → ℝ) (z : E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => coordPartial (A j) i z - coordPartial (A i) j z

theorem basis_expand (v : E4) : ∑ k, v k • coordBasis k = v := by
  simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,coordBasis] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v

theorem differential_expand (g : E4 → ℝ) (z v : E4) :
    fderiv ℝ g z v = ∑ k, v k * coordPartial g k z := by
  calc
    _ = fderiv ℝ g z (∑ k, v k • coordBasis k) := by rw [basis_expand]
    _ = _ := by simp [coordPartial]

theorem component_der {f : E4 → E4} {y : E4} (hf : DifferentiableAt ℝ f y) (j k : Fin 4) :
    jac f j k y = (fderiv ℝ f y (coordBasis j)) k := by
  let pr : E4 →L[ℝ] ℝ := (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) k)
  have h := pr.hasFDerivAt.comp y hf.hasFDerivAt
  exact DFunLike.congr_fun h.fderiv (coordBasis j)

theorem partial_mul {f g : E4 → ℝ} {y : E4} (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) (i : Fin 4) :
    coordPartial (fun z => f z*g z) i y = coordPartial f i y*g y + f y*coordPartial g i y := by
  have h := DFunLike.congr_fun (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv (coordBasis i)
  change fderiv ℝ (f*g) y (coordBasis i) = _
  rw [h]
  simp [coordPartial,smul_eq_mul]
  <;> ring

theorem partial_sum (f : Fin 4 → E4 → ℝ) {y : E4} (hf : ∀ j, DifferentiableAt ℝ (f j) y) (i : Fin 4) :
    coordPartial (fun z => ∑ j, f j z) i y = ∑ j, coordPartial (f j) i y := by
  unfold coordPartial
  rw [fderiv_fun_sum (fun j _ => hf j)]
  simp

theorem symmetric {g : E4 → ℝ} {y : E4} (hg : AM g y) (i j : Fin 4) :
    coordPartial (coordPartial g i) j y = coordPartial (coordPartial g j) i y := by
  have hd := (hg.fderiv_right (m := ω) (by simp)).differentiableAt (by simp)
  have ev (k l : Fin 4) : coordPartial (coordPartial g k) l y =
      fderiv ℝ (fderiv ℝ g) y (coordBasis l) (coordBasis k) := by
    let pr := ContinuousLinearMap.apply ℝ ℝ (coordBasis k)
    exact DFunLike.congr_fun (pr.hasFDerivAt.comp y hd.hasFDerivAt).fderiv (coordBasis l)
  rw [ev,ev]
  exact hg.isSymmSndFDerivAt_of_omega _ _

theorem exterior_derivative_pull {f : E4 → E4} {A : Fin 4 → E4 → ℝ} {y : E4}
    (hf : ContDiffAt ℝ ω f y) (hA : ∀ k, AM (A k) (f y)) (i j : Fin 4) :
    curl (pull f A) y i j =
    matrixBilin (curl A (f y)) (fderiv ℝ f y (coordBasis i)) (fderiv ℝ f y (coordBasis j)) := by
  let d := fderiv ℝ f y
  have df := hf.differentiableAt (by simp)
  have hc (k : Fin 4) : AM (fun x => f x k) y := (contDiffAt_piLp_apply (p := 2) (i := k)).comp y hf
  have hj (l k : Fin 4) : AM (jac f l k) y := Geo.partial_an (hc k) l
  have ha (k : Fin 4) : AM (fun z => A k (f z)) y := (hA k).comp y hf
  have hcomp (u k : Fin 4) : coordPartial (fun z => A k (f z)) u y =
      ∑ l, d (coordBasis u) l * coordPartial (A k) l (f y) := by
    have h := ((hA k).differentiableAt (by simp)).hasFDerivAt.comp y df.hasFDerivAt
    exact (DFunLike.congr_fun h.fderiv (coordBasis u)).trans (differential_expand _ _ _)
  have hterm (u v : Fin 4) : coordPartial (pull f A v) u y =
      ∑ k, ((∑ l, d (coordBasis u) l * coordPartial (A k) l (f y)) * d (coordBasis v) k +
            A k (f y) * coordPartial (jac f v k) u y) := by
    change coordPartial (fun z => ∑ k, A k (f z)*jac f v k z) u y = _
    rw [partial_sum (fun k z => A k (f z)*jac f v k z)
      (fun k => ((ha k).differentiableAt (by simp)).mul ((hj v k).differentiableAt (by simp)))]
    apply Finset.sum_congr rfl; intro k _
    rw [partial_mul ((ha k).differentiableAt (by simp)) ((hj v k).differentiableAt (by simp)),hcomp,
      component_der df]
  have hsym (k : Fin 4) : coordPartial (jac f j k) i y = coordPartial (jac f i k) j y := symmetric (hc k) _ _
  let V := d (coordBasis i)
  let W := d (coordBasis j)
  have eval : matrixBilin (curl A (f y)) V W =
      ∑ k, ∑ l, (curl A (f y) k l * V k * W l) := by
    change Matrix.toLinearMap₂' ℝ (curl A (f y)) (WithLp.ofLp V) (WithLp.ofLp W) = _
    rw [Matrix.toLinearMap₂'_apply (R := ℝ) (curl A (f y)) (WithLp.ofLp V) (WithLp.ofLp W)]
    simp only [smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  change coordPartial (pull f A j) i y - coordPartial (pull f A i) j y = matrixBilin _ V W
  rw [hterm,hterm,eval]
  simp only [hsym,Finset.sum_add_distrib,add_sub_add_right_eq_sub]
  simp only [Finset.sum_mul, curl,sub_mul,Finset.sum_sub_distrib, V,W,d]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl;intro l _; ring
  · apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl;intro l _; ring

end
end NoHair.TwoCentre.Model.Calc
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped ContDiff Manifold BigOperators
namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

theorem electric_an {y : E4} (hy : y ∈ exterior) : AM electricPotential y := by
  have hc (b:ℝ) : AM (squaredDistance b) y := by unfold AM squaredDistance;fun_prop
  have hi (b:ℝ) (h : 0<squaredDistance b y) : AM (inverseDistance b) y :=
    (contDiffAt_const (c := (1:ℝ))).div ((hc b).sqrt h.ne') (Real.sqrt_pos.mpr h).ne'
  have hU : 0<harmonicPotential y := by
    unfold harmonicPotential inverseDistance
    positivity
  exact (contDiffAt_const (c := (1:ℝ))).div
    (((contDiffAt_const (c := (1:ℝ))).add (hi (-1) hy.1)).add (hi 1 hy.2)) hU.ne'

theorem faraday_chart {y : E4} (hy : y ∈ exterior) :
    pullbackCoeffs faraday Model.chart y = TwoCentre.field y := by
  let f := toAdvanced
  let P := Calc.pull f potential
  have hA := reg_data (Model.chart y) |>.2.1
  rw [chart_coe hy] at hA
  have hmatch (i : Fin 4) {z : E4} (hz : z ∈ exterior) :
      P i z = electricPotential z * dt i + coordPartial gauge i z := by
    change (∑ k, potential k (toAdvanced z)*Calc.jac toAdvanced i k z)=_
    simp only [Calc.component_der ((adv_an hz).differentiableAt (by simp))]
    exact potential_chart hz i
  have hd (i j : Fin 4) : coordPartial (P i) j y =
      coordPartial electricPotential j y * dt i + coordPartial (coordPartial gauge i) j y := by
    have hh : P i =ᶠ[𝓝 y] (fun z => electricPotential z*dt i+coordPartial gauge i z) :=
      Filter.mem_of_superset (exterior_open.mem_nhds hy) (fun _ hz => hmatch i hz)
    have he := ((electric_an hy).differentiableAt (by simp)).hasFDerivAt.mul_const (dt i)
    have hg := (partial_an (gauge_an hy) i).differentiableAt (by simp) |>.hasFDerivAt
    have hs := he.add hg
    calc
      _ = fderiv ℝ (fun z => electricPotential z*dt i+coordPartial gauge i z) y (coordBasis j) :=
        DFunLike.congr_fun hh.fderiv_eq _
      _ = _ := by
        calc
          _ = (dt i • fderiv ℝ electricPotential y + fderiv ℝ (coordPartial gauge i) y) (coordBasis j) := DFunLike.congr_fun hs.fderiv _
          _ = _ := by simp [coordPartial,mul_comm]
  funext i j
  unfold pullbackCoeffs
  rw [chart_der hy]
  change matrixBilin (Calc.curl potential (Model.chart y:E4)) (fderiv ℝ f y (coordBasis i))
    (fderiv ℝ f y (coordBasis j)) = _
  rw [chart_coe hy,← Calc.exterior_derivative_pull (f := f) (adv_an hy) hA i j]
  change coordPartial (P j) i y - coordPartial (P i) j y = _
  rw [hd,hd,second_symm (gauge_an hy) j i]
  by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp [TwoCentre.field,dt,hi,hj]

end
end NoHair.TwoCentre.Model.Geo

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
open NoHair.TwoCentre.Model.Geo

end TwoCentreEndTensorPullbacks
namespace TwoCentreEndDecay

open _root_.NoHair _root_.NoHair.KNE
open NoHair NoHair.KNE Set Filter Topology

namespace NoHair.TwoCentre.Isotropic
open _root_.NoHair _root_.NoHair.TwoCentre

noncomputable section

def disp (c : ℝ) (i : Fin 4) (y : E4) : ℝ := ![0, y 1 - c, y 2, y 3] i
def delta (i k : Fin 4) : ℝ := if i = k ∧ i ≠ 0 then 1 else 0
def radius (c : ℝ) (y : E4) := Real.sqrt (squaredDistance c y)
def poleGrad (c : ℝ) (i : Fin 4) (y : E4) : ℝ := -disp c i y / radius c y ^ 3
def grad (i : Fin 4) (y : E4) := poleGrad (-1) i y + poleGrad 1 i y
theorem U_pos (y : E4) : 0 < harmonicPotential y := by
  have hn (c : ℝ) : 0 ≤ inverseDistance c y := by unfold inverseDistance; positivity
  unfold harmonicPotential
  linarith [hn (-1), hn 1]

theorem diff_disp (c : ℝ) (i : Fin 4) (y : E4) :
    HasCP (disp c i) y (delta i) := by
  fin_cases i
  · exact (HasCP.cst 0 y).congr_d (by intro k; simp [delta])
  · apply ((hasCP_coord y 1).sub (HasCP.cst c y)).congr_d
    intro k
    fin_cases k <;> norm_num [delta, coordBasis, PiLp.single_apply]
  · apply (hasCP_coord y 2).congr_d
    intro k
    fin_cases k <;> norm_num [delta, coordBasis, PiLp.single_apply] <;> decide
  · apply (hasCP_coord y 3).congr_d
    intro k
    fin_cases k <;> norm_num [delta, coordBasis, PiLp.single_apply] <;> decide

theorem diff_sqrt {f : E4 → ℝ} {y : E4} {df : Fin 4 → ℝ}
    (h : HasCP f y df) (hne : f y ≠ 0) :
    HasCP (fun z => Real.sqrt (f z)) y (fun i => df i / (2 * Real.sqrt (f y))) := by
  refine ⟨h.diff.sqrt hne, ?_⟩
  intro i
  have hn : f (y + (0 : ℝ) • coordBasis i) ≠ 0 := by simpa using hne
  simpa only [zero_smul, add_zero] using (h.line i).sqrt hn

theorem diff_radius (c : ℝ) {y : E4} (hy : 0 < squaredDistance c y) :
    HasCP (radius c) y (fun k => disp c k y / radius c y) := by
  have h : HasCP (squaredDistance c) y (fun k => 2 * disp c k y) := by
    apply ((((diff_disp c 1 y).pow 2).add ((diff_disp c 2 y).pow 2)).add
      ((diff_disp c 3 y).pow 2)).congr_d
    intro k
    fin_cases k <;> simp [disp, delta]
  apply (diff_sqrt h hy.ne').congr_d
  intro k
  unfold radius
  ring

theorem diff_pole (c : ℝ) {y : E4} (hy : 0 < squaredDistance c y) :
    HasCP (inverseDistance c) y (fun k => poleGrad c k y) := by
  have hr : 0 < radius c y := Real.sqrt_pos.2 hy
  apply ((HasCP.cst 1 y).div (diff_radius c hy) hr.ne').congr_d
  intro k
  unfold poleGrad
  field_simp [hr.ne']
  ring

theorem diff_U {y : E4} (hy : y ∈ exterior) :
    HasCP harmonicPotential y (fun k => grad k y) := by
  apply (((HasCP.cst 1 y).add (diff_pole (-1) hy.1)).add (diff_pole 1 hy.2)).congr_d
  intro k
  simp [grad]

theorem field_values {y : E4} (hy : y ∈ exterior) (i j : Fin 4) :
    field y i j = (if i = 0 then grad j y / harmonicPotential y ^ 2 else 0) -
      (if j = 0 then grad i y / harmonicPotential y ^ 2 else 0) := by
  have hd (k : Fin 4) : coordPartial electricPotential k y = -grad k y / harmonicPotential y ^ 2 := by
    have h := ((HasCP.cst 1 y).div (diff_U hy) (U_pos y).ne').eq k
    change coordPartial (fun w => 1 / harmonicPotential w) k y = _
    simpa only [zero_mul, one_mul, zero_sub] using h
  simp only [field, hd]
  split_ifs <;> ring

end
end NoHair.TwoCentre.Isotropic

open _root_.NoHair _root_.NoHair.KNE
open NoHair NoHair.KNE Set Filter Topology Matrix
open scoped BigOperators

namespace NoHair.TwoCentre.Isotropic
open _root_.NoHair _root_.NoHair.TwoCentre

noncomputable section

end
end NoHair.TwoCentre.Isotropic

open _root_.NoHair _root_.NoHair.KNE
open NoHair NoHair.KNE Set Filter Topology Matrix
open scoped BigOperators

namespace NoHair.TwoCentre.Isotropic
open _root_.NoHair _root_.NoHair.TwoCentre

noncomputable section

def metricSlope (u : ℝ) (i j : Fin 4) : ℝ :=
  if i = j then (if i = 0 then 2 / u ^ 3 else 2 * u) else 0

theorem dmetric {y : E4} (hy : y ∈ exterior) (i j k : Fin 4) :
    coordPartial (fun z => isotropicMetric z i j) k y =
      metricSlope (harmonicPotential y) i j * grad k y := by
  simp only [isotropicMetric, Matrix.diagonal_apply, metricSlope]
  split_ifs
  · have hn := (U_pos y).ne'
    have h := (((HasCP.cst 1 y).div ((diff_U hy).pow 2) (pow_ne_zero 2 hn)).neg).eq k
    rw [h]
    field_simp
    ring
  · rw [((diff_U hy).pow 2).eq k]
    ring
  · exact ((HasCP.cst 0 y).eq k).trans (zero_mul _).symm


end
end NoHair.TwoCentre.Isotropic

open _root_.NoHair
open NoHair Set Topology Matrix
open scoped BigOperators

namespace NoHair.TwoCentre.Isotropic
open _root_.NoHair _root_.NoHair.TwoCentre

noncomputable section

set_option maxHeartbeats 4500000 in
set_option maxHeartbeats 1800000 in
end
end NoHair.TwoCentre.Isotropic

open _root_.NoHair _root_.NoHair.KNE
open NoHair NoHair.KNE Set Matrix

namespace NoHair.TwoCentre.Isotropic
open _root_.NoHair _root_.NoHair.TwoCentre

noncomputable section

theorem radius_from_infinity {y : E4} (hr : 2 < spatialRadius y)
    {c : ℝ} (hc : c = -1 ∨ c = 1) : spatialRadius y / 2 ≤ radius c y := by
  have hr2 : spatialRadius y ^ 2 = y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hd2 : radius c y ^ 2 = (y 1 - c) ^ 2 + y 2 ^ 2 + y 3 ^ 2 :=
    Real.sq_sqrt (by unfold squaredDistance; positivity)
  have hd : 0 ≤ radius c y := Real.sqrt_nonneg _
  have hx : |y 1| ≤ spatialRadius y := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (y 2), sq_nonneg (y 3)]
  have hfar : spatialRadius y - 1 ≤ radius c y := by
    rcases hc with rfl | rfl <;> nlinarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  linarith

theorem displacement_le (c : ℝ) (i : Fin 4) (y : E4) : |disp c i y| ≤ radius c y := by
  have hr : 0 ≤ radius c y := Real.sqrt_nonneg _
  have hr2 : radius c y ^ 2 = (y 1 - c) ^ 2 + y 2 ^ 2 + y 3 ^ 2 :=
    Real.sq_sqrt (by unfold squaredDistance; positivity)
  have h1 : (y 1 - c) ^ 2 ≤ radius c y ^ 2 := by nlinarith [sq_nonneg (y 2), sq_nonneg (y 3)]
  have h2 : y 2 ^ 2 ≤ radius c y ^ 2 := by nlinarith [sq_nonneg (y 1 - c), sq_nonneg (y 3)]
  have h3 : y 3 ^ 2 ≤ radius c y ^ 2 := by nlinarith [sq_nonneg (y 1 - c), sq_nonneg (y 2)]
  fin_cases i
  · simpa [disp] using hr
  · change |y 1 - c| ≤ _
    rwa [← sq_le_sq₀ (abs_nonneg _) hr, sq_abs]
  · change |y 2| ≤ _
    rwa [← sq_le_sq₀ (abs_nonneg _) hr, sq_abs]
  · change |y 3| ≤ _
    rwa [← sq_le_sq₀ (abs_nonneg _) hr, sq_abs]

theorem far_pole_bounds {y : E4} (hr : 2 < spatialRadius y) {c : ℝ}
    (hc : c = -1 ∨ c = 1) :
    0 < squaredDistance c y ∧ inverseDistance c y ≤ 2 / spatialRadius y ∧
    ∀ i, |poleGrad c i y| ≤ 4 / spatialRadius y ^ 2 := by
  have h := radius_from_infinity hr hc
  have hd : 0 < radius c y := by linarith
  have hR : 0 < spatialRadius y := by linarith
  refine ⟨Real.sqrt_pos.mp hd, ?_, ?_⟩
  · change 1 / radius c y ≤ _
    apply (div_le_div_iff₀ hd hR).2
    linarith
  · intro i
    rw [poleGrad, abs_div, abs_neg, abs_of_pos (pow_pos hd _)]
    calc
      _ ≤ radius c y / radius c y ^ 3 := div_le_div_of_nonneg_right (displacement_le _ _ _) (by positivity)
      _ = 1 / radius c y ^ 2 := by field_simp [hd.ne']
      _ ≤ _ := (div_le_div_iff₀ (pow_pos hd 2) (pow_pos hR 2)).2 (by
        nlinarith [sq_le_sq' (by linarith : -(2 * radius c y) ≤ spatialRadius y)
          (by linarith : spatialRadius y ≤ 2 * radius c y)])

theorem asymptotic_decay {y : E4} (hr : 2 < spatialRadius y) :
    y ∈ exterior ∧ ∀ i j k,
    |isotropicMetric y i j - minkowski i j| ≤ 64 / spatialRadius y ∧
    |coordPartial (fun z => isotropicMetric z i j) k y| ≤ 64 / spatialRadius y ^ 2 ∧
    |field y i j| ≤ 64 / spatialRadius y ^ 2 := by
  obtain ⟨h₁, hI₁, hG₁⟩ := far_pole_bounds hr (c := -1) (Or.inl rfl)
  obtain ⟨h₂, hI₂, hG₂⟩ := far_pole_bounds hr (c := 1) (Or.inr rfl)
  have he : y ∈ exterior := ⟨h₁, h₂⟩
  have hR : 0 < spatialRadius y := by linarith
  have hU : 1 ≤ harmonicPotential y := by
    unfold harmonicPotential inverseDistance
    have h (c : ℝ) : 0 ≤ 1 / Real.sqrt (squaredDistance c y) := by positivity
    linarith [h (-1), h 1]
  have hU' : harmonicPotential y - 1 ≤ 4 / spatialRadius y := by
    unfold harmonicPotential
    simp only [div_eq_mul_inv] at hI₁ hI₂ ⊢
    linarith
  have h3 : harmonicPotential y ≤ 3 := by
    linarith [(div_lt_iff₀ hR).2 (by linarith : (4 : ℝ) < 2 * spatialRadius y)]
  have hgrad (i) : |grad i y| ≤ 8 / spatialRadius y ^ 2 := by
    unfold grad
    calc
      _ ≤ |poleGrad (-1) i y| + |poleGrad 1 i y| := abs_add_le _ _
      _ ≤ 4 / spatialRadius y ^ 2 + 4 / spatialRadius y ^ 2 := add_le_add (hG₁ i) (hG₂ i)
      _ = _ := by ring
  have hsq : 1 ≤ harmonicPotential y ^ 2 := by nlinarith [sq_nonneg (harmonicPotential y - 1)]
  have hcube : 1 ≤ harmonicPotential y ^ 3 := by
    simpa [pow_succ] using mul_le_mul hsq hU (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg _)
  have hmetric : harmonicPotential y ^ 2 - 1 ≤ 64 / spatialRadius y := by
    have hprod := mul_le_mul_of_nonneg_left (show harmonicPotential y + 1 ≤ 4 by linarith) (sub_nonneg.mpr hU)
    simp only [div_eq_mul_inv] at hU' ⊢
    nlinarith [inv_nonneg.mpr hR.le]
  have htmetric : |-(1 / harmonicPotential y ^ 2) - -1| ≤ 64 / spatialRadius y := by
    have hU0 := (U_pos y).ne'
    have heq : -(1 / harmonicPotential y ^ 2) - -1 =
        (harmonicPotential y ^ 2 - 1) / harmonicPotential y ^ 2 := by field_simp; ring
    rw [heq, abs_of_nonneg (by positivity : 0 ≤ (harmonicPotential y ^ 2 - 1) / harmonicPotential y ^ 2)]
    exact (div_le_self (sub_nonneg.mpr hsq) hsq).trans hmetric
  have hquot (i) : |grad i y / harmonicPotential y ^ 2| ≤ 8 / spatialRadius y ^ 2 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg (harmonicPotential y))]
    exact (div_le_self (abs_nonneg _) hsq).trans (hgrad i)
  refine ⟨he, ?_⟩
  intro i j k
  refine ⟨?_, ?_, ?_⟩
  · by_cases hij : i = j
    · subst j
      fin_cases i
      · exact htmetric
      all_goals change |harmonicPotential y ^ 2 - 1| ≤ _; rwa [abs_of_nonneg (sub_nonneg.mpr hsq)]
    · simp [isotropicMetric, minkowski, hij]
      positivity
  · rw [dmetric he, abs_mul]
    have hcoef : |metricSlope (harmonicPotential y) i j| ≤ 6 := by
      unfold metricSlope
      split_ifs
      · rw [abs_of_nonneg (by positivity)]
        linarith [div_le_self (by norm_num : (0 : ℝ) ≤ 2) hcube]
      · rw [abs_of_nonneg (by positivity : 0 ≤ 2 * harmonicPotential y)]
        linarith
      · norm_num
    have hp := mul_le_mul hcoef (hgrad k) (abs_nonneg _) (by norm_num)
    simp only [div_eq_mul_inv] at hp ⊢
    linarith [inv_nonneg.mpr (sq_nonneg (spatialRadius y))]
  · rw [field_values he]
    have hd : 0 ≤ 8 / spatialRadius y ^ 2 := by positivity
    have hi : |if i = 0 then grad j y / harmonicPotential y ^ 2 else 0| ≤ 8 / spatialRadius y ^ 2 := by
      split_ifs; exact hquot j; simpa using hd
    have hj : |if j = 0 then grad i y / harmonicPotential y ^ 2 else 0| ≤ 8 / spatialRadius y ^ 2 := by
      split_ifs; exact hquot i; simpa using hd
    apply (abs_sub _ _).trans
    apply (add_le_add hi hj).trans
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)

end
end NoHair.TwoCentre.Isotropic

open _root_.NoHair _root_.NoHair.TwoCentre
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Isotropic

end TwoCentreEndDecay

namespace TwoCentreEndConstruction
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped ContDiff Manifold

private theorem spatial_cont : Continuous spatial := by
  have h : ContDiff ℝ ∞ spatial := contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))
  exact h.continuous

theorem outer_open : IsOpen Model.outer := by
  have h : IsOpen outerRegion := (isOpen_lt continuous_const spatial_cont.norm).inter
    (isOpen_ne_fun spatial_cont continuous_const)
  exact h.preimage continuous_subtype_val

private theorem outer_subset : outerRegion ⊆ spacetime := by
  intro z hz
  exact ⟨lt_trans (by norm_num) hz.1, hz.2⟩

private theorem model_chart_val {y : E4} (hy : y ∈ exterior) :
    (Model.chart y : E4) = toAdvanced y := by
  obtain ⟨_, hmap, _⟩ := _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian.global_chart
  simp [Model.chart, outer_subset (hmap hy)]

theorem model_chart_diffeo : IsDiffeoOnto Model.chart exterior Model.outer := by
  obtain ⟨χ, hf, hb, hl, hr, hfs, hbs⟩ := _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian.global_chart
  have hm : MapsTo Model.chart exterior Model.outer := by
    intro y hy
    change (Model.chart y : E4) ∈ outerRegion
    rw [model_chart_val hy]
    exact hf hy
  refine ⟨χ ∘ Subtype.val, hm, (fun _ hy => hb hy), ?_, ?_, ?_, ?_⟩
  · intro y hy
    change χ (Model.chart y : E4) = y
    rw [model_chart_val hy, hl hy]
  · intro z hz
    apply Subtype.ext
    exact (model_chart_val (hb hz)).trans (hr hz)
  · intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff manifold Model.chart exterior y).mp
    exact hfs.congr (fun _ hz => model_chart_val hz) y hy
  · exact hbs.comp (contMDiff_subtype_val.contMDiffOn) (fun _ hz => hz)

private theorem restrict_chart {S : Set E4} (hS : IsOpen S) (hsub : S ⊆ exterior) :
    IsDiffeoOnto Model.chart S (Model.chart '' S) ∧ IsOpen (Model.chart '' S) := by
  obtain ⟨χ, hf, hb, hl, hr, hfs, hbs⟩ := model_chart_diffeo
  have him : Model.chart '' S = Model.outer ∩ χ ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hf (hsub hy), ?_⟩
      change χ (Model.chart y) ∈ S
      rwa [hl (hsub hy)]
    · rintro ⟨hz, hχ⟩
      exact ⟨χ z, hχ, hr hz⟩
  have hD : Model.chart '' S ⊆ Model.outer := him ▸ inter_subset_left
  refine ⟨⟨χ, fun y hy => mem_image_of_mem _ hy, ?_, hl.mono hsub, hr.mono hD,
    hfs.mono hsub, hbs.mono hD⟩, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [hl (hsub hy)]
    exact hy
  · rw [him]
    exact hbs.continuousOn.isOpen_inter_preimage outer_open hS

private theorem end_equivariant (s : ℝ) (y : E4) (hy : y ∈ exteriorRegion 2) :
    Model.chart (y + s • coordBasis 0) = flow s (Model.chart y) := by
  have hy' := (_root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic.asymptotic_decay (y := y) hy).1
  have ht : spatial (y + s • coordBasis 0) = spatial y := by
    ext i
    simp [spatial, coordBasis]
  have hs : spatialRadius (y + s • coordBasis 0) = spatialRadius y := by
    simp (config := {decide := true}) [spatialRadius, coordBasis]
  have hy₂ := (_root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic.asymptotic_decay (y := y + s • coordBasis 0) (by rw [hs]; exact hy)).1
  apply Subtype.ext
  rw [model_chart_val hy₂]
  change toAdvanced _ = coordinates ((Model.chart y : E4) 0 + s) (spatial (Model.chart y))
  rw [model_chart_val hy']
  simp only [toAdvanced, ht, Model.spatial_coordinates]
  congr 1
  change (y + s • coordBasis 0) 0 + _ = (y 0 + _) + s
  simp [coordBasis]
  ring

/-- The canonical asymptotically flat end in the two-centre isotropic chart. -/
noncomputable def standardEnd : AsymptoticallyFlatEnd metric faraday flow := by
  have hmatch (y : E4) (hy : y ∈ exterior) :
      pullbackCoeffs metric Model.chart y = isotropicMetric y ∧ pullbackCoeffs faraday Model.chart y = TwoCentre.field y :=
    ⟨_root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo.metric_chart hy,_root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo.faraday_chart hy⟩
  have hop : IsOpen (exteriorRegion 2) := isOpen_lt continuous_const (by unfold spatialRadius; fun_prop)
  have hsub : exteriorRegion 2 ⊆ exterior := fun y hy => (_root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic.asymptotic_decay (y := y) hy).1
  have hs (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance; fun_prop
  have heo : IsOpen exterior := (isOpen_lt continuous_const (hs (-1))).inter
    (isOpen_lt continuous_const (hs 1))
  have hd (y : E4) (hy : y ∈ exteriorRegion 2) (i j k : Fin 4) :
      coordPartial (fun z => pullbackCoeffs metric Model.chart z i j) k y =
      coordPartial (fun z => isotropicMetric z i j) k y := by
    have eqv : (fun z => pullbackCoeffs metric Model.chart z i j) =ᶠ[𝓝 y]
        (fun z => isotropicMetric z i j) := by
      filter_upwards [heo.mem_nhds (hsub hy)] with z hz using congrFun (congrFun (hmatch z hz).1 i) j
    unfold coordPartial
    rw [eqv.fderiv_eq]
  have charts := restrict_chart hop hsub
  exact {
    R := 2, ψ := Model.chart, C := 64, R_pos := by norm_num
    diffeo := charts.1, isOpen_image := charts.2, equivariant := end_equivariant
    metric_decay := by
      intro y hy i j
      rw [(hmatch y (hsub hy)).1]
      exact ((_root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic.asymptotic_decay (y := y) hy).2 i j 0).1
    metric_deriv_decay := by
      intro y hy i j k
      rw [hd y hy i j k]
      exact ((_root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic.asymptotic_decay (y := y) hy).2 i j k).2.1
    field_decay := by
      intro y hy i j
      rw [(hmatch y (hsub hy)).2]
      exact ((_root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic.asymptotic_decay (y := y) hy).2 i j 0).2.2 }


@[simp] theorem standardEnd_region : standardEnd.region = Model.chart '' exteriorRegion 2 := rfl
@[simp] theorem standardEnd_radius : standardEnd.R = 2 := rfl
@[simp] theorem standardEnd_chart : standardEnd.ψ = Model.chart := rfl
@[simp] theorem standardEnd_constant : standardEnd.C = 64 := rfl

end TwoCentreEndConstruction


