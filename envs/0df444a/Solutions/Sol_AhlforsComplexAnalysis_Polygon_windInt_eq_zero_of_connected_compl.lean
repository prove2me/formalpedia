-- Prove2me | solution 1 for AhlforsComplexAnalysis.Polygon.windInt_eq_zero_of_connected_compl
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:37:18.561159+00:00
-- url     : https://prove2.me/submissions/6ae3d563-743c-4487-81f2-ffff893cc7a7

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon
import Theorems.Thm_AhlforsComplexAnalysis_Polygon_windInt_locallyConstant
import Theorems.Thm_AhlforsComplexAnalysis_Polygon_windInt_tendsto_zero

set_option autoImplicit false

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

/-- The exterior of a closed ball in `ℂ` is preconnected. -/
lemma w3_isPreconnected_norm_gt (R : ℝ) : IsPreconnected {b : ℂ | R < ‖b‖} := by
  rcases lt_or_ge R 0 with hR | hR
  · have : {b : ℂ | R < ‖b‖} = univ := eq_univ_of_forall fun b => lt_of_lt_of_le hR (norm_nonneg b)
    rw [this]
    exact isPreconnected_univ
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hS : IsConnected (Metric.sphere (0 : ℂ) 1) := isConnected_sphere hrank 0 zero_le_one
  have himg := ((isConnected_Ioi (a := R)).prod hS).image (fun x : ℝ × ℂ => x.1 • x.2)
    (by fun_prop : Continuous fun x : ℝ × ℂ => x.1 • x.2).continuousOn
  convert himg.isPreconnected using 1
  ext b
  simp only [mem_ofPred_eq, mem_image, mem_prod, mem_Ioi, mem_sphere_iff_norm, sub_zero,
    Prod.exists]
  constructor
  · intro hb
    have hb0 : ‖b‖ ≠ 0 := by
      have : 0 < ‖b‖ := lt_of_le_of_lt hR hb
      exact this.ne'
    refine ⟨‖b‖, ‖b‖⁻¹ • b, ⟨hb, ?_⟩, smul_inv_smul₀ hb0 b⟩
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hb0]
  · rintro ⟨r, z, ⟨hr, hz⟩, rfl⟩
    rw [norm_smul, hz, mul_one, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hR hr)]
    exact hr

/-- `windInt l` is constant on a preconnected set missing the trace of a closed polygon. -/
lemma w3_const_of_preconnected {l : List ℂ} (hl : IsClosedPoly l) {V : Set ℂ}
    (hVc : IsPreconnected V) (hV : Disjoint V (polyTrace l)) {x y : ℂ}
    (hx : x ∈ V) (hy : y ∈ V) : windInt l x = windInt l y := by
  have hlc : IsLocallyConstant (fun z : V => windInt l z) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    rw [nhds_subtype, eventually_comap]
    filter_upwards [windInt_locallyConstant hl (Set.disjoint_left.mp hV z.2)] with u hu w hw
    subst hw
    exact hu
  have : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hVc
  exact hlc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

/-- A closed polygon has winding number zero around every point far from its trace. -/
lemma w3_eventually_zero {l : List ℂ} (hl : IsClosedPoly l) :
    ∃ R : ℝ, ∀ b : ℂ, R < ‖b‖ → windInt l b = 0 := by
  obtain ⟨R, hR⟩ := (polyTrace_isCompact l).isBounded.exists_norm_le
  refine ⟨R, fun b hb => ?_⟩
  have hdisj : Disjoint {b : ℂ | R < ‖b‖} (polyTrace l) :=
    Set.disjoint_left.mpr fun z hz hz' => not_lt.mpr (hR z hz') hz
  have hconst : ∀ x ∈ {b : ℂ | R < ‖b‖}, windInt l x = windInt l b := fun x hx =>
    w3_const_of_preconnected hl (w3_isPreconnected_norm_gt R) hdisj hx hb
  have hev : ∀ᶠ x in cocompact ℂ, R < ‖x‖ := tendsto_norm_cocompact_atTop.eventually_gt_atTop R
  have hlim : Tendsto (windInt l) (cocompact ℂ) (𝓝 (windInt l b)) :=
    tendsto_const_nhds.congr' (by filter_upwards [hev] with x hx using (hconst x hx).symm)
  exact tendsto_nhds_unique hlim (windInt_tendsto_zero l)

end AhlforsComplexAnalysis.Polygon

open AhlforsComplexAnalysis.Polygon

/-- Points outside `Ω`, where `Ω ⊇` the polygon and the complement of `Ω` in the Riemann sphere
is connected, have winding number zero. -/
theorem solution {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hc : IsConnected ((((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ))
    {l : List ℂ} (hl : IsClosedPoly l) (hlΩ : PolyIn Ω l) {a : ℂ} (ha : a ∉ Ω) :
    windInt l a = 0 := by
  set S : Set (OnePoint ℂ) := (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ with hS
  let N : OnePoint ℂ → ℂ := fun x => OnePoint.elim x 0 (windInt l)
  have hNinf : N OnePoint.infty = 0 := rfl
  have hNcoe : ∀ b : ℂ, N b = windInt l b := fun b => rfl
  have hloc : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, N y = N x := by
    intro x hx
    induction x using OnePoint.rec with
    | infty =>
      obtain ⟨R, hR⟩ := w3_eventually_zero hl
      rw [OnePoint.nhds_infty_eq, eventually_sup, eventually_map, eventually_pure,
        coclosedCompact_eq_cocompact]
      refine ⟨?_, rfl⟩
      filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with b hb
      rw [hNcoe, hR b hb, hNinf]
    | coe a' =>
      have ha' : a' ∉ Ω := fun h => hx ⟨a', h, rfl⟩
      have hat : a' ∉ polyTrace l := fun h => ha' (polyTrace_subset hlΩ h)
      rw [OnePoint.nhds_coe_eq, eventually_map]
      filter_upwards [windInt_locallyConstant hl hat] with b hb
      rw [hNcoe, hNcoe]
      exact hb
  have hlc : IsLocallyConstant (fun x : S => N x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    rw [nhds_subtype, eventually_comap]
    filter_upwards [hloc x x.2] with y hy z hz
    subst hz
    exact hy
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hc.isPreconnected
  have hinf : (OnePoint.infty : OnePoint ℂ) ∈ S := by
    rintro ⟨z, -, hz⟩
    exact OnePoint.coe_ne_infty z hz
  have haS : ((a : ℂ) : OnePoint ℂ) ∈ S := by
    rintro ⟨z, hz, hza⟩
    exact ha (OnePoint.coe_injective hza ▸ hz)
  have hEq := hlc.apply_eq_of_preconnectedSpace ⟨(a : OnePoint ℂ), haS⟩ ⟨OnePoint.infty, hinf⟩
  exact ((hNcoe a).symm.trans hEq).trans hNinf

#print axioms solution
