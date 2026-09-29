-- Prove2me | Definitions.Def_CK_GeneralCK_PsiEndpointPlaneGraph
-- name    : CK_GeneralCK_PsiEndpointPlaneGraph
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T12:02:05.089191+00:00
-- url     : https://prove2.me/theorems/daa041a2-8e31-4a76-93bd-020838d076ce
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiEndpointPlaneGraph` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiEndpointPlaneGraph` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiEndpointPlaneGraph` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiEndpointPlaneGraph (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiEndpointPlaneGraph.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneLevelUniqueness

-- ===== source module GeneralCK.PsiEndpointPlaneGraph =====
section

/-!
# Explicit parametrization of the first endpoint level

The first logarithmic level determines an explicit graph. Its physical
domain is a single open interval, proved from the sign of the one-variable
base derivative on its nonnegative locus. No asymptotic endpoint estimate
is needed for uniqueness of stationary contact.
-/

namespace GeneralCK.PsiEndpointPlane

open Set Filter

noncomputable def levelBase (A r : ℝ) : ℝ := singularPart r + A * Real.log r

theorem hasDerivAt_levelBase {A r : ℝ} (hr : 0 < r) :
    HasDerivAt (levelBase A) ((r ^ 2 + 2 * A * r - 1) / (2 * r ^ 2)) r := by
  have hd := (hasDerivAt_singularPart hr).add ((Real.hasDerivAt_log hr.ne').const_mul A)
  convert! hd using 1
  field_simp [hr.ne']
  ring

theorem levelBase_deriv_neg_of_nonneg {A r : ℝ} (hA : 0 ≤ A)
    (hr : r ∈ Ioo 0 1) (hbase : 0 ≤ levelBase A r) :
    deriv (levelBase A) r < 0 := by
  have hr0 := hr.1
  have hlog := mul_le_mul_of_nonneg_left (log_le_twice_sub_div_add hr0 hr.2.le) hA
  have hfactor : singularPart r + A * (2 * (r - 1) / (r + 1)) =
      (1 - r) / (2 * r * (1 + r)) * (1 - r ^ 2 - 4 * A * r) := by
    unfold singularPart
    field_simp
    ring
  have hbound : 0 ≤ (1 - r) / (2 * r * (1 + r)) * (1 - r ^ 2 - 4 * A * r) := by
    rw [← hfactor]
    unfold levelBase at hbase
    linarith
  have hcoef : 0 < (1 - r) / (2 * r * (1 + r)) := by
    exact div_pos (sub_pos.mpr hr.2) (by positivity)
  have hnumerator := (mul_nonneg_iff_of_pos_left hcoef).mp hbound
  have hsquare : r ^ 2 < 1 := by
    have hmul := mul_pos (sub_pos.mpr hr.2) (show 0 < 1 + r by linarith)
    nlinarith
  rw [(hasDerivAt_levelBase hr0).deriv]
  exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)

/-- A nonnegative value of the base forces every earlier value to be
strictly larger. This is the single-interval domain argument. -/
theorem levelBase_lt_earlier {A a b : ℝ} (hA : 0 ≤ A)
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (hab : a < b)
    (hbase : 0 ≤ levelBase A b) : levelBase A b < levelBase A a := by
  let f : ℝ → ℝ := fun x => levelBase A (-x)
  have hphysical (x : ℝ) (hx : x ∈ Icc (-b) (-a)) : -x ∈ Ioo 0 1 := by
    constructor <;> linarith [hx.1, hx.2, ha.1, hb.2]
  have hderiv (x : ℝ) (hx : x ∈ Icc (-b) (-a)) :
      HasDerivAt f (-(deriv (levelBase A) (-x))) x := by
    have hd := (hasDerivAt_levelBase (A := A) (hphysical x hx).1).differentiableAt.hasDerivAt
    convert! hd.comp x (hasDerivAt_id x).neg using 1 <;> simp [f]
  have hg := lt_of_deriv_pos_on_nonnegative (f := f) (a := -b) (b := -a)
    (by linarith)
    (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
    (fun x hx hn => by
      rw [(hderiv x hx).deriv]
      exact neg_pos.mpr (levelBase_deriv_neg_of_nonneg hA (hphysical x hx) hn))
    (by simpa [f] using hbase)
  simpa [f] using hg

def graphDomain (A K : ℝ) : Set ℝ := {r | r ∈ Ioo 0 1 ∧ K < levelBase A r}

theorem graphDomain_downward {A K a b : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hb : b ∈ graphDomain A K) (ha : 0 < a) (hab : a ≤ b) :
    a ∈ graphDomain A K := by
  have ha' : a ∈ Ioo 0 1 := ⟨ha, hab.trans_lt hb.1.2⟩
  refine ⟨ha', ?_⟩
  rcases hab.eq_or_lt with he | hlt
  · simpa [he] using hb.2
  · exact hb.2.trans (levelBase_lt_earlier hA ha' hb.1 hlt (hK.trans hb.2.le))

theorem graphDomain_convex {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) :
    Convex ℝ (graphDomain A K) := by
  apply convex_iff_ordConnected.mpr
  constructor
  intro a ha b hb x hx
  exact graphDomain_downward hA hK hb (ha.1.1.trans_le hx.1) hx.2

theorem graphDomain_isOpen (A K : ℝ) : IsOpen (graphDomain A K) := by
  rw [isOpen_iff_mem_nhds]
  intro r hr
  have hphysical : Ioo (0 : ℝ) 1 ∈ nhds r := Ioo_mem_nhds hr.1.1 hr.1.2
  have hbase : {x : ℝ | K < levelBase A x} ∈ nhds r :=
    (hasDerivAt_levelBase hr.1.1).continuousAt (Ioi_mem_nhds hr.2)
  exact inter_mem hphysical hbase

noncomputable def graphHeight (A B K r : ℝ) : ℝ :=
  Real.exp ((K - levelBase A r) / (A + B))

noncomputable def levelGraph (A B K r : ℝ) : ℝ :=
  (1 - graphHeight A B K r) / (1 - r * graphHeight A B K r)

theorem graphHeight_mem {A B K r : ℝ} (hAB : 0 < A + B)
    (hr : r ∈ graphDomain A K) : graphHeight A B K r ∈ Ioo 0 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [graphHeight, Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (sub_neg.mpr hr.2) hAB

theorem levelGraph_mem {A B K r : ℝ} (hAB : 0 < A + B)
    (hr : r ∈ graphDomain A K) : levelGraph A B K r ∈ Ioo 0 1 := by
  have hy := graphHeight_mem hAB hr
  have hprod := product_lt_one hr.1 hy
  have hden : 0 < 1 - r * graphHeight A B K r := sub_pos.mpr hprod
  refine ⟨div_pos (sub_pos.mpr hy.2) hden, ?_⟩
  rw [levelGraph, div_lt_one hden]
  have hmul := mul_lt_mul_of_pos_right hr.1.2 hy.1
  linarith

theorem levelGraph_ratio {A B K r : ℝ} (hAB : 0 < A + B)
    (hr : r ∈ graphDomain A K) :
    (1 - levelGraph A B K r) / (1 - r * levelGraph A B K r) = graphHeight A B K r := by
  have hgr := levelGraph_mem hAB hr
  have hy := graphHeight_mem hAB hr
  have h1r : 1 - r ≠ 0 := by linarith [hr.1.2]
  have hden : 1 - r * graphHeight A B K r ≠ 0 :=
    (sub_pos.mpr (product_lt_one hr.1 hy)).ne'
  apply (div_eq_iff (sub_pos.mpr (product_lt_one hr.1 hgr)).ne').mpr
  unfold levelGraph
  simp only [div_eq_mul_inv]
  have hc := congrArg (fun z => (1 - graphHeight A B K r) * z) (mul_inv_cancel₀ hden)
  nlinarith only [hc]

theorem levelGraph_first_level {A B K r : ℝ} (hAB : 0 < A + B)
    (hr : r ∈ graphDomain A K) : level1 A B r (levelGraph A B K r) = K := by
  change levelBase A r + (A + B) *
    Real.log ((1 - levelGraph A B K r) / (1 - r * levelGraph A B K r)) = K
  rw [levelGraph_ratio hAB hr, graphHeight, Real.log_exp]
  field_simp [hAB.ne']
  ring

theorem levelGraph_differentiableAt {A B K r : ℝ} (hAB : 0 < A + B)
    (hr : r ∈ graphDomain A K) : DifferentiableAt ℝ (levelGraph A B K) r := by
  have hbase := (hasDerivAt_levelBase (A := A) hr.1.1).differentiableAt
  have hy : DifferentiableAt ℝ (graphHeight A B K) r :=
    ((hbase.const_sub K).div_const (A + B)).exp
  have hden : 1 - r * graphHeight A B K r ≠ 0 :=
    (sub_pos.mpr (product_lt_one hr.1 (graphHeight_mem hAB hr))).ne'
  exact (hy.const_sub 1).div ((differentiableAt_id.mul hy).const_sub 1) hden

/-- Every physical solution of the first equation belongs to the explicit
graph domain and equals the graph value. -/
theorem first_level_iff_graph {A B K r s : ℝ} (hAB : 0 < A + B)
    (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1) (hlevel : level1 A B r s = K) :
    r ∈ graphDomain A K ∧ s = levelGraph A B K r := by
  let y : ℝ := (1 - s) / (1 - r * s)
  have hden : 0 < 1 - r * s := sub_pos.mpr (product_lt_one hr hs)
  have hy0 : 0 < y := div_pos (sub_pos.mpr hs.2) hden
  have hy1 : y < 1 := by
    apply (div_lt_one hden).mpr
    have hh := mul_lt_mul_of_pos_right hr.2 hs.1
    linarith
  have hlog : Real.log y < 0 := Real.log_neg hy0 hy1
  have hlevel' : levelBase A r + (A + B) * Real.log y = K := hlevel
  have hrD : r ∈ graphDomain A K := ⟨hr, by nlinarith [mul_neg_of_pos_of_neg hAB hlog]⟩
  have hexponent : (K - levelBase A r) / (A + B) = Real.log y := by
    apply (div_eq_iff hAB.ne').mpr
    linarith
  have hheight : graphHeight A B K r = y := by
    rw [graphHeight, hexponent, Real.exp_log hy0]
  refine ⟨hrD, ?_⟩
  rw [levelGraph, hheight]
  have h1r : 1 - r ≠ 0 := by linarith [hr.2]
  apply (eq_div_iff (sub_pos.mpr (product_lt_one hr ⟨hy0, hy1⟩)).ne').mpr
  dsimp [y]
  simp only [div_eq_mul_inv]
  have hc := congrArg (fun z => (1 - s) * z) (mul_inv_cancel₀ hden.ne')
  nlinarith only [hc]

/-- Uniqueness of the system in Proposition 3.4 for arbitrary nonnegative
target levels. No global plane or minimizer statement is assumed. -/
theorem stationary_level_system_unique {A B K1 K0 r s r' s' : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
    (hK1 : 0 ≤ K1) (hK0 : 0 ≤ K0)
    (hr : r ∈ Ioo 0 1) (hs : s ∈ Ioo 0 1)
    (hr' : r' ∈ Ioo 0 1) (hs' : s' ∈ Ioo 0 1)
    (h1 : level1 A B r s = K1) (h0 : level0 A B r s = K0)
    (h1' : level1 A B r' s' = K1) (h0' : level0 A B r' s' = K0) :
    r = r' ∧ s = s' := by
  obtain ⟨hrD, hsG⟩ := first_level_iff_graph hAB hr hs h1
  obtain ⟨hrD', hsG'⟩ := first_level_iff_graph hAB hr' hs' h1'
  have unique (a b : ℝ) (ha : a ∈ graphDomain A K1) (hb : b ∈ graphDomain A K1)
      (hab : a ≤ b)
      (ha0 : level0 A B a (levelGraph A B K1 a) = K0)
      (hb0 : level0 A B b (levelGraph A B K1 b) = K0) : a = b :=
    second_level_unique_on_graph hA hB hAB hK1 hK0
      (graphDomain_convex hA hK1) (graphDomain_isOpen A K1)
      (fun z hz => ⟨hz.1, levelGraph_mem hAB hz⟩)
      (fun z hz => levelGraph_differentiableAt hAB hz)
      (fun z hz => levelGraph_first_level hAB hz) ha hb hab ha0 hb0
  have hrr : r = r' := by
    rcases le_total r r' with hle | hle
    · exact unique r r' hrD hrD' hle (by simpa [hsG] using h0) (by simpa [hsG'] using h0')
    · exact (unique r' r hrD' hrD hle (by simpa [hsG'] using h0') (by simpa [hsG] using h0)).symm
  exact ⟨hrr, by rw [hsG, hsG', hrr]⟩

#print axioms graphDomain_convex
#print axioms levelGraph_first_level
#print axioms stationary_level_system_unique

end GeneralCK.PsiEndpointPlane

end


