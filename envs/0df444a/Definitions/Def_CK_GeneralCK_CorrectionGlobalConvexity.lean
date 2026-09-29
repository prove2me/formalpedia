-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionGlobalConvexity
-- name    : CK_GeneralCK_CorrectionGlobalConvexity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T02:51:28.184677+00:00
-- url     : https://prove2.me/theorems/5ecfdcca-d342-415a-8b78-377a0ca23ce0
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionGlobalConvexity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionGlobalConvexity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionGlobalConvexity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionGlobalConvexity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionGlobalConvexity.lean)

import Definitions.Def_CK_GeneralCK_CorrectionConvexityCriterion
import Definitions.Def_CK_GeneralCK_CorrectionBasics

namespace GeneralCK.Correction
open Set Filter
open scoped Topology

theorem F_abs_eq (z : ℝ) {h : ℝ} (hh : 0 < h) : F |z| h = F z h+F (-z) h := by
  rcases le_or_gt z 0 with hz | hz
  · rw [abs_of_nonpos hz]
    have : F z h=0 := F_nonpos_radius hz hh
    simp [this]
  · rw [abs_of_pos hz]
    have : F (-z) h=0 := F_nonpos_radius (by linarith) hh
    simp [this]

/-- The absolute radius has a corner, but the physical radial potential has zero
first derivative there. Its two totalized branches give an ordinary derivative. -/
theorem hasDerivAt_F_abs_curve_zero {s h : ℝ → ℝ} {x ds dh : ℝ}
    (hs : HasDerivAt s ds x) (hh : HasDerivAt h dh x)
    (hs0 : s x=0) (hh0 : 0 < h x) :
    HasDerivAt (fun t => F |s t| (h t)) 0 x := by
  have hp := hasDerivAt_F_curve_zero hs hh hs0 hh0
  have hn := hasDerivAt_F_curve_zero hs.neg hh (by simp [hs0]) hh0
  have heq : (fun t => F |s t| (h t)) =ᶠ[𝓝 x] (fun t => F (s t) (h t)+F (-s t) (h t)) := by
    filter_upwards [hh.continuousAt.eventually (Ioi_mem_nhds hh0)] with t ht
    exact F_abs_eq _ ht
  simpa using (hp.add hn).congr_of_eventuallyEq heq

/-- Every differentiable entropy curve through the physical interior diagonal has
zero correction derivative; no derivative of the absolute value is assumed. -/
theorem hasDerivAt_entropyCorrection_curve_diagonal {E G : ℝ → ℝ} {x a b : ℝ}
    (hE : HasDerivAt E a x) (hG : HasDerivAt G b x)
    (he : 0 < E x) (he' : E x < 1) (heg : E x=G x) :
    HasDerivAt (fun t => entropyCorrection (E t) (G t)) 0 x := by
  have hg : 0 < G x := heg ▸ he
  have hg' : G x < 1 := heg ▸ he'
  have hiE := (hasDerivAt_entropyInverse he he').comp x hE
  have hiG := (hasDerivAt_entropyInverse hg hg').comp x hG
  have hjE := (hasDerivAt_entropyJ he he').comp x hE
  have hjG := (hasDerivAt_entropyJ hg hg').comp x hG
  have hs := hiE.sub hiG
  have hm := (hE.add hG).div_const 2
  have hdF := hasDerivAt_F_abs_curve_zero hs hm (by simp [heg]) (by dsimp; linarith)
  have hcost := ((hiG.sub hiE).mul (hjE.sub hjG)).div_const 2
  have heq : (fun t => entropyCorrection (E t) (G t)) =ᶠ[𝓝 x]
      (fun t => (entropyInverse (G t)-entropyInverse (E t))*
        (J (entropyInverse (E t))-J (entropyInverse (G t)))/2-
        F |entropyInverse (E t)-entropyInverse (G t)| ((E t+G t)/2)) := by
    filter_upwards [hE.continuousAt.eventually (Ioo_mem_nhds he he'),
      hG.continuousAt.eventually (Ioo_mem_nhds hg hg')] with t het hgt
    unfold entropyCorrection atomCorrection interiorCost
    rw [(entropyInverse_spec het.1.le het.2.le).2.2,
      (entropyInverse_spec hgt.1.le hgt.2.le).2.2]
  convert! (hcost.sub hdF).congr_of_eventuallyEq heq using 1
  simp [heg]

theorem hasDerivAt_entropyCorrection_affine_diagonal {u v a b t : ℝ}
    (he : 0 < affine u a t) (he' : affine u a t < 1)
    (heg : affine u a t=affine v b t) :
    HasDerivAt (fun s => entropyCorrection (affine u a s) (affine v b s)) 0 t :=
  hasDerivAt_entropyCorrection_curve_diagonal (hasDerivAt_affine _ _ _)
    (hasDerivAt_affine _ _ _) he he' heg

/-- A differentiable scalar function can be stitched across one exceptional
second-derivative point. Ordinary first differentiability prevents a downward corner. -/
theorem convexOn_Icc_of_deriv2_nonneg_except {f : ℝ → ℝ} {l r c : ℝ}
    (hc : c ∈ Icc l r) (hd : ∀ t ∈ Icc l r, DifferentiableAt ℝ f t)
    (hdd : ∀ t ∈ Ioo l r, t ≠ c → DifferentiableAt ℝ (deriv f) t)
    (hpos : ∀ t ∈ Ioo l r, t ≠ c → 0 ≤ deriv (deriv f) t) :
    ConvexOn ℝ (Icc l r) f := by
  have hsubL : Icc l c ⊆ Icc l r := Icc_subset_Icc_right hc.2
  have hsubR : Icc c r ⊆ Icc l r := Icc_subset_Icc_left hc.1
  have hcont : ContinuousOn f (Icc l r) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hL : ConvexOn ℝ (Icc l c) f := by
    apply convexOn_of_deriv2_nonneg (convex_Icc l c) (hcont.mono hsubL)
    · intro t ht
      exact (hd t (hsubL (interior_subset ht))).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hdd t ⟨ht.1, ht.2.trans_le hc.2⟩ ht.2.ne).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hpos t ⟨ht.1, ht.2.trans_le hc.2⟩ ht.2.ne
  have hR : ConvexOn ℝ (Icc c r) f := by
    apply convexOn_of_deriv2_nonneg (convex_Icc c r) (hcont.mono hsubR)
    · intro t ht
      exact (hd t (hsubR (interior_subset ht))).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hdd t ⟨hc.1.trans_lt ht.1, ht.2⟩ ht.1.ne').differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hpos t ⟨hc.1.trans_lt ht.1, ht.2⟩ ht.1.ne'
  have hmL := hL.monotoneOn_deriv (fun t ht => hd t (hsubL ht))
  have hmR := hR.monotoneOn_deriv (fun t ht => hd t (hsubR ht))
  have hm : MonotoneOn (deriv f) (Icc l r) := by
    intro x hx y hy hxy
    by_cases hyc : y ≤ c
    · exact hmL ⟨hx.1, hxy.trans hyc⟩ ⟨hy.1, hyc⟩ hxy
    · by_cases hcx : c ≤ x
      · exact hmR ⟨hcx, hx.2⟩ ⟨hcx.trans hxy, hy.2⟩ hxy
      · exact (hmL ⟨hx.1, (not_le.mp hcx).le⟩ ⟨hc.1, le_rfl⟩ (not_le.mp hcx).le).trans
          (hmR ⟨le_rfl, hc.2⟩ ⟨(not_le.mp hyc).le, hy.2⟩ (not_le.mp hyc).le)
  exact (hm.mono interior_subset).convexOn_of_deriv (convex_Icc l r) hcont
    (fun t ht => (hd t (interior_subset ht)).differentiableWithinAt)

theorem differentiableAt_correction_affine {u v a b t : ℝ}
    (he : affine u a t ∈ Ioo (0:ℝ) 1) (hf : affine v b t ∈ Ioo (0:ℝ) 1) :
    DifferentiableAt ℝ (fun s => entropyCorrection (affine u a s) (affine v b s)) t := by
  rcases lt_trichotomy (affine u a t) (affine v b t) with h | h | h
  · exact (hasDerivAt_correction_curve (hasDerivAt_affine _ _ _) (hasDerivAt_affine _ _ _)
      he.1 h hf.2).differentiableAt
  · exact (hasDerivAt_entropyCorrection_affine_diagonal he.1 he.2 h).differentiableAt
  · have heq : (fun s => entropyCorrection (affine u a s) (affine v b s)) =
        (fun s => entropyCorrection (affine v b s) (affine u a s)) :=
      funext (fun s => entropyCorrection_comm _ _)
    rw [heq]
    exact (hasDerivAt_correction_curve (hasDerivAt_affine _ _ _) (hasDerivAt_affine _ _ _)
      hf.1 h he.2).differentiableAt

theorem correction_affine_deriv2_off_diagonal
    (hleft : ∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2)
    (hdet : ∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2)
    {u v a b t : ℝ} (he : affine u a t ∈ Ioo (0:ℝ) 1)
    (hf : affine v b t ∈ Ioo (0:ℝ) 1) (hne : affine u a t ≠ affine v b t) :
    DifferentiableAt ℝ (deriv (fun s => entropyCorrection (affine u a s) (affine v b s))) t ∧
      0 ≤ deriv (deriv (fun s => entropyCorrection (affine u a s) (affine v b s))) t := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hd := hasDerivAt_deriv_correction_affine he.1 h hf.2
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    exact hessianQuadratic_nonneg he.1 h hf.2
      (hleft (affine u a t, affine v b t) ⟨he.1, h, hf.2⟩) (hdet (affine u a t, affine v b t) ⟨he.1, h, hf.2⟩) _ _
  · have heq : (fun s => entropyCorrection (affine u a s) (affine v b s)) =
        (fun s => entropyCorrection (affine v b s) (affine u a s)) :=
      funext (fun s => entropyCorrection_comm _ _)
    rw [heq]
    have hd := hasDerivAt_deriv_correction_affine hf.1 h he.2
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    exact hessianQuadratic_nonneg hf.1 h he.2
      (hleft (affine v b t, affine u a t) ⟨hf.1, h, he.2⟩) (hdet (affine v b t, affine u a t) ⟨hf.1, h, he.2⟩) _ _

theorem convexOn_correction_affine
    (hleft : ∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2)
    (hdet : ∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2)
    {u v a b : ℝ}
    (hmem : ∀ t ∈ Icc (0:ℝ) 1, affine u a t ∈ Ioo (0:ℝ) 1 ∧ affine v b t ∈ Ioo (0:ℝ) 1) :
    ConvexOn ℝ (Icc (0:ℝ) 1) (fun s => entropyCorrection (affine u a s) (affine v b s)) := by
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) := differentiableAt_correction_affine (hmem t ht).1 (hmem t ht).2
  have hdd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (hne : affine u a t ≠ affine v b t) :=
    correction_affine_deriv2_off_diagonal hleft hdet (hmem t ht).1 (hmem t ht).2 hne
  have hregular (hne : ∀ t ∈ Ioo (0:ℝ) 1, affine u a t ≠ affine v b t) :
      ConvexOn ℝ (Icc (0:ℝ) 1) (fun s => entropyCorrection (affine u a s) (affine v b s)) := by
    apply convexOn_of_deriv2_nonneg (convex_Icc 0 1)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    · exact fun t ht => (hd t (interior_subset ht)).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hdd t ⟨ht.1.le, ht.2.le⟩ (hne t ht)).1.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hdd t ⟨ht.1.le, ht.2.le⟩ (hne t ht)).2
  by_cases hab : a=b
  · by_cases huv : u=v
    · subst v
      subst b
      simpa only [entropyCorrection_self] using
        (convexOn_const (c := (0:ℝ)) (convex_Icc (0:ℝ) 1))
    · apply hregular
      intro t ht heq
      apply huv
      dsimp [affine] at heq
      rw [hab] at heq
      linarith
  · let c := (v-u)/(a-b)
    have hzero (t : ℝ) : affine u a t=affine v b t ↔ t=c := by
      dsimp [affine, c]
      rw [eq_div_iff (sub_ne_zero.mpr hab)]
      constructor <;> intro h <;> nlinarith
    by_cases hc : c ∈ Icc (0:ℝ) 1
    · apply convexOn_Icc_of_deriv2_nonneg_except hc hd
      · intro t ht htc
        exact (hdd t ⟨ht.1.le, ht.2.le⟩ (fun h => htc ((hzero t).mp h))).1
      · intro t ht htc
        exact (hdd t ⟨ht.1.le, ht.2.le⟩ (fun h => htc ((hzero t).mp h))).2
    · apply hregular
      intro t ht heq
      exact hc ((hzero t).mp heq ▸ ⟨ht.1.le, ht.2.le⟩)

theorem convexOn_entropyCorrection_open_square
    (hleft : ∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2)
    (hdet : ∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) :
    ConvexOn ℝ (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) (fun p => entropyCorrection p.1 p.2) := by
  have hcv : Convex ℝ (Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) := (convex_Ioo 0 1).prod (convex_Ioo 0 1)
  refine ⟨hcv, ?_⟩
  intro x hx y hy a b ha hb hab
  let E := affine x.1 (y.1-x.1)
  let G := affine x.2 (y.2-x.2)
  have hmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      E t ∈ Ioo (0:ℝ) 1 ∧ G t ∈ Ioo (0:ℝ) 1 := by
    have hp := hcv hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
    have heq : (E t, G t)=(1-t) • x+t • y := by
      ext <;> dsimp [E, G, affine] <;> ring
    change (E t, G t) ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1
    rw [heq]
    exact hp
  have hconv := convexOn_correction_affine hleft hdet hmem
  have hc := hconv.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num) ha hb hab
  have heqE : E (a*0+b*1) = a*x.1+b*y.1 := by
    dsimp [E, affine]
    rw [show a=1-b by linarith]
    ring
  have heqG : G (a*0+b*1) = a*x.2+b*y.2 := by
    dsimp [G, affine]
    rw [show a=1-b by linarith]
    ring
  change entropyCorrection (a*x.1+b*y.1) (a*x.2+b*y.2) ≤
    a*entropyCorrection x.1 x.2+b*entropyCorrection y.1 y.2
  change entropyCorrection (E (a*0+b*1)) (G (a*0+b*1)) ≤
    a*entropyCorrection (E 0) (G 0)+b*entropyCorrection (E 1) (G 1) at hc
  rw [heqE, heqG] at hc
  simpa only [E, G, affine, zero_mul, add_zero, one_mul, add_sub_cancel] using hc

private theorem scaled_mem_square {p : ℝ × ℝ}
    (hp : p ∈ Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) (1/2)) :
    ((1-t)*p.1, (1-t)*p.2) ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1 := by
  have h1 : 0 < 1-t := by linarith [ht.2]
  refine ⟨⟨mul_pos h1 hp.1.1, ?_⟩, ⟨mul_pos h1 hp.2.1, ?_⟩⟩
  · have := mul_le_mul_of_nonneg_left hp.1.2 h1.le
    nlinarith [ht.1]
  · have := mul_le_mul_of_nonneg_left hp.2.2 h1.le
    nlinarith [ht.1]

private theorem correction_scaled_continuous {p : ℝ × ℝ}
    (hp : p ∈ Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1) :
    ContinuousWithinAt (fun t : ℝ => entropyCorrection ((1-t)*p.1) ((1-t)*p.2))
      (Ioo (0:ℝ) (1/2)) 0 := by
  have hcont : Continuous (fun t : ℝ => ((1-t)*p.1, (1-t)*p.2)) := by fun_prop
  have houter := entropyCorrection_continuousOn p hp
  have hmap : MapsTo (fun t : ℝ => ((1-t)*p.1, (1-t)*p.2))
      (Ioo (0:ℝ) (1/2)) (Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1) := by
    intro t ht
    have h := scaled_mem_square hp ht
    exact ⟨⟨h.1.1, h.1.2.le⟩, ⟨h.2.1, h.2.2.le⟩⟩
  have hbase : ((1-(0:ℝ))*p.1, (1-(0:ℝ))*p.2)=p := by simp
  exact houter.comp_of_eq (f := fun t : ℝ => ((1-t)*p.1, (1-t)*p.2))
    (x := 0) hcont.continuousWithinAt hmap hbase

/-- Full physical entropy-square convexity, including maximum entropy, from only
pointwise open-triangle source-minor inequalities. -/
theorem convexOn_entropyCorrection_square
    (hleft : ∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2)
    (hdet : ∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) :
    ConvexOn ℝ (Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1) (fun p => entropyCorrection p.1 p.2) := by
  have hcv : Convex ℝ (Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1) := (convex_Ioc 0 1).prod (convex_Ioc 0 1)
  have hc := convexOn_entropyCorrection_open_square hleft hdet
  refine ⟨hcv, ?_⟩
  intro x hx y hy a b ha hb hab
  let z : ℝ × ℝ := a • x+b • y
  have hz : z ∈ Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1 := hcv hx hy ha hb hab
  have hzero : (0:ℝ) ∈ closure (Ioo (0:ℝ) (1/2)) := by rw [closure_Ioo (by norm_num : (0:ℝ)≠1/2)]; constructor <;> norm_num
  have hp := ContinuousWithinAt.closure_le hzero (correction_scaled_continuous hz)
    (((correction_scaled_continuous hx).const_mul a).add ((correction_scaled_continuous hy).const_mul b)) (by
      intro t ht
      have h := hc.2 (scaled_mem_square hx ht) (scaled_mem_square hy ht) ha hb hab
      convert! h using 1
      dsimp [z]
      congr 1 <;> ring)
  simpa only [Pi.add_apply, sub_zero, one_mul, smul_eq_mul] using hp

end GeneralCK.Correction


