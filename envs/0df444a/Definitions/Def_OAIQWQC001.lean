-- Prove2me | Definitions.Def_OAIQWQC001
-- name    : OAIQWQC001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T15:57:34.301349+00:00
-- url     : https://prove2.me/theorems/851db637-89a9-4152-b506-420dbf2d8d78
-- title:
--   OpenAI quadric-surface split: plurisubharmonic functions tested on holomorphic disks (definitions bundle 2 of 5)
-- statement:
--   The second definitions bundle of the split of OpenAI's proof of the counterexample to Griffiths' positivity conjecture on the quadric surface (`OAI.QuadricCounterexample.main_theorem`). It holds OpenAI's definitions from `Plurisubharmonic.lean` and `Removability.lean` of `lean/OAI/Geometry/QuadricBundles` (OpenAI, *Ample rank-two bundles on the quadric surface without Griffiths-positive metrics*, OpenAI Math Release, September 24, 2026, result family 050, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a:
--   - `DiskPshOn Ω q`: $q$ is upper semicontinuous on $\Omega$ (a subset of a complex normed space) and $q \circ \gamma$ is `DiskSubharmonicOn D` for every map $\gamma$ complex differentiable on an open $D \subseteq \mathbb C$ with $\gamma(D) \subseteq \Omega$;
--   - `LocalDiskSubmeanOn Ω u`: the disk submean inequality on all sufficiently small disks about each point;
--   - `logBarrier q f δ`: $\max(q + \delta\log|f|, 0)$ off the zeros of $f$, and $0$ on them.
--
--   It also contains the fourteen lemmas about these notions that later definitions use in their bodies: for example locality of plurisubharmonicity (`DiskPshOn.of_locally`, with the maximum principle for local submean functions, `LocalDiskSubmeanOn.eq_const_of_max`, that it rests on), and closure under sums, constants, positive multiples, restriction and composition with holomorphic maps (`DiskPshOn.add`, `diskPshOn_const`, `DiskPshOn.const_mul_of_continuous`, `DiskPshOn.mono`, `DiskPshOn.comp`). It imports the definitions bundle `OAIQWQC000` and is the definitions import of the published statements `OAI.QuadricCounterexample.log_norm_psh` and `OAI.QuadricCounterexample.first_hyperplane_removable`.
--
--   Modules: `Plurisubharmonic.lean`, `Removability.lean`.
-- source:
--   OpenAI, Ample rank-two bundles on the quadric surface without Griffiths-positive metrics, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 050; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/QuadricBundles at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWQC000

section
-- module Solutions.OAIQW_QuadricCounterexample.Plurisubharmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory
noncomputable section
open scoped Pointwise

attribute [local instance] Measure.Subtype.measureSpace

attribute [local instance] OAI.QuadricCounterexample.realDualComplexGroup
attribute [local instance] OAI.QuadricCounterexample.realDualComplexSpace
def DiskPshOn {E : Type u10} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Ω : Set E) (q : E → ℝ) : Prop :=
  UpperSemicontinuousOn q Ω ∧ ∀ (D : Set ℂ), IsOpen D → ∀ γ : ℂ → E,
    DifferentiableOn ℂ γ D → MapsTo γ D Ω → DiskSubharmonicOn D (q ∘ γ)

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Removability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

lemma usc_ge_of_ae_ge {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℝ}
    (hu : UpperSemicontinuousOn u Ω) {c : ℝ}
    (hae : ∀ᵐ x ∂volume.restrict Ω, c ≤ u x) : ∀ x ∈ Ω, c ≤ u x := by
  have hopen : IsOpen {x | x ∈ Ω ∧ u x < c} := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hh := hu x hx.1 c hx.2
    rw [nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds hx.1)] at hh
    exact inter_mem (hΩ.mem_nhds hx.1) hh
  have hz : volume {x | x ∈ Ω ∧ u x < c} = 0 := by
    have hh := (ae_restrict_iff' hΩ.measurableSet).mp hae
    simpa only [ae_iff, not_forall, not_le, Classical.not_imp, exists_prop] using hh
  have he := hopen.eq_empty_of_measure_zero hz
  intro x hx
  by_contra h
  have : x ∈ {x | x ∈ Ω ∧ u x < c} := ⟨hx, lt_of_not_ge h⟩
  rw [he] at this
  exact this

def LocalDiskSubmeanOn (Ω : Set ℂ) (u : ℂ → ℝ) : Prop :=
  UpperSemicontinuousOn u Ω ∧ ∀ x ∈ Ω, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ Ω ∧
    IntegrableOn u (ball x r) ∧
      (volume (ball x r)).toReal * u x ≤ ∫ y in ball x r, u y

theorem LocalDiskSubmeanOn.eq_on_ball_of_max {Ω : Set ℂ} {u : ℂ → ℝ}
    (hu : LocalDiskSubmeanOn Ω u) {x : ℂ} (hx : x ∈ Ω)
    (hmax : ∀ y ∈ Ω, u y ≤ u x) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ Ω ∧ ∀ y ∈ ball x r, u y = u x := by
  obtain ⟨r,hr,hball,hi,hmean⟩ := hu.2 x hx
  have hb : ball x r ⊆ Ω := ball_subset_closedBall.trans hball
  have hle : u ≤ᵐ[volume.restrict (ball x r)] fun _ ↦ u x :=
    (ae_restrict_mem measurableSet_ball).mono fun y hy ↦ hmax y (hb hy)
  have hc : IntegrableOn (fun _ : ℂ ↦ u x) (ball x r) :=
    integrableOn_const measure_ball_lt_top.ne
  have he : (∫ y in ball x r, u y) = ∫ _ in ball x r, u x := by
    apply le_antisymm (integral_mono_ae hi hc hle)
    simpa only [setIntegral_const, measureReal_def, smul_eq_mul] using hmean
  have hae := (integral_eq_iff_of_ae_le hi hc hle).mp he
  have hge := usc_ge_of_ae_ge isOpen_ball (hu.1.mono hb) (hae.mono fun _ h ↦ h.ge)
  exact ⟨r,hr,hb,fun y hy ↦ le_antisymm (hmax y (hb hy)) (hge y hy)⟩

theorem LocalDiskSubmeanOn.eq_const_of_max {Ω : Set ℂ} {u : ℂ → ℝ}
    (hconn : IsPreconnected Ω) (hu : LocalDiskSubmeanOn Ω u)
    {x : ℂ} (hx : x ∈ Ω) (hmax : ∀ y ∈ Ω, u y ≤ u x) :
    ∀ y ∈ Ω, u y = u x := by
  let : PreconnectedSpace Ω := isPreconnected_iff_preconnectedSpace.mp hconn
  let C : Set Ω := {y | u x ≤ u y}
  have hc : IsClosed C :=
    (upperSemicontinuousOn_iff_restrict.mpr hu.1).isClosed_preimage (u x)
  have ho : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hey : u y = u x := le_antisymm (hmax y y.property) hy
    obtain ⟨r,hr,_,he⟩ := hu.eq_on_ball_of_max y.property
      (fun z hz ↦ (hmax z hz).trans hey.ge)
    have hn : {z : Ω | (z : ℂ) ∈ ball (y : ℂ) r} ∈ 𝓝 y :=
      continuous_subtype_val.continuousAt (ball_mem_nhds (y : ℂ) hr)
    apply mem_of_superset hn
    intro z hz
    change u x ≤ u z
    rw [he z hz,hey]
  have hne : C.Nonempty := ⟨⟨x,hx⟩,by change u x ≤ u x; exact le_rfl⟩
  have heq : C = univ := (show IsClopen C from ⟨hc,ho⟩).eq_univ hne
  intro y hy
  have hh : (⟨y,hy⟩ : Ω) ∈ C := heq.symm ▸ mem_univ _
  exact le_antisymm (hmax y hy) hh

theorem LocalDiskSubmeanOn.le_boundary {u : ℂ → ℝ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hc : ContinuousOn u (closedBall c R))
    (hu : LocalDiskSubmeanOn (ball c R) u)
    (hb : ∀ z ∈ sphere c R, u z ≤ M) : ∀ z ∈ closedBall c R, u z ≤ M := by
  obtain ⟨x,hx,hmax⟩ := (isCompact_closedBall c R).exists_isMaxOn
    ⟨c,mem_closedBall_self hR.le⟩ hc
  suffices hh : u x ≤ M from fun z hz ↦ (hmax hz).trans hh
  by_cases hxb : x ∈ sphere c R
  · exact hb x hxb
  · have hxi : x ∈ ball c R := by
      rw [mem_ball,mem_closedBall] at *
      exact lt_of_le_of_ne hx (by simpa only [mem_sphere] using hxb)
    have he := hu.eq_const_of_max (convex_ball c R).isPreconnected hxi
      (fun z hz ↦ hmax (ball_subset_closedBall hz))
    have hec : ∀ z ∈ closedBall c R, u z = u x := by
      exact Set.EqOn.of_subset_closure he hc continuousOn_const
        ball_subset_closedBall (by rw [closure_ball c hR.ne'])
    have hz : c + (R : ℂ) ∈ sphere c R := by simp [hR.le]
    rw [← hec _ (sphere_subset_closedBall hz)]
    exact hb _ hz

theorem compact_family_local_submean
    {α : Type u1} {E : Type u2} [TopologicalSpace α] [CompactSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D : Set ℂ} (hD : IsOpen D) {Φ : α → ℂ → E}
    (hc : ContinuousOn (Function.uncurry Φ) (univ ×ˢ D))
    (hd : ∀ a, DifferentiableOn ℂ (Φ a) D)
    {U : Set E} {q : E → ℝ} (hm : ∀ a, MapsTo (Φ a) D U)
    (hl : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ DiskPshOn V q)
    {z : ℂ} (hz : z ∈ D) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ D ∧ ∀ a,
      IntegrableOn (q ∘ Φ a) (ball z r) ∧
      (volume (ball z r)).toReal * q (Φ a z) ≤ ∫ y in ball z r, q (Φ a y) := by
  classical
  have hh (a : α) : ∃ (A : Set α) (W : Set ℂ) (V : Set E),
      A ∈ 𝓝 a ∧ W ∈ 𝓝 z ∧ IsOpen V ∧ DiskPshOn V q ∧
      ∀ b ∈ A, ∀ y ∈ W, Φ b y ∈ V := by
    obtain ⟨V,hVo,haV,hV⟩ := hl _ (hm a hz)
    have hcont : ContinuousAt (Function.uncurry Φ) (a,z) :=
      hc.continuousAt ((isOpen_univ.prod hD).mem_nhds ⟨mem_univ a,hz⟩)
    have hn : (Function.uncurry Φ) ⁻¹' V ∈ 𝓝 (a,z) := hcont (hVo.mem_nhds haV)
    rw [nhds_prod_eq,mem_prod_iff] at hn
    obtain ⟨A,hA,W,hW,hAW⟩ := hn
    exact ⟨A,W,V,hA,hW,hVo,hV,fun b hb y hy ↦ hAW (show (b,y) ∈ A ×ˢ W from ⟨hb,hy⟩)⟩
  choose A W V hA hW hVo hV hmap using hh
  obtain ⟨t,_,ht⟩ := isCompact_univ.elim_nhds_subcover A (fun a _ ↦ hA a)
  have hn : D ∩ ⋂ a ∈ t, W a ∈ 𝓝 z :=
    inter_mem (hD.mem_nhds hz) ((Filter.biInter_mem t.finite_toSet).mpr (fun a _ ↦ hW a))
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  refine ⟨r,hr,fun y hy ↦ (hball hy).1,?_⟩
  intro a
  obtain ⟨b,hbt,hab⟩ := mem_iUnion₂.mp (ht (mem_univ a))
  let O := D ∩ (Φ a) ⁻¹' V b
  have hO : IsOpen O := (hd a).continuousOn.isOpen_inter_preimage hD (hVo b)
  have hbO : closedBall z r ⊆ O := by
    intro y hy
    have hhy := hball hy
    exact ⟨hhy.1,hmap b a hab y (mem_iInter₂.mp hhy.2 b hbt)⟩
  have hp := (hV b).2 O hO (Φ a) ((hd a).mono inter_subset_left) (fun _ h ↦ h.2)
  exact hp.2 z (hbO (mem_closedBall_self hr.le)) r hr hbO

open scoped Pointwise
noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

theorem submean_of_locally_psh
    {E : Type u3} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {q : E → ℝ} (hq : ContinuousOn q U)
    (hl : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ DiskPshOn V q)
    {D : Set ℂ} (_hD : IsOpen D) {γ : ℂ → E}
    (hγ : DifferentiableOn ℂ γ D) (hm : MapsTo γ D U)
    {c : ℂ} (_hc : c ∈ D) {R : ℝ} (hR : 0 < R) (hb : closedBall c R ⊆ D) :
    (volume (ball c R)).toReal * q (γ c) ≤ ∫ y in ball c R, q (γ y) := by
  let A := closedBall (0 : ℂ) 1
  let : IsFiniteMeasure (volume : Measure A) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall (0 : ℂ) 1).measure_lt_top⟩
  let Φ : A → ℂ → E := fun a z ↦ γ (c+(a : ℂ)*z)
  let F : A → ℂ → ℝ := fun a z ↦ q (Φ a z)
  have hbΦ : ∀ a : A, MapsTo (fun z : ℂ ↦ c+(a : ℂ)*z) (closedBall 0 R)
      (closedBall c R) := by
    intro a z hz
    have ha : ‖(a : ℂ)‖ ≤ 1 := by
      have hh : (a : ℂ) ∈ closedBall 0 1 := a.property
      simpa only [mem_closedBall,dist_zero_right] using hh
    have hz' : ‖z‖ ≤ R := by simpa using hz
    simp only [mem_closedBall,dist_self_add_left,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg z) ha).trans hz'
  have hΦ : ContinuousOn (Function.uncurry Φ) (univ ×ˢ closedBall 0 R) := by
    apply hγ.continuousOn.comp (f := fun p : A × ℂ ↦ c+(p.1 : ℂ)*p.2) (by fun_prop)
    exact fun p hp ↦ hb (hbΦ p.1 hp.2)
  have hF : ContinuousOn (Function.uncurry F) (univ ×ˢ closedBall 0 R) :=
    hq.comp hΦ (fun p hp ↦ hm (hb (hbΦ p.1 hp.2)))
  have hcont := compact_integral_continuousOn (μ := (volume : Measure A)) hF
  have hdΦ : ∀ a, DifferentiableOn ℂ (Φ a) (ball 0 R) := by
    intro a
    apply hγ.comp (f := fun z : ℂ ↦ c+(a : ℂ)*z) (by fun_prop)
    exact fun z hz ↦ hb (hbΦ a (ball_subset_closedBall hz))
  have hΦmap : ∀ a, MapsTo (Φ a) (ball 0 R) U :=
    fun a z hz ↦ hm (hb (hbΦ a (ball_subset_closedBall hz)))
  have hlocal : LocalDiskSubmeanOn (ball 0 R) (fun z ↦ ∫ a : A, F a z) := by
    refine ⟨(hcont.mono ball_subset_closedBall).upperSemicontinuousOn,?_⟩
    intro z hz
    obtain ⟨r,hr,hbr,hs⟩ := compact_family_local_submean isOpen_ball
      (hΦ.mono (prod_mono (Subset.refl univ) ball_subset_closedBall)) hdΦ hΦmap hl hz
    have hprod : Integrable (fun p : A × ℂ ↦ F p.1 p.2)
        ((volume : Measure A).prod (volume.restrict (ball z r))) := by
      have hi := (hF.mono (prod_mono (Subset.refl univ)
        (hbr.trans ball_subset_closedBall))).integrableOn_compact
        (μ := (volume : Measure A).prod volume) (isCompact_univ.prod (isCompact_closedBall z r))
      have hj := hi.mono_set (prod_mono (Subset.refl univ) ball_subset_closedBall)
      unfold IntegrableOn at hj
      rw [← Measure.prod_restrict,Measure.restrict_univ] at hj
      exact hj
    have hp : Integrable (fun a : A ↦ F a z) := by
      have hh : Continuous (fun a : A ↦ F a z) :=
        hF.comp_continuous (f := fun a : A ↦ (a,z)) (by fun_prop)
          (fun _ ↦ ⟨mem_univ _,ball_subset_closedBall hz⟩)
      exact integrableOn_univ.mp (hh.continuousOn.integrableOn_compact isCompact_univ)
    refine ⟨r,hr,hbr,hprod.integral_prod_right,?_⟩
    calc
      (volume (ball z r)).toReal * (∫ a : A, F a z) =
          ∫ a : A, (volume (ball z r)).toReal * F a z := (integral_const_mul _ _).symm
      _ ≤ ∫ a : A, ∫ y in ball z r, F a y :=
        integral_mono_ae (hp.const_mul _) hprod.integral_prod_left
          (Eventually.of_forall fun a ↦ (hs a).2)
      _ = ∫ y in ball z r, ∫ a : A, F a y := integral_integral_swap hprod
  have he (z : ℂ) : (∫ a : A, F a z) = radialIntegral (q ∘ γ) c z := by
    exact integral_subtype (s := closedBall (0 : ℂ) 1) measurableSet_closedBall
      (fun a : ℂ ↦ q (γ (c+a*z)))
  have hm0 := hlocal.le_boundary hR hcont (M := radialIntegral (q ∘ γ) c (R : ℂ)) (by
    intro z hz
    rw [he]
    apply le_of_eq
    apply radialIntegral_eq_of_norm_eq
    simpa only [mem_sphere,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR] using hz)
    0 (mem_closedBall_self hR.le)
  rw [he,radialIntegral_zero,radialIntegral_pos_radius _ _ hR] at hm0
  have hv := radialIntegral_pos_radius (fun _ ↦ (1 : ℝ)) c hR
  simp only [radialIntegral,setIntegral_const,measureReal_def,smul_eq_mul,mul_one] at hv
  have heR := complex_closedBall_ae_ball c R
  rw [measure_congr heR] at hv
  rw [← setIntegral_congr_set heR]
  have hn : R^2 ≠ 0 := pow_ne_zero _ hR.ne'
  have hscale : R^2 * (R^2)⁻¹ = 1 := mul_inv_cancel₀ hn
  have hmul := mul_le_mul_of_nonneg_left hm0 (sq_nonneg R)
  calc
    (volume (ball c R)).toReal * q (γ c) =
        R^2 * ((volume (closedBall (0 : ℂ) 1)).toReal * q (γ c)) := by
      rw [hv]
      rw [← mul_assoc,← mul_assoc,hscale,one_mul]
    _ ≤ R^2 * ((R^2)⁻¹ * ∫ y in closedBall c R, q (γ y)) := hmul
    _ = ∫ y in closedBall c R, q (γ y) := by rw [← mul_assoc,hscale,one_mul]

theorem DiskPshOn.of_locally
    {E : Type u4} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {q : E → ℝ} (hq : ContinuousOn q U)
    (hl : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ DiskPshOn V q) :
    DiskPshOn U q := by
  refine ⟨hq.upperSemicontinuousOn,?_⟩
  intro D hD γ hγ hm
  have hcont := hq.comp hγ.continuousOn hm
  refine ⟨hcont.upperSemicontinuousOn,?_⟩
  intro c hc R hR hb
  refine ⟨((hcont.mono hb).integrableOn_compact (isCompact_closedBall c R)).mono_set
    ball_subset_closedBall,?_⟩
  exact submean_of_locally_psh hq hl hD hγ hm hc hR hb

open Real

lemma DiskPshOn.comp {E : Type u6} {F : Type u7} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {Ω : Set E} {U : Set F}
    {q : E → ℝ} (hq : DiskPshOn Ω q) {f : F → E}
    (hf : DifferentiableOn ℂ f U) (hmap : MapsTo f U Ω) :
    DiskPshOn U (q ∘ f) := by
  refine ⟨hq.1.comp hf.continuousOn hmap, ?_⟩
  intro D hD γ hγ hγmap
  exact hq.2 D hD (f ∘ γ) (hf.comp hγ hγmap) (hmap.comp hγmap)

lemma DiskSubharmonicOn.add {D : Set ℂ} {u v : ℂ → ℝ}
    (hu : DiskSubharmonicOn D u) (hv : DiskSubharmonicOn D v) :
    DiskSubharmonicOn D (fun z ↦ u z + v z) := by
  refine ⟨hu.1.add hv.1,?_⟩
  intro c hc R hR hb
  obtain ⟨hui,hus⟩ := hu.2 c hc R hR hb
  obtain ⟨hvi,hvs⟩ := hv.2 c hc R hR hb
  refine ⟨hui.add hvi,?_⟩
  rw [integral_add hui hvi,mul_add]
  exact add_le_add hus hvs

lemma DiskPshOn.add {E : Type u8} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {u v : E → ℝ} (hu : DiskPshOn U u) (hv : DiskPshOn U v) :
    DiskPshOn U (fun z ↦ u z + v z) := by
  refine ⟨hu.1.add hv.1,?_⟩
  intro D hD γ hγ hm
  exact (hu.2 D hD γ hγ hm).add (hv.2 D hD γ hγ hm)

lemma diskPshOn_const {E : Type u10} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (c : ℝ) : DiskPshOn U (fun _ ↦ c) := by
  refine ⟨continuousOn_const.upperSemicontinuousOn,?_⟩
  intro D hD γ hγ hm
  refine ⟨continuousOn_const.upperSemicontinuousOn,?_⟩
  intro z hz R hR hb
  refine ⟨integrableOn_const measure_ball_lt_top.ne,?_⟩
  simp only [Function.comp_apply,setIntegral_const,measureReal_def,smul_eq_mul,le_refl]

lemma DiskPshOn.const_mul_of_continuous {E : Type u11} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {u : E → ℝ} (hu : DiskPshOn U u) (hc : ContinuousOn u U)
    {δ : ℝ} (hδ : 0 ≤ δ) : DiskPshOn U (fun z ↦ δ*u z) := by
  refine ⟨(hc.const_mul δ).upperSemicontinuousOn,?_⟩
  intro D hD γ hγ hm
  refine ⟨((hc.comp hγ.continuousOn hm).const_mul δ).upperSemicontinuousOn,?_⟩
  intro z hz R hR hb
  obtain ⟨hi,hs⟩ := (hu.2 D hD γ hγ hm).2 z hz R hR hb
  refine ⟨hi.const_mul δ,?_⟩
  change (volume (ball z R)).toReal * (δ*u (γ z)) ≤ ∫ y in ball z R, δ*u (γ y)
  rw [integral_const_mul,mul_left_comm]
  exact mul_le_mul_of_nonneg_left hs hδ

lemma DiskPshOn.mono {E : Type u12} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U V : Set E} {u : E → ℝ} (hu : DiskPshOn U u) (hVU : V ⊆ U) : DiskPshOn V u :=
  ⟨hu.1.mono hVU,fun D hD γ hγ hm ↦ hu.2 D hD γ hγ (fun _ hz ↦ hVU (hm hz))⟩

lemma DiskPshOn.congr {E : Type u13} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {u v : E → ℝ} (hu : DiskPshOn U u) (he : EqOn u v U) :
    DiskPshOn U v := by
  refine ⟨fun x hx ↦ UpperSemicontinuousWithinAt.congr_of_eventuallyEq (hu.1 x hx) hx
    ((show ∀ᶠ y in 𝓝[U] x, y ∈ U from self_mem_nhdsWithin).mono (fun y hy ↦ he hy)),?_⟩
  intro D hD γ hγ hm
  have hd := hu.2 D hD γ hγ hm
  refine ⟨fun z hz ↦ UpperSemicontinuousWithinAt.congr_of_eventuallyEq (hd.1 z hz) hz
    ((show ∀ᶠ y in 𝓝[D] z, y ∈ D from self_mem_nhdsWithin).mono (fun y hy ↦ he (hm hy))),?_⟩
  intro z hz R hR hb
  have he' : (fun y ↦ u (γ y)) =ᵐ[volume.restrict (ball z R)] (fun y ↦ v (γ y)) :=
    (ae_restrict_mem measurableSet_ball).mono (fun y hy ↦ he (hm (hb (ball_subset_closedBall hy))))
  obtain ⟨hi,hs⟩ := hd.2 z hz R hR hb
  refine ⟨hi.congr he',?_⟩
  change (volume (ball z R)).toReal * v (γ z) ≤ ∫ y in ball z R, v (γ y)
  change (volume (ball z R)).toReal * u (γ z) ≤ ∫ y in ball z R, u (γ y) at hs
  rwa [integral_congr_ae he',he (hm hz)] at hs
def logBarrier {E : Type u14} (q : E → ℝ) (f : E → ℂ) (δ : ℝ) (x : E) : ℝ :=
  if f x = 0 then 0 else max (q x + δ * Real.log ‖f x‖) 0

end
end QuadricCounterexample

end OAI
end


