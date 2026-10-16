-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Index
-- name    : OAI_Geometry_ConjugatePoints_Index
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:28:25.387996+00:00
-- url     : https://prove2.me/theorems/35f48e3d-c5fe-4a8f-8e7c-7e27e30f2752
-- title:
--   Index form along a curve, smooth cutoffs, and the index criterion for absence of conjugate points
-- statement:
--   This file defines the index form of a curve in a Riemannian three-manifold together with smooth cutoff fields, and proves the index criterion: nonnegativity of the index form along geodesics rules out conjugate points.
--
--   **Setting.** $M$ is a $C^\infty$ manifold modelled on $\mathbb{R}^3$ with a smooth Riemannian metric $g$; $\gamma : \mathbb{R} \to M$ is a curve and $J, H$ are vector fields along it ($J(s) \in T_{\gamma(s)}M$). Working in the charts of the atlas, $D_s J$ denotes the covariant derivative of $J$ along $\gamma$ (in a chart: $F' + \Gamma(x', F)$ with $\Gamma$ the Christoffel symbols of $g$), $R(J,\gamma')\gamma'$ the curvature term along $\gamma$ (in a chart: $R(F, x')x'$ with the coordinate curvature tensor of $g$), and a field is *smooth on* $U \subseteq \mathbb{R}$ if its coordinates in every atlas chart are $C^\infty$ on $U \cap \gamma^{-1}(\operatorname{dom} c)$. A geodesic on $U$ is a $C^\infty$ curve with $D_s\gamma' = 0$ written chartwise; a Jacobi field on $U$ satisfies, chartwise, $D_sD_sJ + R(J,\gamma')\gamma' = 0$ with $C^\infty$ coordinates; and $g$ has *no conjugate points* if for every open order-connected $U \subseteq \mathbb{R}$ (an open interval, possibly unbounded), every geodesic $\gamma$ on $U$ and every Jacobi field $J$ on $U$, $J(a) = J(b) = 0$ for some $a \neq b$ in $U$ implies $J \equiv 0$ on $U$.
--
--   1. **Cutoffs.** With $\psi$ the standard smooth transition function ($C^\infty$, nondecreasing, $0$ on $(-\infty, 0]$, $1$ on $[1, \infty)$), for $a, b, \varepsilon \in \mathbb{R}$
--   $$
--   \chi_{a,b,\varepsilon}(s) = \psi\Bigl(\frac{s-a}{\varepsilon}\Bigr)\,\psi\Bigl(\frac{b-s}{\varepsilon}\Bigr),
--   $$
--   and the cutoff of a function $f$ with values in a normed space is $s \mapsto \chi_{a,b,\varepsilon}(s)\, f(s)$. Established: $\chi_{a,b,\varepsilon}$ is $C^\infty$ with values in $[0,1]$; for $\varepsilon > 0$ it vanishes outside $(a,b)$ (so cutoff fields have compact support in $[a,b]$) and equals $1$ when $s - a \ge \varepsilon$ and $b - s \ge \varepsilon$.
--   2. **Index form.** The index density and the index form are
--   $$
--   I_s(J, H) = g\bigl(D_sJ, D_sH\bigr) - g\bigl(R(J,\gamma')\gamma',\ H\bigr), \qquad I(J, H) = \int_{\mathbb{R}} I_s(J, H)\, ds .
--   $$
--   3. **Nonnegative index.** The index form of $\gamma$ is *nonnegative on* $U$ if $I(J, J) \ge 0$ for every field $J$ that is smooth on $U$ and has compact support contained in $U$.
--   4. **Chart-constant fields and passages.** For a chart $c$ and $u \in \mathbb{R}^3$, the field $s \mapsto Dc^{-1}\bigl(c(\gamma(s))\bigr)\,u$; and for $U \subseteq \mathbb{R}$, the set of connected components of $U$ (the passages of $U$).
--
--   **Main properties established.** Along a $C^\infty$ curve on an open set $U$: $g(R(J,\gamma')\gamma', H) = g(R(H,\gamma')\gamma', J)$; the index density is $C^\infty$ on $U$, supported in the support of $J$, and integrable for compactly supported $J$; the index form is a quadratic form, so under nonnegativity $I(J,H)^2 \le I(J,J)\,I(H,H)$; for a Jacobi field $J$ one has $\frac{d}{ds}\, g(D_sJ, H) = I_s(J,H)$, hence for $[a,b] \subseteq U$
--   $$
--   \int_a^b I_s(J, H)\, ds = g\bigl(D_sJ(b), H(b)\bigr) - g\bigl(D_sJ(a), H(a)\bigr);
--   $$
--   if moreover $U$ is open and order-connected and $J(a) = J(b) = 0$, then as $\varepsilon \to 0^+$ the cutoffs $J_\varepsilon = \chi_{a,b,\varepsilon} J$ satisfy $I(J_\varepsilon, J_\varepsilon) \to 0$ and $I(J_\varepsilon, H) \to \int_a^b I_s(J,H)\,ds$; and compactly supported smooth fields with prescribed value at $a$ and vanishing at $b$ exist. The resulting **index criterion**: if $U$ is open and order-connected, $\gamma$ is $C^\infty$ on $U$, $J$ is a Jacobi field on $U$, the index form is nonnegative on $U$, and $J(a) = J(b) = 0$ for some $a < b$ in $U$, then $D_sJ(a) = 0$ and therefore $J \equiv 0$ on $U$. Consequently, if for every open order-connected $U$ and every geodesic $\gamma$ on $U$ the index form of $\gamma$ is nonnegative on $U$, then $g$ has no conjugate points.
--
--   This reduces the no-conjugate-points property required by the main theorem to a nonnegativity statement for an integral quadratic form, which can then be verified piece by piece along each geodesic (for instance passage by passage through the necks of the manifold).
--
--   **Formalization Note** The Lean names are `IndexCutoff.cutoff`, `IndexCutoff.field`, `RiemannianCoordinates.indexPairDensity`, `indexPair`, `NonnegativeIndexOn`, `chartConstantField` and `GlobalAssembly.Passages`; the two named results are `intrinsic_index_criterion` and `noConjugatePoints_of_intrinsic_index`. The index form is a Bochner integral over $\mathbb{R}$, which Lean sets to $0$ for non-integrable integrands (the integrand is integrable in all uses). Supports are closed supports (`tsupport`), and the cutoff divides by $\varepsilon$ with the convention $x/0 = 0$. Covariant derivative and curvature along $\gamma$ are computed in `chartAt E3 (γ s)`, with `E3 = Fin 3 → ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Index.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Index.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ConjugatePoints mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning

namespace OAI

noncomputable section

/-!
# Index forms, cutoff fields, and assembly of local estimates.
-/

section

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
namespace ThreeManifold.IndexCutoff

lemma transition_smooth : ContDiff ℝ ∞ smoothTransition := smoothTransition.contDiff (n := ⊤)

lemma transition_deriv_eq_zero {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    deriv smoothTransition x = 0 := by
  rcases lt_or_ge x 0 with h | h
  · have he : smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [gt_mem_nhds h] with y hy
      exact smoothTransition.zero_of_nonpos hy.le
    exact ((hasDerivAt_const x 0).congr_of_eventuallyEq he).deriv
  · have h' : 1 < x := lt_of_not_ge (fun h' => hx ⟨h, h'⟩)
    have he : smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [lt_mem_nhds h'] with y hy
      exact smoothTransition.one_of_one_le hy.le
    exact ((hasDerivAt_const x 1).congr_of_eventuallyEq he).deriv

lemma transition_deriv_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖deriv smoothTransition x‖ ≤ C := by
  have hd : Continuous (deriv smoothTransition) :=
    transition_smooth.continuous_deriv (by simp)
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩) hd.norm.continuousOn
  refine ⟨‖deriv smoothTransition x‖, norm_nonneg _, fun y => ?_⟩
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · exact hmax hy
  · rw [transition_deriv_eq_zero hy, norm_zero]
    positivity

def cutoff (a b ε s : ℝ) : ℝ :=
  smoothTransition ((s - a) / ε) * smoothTransition ((b - s) / ε)

lemma cutoff_smooth (a b ε : ℝ) : ContDiff ℝ ∞ (cutoff a b ε) := by
  unfold cutoff
  fun_prop

lemma cutoff_mem_Icc (a b ε s : ℝ) : cutoff a b ε s ∈ Icc (0 : ℝ) 1 := by
  refine ⟨mul_nonneg (smoothTransition.nonneg _) (smoothTransition.nonneg _), ?_⟩
  exact (mul_le_mul_of_nonneg_right (smoothTransition.le_one _) (smoothTransition.nonneg _)).trans
    (by simpa only [one_mul] using smoothTransition.le_one ((b - s) / ε))

lemma cutoff_eq_zero {a b ε s : ℝ} (hε : 0 < ε) (hs : s ∉ Ioo a b) :
    cutoff a b ε s = 0 := by
  rcases le_or_gt s a with h | h
  · rw [cutoff, smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr h) hε.le), zero_mul]
  · have h' : b ≤ s := le_of_not_gt (fun h' => hs ⟨h, h'⟩)
    rw [cutoff, smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr h') hε.le), mul_zero]

lemma cutoff_eq_one {a b ε s : ℝ} (hε : 0 < ε) (ha : ε ≤ s - a) (hb : ε ≤ b - s) :
    cutoff a b ε s = 1 := by
  rw [cutoff, smoothTransition.one_of_one_le ((le_div_iff₀ hε).mpr (by simpa using ha)),
    smoothTransition.one_of_one_le ((le_div_iff₀ hε).mpr (by simpa using hb)), mul_one]

lemma cutoff_hasDerivAt (a b ε s : ℝ) : HasDerivAt (cutoff a b ε)
    ((deriv smoothTransition ((s - a) / ε) / ε) * smoothTransition ((b - s) / ε) -
      smoothTransition ((s - a) / ε) * (deriv smoothTransition ((b - s) / ε) / ε)) s := by
  have h₁ := (transition_smooth.differentiable (by simp) ((s - a) / ε)).hasDerivAt.comp s (((hasDerivAt_id s).sub_const a).div_const ε)
  have h₂ := (transition_smooth.differentiable (by simp) ((b - s) / ε)).hasDerivAt.comp s (((hasDerivAt_id s).const_sub b).div_const ε)
  have hh := h₁.mul h₂
  simp only [Function.comp_apply, id_eq] at hh
  change HasDerivAt (cutoff a b ε) _ s at hh
  convert hh using 1
  first | rfl | ring

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma contractive_smul {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (v : V) : ‖r • v‖ ≤ ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hr.2

def field (a b ε : ℝ) (f : ℝ → V) (s : ℝ) : V := cutoff a b ε s • f s

lemma field_tsupport {a b ε : ℝ} (hε : 0 < ε) (f : ℝ → V) :
    tsupport (field a b ε f) ⊆ Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  by_contra h
  have hz := cutoff_eq_zero hε (fun hi => h (Ioo_subset_Icc_self hi))
  exact hs (by simp [field, hz])

lemma field_compactSupport {a b ε : ℝ} (hε : 0 < ε) (f : ℝ → V) :
    HasCompactSupport (field a b ε f) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (field_tsupport hε f)

lemma scaled_transition_bound {C D ε x : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    (hC : ∀ t, ‖deriv smoothTransition t‖ ≤ C) (v : V) (hv : ‖v‖ ≤ D * |x|) :
    ‖(deriv smoothTransition (x / ε) / ε) • v‖ ≤ C * D := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  by_cases hx : x / ε ∈ Icc (0 : ℝ) 1
  · have hx0 : 0 ≤ x := by simpa using (le_div_iff₀ hε).mp hx.1
    have hxε : x ≤ ε := (div_le_one hε).mp hx.2
    have hv' : ‖v‖ ≤ D * ε := hv.trans (by rw [abs_of_nonneg hx0]; gcongr)
    rw [norm_smul, norm_div, Real.norm_eq_abs ε, abs_of_pos hε]
    calc
      ‖deriv smoothTransition (x / ε)‖ / ε * ‖v‖ ≤ (C / ε) * (D * ε) := by
        gcongr
        exact hC _
      _ = C * D := by field_simp
  · rw [transition_deriv_eq_zero hx, zero_div, zero_smul, norm_zero]
    positivity

lemma field_deriv_bound {a b ε C D : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    (hC : ∀ t, ‖deriv smoothTransition t‖ ≤ C) {f : ℝ → V}
    (hf : ContDiff ℝ ∞ f) (hfd : ∀ s ∈ Icc a b, ‖deriv f s‖ ≤ D)
    (hfa : f a = 0) (hfb : f b = 0) :
    ∀ s, ‖deriv (field a b ε f) s‖ ≤ (2 * C + 1) * D := by
  intro s
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  by_cases hs : s ∈ Icc a b
  · have hab := hs.1.trans hs.2
    have hfa' : ‖f s‖ ≤ D * |s - a| := by
      simpa [hfa, Real.norm_eq_abs] using (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
        (fun t _ => hf.differentiable (by simp) t) hfd (left_mem_Icc.mpr hab) hs
    have hfb' : ‖f s‖ ≤ D * |b - s| := by
      simpa [hfb, Real.norm_eq_abs] using (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
        (fun t _ => hf.differentiable (by simp) t) hfd hs (right_mem_Icc.mpr hab)
    have h₁ := scaled_transition_bound hε hD hC (f s) hfa'
    have h₂ := scaled_transition_bound hε hD hC (f s) hfb'
    have hd := (cutoff_hasDerivAt a b ε s).smul (hf.differentiable (by simp) s).hasDerivAt
    change HasDerivAt (field a b ε f) _ s at hd
    have he : deriv (field a b ε f) s =
        smoothTransition ((b - s) / ε) • ((deriv smoothTransition ((s - a) / ε) / ε) • f s) -
        smoothTransition ((s - a) / ε) • ((deriv smoothTransition ((b - s) / ε) / ε) • f s) +
        cutoff a b ε s • deriv f s := by
      rw [hd.deriv]
      rw [add_comm]
      simp only [sub_smul, mul_smul]
      congr 1
      exact congrArg₂ (· - ·) (smul_comm _ _ _) rfl
    rw [he]
    calc
      _ ≤ ‖smoothTransition ((b - s) / ε) • ((deriv smoothTransition ((s - a) / ε) / ε) • f s)‖ +
          ‖smoothTransition ((s - a) / ε) • ((deriv smoothTransition ((b - s) / ε) / ε) • f s)‖ +
          ‖cutoff a b ε s • deriv f s‖ := (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ C * D + C * D + D := by
        apply add_le_add
        · apply add_le_add
          · exact (contractive_smul ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩ _).trans h₁
          · exact (contractive_smul ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩ _).trans h₂
        · exact (contractive_smul (cutoff_mem_Icc a b ε s) _).trans (hfd s hs)
      _ = _ := by ring
  · rw [deriv_of_notMem_tsupport (fun h => hs (field_tsupport hε f h)), norm_zero]
    positivity

lemma field_eventuallyEq {a b ε s : ℝ} (hε : 0 < ε)
    (ha : ε < s - a) (hb : ε < b - s) (f : ℝ → V) :
    field a b ε f =ᶠ[𝓝 s] f := by
  filter_upwards [Ioo_mem_nhds (show a + ε < s by linarith) (show s < b - ε by linarith)] with t ht
  simp only [field, cutoff_eq_one (a := a) (b := b) (s := t) hε (by linarith [ht.1]) (by linarith [ht.2]), one_smul]

lemma field_jet_eventuallyEq {a b s : ℝ} (hs : s ∈ Ioo a b) (f : ℝ → V) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      field a b ε f s = f s ∧ deriv (field a b ε f) s = deriv f s := by
  have ha : {ε : ℝ | ε < s - a} ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (sub_pos.mpr hs.1))
  have hb : {ε : ℝ | ε < b - s} ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (sub_pos.mpr hs.2))
  filter_upwards [self_mem_nhdsWithin, ha, hb] with ε hε ha hb
  have he := field_eventuallyEq hε ha hb f
  exact ⟨he.eq_of_nhds, he.deriv_eq⟩

end ThreeManifold.IndexCutoff

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace ThreeManifold.IndexForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end ThreeManifold.IndexForm

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
namespace ThreeManifold.IndexForm

section
open IndexCutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
lemma bound_nonneg {a b : ℝ} (hab : a ≤ b) {f : ℝ → V} (hf : Continuous f) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s ∈ Icc a b, ‖f s‖ ≤ D := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨D, (norm_nonneg _).trans (hD a (left_mem_Icc.mpr hab)), hD⟩

end

section
open IndexCutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end

open IndexCutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma interval_enlargement {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    {a b : ℝ} (ha : a ∈ U) (hb : b ∈ U) :
    ∃ c d : ℝ, c < a ∧ b < d ∧ Icc c d ⊆ U := by
  obtain ⟨l, r, har, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds ha)
  obtain ⟨l', r', hbr, hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hb)
  have hc : (l+a)/2 ∈ U := hsub ⟨by linarith [har.1], by linarith [har.1,har.2]⟩
  have hd : (b+r')/2 ∈ U := hsub' ⟨by linarith [hbr.1,hbr.2], by linarith [hbr.2]⟩
  exact ⟨(l+a)/2, (b+r')/2, by linarith [har.1], by linarith [hbr.2], hUc.out hc hd⟩

lemma smooth_extension_near_interval {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    {a b : ℝ} (ha : a ∈ U) (hb : b ∈ U) {f : ℝ → V} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ F : ℝ → V, ContDiff ℝ ∞ F ∧ ∀ s ∈ Icc a b, F =ᶠ[𝓝 s] f := by
  obtain ⟨c,d,hca,hbd,hcdU⟩ := interval_enlargement hU hUc ha hb
  let ε := min (a-c) (d-b)/2
  have hε : 0 < ε := by dsimp [ε]; exact half_pos (lt_min (sub_pos.mpr hca) (sub_pos.mpr hbd))
  have hεa : ε < a-c := by dsimp [ε]; linarith [min_le_left (a-c) (d-b)]
  have hεb : ε < d-b := by dsimp [ε]; linarith [min_le_right (a-c) (d-b)]
  refine ⟨field c d ε f, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro s
    by_cases hs : s ∈ U
    · exact (cutoff_smooth c d ε).contDiffAt.smul ((hf s hs).contDiffAt (hU.mem_nhds hs))
    · have hn : s ∉ tsupport (field c d ε f) := fun h => hs (hcdU (field_tsupport hε f h))
      exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)
  · intro s hs
    exact field_eventuallyEq hε (by linarith [hs.1]) (by linarith [hs.2]) f

end ThreeManifold.IndexForm
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

def indexPairDensity (g : SmoothMetric M) (γ : ℝ → M)
    (J H : ∀ s, TangentSpace I3 (γ s)) (s : ℝ) : ℝ :=
  g.inner (γ s) (covariantDerivative g γ J s) (covariantDerivative g γ H s) -
    g.inner (γ s) (curvatureAlong g γ J s) (H s)

def indexPair (g : SmoothMetric M) (γ : ℝ → M)
    (J H : ∀ s, TangentSpace I3 (γ s)) : ℝ := ∫ s, indexPairDensity g γ J H s

def NonnegativeIndexOn (g : SmoothMetric M) (γ : ℝ → M) (U : Set ℝ) : Prop :=
  ∀ J : ∀ s, TangentSpace I3 (γ s), SmoothFieldOn γ J U →
    HasCompactSupport J → tsupport J ⊆ U → 0 ≤ indexPair g γ J J

lemma curvatureAlong_pairing_symm (g : SmoothMetric M) {γ : ℝ → M}
    (J H : ∀ s, TangentSpace I3 (γ s)) {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) :
    g.inner (γ s) (curvatureAlong g γ J s) (H s) =
      g.inner (γ s) (curvatureAlong g γ H s) (J s) := by
  have hc := chart_mem_atlas E3 (γ s)
  have hsc := mem_chart_source E3 (γ s)
  rw [← metric_field_coordinates g (curvatureAlong g γ J) H hc hsc,
    ← metric_field_coordinates g (curvatureAlong g γ H) J hc hsc,
    curvatureAlong_coordinates g J hγ hc hsc,curvatureAlong_coordinates g H hγ hc hsc]
  exact curvature_pairing_selfAdjoint g hc ((chartAt E3 (γ s)).map_source hsc) _ _ _

lemma covariantDerivative_eq_zero_of_notMem_tsupport (g : SmoothMetric M) (γ : ℝ → M)
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ} (hs : s ∉ tsupport J) :
    covariantDerivative g γ J s = 0 := by
  have he : fieldCoordinates γ J (chartAt E3 (γ s)) =ᶠ[𝓝 s] (fun _ => (0:E3)) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hs] with r hr
    change J r = 0 at hr
    exact (congrArg (mfderiv I3 I3 (chartAt E3 (γ s)) (γ r)) hr).trans (map_zero _)
  have hd : deriv (fieldCoordinates γ J (chartAt E3 (γ s))) s = 0 := by
    rw [he.deriv_eq,deriv_const]
  let c := chartAt E3 (γ s)
  let P : E3 →L[ℝ] TangentSpace I3 (γ s) := mfderiv I3 I3 c.symm (c (γ s))
  change P (deriv (fieldCoordinates γ J c) s +
    connectionTerm g c (c (γ s)) (deriv (c ∘ γ) s) (fieldCoordinates γ J c s)) = 0
  rw [hd,he.eq_of_nhds,← connectionLinear_apply,map_zero,add_zero,map_zero]

lemma curvatureAlong_eq_zero (g : SmoothMetric M) (γ : ℝ → M)
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ} (hs : J s = 0) :
    curvatureAlong g γ J s = 0 := by
  let c := chartAt E3 (γ s)
  let P : E3 →L[ℝ] TangentSpace I3 (γ s) := mfderiv I3 I3 c.symm (c (γ s))
  have hz : fieldCoordinates γ J c s = 0 :=
    (congrArg (mfderiv I3 I3 c (γ s)) hs).trans (map_zero _)
  change P (curvatureTerm g c (c (γ s)) (fieldCoordinates γ J c s)
    (deriv (c ∘ γ) s) (deriv (c ∘ γ) s)) = 0
  rw [hz,← curvatureLinear_apply,map_zero,map_zero]

lemma indexPairDensity_support (g : SmoothMetric M) (γ : ℝ → M)
    (J H : ∀ s, TangentSpace I3 (γ s)) :
    Function.support (indexPairDensity g γ J H) ⊆ tsupport J := by
  intro s hs
  by_contra hn
  apply hs
  simp only [indexPairDensity,covariantDerivative_eq_zero_of_notMem_tsupport g γ J hn,
    curvatureAlong_eq_zero g γ J (image_eq_zero_of_notMem_tsupport hn),map_zero,
    _root_.zero_apply,sub_zero]

lemma indexPairDensity_smooth (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U)
    (hH : SmoothFieldOn γ H U) : ContDiffOn ℝ ∞ (indexPairDensity g γ J H) U :=
  (intrinsic_pairing_smooth g hU hγ (covariantDerivative_smooth g hU hγ hJ)
    (covariantDerivative_smooth g hU hγ hH)).sub
    (intrinsic_pairing_smooth g hU hγ (curvatureAlong_smooth g hU hγ hJ) hH)

lemma indexPairDensity_continuous (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U)
    (hH : SmoothFieldOn γ H U) (hJU : tsupport J ⊆ U) :
    Continuous (indexPairDensity g γ J H) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : s ∈ U
  · exact ((indexPairDensity_smooth g hU hγ hJ hH).continuousOn s hs).continuousAt (hU.mem_nhds hs)
  · have hn : s ∉ tsupport (indexPairDensity g γ J H) := fun hn =>
      hs (hJU (closure_minimal (indexPairDensity_support g γ J H) isClosed_closure hn))
    exact continuousAt_const.congr (notMem_tsupport_iff_eventuallyEq.mp hn).symm

lemma indexPairDensity_integrable (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U)
    (hH : SmoothFieldOn γ H U) (hJc : HasCompactSupport J) (hJU : tsupport J ⊆ U) :
    Integrable (indexPairDensity g γ J H) :=
  (indexPairDensity_continuous g hU hγ hJ hH hJU).integrable_of_hasCompactSupport
    (hJc.mono' (indexPairDensity_support g γ J H))

lemma indexPairDensity_quadratic (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U)
    (hH : SmoothFieldOn γ H U) {s : ℝ} (hs : s ∈ U) (t : ℝ) :
    indexPairDensity g γ (fun r => J r + t • H r) (fun r => J r + t • H r) s =
      indexPairDensity g γ J J s + 2*t*indexPairDensity g γ J H s +
        t^2*indexPairDensity g γ H H s := by
  have hd : covariantDerivative g γ (fun r => t • H r) s = t • covariantDerivative g γ H s := by
    rw [covariantDerivative_smul g hU hγ hH hs (differentiableAt_const t),deriv_const,
      zero_smul,zero_add]
  unfold indexPairDensity
  rw [covariantDerivative_add g hU hγ hJ (smoothField_smul contDiffOn_const hH) hs,
    hd,curvatureAlong_add,curvatureAlong_smul]
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  rw [g.symm (γ s) (covariantDerivative g γ H s) (covariantDerivative g γ J s),
    curvatureAlong_pairing_symm g H J (hγ.contMDiffAt (hU.mem_nhds hs))]
  ring

lemma indexPair_quadratic (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U)
    (hH : SmoothFieldOn γ H U) (hJc : HasCompactSupport J) (hHc : HasCompactSupport H)
    (hJU : tsupport J ⊆ U) (hHU : tsupport H ⊆ U) (t : ℝ) :
    indexPair g γ (fun r => J r + t • H r) (fun r => J r + t • H r) =
      indexPair g γ J J + 2*t*indexPair g γ J H + t^2*indexPair g γ H H := by
  have hff := indexPairDensity_integrable g hU hγ hJ hJ hJc hJU
  have hfg := indexPairDensity_integrable g hU hγ hJ hH hJc hJU
  have hgg := indexPairDensity_integrable g hU hγ hH hH hHc hHU
  have he (s : ℝ) : indexPairDensity g γ (fun r => J r + t • H r) (fun r => J r + t • H r) s =
      indexPairDensity g γ J J s + 2*t*indexPairDensity g γ J H s + t^2*indexPairDensity g γ H H s := by
    by_cases hs : s ∈ U
    · exact indexPairDensity_quadratic g hU hγ hJ hH hs t
    · have hz {F G : ∀ s, TangentSpace I3 (γ s)} (hF : tsupport F ⊆ U) : indexPairDensity g γ F G s = 0 := by
        by_contra hn
        exact hs (hF (indexPairDensity_support g γ F G hn))
      rw [hz hJU,hz hJU,hz hHU,hz (show tsupport (fun r => J r + t • H r) ⊆ U from
        (tsupport_add _ _).trans (union_subset hJU ((tsupport_smul_subset_right _ _).trans hHU)))]
      ring
  simp only [indexPair,he]
  have hi : Integrable (fun s => indexPairDensity g γ J J s + (2*t) * indexPairDensity g γ J H s) :=
    hff.add (hfg.const_mul (2*t))
  rw [integral_add hi (hgg.const_mul (t^2)),
    integral_add hff (hfg.const_mul (2*t)),integral_const_mul,integral_const_mul]

lemma indexPair_polynomial_nonneg (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hpos : NonnegativeIndexOn g γ U)
    (hJ : SmoothFieldOn γ J U) (hH : SmoothFieldOn γ H U)
    (hJc : HasCompactSupport J) (hHc : HasCompactSupport H)
    (hJU : tsupport J ⊆ U) (hHU : tsupport H ⊆ U) (t : ℝ) :
    0 ≤ indexPair g γ J J + 2*t*indexPair g γ J H + t^2*indexPair g γ H H := by
  have hts : tsupport (fun r => J r + t • H r) ⊆ tsupport J ∪ tsupport H :=
    (tsupport_add _ _).trans (union_subset_union Subset.rfl (tsupport_smul_subset_right _ _))
  have hHs : SmoothFieldOn γ (fun r => t • H r) U := smoothField_smul contDiffOn_const hH
  have hJs : SmoothFieldOn γ (fun r => J r + t • H r) U := smoothField_add hJ hHs
  have hcs : HasCompactSupport (fun r => J r + t • H r) :=
    (hJc.union hHc).of_isClosed_subset isClosed_closure hts
  have hp := hpos (fun r => J r + t • H r) hJs hcs (hts.trans (union_subset hJU hHU))
  rwa [indexPair_quadratic g hU hγ hJ hH hJc hHc hJU hHU t] at hp

lemma indexPair_cauchy_schwarz (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hpos : NonnegativeIndexOn g γ U)
    (hJ : SmoothFieldOn γ J U) (hH : SmoothFieldOn γ H U)
    (hJc : HasCompactSupport J) (hHc : HasCompactSupport H)
    (hJU : tsupport J ⊆ U) (hHU : tsupport H ⊆ U) :
    indexPair g γ J H ^ 2 ≤ indexPair g γ J J * indexPair g γ H H := by
  have hp := indexPair_polynomial_nonneg g hU hγ hpos hJ hH hJc hHc hJU hHU
  have hd := discrim_le_zero (a := indexPair g γ H H) (b := 2*indexPair g γ J H)
    (c := indexPair g γ J J) (fun t => by nlinarith [hp t])
  unfold discrim at hd
  nlinarith

lemma indexPairDensity_smul (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U)
    {f : ℝ → ℝ} {s : ℝ} (hs : s ∈ U) (hf : DifferentiableAt ℝ f s) :
    indexPairDensity g γ (fun r => f r • J r) H s =
      f s * indexPairDensity g γ J H s + deriv f s * g.inner (γ s) (J s) (covariantDerivative g γ H s) := by
  unfold indexPairDensity
  rw [covariantDerivative_smul g hU hγ hJ hs hf,curvatureAlong_smul]
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  ring

lemma indexDensity_smul (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U)
    {f : ℝ → ℝ} {s : ℝ} (hs : s ∈ U) (hf : DifferentiableAt ℝ f s) :
    indexPairDensity g γ (fun r => f r • J r) (fun r => f r • J r) s =
      (f s)^2 * indexPairDensity g γ J J s + 2*f s*deriv f s *
        g.inner (γ s) (covariantDerivative g γ J s) (J s) +
      (deriv f s)^2 * g.inner (γ s) (J s) (J s) := by
  unfold indexPairDensity
  rw [covariantDerivative_smul g hU hγ hJ hs hf,curvatureAlong_smul]
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  rw [g.symm (γ s) (J s) (covariantDerivative g γ J s)]
  ring

lemma jacobi_indexPairDensity_hasDerivAt (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : IsJacobiFieldOn g γ J U)
    (hH : SmoothFieldOn γ H U) {s : ℝ} (hs : s ∈ U) :
    HasDerivAt (fun r => g.inner (γ r) (covariantDerivative g γ J r) (H r))
      (indexPairDensity g γ J H s) s := by
  have hd := intrinsic_pairing_hasDerivAt g hU hγ
    (covariantDerivative_smooth g hU hγ (jacobi_smoothField g hJ)) hH hs
  have he := eq_neg_of_add_eq_zero_left (jacobi_intrinsic_equation g hU hγ hJ hs)
  simpa only [indexPairDensity,he,map_neg,_root_.neg_apply,sub_eq_add_neg,add_comm] using hd

lemma jacobi_indexPair_integral (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : IsJacobiFieldOn g γ J U)
    (hH : SmoothFieldOn γ H U) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U) :
    (∫ s in Ioo a b, indexPairDensity g γ J H s) =
      g.inner (γ b) (covariantDerivative g γ J b) (H b) -
        g.inner (γ a) (covariantDerivative g γ J a) (H a) := by
  rw [← integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    apply jacobi_indexPairDensity_hasDerivAt g hU hγ hJ hH
    exact hsub (by simpa only [uIcc_of_le hab] using hs)
  · apply ContinuousOn.intervalIntegrable
    exact ((indexPairDensity_smooth g hU hγ (jacobi_smoothField g hJ) hH).continuousOn.mono hsub).mono
      (by rw [uIcc_of_le hab])
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter MeasureTheory Real
open scoped Topology ContDiff
namespace ThreeManifold.IndexCutoff

lemma endpoint_second_order_bound {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    {a b D : ℝ} (_hab : a ≤ b) (hD : 0 ≤ D)
    (hbound : ∀ s ∈ Icc a b, ‖deriv (deriv q) s‖ ≤ D)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hq0 : q x = 0) (hqd0 : deriv q x = 0) : ‖q y‖ ≤ D * |y-x| ^ 2 := by
  have hqd : ContDiff ℝ ∞ (deriv q) := (contDiff_infty_iff_deriv.mp hq).2
  have hsub : uIcc x y ⊆ Icc a b := (ordConnected_Icc).uIcc_subset hx hy
  have hdist (r : ℝ) (hr : r ∈ uIcc x y) : |r-x| ≤ |y-x| := by
    rcases le_total x y with hxy | hyx
    · rw [uIcc_of_le hxy] at hr
      rw [abs_of_nonneg (sub_nonneg.mpr hr.1),abs_of_nonneg (sub_nonneg.mpr hxy)]
      linarith [hr.2]
    · rw [uIcc_of_ge hyx] at hr
      rw [abs_of_nonpos (sub_nonpos.mpr hr.2),abs_of_nonpos (sub_nonpos.mpr hyx)]
      linarith [hr.1]
  have hderiv (r : ℝ) (hr : r ∈ uIcc x y) : ‖deriv q r‖ ≤ D * |y-x| := by
    have hh := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (fun s _ => hqd.differentiable (by simp) s) hbound hx (hsub hr)
    have hh' : ‖deriv q r‖ ≤ D * |r-x| := by
      simpa only [hqd0,sub_zero,Real.norm_eq_abs] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left (hdist r hr) hD)
  have hh := (convex_uIcc x y).norm_image_sub_le_of_norm_deriv_le
    (fun s _ => hq.differentiable (by simp) s) hderiv (left_mem_uIcc) (right_mem_uIcc)
  simpa only [hq0,sub_zero,Real.norm_eq_abs,mul_assoc,pow_two] using hh

lemma scaled_transition_square_bound {C D ε x z : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    (hC : ∀ t, ‖deriv smoothTransition t‖ ≤ C) (hz : ‖z‖ ≤ D * x ^ 2) :
    (deriv smoothTransition (x/ε) / ε) ^ 2 * ‖z‖ ≤ C ^ 2 * D := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  by_cases hx : x/ε ∈ Icc (0:ℝ) 1
  · have hx0 : 0 ≤ x := by simpa using (le_div_iff₀ hε).mp hx.1
    have hxε : x ≤ ε := (div_le_one hε).mp hx.2
    have hz' : ‖z‖ ≤ D * ε ^ 2 := hz.trans (mul_le_mul_of_nonneg_left
      (by nlinarith) hD)
    have ha : (deriv smoothTransition (x/ε) / ε)^2 ≤ (C/ε)^2 := by
      have hn : |deriv smoothTransition (x/ε)| ≤ C := hC _
      rw [div_pow,div_pow]
      exact div_le_div_of_nonneg_right (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC0).mpr hn) (sq_nonneg ε)
    calc
      _ ≤ (C/ε)^2 * (D*ε^2) := mul_le_mul ha hz' (norm_nonneg _) (sq_nonneg _)
      _ = C^2*D := by field_simp
  · rw [transition_deriv_eq_zero hx,zero_div,zero_pow (by decide),zero_mul]
    positivity

lemma cutoff_square_bound {a b C D ε : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    (hC : ∀ t, ‖deriv smoothTransition t‖ ≤ C) (q : ℝ → ℝ)
    (hleft : ∀ s ∈ Icc a b, ‖q s‖ ≤ D * (s-a)^2)
    (hright : ∀ s ∈ Icc a b, ‖q s‖ ≤ D * (b-s)^2)
    {s : ℝ} (hs : s ∈ Icc a b) :
    ‖(deriv (cutoff a b ε) s)^2 * q s‖ ≤ 4 * C^2*D := by
  have hl := scaled_transition_square_bound hε hD hC (hleft s hs)
  have hr := scaled_transition_square_bound hε hD hC (hright s hs)
  let A := deriv smoothTransition ((s-a)/ε)/ε
  let B := deriv smoothTransition ((b-s)/ε)/ε
  let f := smoothTransition ((s-a)/ε)
  let h := smoothTransition ((b-s)/ε)
  have hf : f ∈ Icc (0:ℝ) 1 := ⟨smoothTransition.nonneg _,smoothTransition.le_one _⟩
  have hh : h ∈ Icc (0:ℝ) 1 := ⟨smoothTransition.nonneg _,smoothTransition.le_one _⟩
  have hsq : (A*h-f*B)^2 ≤ 2*A^2+2*B^2 := by
    have hf2 : f^2 ≤ 1 := by nlinarith [hf.1,hf.2]
    have hh2 : h^2 ≤ 1 := by nlinarith [hh.1,hh.2]
    have hfB : (f*B)^2 ≤ B^2 := by nlinarith [mul_le_mul_of_nonneg_right hf2 (sq_nonneg B)]
    have hhA : (A*h)^2 ≤ A^2 := by nlinarith [mul_le_mul_of_nonneg_left hh2 (sq_nonneg A)]
    nlinarith [sq_nonneg (A*h+f*B)]
  rw [(cutoff_hasDerivAt a b ε s).deriv,norm_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  change (A*h-f*B)^2 * ‖q s‖ ≤ _
  have hn := mul_le_mul_of_nonneg_right hsq (norm_nonneg (q s))
  change A^2 * ‖q s‖ ≤ _ at hl
  change B^2 * ‖q s‖ ≤ _ at hr
  nlinarith

lemma cutoff_deriv_mul_bound {a b C D ε : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    (hC : ∀ t, ‖deriv smoothTransition t‖ ≤ C) {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (hbound : ∀ s ∈ Icc a b, ‖deriv q s‖ ≤ D)
    (ha : q a = 0) (hb : q b = 0) {s : ℝ} (hs : s ∈ Icc a b) :
    ‖deriv (cutoff a b ε) s * q s‖ ≤ (2*C+2)*D := by
  have hd := field_deriv_bound hε hD hC hq hbound ha hb s
  have h := (((cutoff_smooth a b ε).differentiable (by simp) s).hasDerivAt.mul
    (hq.differentiable (by simp) s).hasDerivAt).deriv
  have h' : deriv (field a b ε q) s = deriv (cutoff a b ε) s * q s + cutoff a b ε s * deriv q s := by
    convert h using 1 ; rfl
  have hh : ‖cutoff a b ε s * deriv q s‖ ≤ D :=
    (contractive_smul (cutoff_mem_Icc a b ε s) (deriv q s)).trans (hbound s hs)
  rw [h'] at hd
  have hn := norm_sub_le (deriv (cutoff a b ε) s * q s + cutoff a b ε s * deriv q s)
    (cutoff a b ε s * deriv q s)
  rw [add_sub_cancel_right] at hn
  nlinarith
end ThreeManifold.IndexCutoff
end

section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace ThreeManifold.IndexCutoff

lemma cutoff_jet_eventually {a b s : ℝ} (hs : s ∈ Ioo a b) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), cutoff a b ε s = 1 ∧ deriv (cutoff a b ε) s = 0 := by
  filter_upwards [field_jet_eventuallyEq hs (fun _ : ℝ => (1:ℝ))] with ε he
  have hfun : field a b ε (fun _ : ℝ => (1:ℝ)) = cutoff a b ε := by
    funext r; simp only [field,smul_eq_mul,mul_one]
  rw [hfun,deriv_const] at he
  exact he

lemma cutoff_square_integral_tendsto_zero {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    {a b : ℝ} (hab : a ≤ b) (ha : a ∈ U) (hb : b ∈ U) {q : ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hqa : q a = 0) (hqb : q b = 0)
    (hqda : deriv q a = 0) (hqdb : deriv q b = 0) :
    Tendsto (fun ε => ∫ s in Ioo a b, (deriv (cutoff a b ε) s)^2 * q s)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨Q,hQ,hEq⟩ := IndexForm.smooth_extension_near_interval hU hUc ha hb hq
  have hQa : Q a = 0 := (hEq a (left_mem_Icc.mpr hab)).eq_of_nhds.trans hqa
  have hQb : Q b = 0 := (hEq b (right_mem_Icc.mpr hab)).eq_of_nhds.trans hqb
  have hQda : deriv Q a = 0 := (hEq a (left_mem_Icc.mpr hab)).deriv_eq.trans hqda
  have hQdb : deriv Q b = 0 := (hEq b (right_mem_Icc.mpr hab)).deriv_eq.trans hqdb
  have hQd : ContDiff ℝ ∞ (deriv Q) := (contDiff_infty_iff_deriv.mp hQ).2
  obtain ⟨C,hC0,hC⟩ := transition_deriv_bounded
  obtain ⟨D,hD0,hD⟩ := IndexForm.bound_nonneg hab (hQd.continuous_deriv (by simp))
  have hleft (s) (hs : s ∈ Icc a b) : ‖Q s‖ ≤ D*(s-a)^2 := by
    simpa only [sq_abs] using endpoint_second_order_bound hQ hab hD0 hD
      (left_mem_Icc.mpr hab) hs hQa hQda
  have hright (s) (hs : s ∈ Icc a b) : ‖Q s‖ ≤ D*(b-s)^2 := by
    have he := endpoint_second_order_bound hQ hab hD0 hD (right_mem_Icc.mpr hab) hs hQb hQdb
    simpa only [sq_abs,sub_sq_comm] using he
  have hlim : Tendsto (fun ε => ∫ s in Ioo a b, (deriv (cutoff a b ε) s)^2 * Q s)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ _ : ℝ in Ioo a b, (0:ℝ))) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Filter.Eventually.of_forall (fun ε =>
        (((cutoff_smooth a b ε).continuous_deriv (by simp)).pow 2 |>.mul hQ.continuous).aestronglyMeasurable)
    · refine ⟨4*C^2*D, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact cutoff_square_bound hε hD0 hC Q hleft hright (Ioo_subset_Icc_self hs)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_jet_eventually hs] with ε he
      simp [he.2]
  simp only [integral_zero] at hlim
  apply hlim.congr'
  exact Filter.Eventually.of_forall (fun ε => setIntegral_congr_fun measurableSet_Ioo
    (fun s hs => by rw [(hEq s (Ioo_subset_Icc_self hs)).eq_of_nhds]))

lemma cutoff_mixed_integral_tendsto {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    {a b : ℝ} (hab : a ≤ b) (ha : a ∈ U) (hb : b ∈ U) {q r : ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hr : ContinuousOn r (Icc a b)) (hqa : q a = 0) (hqb : q b = 0) :
    Tendsto (fun ε => ∫ s in Ioo a b, cutoff a b ε s * r s + deriv (cutoff a b ε) s * q s)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ s in Ioo a b, r s)) := by
  obtain ⟨Q,hQ,hEq⟩ := IndexForm.smooth_extension_near_interval hU hUc ha hb hq
  have hQa : Q a = 0 := (hEq a (left_mem_Icc.mpr hab)).eq_of_nhds.trans hqa
  have hQb : Q b = 0 := (hEq b (right_mem_Icc.mpr hab)).eq_of_nhds.trans hqb
  obtain ⟨C,hC0,hC⟩ := transition_deriv_bounded
  obtain ⟨D,hD0,hD⟩ := IndexForm.bound_nonneg hab (hQ.continuous_deriv (by simp))
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hr
  have hlim : Tendsto
      (fun ε => ∫ s in Ioo a b, cutoff a b ε s * r s + deriv (cutoff a b ε) s * Q s)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ s in Ioo a b, r s)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · refine Filter.Eventually.of_forall (fun ε => ?_)
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
      exact (((cutoff_smooth a b ε).continuous.continuousOn.mul (hr.mono Ioo_subset_Icc_self)).add
        (((cutoff_smooth a b ε).continuous_deriv (by simp)).continuousOn.mul hQ.continuous.continuousOn))
    · refine ⟨K+(2*C+2)*D, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hfr : ‖cutoff a b ε s * r s‖ ≤ K :=
        (contractive_smul (cutoff_mem_Icc a b ε s) (r s)).trans (hK s (Ioo_subset_Icc_self hs))
      exact (norm_add_le _ _).trans (add_le_add hfr
        (cutoff_deriv_mul_bound hε hD0 hC hQ hD hQa hQb (Ioo_subset_Icc_self hs)))
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_jet_eventually hs] with ε he
      simp only [he.1,he.2,one_mul,zero_mul,add_zero]
  apply hlim.congr'
  exact Filter.Eventually.of_forall (fun ε => setIntegral_congr_fun measurableSet_Ioo
    (fun s hs => by rw [(hEq s (Ioo_subset_Icc_self hs)).eq_of_nhds]))
end ThreeManifold.IndexCutoff
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
open IndexCutoff

lemma cutoff_indexPair_eq_Ioo (g : SmoothMetric M) (γ : ℝ → M)
    (J H : ∀ s, TangentSpace I3 (γ s)) {a b ε : ℝ} (hε : 0 < ε) :
    indexPair g γ (field a b ε J) H = ∫ s in Ioo a b, indexPairDensity g γ (field a b ε J) H s := by
  change (∫ s, indexPairDensity g γ (field a b ε J) H s) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a b)]
  · exact integral_Icc_eq_integral_Ioo
  · intro s hs
    by_contra hn
    exact hs (field_tsupport hε J (indexPairDensity_support g γ (field a b ε J) H hn))

lemma jacobi_cutoff_energy (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : IsJacobiFieldOn g γ J U)
    {a b ε : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U) (hε : 0 < ε) :
    indexPair g γ (field a b ε J) (field a b ε J) =
      ∫ s in Ioo a b, (deriv (cutoff a b ε) s)^2 * g.inner (γ s) (J s) (J s) := by
  let f := cutoff a b ε
  let W := field a b ε J
  have hJs := jacobi_smoothField g hJ
  have hWs : SmoothFieldOn γ W U := smoothField_smul (cutoff_smooth a b ε).contDiffOn hJs
  let p := fun s => g.inner (γ s) (covariantDerivative g γ J s) (J s)
  let q := fun s => (deriv f s)^2 * g.inner (γ s) (J s) (J s)
  have he (s) (hs : s ∈ Icc a b) : HasDerivAt (fun r => (f r)^2*p r)
      (indexPairDensity g γ W W s - q s) s := by
    have hf := ((cutoff_smooth a b ε).differentiable (by simp) s).hasDerivAt
    have hp := jacobi_indexPairDensity_hasDerivAt g hU hγ hJ hJs (hsub hs)
    have hh := (hf.pow 2).mul hp
    apply hh.congr_deriv
    change _ = indexPairDensity g γ (fun r => f r • J r) (fun r => f r • J r) s - q s
    rw [indexDensity_smul g hU hγ hJs (hsub hs) hf.differentiableAt]
    dsimp only [p,q,f,Pi.pow_apply]
    ring
  have hi : IntervalIntegrable (indexPairDensity g γ W W) volume a b :=
    (((indexPairDensity_smooth g hU hγ hWs hWs).continuousOn.mono hsub).mono
      (by rw [uIcc_of_le hab])).intervalIntegrable
  have hq : IntervalIntegrable q volume a b := by
    have hc : ContinuousOn q (Icc a b) :=
      ((cutoff_smooth a b ε).continuous_deriv (by simp)).continuousOn.pow 2 |>.mul
        ((intrinsic_pairing_smooth g hU hγ hJs hJs).continuousOn.mono hsub)
    exact (hc.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => he s (by simpa only [uIcc_of_le hab] using hs)) (hi.sub hq)
  rw [intervalIntegral.integral_sub hi hq] at hFTC
  have hfa : f a = 0 := cutoff_eq_zero hε (by simp)
  have hfb : f b = 0 := cutoff_eq_zero hε (by simp)
  simp only [hfa,hfb,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,sub_self] at hFTC
  have hInt : (∫ s in a..b, indexPairDensity g γ W W s) = ∫ s in a..b, q s := sub_eq_zero.mp hFTC
  rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc,← integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioo] at hInt
  rw [cutoff_indexPair_eq_Ioo g γ J (field a b ε J) hε]
  exact hInt

lemma jacobi_cutoff_index_tendsto_zero (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : IsJacobiFieldOn g γ J U)
    {a b : ℝ} (hab : a ≤ b) (ha : a ∈ U) (hb : b ∈ U) (hJa : J a = 0) (hJb : J b = 0) :
    Tendsto (fun ε => indexPair g γ (field a b ε J) (field a b ε J)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hJs := jacobi_smoothField g hJ
  let q := fun s => g.inner (γ s) (J s) (J s)
  have hq : ContDiffOn ℝ ∞ q U := intrinsic_pairing_smooth g hU hγ hJs hJs
  have hqa : q a = 0 := by simp only [q,hJa,map_zero]
  have hqb : q b = 0 := by simp only [q,hJb,map_zero]
  have hqda : deriv q a = 0 := by
    have hh := (intrinsic_pairing_hasDerivAt g hU hγ hJs hJs ha).deriv
    simpa only [hJa,map_zero,_root_.zero_apply,add_zero] using hh
  have hqdb : deriv q b = 0 := by
    have hh := (intrinsic_pairing_hasDerivAt g hU hγ hJs hJs hb).deriv
    simpa only [hJb,map_zero,_root_.zero_apply,add_zero] using hh
  have hl := cutoff_square_integral_tendsto_zero hU hUc hab ha hb hq hqa hqb hqda hqdb
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (jacobi_cutoff_energy g hU hγ hJ hab (hUc.out ha hb) hε).symm

lemma cutoff_indexPair_tendsto (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U) (hH : SmoothFieldOn γ H U)
    {a b : ℝ} (hab : a ≤ b) (ha : a ∈ U) (hb : b ∈ U) (hJa : J a = 0) (hJb : J b = 0) :
    Tendsto (fun ε => indexPair g γ (field a b ε J) H) (𝓝[>] (0:ℝ))
      (𝓝 (∫ s in Ioo a b, indexPairDensity g γ J H s)) := by
  let q := fun s => g.inner (γ s) (J s) (covariantDerivative g γ H s)
  have hq : ContDiffOn ℝ ∞ q U := intrinsic_pairing_smooth g hU hγ hJ
    (covariantDerivative_smooth g hU hγ hH)
  have hqa : q a = 0 := by simp only [q,hJa,map_zero,_root_.zero_apply]
  have hqb : q b = 0 := by simp only [q,hJb,map_zero,_root_.zero_apply]
  have hl := cutoff_mixed_integral_tendsto hU hUc hab ha hb hq
    ((indexPairDensity_smooth g hU hγ hJ hH).continuousOn.mono (hUc.out ha hb)) hqa hqb
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [cutoff_indexPair_eq_Ioo g γ J H hε]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hs
  exact (indexPairDensity_smul g hU hγ hJ (hUc.out ha hb (Ioo_subset_Icc_self hs))
    ((cutoff_smooth a b ε).differentiable (by simp) s)).symm
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

def chartConstantField (γ : ℝ → M) (c : OpenPartialHomeomorph M E3) (u : E3)
    (s : ℝ) : TangentSpace I3 (γ s) := mfderiv I3 I3 c.symm (c (γ s)) u

lemma chartConstantField_coordinates {γ : ℝ → M} {c d : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M) {s : ℝ}
    (hsc : γ s ∈ c.source) (hsd : γ s ∈ d.source) (u : E3) :
    fieldCoordinates γ (chartConstantField γ c u) d s = fderiv ℝ (d ∘ c.symm) (c (γ s)) u :=
  push_from_chart hc hd hsc hsd u

lemma chartConstantField_smoothAt {γ : ℝ → M} {c d : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M) {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) (hsc : γ s ∈ c.source) (hsd : γ s ∈ d.source) (u : E3) :
    ContDiffAt ℝ ∞ (fieldCoordinates γ (chartConstantField γ c u) d) s := by
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  have hx : ContDiffAt ℝ ∞ (c ∘ γ) s := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (subset_maximalAtlas hc) hsc).comp s hγ)
  have htr := transition_smoothAt hc hd (c.map_source hsc)
    (show c.symm (c (γ s)) ∈ d.source by rw [c.left_inv hsc];exact hsd)
  have he : fieldCoordinates γ (chartConstantField γ c u) d =ᶠ[𝓝 s]
      (fun r => fderiv ℝ (d ∘ c.symm) (c (γ r)) u) := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds
      ((c.open_source.inter d.open_source).mem_nhds ⟨hsc,hsd⟩)] with r hr
    exact chartConstantField_coordinates hc hd hr.1 hr.2 u
  exact (((htr.fderiv_right (m := ∞) (by simp)).comp s hx).clm_apply contDiffAt_const).congr_of_eventuallyEq he

lemma smooth_bump_field {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) {a b : ℝ} (ha : a ∈ U) (hab : a < b)
    (v : TangentSpace I3 (γ a)) :
    ∃ W : ∀ s, TangentSpace I3 (γ s), SmoothFieldOn γ W U ∧ HasCompactSupport W ∧
      tsupport W ⊆ U ∧ W a = v ∧ W b = 0 := by
  let c := chartAt E3 (γ a)
  have hc := chart_mem_atlas E3 (γ a)
  have hca := mem_chart_source E3 (γ a)
  have hn : U ∩ γ ⁻¹' c.source ∩ Iio b ∈ 𝓝 a := inter_mem
    (inter_mem (hU.mem_nhds ha) ((hγ.contMDiffAt (hU.mem_nhds ha)).continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds hca))) (Iio_mem_nhds hab)
  obtain ⟨l,r,har,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  let e := min (a-l) (r-a)/4
  have he : 0 < e := by dsimp [e]; exact div_pos (lt_min (sub_pos.mpr har.1) (sub_pos.mpr har.2)) (by norm_num)
  have heL : 2*e < a-l := by dsimp [e]; nlinarith [min_le_left (a-l) (r-a),har.1,har.2]
  have heR : 2*e < r-a := by dsimp [e]; nlinarith [min_le_right (a-l) (r-a),har.1,har.2]
  let f := IndexCutoff.cutoff (a-2*e) (a+2*e) e
  let u : E3 := mfderiv I3 I3 c (γ a) v
  let W : ∀ s, TangentSpace I3 (γ s) := fun s => f s • chartConstantField γ c u s
  have hts : tsupport W ⊆ Icc (a-2*e) (a+2*e) := IndexCutoff.field_tsupport he _
  have hts' : tsupport W ⊆ U ∩ γ ⁻¹' c.source ∩ Iio b := by
    intro s hs
    have hs' := hts hs
    exact hsub ⟨by linarith [hs'.1],by linarith [hs'.2]⟩
  refine ⟨W,?_,IndexCutoff.field_compactSupport he _,fun s hs => (hts' hs).1.1,?_,?_⟩
  · intro d hd s hs
    apply ContDiffAt.contDiffWithinAt
    by_cases hsc : γ s ∈ c.source
    · have hf : ContDiffAt ℝ ∞ f s := (IndexCutoff.cutoff_smooth _ _ _).contDiffAt
      have hW := hf.smul (chartConstantField_smoothAt hc hd (hγ.contMDiffAt (hU.mem_nhds hs.1)) hsc hs.2 u)
      change ContDiffAt ℝ ∞ (fieldCoordinates γ (fun r => f r • chartConstantField γ c u r) d) s
      rw [fieldCoordinates_smul]
      convert hW using 1 <;> rfl
    · have hn : s ∉ tsupport W := fun hh => hsc (hts' hh).1.2
      have hz : fieldCoordinates γ W d =ᶠ[𝓝 s] (fun _ => (0:E3)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with r hr
        change W r = 0 at hr
        exact (congrArg (mfderiv I3 I3 d (γ r)) hr).trans (map_zero _)
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · have hf : f a = 1 := IndexCutoff.cutoff_eq_one he (by linarith) (by linarith)
    change f a • chartConstantField γ c u a = v
    rw [hf,one_smul]
    exact congrArg (fun L => L v) ((mdifferentiable_of_mem_atlas (I := I3) hc).symm_comp_deriv hca)
  · exact image_eq_zero_of_notMem_tsupport (fun hh => lt_irrefl b (hts' hh).2)
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
open IndexCutoff

lemma jacobi_indexPair_integral_zero (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : IsJacobiFieldOn g γ J U)
    (hH : SmoothFieldOn γ H U) (hHc : HasCompactSupport H) (hHU : tsupport H ⊆ U)
    (hpos : NonnegativeIndexOn g γ U)
    {a b : ℝ} (hab : a ≤ b) (ha : a ∈ U) (hb : b ∈ U) (hJa : J a = 0) (hJb : J b = 0) :
    (∫ s in Ioo a b, indexPairDensity g γ J H s) = 0 := by
  have hJs := jacobi_smoothField g hJ
  have hI := jacobi_cutoff_index_tendsto_zero g hU hUc hγ hJ hab ha hb hJa hJb
  have hB := cutoff_indexPair_tendsto g hU hUc hγ hJs hH hab ha hb hJa hJb
  have hle : (∫ s in Ioo a b, indexPairDensity g γ J H s)^2 ≤ (0:ℝ) * indexPair g γ H H := by
    apply le_of_tendsto_of_tendsto (hB.pow 2) (hI.mul tendsto_const_nhds)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact indexPair_cauchy_schwarz g hU hγ hpos
      (smoothField_smul (cutoff_smooth a b ε).contDiffOn hJs) hH
      (field_compactSupport hε J) hHc ((field_tsupport hε J).trans (hUc.out ha hb)) hHU
  exact sq_eq_zero_iff.mp (le_antisymm (by simpa only [zero_mul] using hle) (sq_nonneg _))

lemma jacobi_initial_covariantDerivative_zero (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : IsJacobiFieldOn g γ J U)
    (hpos : NonnegativeIndexOn g γ U)
    {a b : ℝ} (hab : a < b) (ha : a ∈ U) (hb : b ∈ U) (hJa : J a = 0) (hJb : J b = 0) :
    covariantDerivative g γ J a = 0 := by
  obtain ⟨W,hW,hWc,hWU,hWa,hWb⟩ := smooth_bump_field hU hγ ha hab (covariantDerivative g γ J a)
  have hh := jacobi_indexPair_integral_zero g hU hUc hγ hJ hW hWc hWU hpos hab.le ha hb hJa hJb
  rw [jacobi_indexPair_integral g hU hγ hJ hW hab.le (hUc.out ha hb),hWa,hWb,map_zero,
    zero_sub,neg_eq_zero] at hh
  by_contra hn
  exact (ne_of_gt (g.pos (γ a) (covariantDerivative g γ J a) hn)) hh

theorem intrinsic_index_criterion (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : IsJacobiFieldOn g γ J U)
    (hpos : NonnegativeIndexOn g γ U)
    {a b : ℝ} (hab : a < b) (ha : a ∈ U) (hb : b ∈ U) (hJa : J a = 0) (hJb : J b = 0) :
    ∀ s ∈ U, J s = 0 :=
  jacobi_zero_of_intrinsic_initial g hU hUc hγ hJ ha hJa
    (jacobi_initial_covariantDerivative_zero g hU hUc hγ hJ hpos hab ha hb hJa hJb)

theorem noConjugatePoints_of_intrinsic_index (g : SmoothMetric M)
    (hpos : ∀ (U : Set ℝ), IsOpen U → OrdConnected U → ∀ γ : ℝ → M,
      IsGeodesicOn g γ U → NonnegativeIndexOn g γ U) : NoConjugatePoints g := by
  intro U hU hUc γ hγ J hJ a ha b hb hab hJa hJb
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact intrinsic_index_criterion g hU hUc hγ.1 hJ (hpos U hU hUc γ hγ) hlt ha hb hJa hJb
  · exact intrinsic_index_criterion g hU hUc hγ.1 hJ (hpos U hU hUc γ hγ) hgt hb ha hJb hJa
end ThreeManifold.RiemannianCoordinates
end

open Set MeasureTheory Topology Function

namespace ThreeManifold.GlobalAssembly

def Passages (U : Set ℝ) := {J : Set ℝ // ∃ x ∈ U, J = connectedComponentIn U x}

end ThreeManifold.GlobalAssembly

end

end OAI


