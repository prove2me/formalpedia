-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
-- name    : OAI_Geometry_ConjugatePoints_Geodesics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:59:04.476404+00:00
-- url     : https://prove2.me/theorems/b14e91f4-061a-4072-bff6-7388c2fb292c
-- title:
--   Geodesic flow, Jacobi fields of geodesic variations, and the exponential map on compact Riemannian 3-manifolds
-- statement:
--   This file develops the basic theory of geodesics on a smooth three-manifold with a smooth Riemannian metric, working entirely in charts: local and global existence and uniqueness of geodesics, the geodesic flow and its differentiability, the identification of variations of geodesics with Jacobi fields, consequences of nonpositive curvature for Jacobi fields, and the exponential map.
--
--   **Notation.** $M$ is a smooth manifold modelled on $\mathbb{R}^3$ with smooth Riemannian metric $g$; tangent spaces are identified with $\mathbb{R}^3$. In a chart $c$, $\Gamma_c(x)(u, v) = \big(\sum_{j,k}\Gamma^i_{jk}(x)u^jv^k\big)_i$ with $\Gamma^i_{jk} = \tfrac12\sum_l g^{il}(\partial_j g_{lk} + \partial_k g_{lj} - \partial_l g_{jk})$ and $R(u,v)w$ is the coordinate curvature term. For a curve $x(s)$ in chart coordinates and a field $w(s)$ along it, $D_s w = \dot w + \Gamma_c(x)(\dot x, w)$. A curve $\gamma$ is a *geodesic on* $U \subseteq \mathbb{R}$ if it is smooth on $U$ and $D_s \dot x = 0$ in every chart; a field $J$ along $\gamma$ is a *Jacobi field on* $U$ if in every chart its coordinates are smooth on $U$ and $D_s^2 J + R(J, \dot\gamma)\dot\gamma = 0$. $g$ has *no conjugate points* if every Jacobi field along a geodesic on an open interval $U$ that vanishes at two distinct points of $U$ vanishes on all of $U$.
--
--   The file contains:
--
--   1. **First variation of ODE flows** (in a complete normed space $E$). For $f : E \to E$, the variation vector field is $(x, A) \mapsto \big(f(x),\ Df(x) \circ A\big)$. If $f$ is $C^2$ near $x$, there are $r, \varepsilon > 0$ and a flow $X(y, t)$, $y$ in the ball $B(x, r)$, $|t| < \varepsilon$, with $X(y, 0) = y$, $\partial_t X = f(X)$, $X$ jointly $C^1$, and $D_yX(y, t) = A(y, t)$ where $\partial_t A = Df(X)\,A$, $A(y, 0) = \mathrm{id}$. Solutions of $\dot x = f(x)$ with $f$ smooth on a set containing their values are smooth.
--
--   2. **Geodesic spray.** In a chart $c$ the spray is
--   $$
--   F_c(x, v) = \big(v,\ -\Gamma_c(x)(v, v)\big),
--   $$
--   and curves solving $\dot z = F_c(z)$ project to geodesics. Hence local geodesic flows exist in each chart.
--
--   3. **Phase lifts and uniqueness.** $\hat\gamma(t) = (\gamma(t), \dot\gamma(t)) \in TM$. If $M$ is Hausdorff and two geodesics on an open order-connected set $U$ have the same phase lift at one time $t \in U$, they coincide on $U$.
--
--   4. **Abstract continuation.** An *equation* on a space $X$ is a predicate on pairs (curve $z : \mathbb{R} \to X$, time $t$) that depends only on the germ of $z$ at $t$, is invariant under time translation, and has unique solutions on open intervals given one common value. If solutions starting in a set $K$ exist on a uniform time interval and solutions starting in $K$ remain in $K$ (or, for compact $K$, solutions exist locally uniformly near each point of $K$), then every point of $K$ admits a solution defined for all times.
--
--   5. **Global geodesics and the geodesic flow** (for $M$ compact and Hausdorff). The energy $E(p, v) = g_p(v, v)$ has compact sublevel sets and is conserved along geodesics, so for every $(p, v) \in TM$ there is a geodesic $\gamma_{(p,v)} : \mathbb{R} \to M$ with $\hat\gamma_{(p,v)}(0) = (p, v)$. A choice of such geodesics defines the geodesic flow $\phi_t(p, v) = \hat\gamma_{(p,v)}(t)$, which satisfies $\phi_0 = \mathrm{id}$, $\phi_t \circ \phi_s = \phi_{s+t}$, and is jointly $C^1$ on $TM \times \mathbb{R}$.
--
--   6. **Variations of geodesics are Jacobi fields.** For a map $f : E \to TM$ from a normed space, set $\gamma_a(t) = \operatorname{pr}(\phi_t(f(a)))$ and, for $b \in E$, $J(t) = \frac{\partial}{\partial a}\gamma_a(t)\,[b]$. Each $\gamma_a$ is a geodesic on $\mathbb{R}$, and if $f$ is $C^1$ at $a$ then $J$ is a Jacobi field along $\gamma_a$ on all of $\mathbb{R}$; the underlying fact is that the linearization of the spray equation is the Jacobi equation.
--
--   7. **Nonpositive curvature and Jacobi fields.** If $g$ has nonpositive sectional curvature then $g$ has no conjugate points. With $|J| = \sqrt{g(J, J)}$: $\frac{d}{ds}|J|^2 = 2g(D_sJ, J)$; if the curve $\gamma$ is smooth, $J$ is a Jacobi field on $\mathbb{R}$ and $J(t) \neq 0$ for $t > 0$, then $|J|$ is convex on $[0, \infty)$; and if $\gamma$ is a geodesic on $\mathbb{R}$, $J$ a Jacobi field on $\mathbb{R}$ with $J(0) = 0$, then for all $t \ge 0$
--   $$
--   t\,|D_sJ(0)| \le |J(t)| .
--   $$
--
--   8. **The exponential map** (for $M$ compact and Hausdorff). $\exp_x(v) = \gamma_{(x, v)}(1)$ for $v \in \mathbb{R}^3 = T_xM$. It is $C^1$, $\exp_x(0) = x$ and $\exp_x(kv) = \gamma_{(x,v)}(k)$. If $g$ has no conjugate points, the differential of $\exp_x$ is injective at every $v$ and $\exp_x$ is a local homeomorphism (via the general fact that a $C^1$ map $\mathbb{R}^3 \to M$ with everywhere injective differential is a local homeomorphism). If $g$ has nonpositive sectional curvature, $\exp_x$ is expanding: $g_x(b, b) \le g_{\exp_x v}\big(d(\exp_x)_v b,\ d(\exp_x)_v b\big)$ for all $v, b$.
--
--   These results supply the analytic input for the Cartan–Hadamard argument used later: geodesic completeness of compact manifolds, the Jacobi-field description of $d\exp$, and the injectivity and expansion of $d\exp$ under the curvature hypotheses.
--
--   **Formalization Note** Smoothness is $C^\infty$ for metrics and geodesics but only $C^1$ for the flow, the exponential map and variations. `globalGeodesic` is chosen with `Classical.choose` from `exists_global_geodesic`; the exponential map and flow require `[CompactSpace M] [T2Space M]`. Geodesics, Jacobi fields and curvature are the chartwise notions `IsGeodesicOn`, `IsJacobiFieldOn`, `NonpositiveSectionalCurvature`, `NoConjugatePoints` of the challenge file; $D_s$ is `covariantDerivative`, computed in the chart at $\gamma(s)$. The private `ite_eq_left`, `ite_eq_right`, `dite_eq_left` and various translation and germ lemmas are plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Geodesics.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Geodesics.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

/-!
# Geodesic flow, variation equations, and the Gauss lemma.
-/

section

open Set Filter Topology Asymptotics
open scoped NNReal
namespace ThreeManifold.ODEVariation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma remainder_bound {f : E → E} {D : E → E →L[ℝ] E}
    {u v : ℝ → E} {A : ℝ → E →L[ℝ] E} {x y : E} {a b K C L : ℝ}
    (hK : 0 < K) (hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (f (u t)) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (f (v t)) t)
    (hA : ∀ t ∈ Icc a b, ∀ z, HasDerivAt (fun s => A s z) (D (u t) (A t z)) t)
    (hua : u a = x) (hva : v a = y) (hAa : A a = ContinuousLinearMap.id ℝ E)
    (hD : ∀ t ∈ Icc a b, ‖D (u t)‖ ≤ K)
    (hLip : ∀ t ∈ Icc a b, ‖v t - u t‖ ≤ L * ‖y-x‖)
    (hTaylor : ∀ t ∈ Icc a b,
      ‖f (v t) - f (u t) - D (u t) (v t-u t)‖ ≤ C * ‖v t-u t‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖v t - u t - A t (y-x)‖ ≤
        (C * L^2 / K * (Real.exp (K * (t-a))-1)) * ‖y-x‖^2 := by
  intro t ht
  let R : ℝ → E := fun s => v s-u s-A s (y-x)
  let R' : ℝ → E := fun s => f (v s)-f (u s)-D (u s) (A s (y-x))
  have hd : ∀ s ∈ Icc a b, HasDerivAt R (R' s) s := fun s hs =>
    ((hv s hs).sub (hu s hs)).sub (hA s hs (y-x))
  have hb : ∀ s ∈ Ico a b, ‖R' s‖ ≤ K * ‖R s‖ + C*L^2*‖y-x‖^2 := by
    intro s hs
    have hsc := Ico_subset_Icc_self hs
    have he : R' s = D (u s) (R s) +
        (f (v s)-f (u s)-D (u s) (v s-u s)) := by
      simp only [R', R, map_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖D (u s) (R s)‖ + ‖f (v s)-f (u s)-D (u s) (v s-u s)‖ := norm_add_le _ _
      _ ≤ K * ‖R s‖ + C * ‖v s-u s‖^2 := add_le_add
        ((D (u s)).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hD s hsc) (norm_nonneg _)))
        (hTaylor s hsc)
      _ ≤ K * ‖R s‖ + C*L^2*‖y-x‖^2 := by
        have hh : ‖v s-u s‖^2 ≤ (L*‖y-x‖)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hLip s hsc) 2
        nlinarith [mul_le_mul_of_nonneg_left hh hC]
  have hr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := R) (f' := R') (K := K) (ε := C*L^2*‖y-x‖^2) (δ := 0)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by simp [R,hua,hva,hAa]) hb t ht
  dsimp [gronwallBound] at hr
  rw [ite_eq_right hK.ne', zero_mul, zero_add] at hr
  change ‖R t‖ ≤ _
  convert hr using 1 ; ring

lemma hasFDerivAt_of_quadratic_error {F : E → E} {A : E →L[ℝ] E} {x : E}
    {Q : ℝ} (h : ∀ᶠ y in 𝓝 x, ‖F y-F x-A (y-x)‖ ≤ Q*‖y-x‖^2) :
    HasFDerivAt F A x := by
  rw [hasFDerivAt_iff_isLittleO]
  have hb : (fun y => F y-F x-A (y-x)) =O[𝓝 x] (fun y => ‖y-x‖^2) := by
    apply isBigO_iff.mpr
    refine ⟨Q,?_⟩
    filter_upwards [h] with y hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y-x‖)] using hy
  exact hb.trans_isLittleO (isLittleO_pow_sub_sub x (by norm_num : 1 < (2 : ℕ)))

lemma flow_hasFDerivAt {f : E → E} {D : E → E →L[ℝ] E}
    {X : E → ℝ → E} {A : ℝ → E →L[ℝ] E} {x : E} {a b K C L : ℝ}
    (hK : 0 < K) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hx : ∀ t ∈ Icc a b, HasDerivAt (X x) (f (X x t)) t)
    (hA : ∀ t ∈ Icc a b, ∀ z,
      HasDerivAt (fun s => A s z) (D (X x t) (A t z)) t)
    (hxa : X x a = x) (hAa : A a = ContinuousLinearMap.id ℝ E)
    (hD : ∀ t ∈ Icc a b, ‖D (X x t)‖ ≤ K)
    (hnear : ∀ᶠ y in 𝓝 x, X y a = y ∧
      (∀ t ∈ Icc a b, HasDerivAt (X y) (f (X y t)) t) ∧
      (∀ t ∈ Icc a b, ‖X y t-X x t‖ ≤ L*‖y-x‖) ∧
      (∀ t ∈ Icc a b, ‖f (X y t)-f (X x t)-D (X x t) (X y t-X x t)‖ ≤
        C*‖X y t-X x t‖^2)) {t : ℝ} (ht : t ∈ Icc a b) :
    HasFDerivAt (fun y => X y t) (A t) x := by
  apply hasFDerivAt_of_quadratic_error (Q := C*L^2/K*(Real.exp (K*(t-a))-1))
  filter_upwards [hnear] with y hy
  exact remainder_bound hK hC hL hx hy.2.1 hA hxa hy.1 hAa hD hy.2.2.1 hy.2.2.2 t ht

lemma quadratic_taylor {f : E → E} {S : Set E} {C : ℝ≥0}
    (hS : Convex ℝ S) (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hD : LipschitzOnWith C (fderiv ℝ f) S) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖ ≤ C*‖y-x‖^2 := by
  have hseg := hS.segment_subset hx hy
  have hd : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z-fderiv ℝ f x‖ ≤ C*‖y-x‖ := by
    intro z hz
    exact (hD.norm_sub_le (hseg hz) hx).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) C.coe_nonneg)
  have hh := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => hf z (hseg hz)) hd (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [pow_two,mul_assoc] using hh

lemma local_bounds {f : E → E} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ∃ r > (0 : ℝ), ∃ K > (0 : ℝ), ∃ C : ℝ≥0,
      (∀ z ∈ Metric.ball x r, DifferentiableAt ℝ f z) ∧
      (∀ z ∈ Metric.ball x r, ‖fderiv ℝ f z‖ ≤ K) ∧
      (∀ z ∈ Metric.ball x r, ∀ w ∈ Metric.ball x r,
        ‖f w-f z-fderiv ℝ f z (w-z)‖ ≤ C*‖w-z‖^2) := by
  have hD : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  obtain ⟨C,S,hS,hLip⟩ := hD.exists_lipschitzOnWith
  have hdiff : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z := by
    filter_upwards [hf.eventually (by norm_num)] with z hz
    exact hz.differentiableAt (by norm_num)
  have hbound : ∀ᶠ z in 𝓝 x, ‖fderiv ℝ f z‖ < ‖fderiv ℝ f x‖+1 :=
    hD.continuousAt.norm.eventually_lt_const (by linarith)
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (inter_mem hS (inter_mem hdiff hbound))
  refine ⟨r,hr,‖fderiv ℝ f x‖+1,by positivity,C,?_,?_,?_⟩
  · intro z hz; exact (hrs hz).2.1
  · intro z hz; exact (hrs hz).2.2.le
  · intro z hz w hw
    exact quadratic_taylor (convex_ball x r) (fun z hz => (hrs hz).2.1)
      (hLip.mono (fun z hz => (hrs hz).1)) hz hw
end ThreeManifold.ODEVariation
end

section
open Set Filter Topology Metric
open scoped NNReal
namespace ThreeManifold.ODEVariation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def variationVector (f : E → E) (z : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (f z.1, (fderiv ℝ f z.1).comp z.2)

lemma variationVector_smoothAt {f : E → E} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (A : E →L[ℝ] E) :
    ContDiffAt ℝ 1 (variationVector f) (x,A) := by
  let _ : CompleteSpace E := inferInstance
  exact ((hf.of_le (by norm_num)).comp (x,A) contDiffAt_fst).prodMk
    (((hf.fderiv_right (m := 1) (by norm_num)).comp (x,A) contDiffAt_fst).clm_comp contDiffAt_snd)

lemma exists_variation_flow {f : E → E} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ X : E → ℝ → E,
      ∃ A : E → ℝ → E →L[ℝ] E, ∃ L : ℝ≥0,
      (∀ y ∈ closedBall x r, X y 0 = y ∧ A y 0 = ContinuousLinearMap.id ℝ E) ∧
      (∀ y ∈ closedBall x r, ∀ t ∈ Icc (-ε) ε,
        HasDerivAt (X y) (f (X y t)) t ∧
        HasDerivAt (A y) ((fderiv ℝ f (X y t)).comp (A y t)) t) ∧
      (∀ t ∈ Icc (-ε) ε, ∀ y ∈ closedBall x r, ∀ z ∈ closedBall x r,
        ‖X y t-X z t‖ ≤ L*‖y-z‖ ∧ ‖A y t-A z t‖ ≤ L*‖y-z‖) ∧
      ContinuousOn (fun yt : E × ℝ => (X yt.1 yt.2,A yt.1 yt.2))
        (closedBall x r ×ˢ Icc (-ε) ε) := by
  let z₀ : E × (E →L[ℝ] E) := (x,ContinuousLinearMap.id ℝ E)
  obtain ⟨ε,hε,a,r,B,K,hr,hpl⟩ := IsPicardLindelof.of_contDiffAt_one
    (variationVector_smoothAt hf (ContinuousLinearMap.id ℝ E))
  obtain ⟨Y,hY,L,hLip⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  have hcont : ContinuousOn (Function.uncurry Y) (closedBall z₀ r ×ˢ Icc (0-ε) (0+ε)) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L _ hLip
    intro z hz
    exact HasDerivWithinAt.continuousOn (hY z hz).2
  let ι : E → E × (E →L[ℝ] E) := fun y => (y,ContinuousLinearMap.id ℝ E)
  have hi : LipschitzWith 1 ι := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp [ι,Prod.dist_eq]
  have hi_mem : ∀ y ∈ closedBall x r, ι y ∈ closedBall z₀ r := by
    intro y hy
    change dist y x ≤ (r : ℝ) at hy
    change dist (ι y) z₀ ≤ (r : ℝ)
    simpa only [ι,z₀,Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using hy
  have htime : Icc (-(ε/2)) (ε/2) ⊆ Icc (0-ε) (0+ε) := by
    rintro t ⟨ht1,ht2⟩; constructor <;> linarith
  have htime_nhds : ∀ t ∈ Icc (-(ε/2)) (ε/2), Icc (0-ε) (0+ε) ∈ 𝓝 t := by
    rintro t ⟨ht1,ht2⟩
    apply Icc_mem_nhds <;> linarith
  refine ⟨r,hr,ε/2,half_pos hε,(fun y t => (Y (ι y) t).1),
    (fun y t => (Y (ι y) t).2),L,?_,?_,?_,?_⟩
  · intro y hy
    have hy0 := (hY (ι y) (hi_mem y hy)).1
    exact ⟨congrArg Prod.fst hy0,congrArg Prod.snd hy0⟩
  · intro y hy t ht
    have hd := ((hY (ι y) (hi_mem y hy)).2 t (htime ht)).hasDerivAt (htime_nhds t ht)
    exact ⟨hd.fst,hd.snd⟩
  · intro t ht y hy z hz
    have hh := (hLip t (htime ht)).norm_sub_le (hi_mem y hy) (hi_mem z hz)
    have he : ‖ι y-ι z‖ = ‖y-z‖ := by
      change max ‖y-z‖ ‖(ContinuousLinearMap.id ℝ E)-(ContinuousLinearMap.id ℝ E)‖ = ‖y-z‖
      simp
    rw [he] at hh
    exact ⟨(norm_fst_le _).trans hh,(norm_snd_le _).trans hh⟩
  · change ContinuousOn (Function.uncurry Y ∘ (fun yt : E × ℝ => (ι yt.1,yt.2))) _
    apply hcont.comp ((hi.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
    intro yt hyt
    exact ⟨hi_mem yt.1 hyt.1,htime hyt.2⟩

lemma flow_derivative_on {f : E → E} {X : E → ℝ → E} {A : E → ℝ → E →L[ℝ] E}
    {S : Set E} {ε K C L : ℝ} (hS : IsOpen S) (hK : 0 < K) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (h0 : ∀ y ∈ S, X y 0 = y ∧ A y 0 = ContinuousLinearMap.id ℝ E)
    (hODE : ∀ y ∈ S, ∀ t ∈ Icc (-ε) ε,
      HasDerivAt (X y) (f (X y t)) t ∧
      HasDerivAt (A y) ((fderiv ℝ f (X y t)).comp (A y t)) t)
    (hD : ∀ y ∈ S, ∀ t ∈ Icc (-ε) ε, ‖fderiv ℝ f (X y t)‖ ≤ K)
    (hLip : ∀ y ∈ S, ∀ z ∈ S, ∀ t ∈ Icc (-ε) ε, ‖X z t-X y t‖ ≤ L*‖z-y‖)
    (hTaylor : ∀ y ∈ S, ∀ z ∈ S, ∀ t ∈ Icc (-ε) ε,
      ‖f (X z t)-f (X y t)-fderiv ℝ f (X y t) (X z t-X y t)‖ ≤ C*‖X z t-X y t‖^2)
    {y : E} (hy : y ∈ S) {t : ℝ} (ht : t ∈ Icc (-ε) ε) :
    HasFDerivAt (fun z => X z t) (A y t) y := by
  let _ : CompleteSpace E := inferInstance
  have hε : 0 ≤ ε := by have := ht.1; have := ht.2; linarith
  have hp : Icc (0 : ℝ) ε ⊆ Icc (-ε) ε := by
    rintro s ⟨hs0,hsε⟩; exact ⟨by linarith,hsε⟩
  have hm : ∀ s ∈ Icc (0 : ℝ) ε, -s ∈ Icc (-ε) ε := by
    rintro s ⟨hs0,hsε⟩; constructor <;> linarith
  by_cases ht0 : 0 ≤ t
  · apply flow_hasFDerivAt hK hC hL (b := ε)
      (fun s hs => (hODE y hy s (hp hs)).1)
      (fun s hs z => by
        simpa only [ContinuousLinearMap.comp_apply,map_zero,add_zero] using
          (hODE y hy s (hp hs)).2.clm_apply (hasDerivAt_const s z))
      (h0 y hy).1 (h0 y hy).2 (fun s hs => hD y hy s (hp hs)) (ht := ⟨ht0,ht.2⟩)
    filter_upwards [hS.mem_nhds hy] with z hz
    exact ⟨(h0 z hz).1,(fun s hs => (hODE z hz s (hp hs)).1),
      (fun s hs => hLip y hy z hz s (hp hs)),(fun s hs => hTaylor y hy z hz s (hp hs))⟩
  · have hxrev : ∀ z ∈ S, ∀ s ∈ Icc (0 : ℝ) ε,
        HasDerivAt (fun r => X z (-r)) (-(f (X z (-s)))) s := by
      intro z hz s hs
      simpa only [Function.comp_def,neg_one_smul] using
        ((hODE z hz (-s) (hm s hs)).1.scomp s (hasDerivAt_id s).neg)
    have hArev : ∀ s ∈ Icc (0 : ℝ) ε, ∀ v,
        HasDerivAt (fun r => A y (-r) v)
          ((-fderiv ℝ f (X y (-s))) (A y (-s) v)) s := by
      intro s hs v
      have hh := ((hODE y hy (-s) (hm s hs)).2.clm_apply (hasDerivAt_const (-s) v)).scomp s
        (hasDerivAt_id s).neg
      simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,_root_.neg_apply,
        neg_one_smul,map_zero,add_zero] using hh
    have hh : HasFDerivAt (fun z => X z (-(-t))) (A y (-(-t))) y := by
      apply flow_hasFDerivAt (f := fun w => -f w) (D := fun w => -fderiv ℝ f w)
        (X := fun z s => X z (-s)) (A := fun s => A y (-s)) hK hC hL
        (b := ε) (hxrev y hy) hArev (by simpa using (h0 y hy).1)
        (by simpa using (h0 y hy).2)
        (fun s hs => by simpa only [norm_neg] using hD y hy (-s) (hm s hs))
        (ht := ⟨by linarith,by linarith [ht.1]⟩)
      filter_upwards [hS.mem_nhds hy] with z hz
      refine ⟨by simpa using (h0 z hz).1,hxrev z hz,(fun s hs => hLip y hy z hz (-s) (hm s hs)),?_⟩
      intro s hs
      have he : (-f (X z (-s)))-(-f (X y (-s)))-(-fderiv ℝ f (X y (-s))) (X z (-s)-X y (-s)) =
          -(f (X z (-s))-f (X y (-s))-fderiv ℝ f (X y (-s)) (X z (-s)-X y (-s))) := by
        simp only [_root_.neg_apply]; abel
      rw [he,norm_neg]
      exact hTaylor y hy z hz (-s) (hm s hs)
    simpa only [neg_neg] using hh

lemma shrink_flow_image {x : E} {r ε R : ℝ} {X : E → ℝ → E}
    (hr : 0 < r) (hε : 0 < ε) (hR : 0 < R) (h0 : X x 0 = x)
    (hc : ContinuousOn (Function.uncurry X) (closedBall x r ×ˢ Icc (-ε) ε)) :
    ∃ ρ > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ y ∈ ball x ρ, ∀ t ∈ Icc (-δ) δ,
      X y t ∈ ball x R ∧ y ∈ closedBall x r ∧ t ∈ Icc (-ε) ε := by
  let _ : NormedSpace ℝ E := inferInstance
  let _ : CompleteSpace E := inferInstance
  have hn : closedBall x r ×ˢ Icc (-ε) ε ∈ 𝓝 (x,(0 : ℝ)) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (closedBall_mem_nhds x hr) (Icc_mem_nhds (by linarith) hε)
  have hxc : ContinuousAt (Function.uncurry X) (x,(0 : ℝ)) := hc.continuousAt hn
  have hm : (Function.uncurry X) ⁻¹' ball x R ∈ 𝓝 (x,(0 : ℝ)) := by
    apply hxc.preimage_mem_nhds
    apply isOpen_ball.mem_nhds
    simpa only [Function.uncurry_apply_pair,h0] using mem_ball_self hR
  have hd : ball x r ×ˢ Ioo (-ε) ε ∈ 𝓝 (x,(0 : ℝ)) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x hr) (Ioo_mem_nhds (by linarith) hε)
  obtain ⟨η,hη,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hm hd)
  refine ⟨η/2,half_pos hη,η/2,half_pos hη,?_⟩
  intro y hy t ht
  have hp : (y,t) ∈ ball (x,(0 : ℝ)) η := by
    rw [mem_ball,Prod.dist_eq,max_lt_iff]
    constructor
    · exact lt_trans hy (half_lt_self hη)
    · rw [Real.dist_eq,sub_zero,abs_lt]
      constructor <;> linarith [ht.1,ht.2]
  exact ⟨(hsub hp).1,ball_subset_closedBall (hsub hp).2.1,
    Ioo_subset_Icc_self (hsub hp).2.2⟩

lemma exists_contDiff_variation_flow {f : E → E} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ X : E → ℝ → E,
      (∀ y ∈ ball x r, X y 0 = y) ∧
      (∀ y ∈ ball x r, ∀ t ∈ Ioo (-ε) ε, HasDerivAt (X y) (f (X y t)) t) ∧
      ContDiffOn ℝ 1 (Function.uncurry X) (ball x r ×ˢ Ioo (-ε) ε) ∧
      ∃ A : E → ℝ → E →L[ℝ] E,
        (∀ y ∈ ball x r, A y 0 = ContinuousLinearMap.id ℝ E) ∧
        (∀ y ∈ ball x r, ∀ t ∈ Ioo (-ε) ε, HasFDerivAt (fun z => X z t) (A y t) y) ∧
        (∀ y ∈ ball x r, ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt (A y) ((fderiv ℝ f (X y t)).comp (A y t)) t) := by
  obtain ⟨R,hR,K,hK,C,hfd,hDf,hTaylor⟩ := local_bounds hf
  obtain ⟨r,hr,ε,hε,X,A,L,h0,hODE,hLip,hcont⟩ := exists_variation_flow hf
  have h0x : X x 0 = x := (h0 x (mem_closedBall_self hr.le)).1
  obtain ⟨ρ,hρ,δ,hδ,hsmall⟩ := shrink_flow_image hr hε hR h0x hcont.fst
  have hz : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith,hδ.le⟩
  have hinit : ∀ y ∈ ball x ρ, y ∈ closedBall x r := fun y hy => (hsmall y hy 0 hz).2.1
  have htime : Icc (-δ) δ ⊆ Icc (-ε) ε :=
    fun t ht => (hsmall x (mem_ball_self hρ) t ht).2.2
  have hdf : ∀ y ∈ ball x ρ, ∀ t ∈ Icc (-δ) δ,
      HasFDerivAt (fun z => X z t) (A y t) y := by
    intro y hy t ht
    apply flow_derivative_on isOpen_ball hK C.coe_nonneg L.coe_nonneg
      (fun y hy => h0 y (hinit y hy))
      (fun y hy t ht => hODE y (hinit y hy) t (htime ht))
      (fun y hy t ht => hDf _ (hsmall y hy t ht).1)
      (fun y hy z hz t ht => (hLip t (htime ht) z (hinit z hz) y (hinit y hy)).1)
      (fun y hy z hz t ht => hTaylor _ (hsmall y hy t ht).1 _ (hsmall z hz t ht).1)
      hy ht
  let O := ball x ρ ×ˢ Ioo (-δ) δ
  have hO : IsOpen O := isOpen_ball.prod isOpen_Ioo
  have hcont' : ContinuousOn (fun yt : E × ℝ => (X yt.1 yt.2,A yt.1 yt.2)) O :=
    hcont.mono (fun p hp => ⟨hinit p.1 hp.1,htime (Ioo_subset_Icc_self hp.2)⟩)
  have hX : ContinuousOn (Function.uncurry X) O := hcont'.fst
  have hA : ContinuousOn (Function.uncurry A) O := hcont'.snd
  have hfX : ContinuousOn (fun p : E × ℝ => f (X p.1 p.2)) O := by
    intro p hp
    exact (hfd _ (hsmall p.1 hp.1 p.2 (Ioo_subset_Icc_self hp.2)).1).continuousAt.comp_continuousWithinAt (f := Function.uncurry X)
      (hX p hp)
  let B : E × ℝ → ℝ →L[ℝ] E := fun p => ContinuousLinearMap.toSpanSingleton ℝ (f (X p.1 p.2))
  have hB : ContinuousOn B O :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).continuous.comp_continuousOn hfX
  let D : E × ℝ → (E × ℝ) →L[ℝ] E := fun p => (A p.1 p.2).coprod (B p)
  have hd : ∀ p ∈ O, HasFDerivAt (Function.uncurry X) (D p) p := by
    intro p hp
    apply HasStrictFDerivAt.hasFDerivAt
    apply hasStrictFDerivAt_uncurry_coprod (f₁ := A) (f₂ := fun y t => B (y,t))
    · filter_upwards [hO.mem_nhds hp] with q hq
      exact hdf q.1 hq.1 q.2 (Ioo_subset_Icc_self hq.2)
    · filter_upwards [hO.mem_nhds hp] with q hq
      exact (hODE q.1 (hinit q.1 hq.1) q.2 (htime (Ioo_subset_Icc_self hq.2))).1.hasFDerivAt
    · exact hA.continuousAt (hO.mem_nhds hp)
    · exact hB.continuousAt (hO.mem_nhds hp)
  have hD : ContinuousOn D O := by
    have hh := (hA.clm_comp (continuousOn_const (c := ContinuousLinearMap.fst ℝ E ℝ))).add
      (hB.clm_comp (continuousOn_const (c := ContinuousLinearMap.snd ℝ E ℝ)))
    exact hh
  refine ⟨ρ,hρ,δ,hδ,X,(fun y hy => (h0 y (hinit y hy)).1),
    (fun y hy t ht => (hODE y (hinit y hy) t (htime (Ioo_subset_Icc_self ht))).1),?_⟩
  constructor
  · apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hO).mpr
    refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt,by simp,?_⟩
    rw [contDiffOn_zero]
    exact hD.congr (fun p hp => (hd p hp).fderiv)
  · exact ⟨A,(fun y hy => (h0 y (hinit y hy)).2),
      (fun y hy t ht => hdf y hy t (Ioo_subset_Icc_self ht)),
      (fun y hy t ht => (hODE y (hinit y hy) t (htime (Ioo_subset_Icc_self ht))).2)⟩

lemma exists_contDiff_flow {f : E → E} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ X : E → ℝ → E,
      (∀ y ∈ ball x r, X y 0 = y) ∧
      (∀ y ∈ ball x r, ∀ t ∈ Ioo (-ε) ε, HasDerivAt (X y) (f (X y t)) t) ∧
      ContDiffOn ℝ 1 (Function.uncurry X) (ball x r ×ˢ Ioo (-ε) ε) := by
  obtain ⟨r,hr,ε,hε,X,h0,hd,hs,_⟩ := exists_contDiff_variation_flow hf
  exact ⟨r,hr,ε,hε,X,h0,hd,hs⟩
end ThreeManifold.ODEVariation
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ODEVariation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma solution_smooth {f : E → E} {S : Set E} {U : Set ℝ} {x : ℝ → E}
    (hf : ContDiffOn ℝ ∞ f S) (hU : IsOpen U) (hx : MapsTo x U S)
    (hd : ∀ t ∈ U, HasDerivAt x (f (x t)) t) : ContDiffOn ℝ ∞ x U := by
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero => exact (contDiffOn_zero).2 (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  | succ n hn =>
    rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_deriv_of_isOpen hU]
    refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt,by simp,?_⟩
    exact ((contDiffOn_infty.mp hf n).comp hn hx).congr (fun t ht => (hd t ht).deriv)
end ThreeManifold.ODEVariation
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

def geodesicPhase (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (z : E3 × E3) : E3 × E3 :=
  (z.2,-connectionTerm g c z.1 z.2 z.2)

lemma geodesicPhase_smoothAt (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {z : E3 × E3} (hz : z.1 ∈ c.target) :
    ContDiffAt ℝ ∞ (geodesicPhase g c) z := by
  apply contDiffAt_snd.prodMk
  apply ContDiffAt.neg
  apply contDiffAt_pi.mpr
  intro i
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.sum
  intro k _
  exact (((christoffel_smoothAt g hc hz i j k).comp z contDiffAt_fst).mul
    (contDiffAt_pi.mp contDiffAt_snd j)).mul (contDiffAt_pi.mp contDiffAt_snd k)

lemma chart_geodesic (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {U : Set ℝ} (hU : IsOpen U) {z : ℝ → E3 × E3}
    (hz : ∀ t ∈ U, (z t).1 ∈ c.target)
    (hd : ∀ t ∈ U, HasDerivAt z (geodesicPhase g c (z t)) t) :
    IsGeodesicOn g (fun t => c.symm (z t).1) U := by
  have hzs : ContDiffOn ℝ ∞ z U := ODEVariation.solution_smooth
    (fun x hx => (geodesicPhase_smoothAt g hc hx).contDiffWithinAt) hU hz hd
  have hxs : ContDiffOn ℝ ∞ (fun t => (z t).1) U := hzs.fst
  have hvs : ContDiffOn ℝ ∞ (fun t => (z t).2) U := hzs.snd
  have hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ (fun t => c.symm (z t).1) U := by
    intro t ht
    exact ((contMDiffAt_symm_of_mem_maximalAtlas (subset_maximalAtlas hc) (hz t ht)).comp t
      (contMDiffAt_iff_contDiffAt.mpr (hxs.contDiffAt (hU.mem_nhds ht)))).contMDiffWithinAt
  refine ⟨hγ,?_⟩
  intro d hdc t ht hdt
  have hdx : ∀ r ∈ U, HasDerivAt (fun s => (z s).1) (z r).2 r := fun r hr => (hd r hr).fst
  have hdv : ∀ r ∈ U, HasDerivAt (fun s => (z s).2)
      (-connectionTerm g c (z r).1 (z r).2 (z r).2) r := fun r hr => (hd r hr).snd
  have heq : (fun r => deriv (fun s => (z s).1) r) =ᶠ[𝓝 t] fun r => (z r).2 := by
    filter_upwards [hU.mem_nhds ht] with r hr
    exact (hdx r hr).deriv
  have hacc : alongDerivative g c (fun s => (z s).1) (fun s => (z s).2) t = 0 := by
    rw [alongDerivative,(hdx t ht).deriv,(hdv t ht).deriv,neg_add_cancel]
  have hchange := along_change g hc hdc (hdx t ht).differentiableAt
    (hdv t ht).differentiableAt (hz t ht) hdt
  dsimp only at hchange
  rw [hacc,map_zero] at hchange
  have hdtrans : (fun r => fderiv ℝ (d ∘ c.symm) ((z r).1) ((z r).2)) =ᶠ[𝓝 t]
      deriv ((d ∘ c.symm) ∘ (fun r => (z r).1)) := by
    have hnh := (hγ.continuousOn.continuousAt (hU.mem_nhds ht)).preimage_mem_nhds
      (d.open_source.mem_nhds hdt)
    filter_upwards [hU.mem_nhds ht,hnh] with r hr hdr
    exact ((transition_smoothAt hc hdc (hz r hr) hdr).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt r (hdx r hr) |>.deriv |>.symm
  rw [along_congr g d Filter.EventuallyEq.rfl hdtrans] at hchange
  exact hchange

theorem exists_geodesic_local_flow (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {z : E3 × E3} (hz : z.1 ∈ c.target) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ X : (E3 × E3) → ℝ → E3 × E3,
      (∀ y ∈ Metric.ball z r, X y 0 = y) ∧
      (∀ y ∈ Metric.ball z r, IsGeodesicOn g (fun t => c.symm (X y t).1) (Ioo (-ε) ε)) ∧
      (∀ y ∈ Metric.ball z r, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (X y) (geodesicPhase g c (X y t)) t) ∧
      (∀ y ∈ Metric.ball z r, ∀ t ∈ Ioo (-ε) ε, (X y t).1 ∈ c.target) ∧
      ContDiffOn ℝ 1 (Function.uncurry X) (Metric.ball z r ×ˢ Ioo (-ε) ε) := by
  obtain ⟨r,hr,ε,hε,X,h0,hd,hs⟩ :=
    ODEVariation.exists_contDiff_flow (contDiffAt_infty.mp (geodesicPhase_smoothAt g hc hz) 2)
  have hO : IsOpen (Metric.ball z r ×ˢ Ioo (-ε) ε) := Metric.isOpen_ball.prod isOpen_Ioo
  have hp : (z,(0:ℝ)) ∈ Metric.ball z r ×ˢ Ioo (-ε) ε := ⟨Metric.mem_ball_self hr,by constructor <;> linarith⟩
  have hx : ContinuousAt (Function.uncurry X) (z,0) := hs.continuousOn.continuousAt (hO.mem_nhds hp)
  have hmem : {p : (E3 × E3) × ℝ | (X p.1 p.2).1 ∈ c.target} ∈ 𝓝 (z,0) := by
    apply hx.fst.preimage_mem_nhds
    simpa only [Function.uncurry_apply_pair,h0 z (Metric.mem_ball_self hr)] using c.open_target.mem_nhds hz
  obtain ⟨η,hη,hsmall⟩ := Metric.mem_nhds_iff.mp (inter_mem hmem (hO.mem_nhds hp))
  have hsub : ∀ y ∈ Metric.ball z (η/2), ∀ t ∈ Ioo (-(η/2)) (η/2),
      (X y t).1 ∈ c.target ∧ (y,t) ∈ Metric.ball z r ×ˢ Ioo (-ε) ε := by
    intro y hy t ht
    apply hsmall (a := (y,t))
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨lt_trans hy (half_lt_self hη),by rw [Real.dist_eq,sub_zero,abs_lt]; constructor <;> linarith [ht.1,ht.2]⟩
  refine ⟨η/2,half_pos hη,η/2,half_pos hη,X,?_,?_,?_,?_,?_⟩
  · intro y hy
    exact h0 y (hsub y hy 0 ⟨by linarith,by linarith⟩).2.1
  · intro y hy
    exact chart_geodesic g hc isOpen_Ioo (fun t ht => (hsub y hy t ht).1)
      (fun t ht => hd y (hsub y hy t ht).2.1 t (hsub y hy t ht).2.2)
  · intro y hy t ht
    exact hd y (hsub y hy t ht).2.1 t (hsub y hy t ht).2.2
  · exact fun y hy t ht => (hsub y hy t ht).1
  · exact hs.mono (fun p hp => (hsub p.1 hp.1 p.2 hp.2).2)
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle
namespace ThreeManifold

theorem fiberBundle_t2 {B F : Type*} {E : B → Type*}
    [TopologicalSpace B] [T2Space B] [TopologicalSpace F] [T2Space F]
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] :
    T2Space (TotalSpace F E) := by
  classical
  rw [t2Space_iff_disjoint_nhds]
  intro p q hpq
  by_cases hb : p.1 = q.1
  · let e := trivializationAt F E p.1
    have hp : p ∈ e.source := e.mem_source.mpr (FiberBundle.mem_baseSet_trivializationAt' p.1)
    have hq : q ∈ e.source := e.mem_source.mpr (hb ▸ FiberBundle.mem_baseSet_trivializationAt' p.1)
    have he : e p ≠ e q := fun h => hpq (e.toOpenPartialHomeomorph.injOn hp hq h)
    exact Filter.disjoint_of_map ((disjoint_nhds_nhds.mpr he).mono
      (e.toOpenPartialHomeomorph.continuousAt hp) (e.toOpenPartialHomeomorph.continuousAt hq))
  · exact Filter.disjoint_of_map ((disjoint_nhds_nhds.mpr hb).mono
      (FiberBundle.continuous_proj F E).continuousAt (FiberBundle.continuous_proj F E).continuousAt)
end ThreeManifold
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

def phaseLift (γ : ℝ → M) (t : ℝ) : TangentBundle I3 M := ⟨γ t,velocity γ t⟩

def chartPhase (c : OpenPartialHomeomorph M E3) (γ : ℝ → M) (t : ℝ) : E3 × E3 :=
  (c (γ t),deriv (c ∘ γ) t)

lemma phaseLift_chart {γ : ℝ → M} {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ t)
    {p : TangentBundle I3 M} (hp : γ t ∈ (chartAt E3 p.1).source) :
    chartAt (ModelProd E3 E3) p (phaseLift γ t) = chartPhase (chartAt E3 p.1) γ t := by
  apply Prod.ext
  · rfl
  · have he := congrArg (fun q : TangentBundle I3 E3 => q.2)
      (tangentMap_chart (I := I3) (p := p) (q := phaseLift γ t) hp)
    exact he.symm.trans (velocity_coordinates hγ (chart_mem_atlas E3 p.1) hp)

lemma phaseLift_continuousAt {γ : ℝ → M} {t : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hγU : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (htU : t ∈ U) :
      ContinuousAt (phaseLift γ) t := by
  have hγ := hγU.contMDiffAt (hU.mem_nhds htU)
  let p := phaseLift γ t
  let c := chartAt E3 (γ t)
  have ht : γ t ∈ c.source := mem_chart_source E3 (γ t)
  have hn : γ ⁻¹' c.source ∈ 𝓝 t := hγ.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds ht)
  apply ((chartAt (ModelProd E3 E3) p).continuousAt_iff_continuousAt_comp_left
    (show (phaseLift γ) ⁻¹' (chartAt (ModelProd E3 E3) p).source ∈ 𝓝 t by
      filter_upwards [hn] with r hr
      exact (TangentBundle.mem_chart_source_iff _ _).mpr hr)).mpr
  have hcγ : ContDiffAt ℝ ∞ (c ∘ γ) t := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (subset_maximalAtlas (chart_mem_atlas E3 (γ t))) ht).comp t hγ)
  have hs : ∀ᶠ r in 𝓝 t, ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ r := by
    filter_upwards [hU.mem_nhds htU] with r hr
    exact hγU.contMDiffAt (hU.mem_nhds hr)
  apply (hcγ.continuousAt.prodMk (hcγ.derivWithin (m := ∞) (by simp)).continuousAt).congr_of_eventuallyEq
  filter_upwards [hn,hs] with r hr hrs
  exact phaseLift_chart hrs hr

lemma chartPhase_contDiffAt {γ : ℝ → M} {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ t) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (ht : γ t ∈ c.source) : ContDiffAt ℝ ∞ (chartPhase c γ) t := by
  have h : ContDiffAt ℝ ∞ (c ∘ γ) t := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (subset_maximalAtlas hc) ht).comp t hγ)
  exact h.prodMk (h.derivWithin (m := ∞) (by simp))

lemma geodesic_chartPhase_ode (g : SmoothMetric M) {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : IsGeodesicOn g γ U) {t : ℝ} (ht : t ∈ U)
    {c : OpenPartialHomeomorph M E3} (hc : c ∈ atlas E3 M) (hct : γ t ∈ c.source) :
    HasDerivAt (chartPhase c γ) (geodesicPhase g c (chartPhase c γ t)) t := by
  have hs := chartPhase_contDiffAt (hγ.1.contMDiffAt (hU.mem_nhds ht)) hc hct
  have hd := hs.snd.differentiableAt (by simp) |>.hasDerivAt
  have he := hγ.2 c hc t ht hct
  change deriv (deriv (c ∘ γ)) t + connectionTerm g c (c (γ t)) (deriv (c ∘ γ) t)
    (deriv (c ∘ γ) t) = 0 at he
  have he' : deriv (deriv (c ∘ γ)) t =
      -connectionTerm g c (c (γ t)) (deriv (c ∘ γ) t) (deriv (c ∘ γ) t) := eq_neg_of_add_eq_zero_left he
  exact (hs.fst.differentiableAt (by simp)).hasDerivAt.prodMk (hd.congr_deriv he')

lemma geodesic_eventuallyEq (g : SmoothMetric M) {γ η : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : IsGeodesicOn g γ U) (hη : IsGeodesicOn g η U)
    {t : ℝ} (ht : t ∈ U) (he : phaseLift γ t = phaseLift η t) : γ =ᶠ[𝓝 t] η := by
  let c := chartAt E3 (γ t)
  have hc := chart_mem_atlas E3 (γ t)
  have hct : γ t ∈ c.source := mem_chart_source E3 (γ t)
  have hbase : γ t = η t := congrArg Bundle.TotalSpace.proj he
  have hηt : η t ∈ c.source := hbase ▸ hct
  have hγs := hγ.1.contMDiffAt (hU.mem_nhds ht)
  have hηs := hη.1.contMDiffAt (hU.mem_nhds ht)
  have hinitial : chartPhase c γ t = chartPhase c η t := by
    have h1 := phaseLift_chart (p := phaseLift γ t) hγs hct
    have h2 := phaseLift_chart (p := phaseLift γ t) hηs hηt
    change _ = chartPhase c γ t at h1
    change _ = chartPhase c η t at h2
    rw [← h1, ← h2, he]
  obtain ⟨K,S,hS,hL⟩ :=
    (geodesicPhase_smoothAt g (z := chartPhase c γ t) hc (c.map_source hct)).of_le (show (1:ℕ∞ω) ≤ ∞ by simp)
      |>.exists_lipschitzOnWith
  have hγn : ∀ᶠ r in 𝓝 t, r ∈ U ∧ γ r ∈ c.source ∧ chartPhase c γ r ∈ S :=
    Filter.Eventually.and (hU.mem_nhds ht) (Filter.Eventually.and
      (hγs.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hct))
      ((chartPhase_contDiffAt hγs hc hct).continuousAt.preimage_mem_nhds hS))
  have hηn : ∀ᶠ r in 𝓝 t, r ∈ U ∧ η r ∈ c.source ∧ chartPhase c η r ∈ S :=
    Filter.Eventually.and (hU.mem_nhds ht) (Filter.Eventually.and
      (hηs.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hηt))
      ((chartPhase_contDiffAt hηs hc hηt).continuousAt.preimage_mem_nhds (hinitial ▸ hS)))
  have hode := ODE_solution_unique_of_eventually (v := fun _ => geodesicPhase g c)
    (s := fun _ => S) (Filter.Eventually.of_forall (fun _ => hL))
    (hγn.mono (fun r hr => ⟨geodesic_chartPhase_ode g hU hγ hr.1 hc hr.2.1,hr.2.2⟩))
    (hηn.mono (fun r hr => ⟨geodesic_chartPhase_ode g hU hη hr.1 hc hr.2.1,hr.2.2⟩)) hinitial
  filter_upwards [hode,hγn,hηn] with r hr hgr her
  exact c.injOn hgr.2.1 her.2.1 (congrArg Prod.fst hr)

lemma phaseLift_eventuallyEq {γ η : ℝ → M} {t : ℝ} (he : γ =ᶠ[𝓝 t] η) :
    phaseLift γ =ᶠ[𝓝 t] phaseLift η := by
  let _ : IsManifold I3 ∞ M := inferInstance
  filter_upwards [he.eventually_nhds] with r hr
  change γ =ᶠ[𝓝 r] η at hr
  have hb := hr.eq_of_nhds
  have hd := congrArg (fun L : ℝ →L[ℝ] E3 => L 1) (hr.mfderiv_eq (I := 𝓘(ℝ,ℝ)) (I' := I3))
  unfold phaseLift velocity
  exact Bundle.TotalSpace.ext hb (heq_of_eq hd)

theorem geodesic_unique [T2Space M] (g : SmoothMetric M) {γ η : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hUc : OrdConnected U) (hγ : IsGeodesicOn g γ U) (hη : IsGeodesicOn g η U)
    {t : ℝ} (ht : t ∈ U) (he : phaseLift γ t = phaseLift η t) : EqOn γ η U := by
  let : T2Space (TangentBundle I3 M) := fiberBundle_t2
  let Z : Set U := {s | phaseLift γ s = phaseLift η s}
  let : PreconnectedSpace U := Subtype.preconnectedSpace hUc.isPreconnected
  have hZ : IsClopen Z := by
    constructor
    · apply isClosed_eq
      · exact continuous_iff_continuousAt.mpr (fun s =>
          (phaseLift_continuousAt hU hγ.1 s.property).comp continuous_subtype_val.continuousAt)
      · exact continuous_iff_continuousAt.mpr (fun s =>
          (phaseLift_continuousAt hU hη.1 s.property).comp continuous_subtype_val.continuousAt)
    · apply isOpen_iff_mem_nhds.mpr
      intro s hs
      exact continuous_subtype_val.continuousAt.preimage_mem_nhds
        (phaseLift_eventuallyEq (geodesic_eventuallyEq g hU hγ hη s.property hs))
  have hZu := hZ.eq_univ ⟨⟨t,ht⟩,he⟩
  intro s hs
  have hsz : (⟨s,hs⟩ : U) ∈ Z := by rw [hZu]; trivial
  exact congrArg Bundle.TotalSpace.proj hsz
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle
namespace ThreeManifold.CompactEnergy
variable {B : Type*} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
variable {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

lemma continuous_fiberNorm : Continuous (fun p : TotalSpace F E => ‖p.2‖) := by
  let _ : CompactSpace B := inferInstance
  let _ : T2Space B := inferInstance
  let _ : ProperSpace F := inferInstance
  have h : Continuous (fun p : TotalSpace F E => inner ℝ p.2 p.2) :=
    Continuous.inner_bundle continuous_id continuous_id
  convert h.sqrt using 1
  ext p
  simp

theorem isCompact_fiberDisk (R : ℝ) :
    IsCompact {p : TotalSpace F E | ‖p.2‖ ≤ R} := by
  classical
  have hlocal : ∀ x : B, ∃ C > (0:ℝ), ∃ K : Set B,
      K ∈ 𝓝 x ∧ IsCompact K ∧ K ⊆ (trivializationAt F E x).baseSet ∧
      ∀ y ∈ K, ‖(trivializationAt F E x).continuousLinearMapAt ℝ y‖ ≤ C := by
    intro x
    obtain ⟨C,hC,hb⟩ := eventually_norm_trivializationAt_lt F E x
    obtain ⟨K,hK,hsub,hcomp⟩ := local_compact_nhds
      (inter_mem hb ((trivializationAt F E x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' x)))
    exact ⟨C,hC,K,hK,hcomp,fun y hy => (hsub hy).2,fun y hy => (hsub hy).1.le⟩
  choose C hC K hKn hKc hKb hbound using hlocal
  obtain ⟨T,_,hcover⟩ := isCompact_univ.elim_nhds_subcover K (fun x _ => hKn x)
  let L : B → Set (TotalSpace F E) := fun x =>
    (trivializationAt F E x).toOpenPartialHomeomorph.symm ''
      (K x ×ˢ Metric.closedBall (0:F) (C x * max R 0))
  have hLc : ∀ x, IsCompact (L x) := by
    intro x
    apply ((hKc x).prod (isCompact_closedBall _ _)).image_of_continuousOn
    exact (trivializationAt F E x).toOpenPartialHomeomorph.continuousOn_symm.mono
      (fun z hz => (trivializationAt F E x).mem_target.mpr (hKb x hz.1))
  apply (T.isCompact_biUnion (fun x _ => hLc x)).of_isClosed_subset
    (isClosed_le continuous_fiberNorm continuous_const)
  intro p hp
  obtain ⟨x,hx,hpx⟩ := mem_iUnion₂.mp (hcover (mem_univ p.1))
  apply mem_iUnion₂.mpr
  refine ⟨x,hx,?_⟩
  let e := trivializationAt F E x
  have hps : p ∈ e.source := e.mem_source.mpr (hKb x hpx)
  refine ⟨e p,⟨?_,?_⟩,e.symm_apply_apply hps⟩
  · simpa only [e.coe_fst hps] using hpx
  · rw [Metric.mem_closedBall,dist_zero_right]
    have he : (e p).2 = e.continuousLinearMapAt ℝ p.1 p.2 := by
      exact (e.continuousLinearMapAt_apply_of_mem ℝ (hKb x hpx) p.2).symm
    rw [he]
    calc
      ‖e.continuousLinearMapAt ℝ p.1 p.2‖ ≤ ‖e.continuousLinearMapAt ℝ p.1‖ * ‖p.2‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ C x * max R 0 := mul_le_mul (hbound x p.1 hpx) (hp.trans (le_max_left _ _))
        (norm_nonneg _) (hC x).le
end ThreeManifold.CompactEnergy
end

section
open Set Filter Topology Bundle Manifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

def phaseEnergy (g : SmoothMetric M) (p : TangentBundle I3 M) : ℝ := g.inner p.1 p.2 p.2

lemma continuous_phaseEnergy (g : SmoothMetric M) : Continuous (phaseEnergy g) := by
  let _ : CompactSpace M := inferInstance
  let _ : T2Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace I3 x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  have h : Continuous (fun p : TangentBundle I3 M => inner ℝ p.2 p.2) :=
    Continuous.inner_bundle continuous_id continuous_id
  exact h

theorem isCompact_phaseEnergy (g : SmoothMetric M) (R : ℝ) :
    IsCompact {p : TangentBundle I3 M | phaseEnergy g p ≤ R} := by
  let : RiemannianBundle (fun x : M => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace I3 x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  apply (CompactEnergy.isCompact_fiberDisk (F := E3) (E := fun x : M => TangentSpace I3 x)
    (Real.sqrt (max R 0))).of_isClosed_subset (isClosed_le (continuous_phaseEnergy g) continuous_const)
  intro p hp
  change ‖p.2‖ ≤ Real.sqrt (max R 0)
  rw [norm_eq_sqrt_real_inner]
  apply Real.sqrt_le_sqrt
  exact hp.trans (le_max_left _ _)
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology
namespace ThreeManifold.FlowContinuation

structure Equation (X : Type*) where
  Holds : (ℝ → X) → ℝ → Prop
  germ {z w : ℝ → X} {t : ℝ} : z =ᶠ[𝓝 t] w → Holds z t → Holds w t
  shift (z : ℝ → X) (a t : ℝ) : Holds (fun r => z (r+a)) t ↔ Holds z (t+a)
  unique {z w : ℝ → X} {a b t : ℝ} :
    (∀ r ∈ Ioo a b, Holds z r) → (∀ r ∈ Ioo a b, Holds w r) →
      t ∈ Ioo a b → z t = w t → EqOn z w (Ioo a b)
namespace Equation
variable {X : Type*} (P : Equation X)
def CurveOn (z : ℝ → X) (U : Set ℝ) : Prop := ∀ t ∈ U, P.Holds z t
lemma CurveOn.mono {z : ℝ → X} {U V : Set ℝ} (h : P.CurveOn z U) (hVU : V ⊆ U) :
    P.CurveOn z V := fun t ht => h t (hVU ht)
lemma CurveOn.comp_add {z : ℝ → X} {U : Set ℝ} (h : P.CurveOn z U) (a : ℝ) :
    P.CurveOn (fun r => z (r+a)) ((fun r => r+a) ⁻¹' U) := by
  intro t ht
  exact (P.shift z a t).mpr (h (t+a) ht)
lemma eqOn_piecewise {z w : ℝ → X} {a b c d t : ℝ}
    (hz : P.CurveOn z (Ioo a b)) (hw : P.CurveOn w (Ioo c d))
    (ht : t ∈ Ioo a b ∩ Ioo c d) (he : z t = w t) :
    EqOn (piecewise (Ioo a b) z w) w (Ioo c d) := by
  classical
  have H : EqOn z w (Ioo (max a c) (min b d)) :=
    P.unique (hz.mono P (Ioo_subset_Ioo (le_max_left ..) (min_le_left ..)))
      (hw.mono P (Ioo_subset_Ioo (le_max_right ..) (min_le_right ..)))
      ⟨max_lt ht.1.1 ht.2.1,lt_min ht.1.2 ht.2.2⟩ he
  intro r hr
  by_cases hrz : r ∈ Ioo a b
  · rw [piecewise,ite_eq_left hrz]
    exact H ⟨max_lt hrz.1 hr.1,lt_min hrz.2 hr.2⟩
  · rw [piecewise,ite_eq_right hrz]
lemma curveOn_piecewise {z w : ℝ → X} {a b c d t : ℝ}
    (hz : P.CurveOn z (Ioo a b)) (hw : P.CurveOn w (Ioo c d))
    (ht : t ∈ Ioo a b ∩ Ioo c d) (he : z t = w t) :
    P.CurveOn (piecewise (Ioo a b) z w) (Ioo a b ∪ Ioo c d) := by
  classical
  intro r hr
  by_cases hrz : r ∈ Ioo a b
  · exact P.germ (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hrz)
      (fun s hs => (piecewise_eq_of_mem (Ioo a b) z w hs).symm)) (hz r hrz)
  · have hrw := hr.resolve_left hrz
    exact P.germ (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hrw)
      (fun s hs => (P.eqOn_piecewise hz hw ht he hs).symm)) (hw r hrw)

lemma global_of_arbitrarily_long {x : X}
    (h : ∀ a : ℝ, ∃ z, z 0 = x ∧ P.CurveOn z (Ioo (-a) a)) :
    ∃ z, z 0 = x ∧ ∀ t, P.Holds z t := by
  choose z h0 hz using h
  have he {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : EqOn (z a) (z b) (Ioo (-a) a) :=
    P.unique (hz a) ((hz b).mono P (Ioo_subset_Ioo (neg_le_neg hab) hab))
      ⟨neg_lt_zero.mpr ha,ha⟩ ((h0 a).trans (h0 b).symm)
  let w : ℝ → X := fun t => z (|t|+1) t
  have hw {a : ℝ} : EqOn w (z a) (Ioo (-a) a) := by
    intro t ht
    by_cases hta : |t|+1 ≤ a
    · exact he (by positivity) hta (abs_lt.mp (lt_add_one _))
    · exact (he (by linarith [ht.1,ht.2]) (le_of_not_ge hta) ht).symm
  refine ⟨w,h0 (|0|+1),fun t => ?_⟩
  have ht : t ∈ Ioo (-(|t|+1)) (|t|+1) := abs_lt.mp (lt_add_one _)
  exact P.germ (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun r hr => (hw hr).symm))
    (hz (|t|+1) t ht)

theorem exists_global_of_uniform_invariant {K : Set X} {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ x ∈ K, ∃ z : ℝ → X, z 0 = x ∧ P.CurveOn z (Ioo (-ε) ε))
    (hinv : ∀ (z : ℝ → X) (a : ℝ), 0 < a → z 0 ∈ K →
      P.CurveOn z (Ioo (-a) a) → MapsTo z (Ioo (-a) a) K)
    {x : X} (hx : x ∈ K) : ∃ z, z 0 = x ∧ ∀ t, P.Holds z t := by
  classical
  let S := {a : ℝ | ∃ z, z 0 = x ∧ P.CurveOn z (Ioo (-a) a)}
  have hεS : ε ∈ S := hloc x hx
  apply P.global_of_arbitrarily_long
  suffices hnb : ¬ BddAbove S by
    intro a
    obtain ⟨b,hb,hab⟩ := not_bddAbove_iff.mp hnb a
    obtain ⟨z,hz0,hz⟩ := hb
    exact ⟨z,hz0,hz.mono P (Ioo_subset_Ioo (neg_le_neg hab.le) hab.le)⟩
  intro hbdd
  let A := sSup S
  have hεA : ε ≤ A := le_csSup hbdd hεS
  obtain ⟨a,⟨z,hz0,hz⟩,ha⟩ := Real.add_neg_lt_sSup (⟨ε,hεS⟩ : S.Nonempty)
    (ε := -(ε/2)) (by linarith)
  change A + -(ε/2) < a at ha
  have ha0 : 0 < a := by linarith
  have hleft : -(A-ε/2) ∈ Ioo (-a) a := ⟨by linarith,by linarith⟩
  have hright : A-ε/2 ∈ Ioo (-a) a := ⟨by linarith,by linarith⟩
  have hzK := hinv z a ha0 (hz0 ▸ hx) hz
  obtain ⟨z1,h10,h1⟩ := hloc (z (-(A-ε/2))) (hzK hleft)
  obtain ⟨z2,h20,h2⟩ := hloc (z (A-ε/2)) (hzK hright)
  let w1 : ℝ → X := fun t => z1 (t+(A-ε/2))
  let w2 : ℝ → X := fun t => z2 (t-(A-ε/2))
  have hw1 : P.CurveOn w1 (Ioo (-(A+ε/2)) (-(A-3*ε/2))) := by
    apply (h1.comp_add P (A-ε/2)).mono P
    intro t ht; change -ε < t+(A-ε/2) ∧ t+(A-ε/2) < ε
    constructor <;> linarith [ht.1,ht.2]
  have hw2 : P.CurveOn w2 (Ioo (A-3*ε/2) (A+ε/2)) := by
    apply (h2.comp_add P (-(A-ε/2))).mono P
    intro t ht; change -ε < t+ -(A-ε/2) ∧ t+ -(A-ε/2) < ε
    constructor <;> linarith [ht.1,ht.2]
  have he1 : z (-(A-ε/2)) = w1 (-(A-ε/2)) := by simp [w1,h10]
  have he2 : z (A-ε/2) = w2 (A-ε/2) := by simp [w2,h20]
  let w : ℝ → X := piecewise (Ioo (-(A+ε/2)) a) (piecewise (Ioo (-a) a) z w1) w2
  have hw0 : w 0 = x := by
    simp only [w,piecewise,ite_eq_left (show 0 ∈ Ioo (-(A+ε/2)) a from ⟨by linarith,ha0⟩),
      ite_eq_left (show 0 ∈ Ioo (-a) a from ⟨by linarith,ha0⟩),hz0]
  have hw : P.CurveOn w (Ioo (-(A+ε/2)) (A+ε/2)) := by
    apply (P.curveOn_piecewise (t := A-ε/2) ?_ hw2
      ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
      (by rw [piecewise,ite_eq_left hright]; exact he2)).mono P
      (Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith))
    exact (P.curveOn_piecewise hz hw1
      ⟨hleft,⟨by linarith,by linarith⟩⟩ he1).mono P
      (union_comm _ _ ▸ Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl)
  exact (not_lt.mpr (le_csSup hbdd (show A+ε/2 ∈ S from ⟨w,hw0,hw⟩)))
    (lt_add_of_pos_right A (half_pos hε))

theorem exists_global_of_compact_invariant [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (hloc : ∀ x ∈ K, ∃ U ∈ 𝓝 x, ∃ ε > (0:ℝ), ∀ y ∈ U,
      ∃ z, z 0 = y ∧ P.CurveOn z (Ioo (-ε) ε))
    (hinv : ∀ (z : ℝ → X) (a : ℝ), 0 < a → z 0 ∈ K →
      P.CurveOn z (Ioo (-a) a) → MapsTo z (Ioo (-a) a) K)
    {x : X} (hx : x ∈ K) : ∃ z, z 0 = x ∧ ∀ t, P.Holds z t := by
  classical
  choose U hUn ε hε hsol using hloc
  obtain ⟨T,hcover⟩ := hK.elim_nhds_subcover' U hUn
  have hT : T.Nonempty := by
    obtain ⟨i,hi,_⟩ := mem_iUnion₂.mp (hcover hx)
    exact ⟨i,hi⟩
  let e := T.inf' hT (fun i => ε i i.property)
  have he : 0 < e := (Finset.lt_inf'_iff hT).mpr (fun i _ => hε i i.property)
  apply P.exists_global_of_uniform_invariant he ?_ hinv hx
  intro y hy
  obtain ⟨i,hi,hyi⟩ := mem_iUnion₂.mp (hcover hy)
  obtain ⟨z,hz0,hz⟩ := hsol i i.property y hyi
  have hei : e ≤ ε i i.property := Finset.inf'_le _ hi
  exact ⟨z,hz0,hz.mono P (Ioo_subset_Ioo (neg_le_neg hei) hei)⟩
end Equation
end ThreeManifold.FlowContinuation
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma deriv_comp_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a t : ℝ} (hf : DifferentiableAt ℝ f (t+a)) :
    deriv (fun r => f (r+a)) t = deriv f (t+a) := by
  exact (hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).add_const a)).deriv

lemma geodesic_translate (g : SmoothMetric M) {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : IsGeodesicOn g γ U) (a : ℝ) :
    IsGeodesicOn g (fun r => γ (r+a)) ((fun r => r+a) ⁻¹' U) := by
  have htA : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun r : ℝ => r+a) :=
    contMDiff_iff_contDiff.mpr (contDiff_id.add contDiff_const)
  refine ⟨hγ.1.comp htA.contMDiffOn (fun _ h => h),?_⟩
  intro c hc t ht hct
  have hs := chartPhase_contDiffAt (hγ.1.contMDiffAt (hU.mem_nhds ht)) hc hct
  have hn : ∀ᶠ r in 𝓝 t, r+a ∈ U ∧ γ (r+a) ∈ c.source :=
    continuousAt_id.add continuousAt_const |>.preimage_mem_nhds
      (Filter.Eventually.and (hU.mem_nhds ht)
        ((hγ.1.contMDiffAt (hU.mem_nhds ht)).continuousAt.preimage_mem_nhds
          (c.open_source.mem_nhds hct)))
  have hd : deriv (c ∘ (fun r => γ (r+a))) =ᶠ[𝓝 t] fun r => deriv (c ∘ γ) (r+a) := by
    filter_upwards [hn] with r hr
    exact deriv_comp_translate ((chartPhase_contDiffAt
      (hγ.1.contMDiffAt (hU.mem_nhds hr.1)) hc hr.2).fst.differentiableAt (by simp))
  have hdd : deriv (deriv (c ∘ (fun r => γ (r+a)))) t = deriv (deriv (c ∘ γ)) (t+a) :=
    hd.deriv_eq.trans (deriv_comp_translate (hs.snd.differentiableAt (by simp)))
  change _ + _ = 0
  rw [hdd,hd.eq_of_nhds]
  exact hγ.2 c hc (t+a) ht hct

lemma phaseLift_translate {γ : ℝ → M} {a t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ (t+a)) :
    phaseLift (fun r => γ (r+a)) t = phaseLift γ (t+a) := by
  let p := phaseLift γ (t+a)
  let c := chartAt (ModelProd E3 E3) p
  have htrans : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ (fun r => γ (r+a)) t := hγ.comp t
    (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_id.add contDiffAt_const))
  have hs : phaseLift (fun r => γ (r+a)) t ∈ c.source :=
    (TangentBundle.mem_chart_source_iff _ _).mpr (mem_chart_source E3 (γ (t+a)))
  apply c.injOn hs (mem_chart_source (ModelProd E3 E3) p)
  rw [phaseLift_chart htrans (mem_chart_source E3 (γ (t+a))),
    phaseLift_chart hγ (mem_chart_source E3 (γ (t+a)))]
  apply Prod.ext
  · rfl
  exact deriv_comp_translate ((chartPhase_contDiffAt hγ (chart_mem_atlas E3 (γ (t+a)))
    (mem_chart_source E3 (γ (t+a)))).fst.differentiableAt (by simp))

def PhaseGeodesicAt (g : SmoothMetric M) (z : ℝ → TangentBundle I3 M) (t : ℝ) : Prop :=
  ∃ (γ : ℝ → M) (U : Set ℝ), IsOpen U ∧ t ∈ U ∧ IsGeodesicOn g γ U ∧ EqOn z (phaseLift γ) U

lemma phaseGeodesic_germ (g : SmoothMetric M) {z w : ℝ → TangentBundle I3 M} {t : ℝ}
    (he : z =ᶠ[𝓝 t] w) (hz : PhaseGeodesicAt g z t) : PhaseGeodesicAt g w t := by
  obtain ⟨γ,U,hU,ht,hγ,hz⟩ := hz
  obtain ⟨V,hV,hVo,htV⟩ := mem_nhds_iff.mp he
  exact ⟨γ,U ∩ V,hU.inter hVo,⟨ht,htV⟩,⟨hγ.1.mono inter_subset_left,
    fun c hc s hs hsc => hγ.2 c hc s hs.1 hsc⟩,
    fun s hs => (hV hs.2).symm.trans (hz hs.1)⟩

lemma phaseGeodesic_translate (g : SmoothMetric M) {z : ℝ → TangentBundle I3 M} {a t : ℝ}
    (hz : PhaseGeodesicAt g z (t+a)) : PhaseGeodesicAt g (fun r => z (r+a)) t := by
  obtain ⟨γ,U,hU,ht,hγ,hz⟩ := hz
  refine ⟨fun r => γ (r+a),(fun r => r+a) ⁻¹' U,
    hU.preimage (continuous_id.add continuous_const),ht,geodesic_translate g hU hγ a,?_⟩
  intro r hr
  exact (hz hr).trans (phaseLift_translate (hγ.1.contMDiffAt (hU.mem_nhds hr))).symm

lemma phaseGeodesicOn_base (g : SmoothMetric M) {z : ℝ → TangentBundle I3 M} {U : Set ℝ}
    (_hU : IsOpen U) (hz : ∀ t ∈ U, PhaseGeodesicAt g z t) :
    IsGeodesicOn g (fun t => (z t).proj) U ∧ EqOn z (phaseLift (fun t => (z t).proj)) U := by
  have hlocal (t : ℝ) (ht : t ∈ U) : ∃ γ V, IsOpen V ∧ t ∈ V ∧ IsGeodesicOn g γ V ∧
      (fun r => (z r).proj) =ᶠ[𝓝 t] γ ∧ z t = phaseLift γ t := by
    obtain ⟨γ,V,hV,htV,hγ,he⟩ := hz t ht
    exact ⟨γ,V,hV,htV,hγ,(Filter.eventually_of_mem (hV.mem_nhds htV)
      (fun r hr => congrArg Bundle.TotalSpace.proj (he hr))),he htV⟩
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro t ht
    obtain ⟨γ,V,hV,htV,hγ,he,_⟩ := hlocal t ht
    exact ((hγ.1.contMDiffAt (hV.mem_nhds htV)).congr_of_eventuallyEq he).contMDiffWithinAt
  · intro c hc t ht hct
    obtain ⟨γ,V,hV,htV,hγ,he,_⟩ := hlocal t ht
    have hec := he.fun_comp c
    rw [along_congr g c hec hec.deriv]
    exact hγ.2 c hc t htV (he.eq_of_nhds ▸ hct)
  · intro t ht
    obtain ⟨γ,V,hV,htV,hγ,he,het⟩ := hlocal t ht
    exact het.trans (phaseLift_eventuallyEq he).eq_of_nhds.symm

def geodesicEquation [T2Space M] (g : SmoothMetric M) : FlowContinuation.Equation (TangentBundle I3 M) where
  Holds := PhaseGeodesicAt g
  germ := phaseGeodesic_germ g
  shift z a t := by
    constructor
    · intro h
      have hh := phaseGeodesic_translate g (a := -a) (t := t+a) (by simpa using h)
      simpa only [add_assoc,neg_add_cancel,add_zero] using hh
    · exact phaseGeodesic_translate g
  unique := by
    intro z w a b t hz hw ht he
    obtain ⟨hγ,hzp⟩ := phaseGeodesicOn_base g isOpen_Ioo hz
    obtain ⟨hη,hwp⟩ := phaseGeodesicOn_base g isOpen_Ioo hw
    have hbase := geodesic_unique g isOpen_Ioo ordConnected_Ioo hγ hη ht
      ((hzp ht).symm.trans (he.trans (hwp ht)))
    intro r hr
    have hphase := phaseLift_eventuallyEq
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hr) (fun s hs => hbase hs))
    exact (hzp hr).trans (hphase.eq_of_nhds.trans (hwp hr).symm)

lemma phaseGeodesic_local_existence (g : SmoothMetric M) (p : TangentBundle I3 M) :
    ∃ U ∈ 𝓝 p, ∃ ε > (0:ℝ), ∀ y ∈ U,
      ∃ z, z 0 = y ∧ ∀ t ∈ Ioo (-ε) ε, PhaseGeodesicAt g z t := by
  let c := chartAt E3 p.1
  let C := chartAt (ModelProd E3 E3) p
  have hp : p ∈ C.source := mem_chart_source _ p
  have hp' : (C p).1 ∈ c.target := c.map_source (mem_chart_source E3 p.1)
  obtain ⟨r,hr,ε,hε,X,h0,hγ,hd,hXt,_⟩ := exists_geodesic_local_flow g (chart_mem_atlas E3 p.1) hp'
  let q : TangentBundle I3 M → E3 × E3 := fun y => C y
  let U := C.source ∩ q ⁻¹' Metric.ball (q p) r
  have hUn : U ∈ 𝓝 p := inter_mem (C.open_source.mem_nhds hp)
    ((show ContinuousAt q p from C.continuousAt hp).preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)))
  refine ⟨U,hUn,ε,hε,?_⟩
  intro y hy
  let γ : ℝ → M := fun t => c.symm (X (C y) t).1
  have hyb : C y ∈ Metric.ball (q p) r := hy.2
  have hzero : (0:ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,by linarith⟩
  have hγs : IsGeodesicOn g γ (Ioo (-ε) ε) := hγ (C y) hyb
  have hm : γ 0 ∈ c.source := c.map_target (hXt (C y) hyb 0 hzero)
  have hchart : chartPhase c γ 0 = C y := by
    have he : c ∘ γ =ᶠ[𝓝 (0:ℝ)] fun t => (X (C y) t).1 :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hzero)
        (fun t ht => c.right_inv (hXt (C y) hyb t ht))
    apply Prod.ext
    · exact he.eq_of_nhds.trans (congrArg Prod.fst (h0 (C y) hyb))
    · have hd1 : HasDerivAt (fun t => (X (C y) t).1) (X (C y) 0).2 0 :=
        (hd (C y) hyb 0 hzero).fst
      exact he.deriv_eq.trans (hd1.deriv.trans (congrArg Prod.snd (h0 (C y) hyb)))
  refine ⟨phaseLift γ,?_,fun t ht => ⟨γ,Ioo (-ε) ε,isOpen_Ioo,ht,hγs,fun _ _ => rfl⟩⟩
  apply C.injOn ((TangentBundle.mem_chart_source_iff _ _).mpr hm) hy.1
  exact (phaseLift_chart (p := p) (hγs.1.contMDiffAt (isOpen_Ioo.mem_nhds hzero)) hm).trans hchart

lemma phaseEnergy_conserved [CompactSpace M] [T2Space M] (g : SmoothMetric M)
    {z : ℝ → TangentBundle I3 M} {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hz : ∀ t ∈ U, PhaseGeodesicAt g z t) {s t : ℝ} (hs : s ∈ U) (ht : t ∈ U) :
    phaseEnergy g (z s) = phaseEnergy g (z t) := by
  obtain ⟨hγ,he⟩ := phaseGeodesicOn_base g hU hz
  let f : ℝ → ℝ := fun r => g.inner (z r).proj (velocity (fun u => (z u).proj) r)
    (velocity (fun u => (z u).proj) r)
  have hd : ∀ r ∈ U, HasDerivAt f 0 r := fun r hr => geodesic_speed_hasDerivAt g hU hγ hr
  have hc : f s = f t := hU.is_const_of_deriv_eq_zero hUc.isPreconnected
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht
  change _ = _
  rw [he hs,he ht]
  exact hc

theorem exists_global_geodesic [CompactSpace M] [T2Space M] (g : SmoothMetric M)
    (p : TangentBundle I3 M) :
    ∃ γ : ℝ → M, phaseLift γ 0 = p ∧ IsGeodesicOn g γ univ := by
  let K := {q : TangentBundle I3 M | phaseEnergy g q ≤ phaseEnergy g p}
  have hinv : ∀ (z : ℝ → TangentBundle I3 M) (a : ℝ), 0 < a → z 0 ∈ K →
      (geodesicEquation g).CurveOn z (Ioo (-a) a) → MapsTo z (Ioo (-a) a) K := by
    intro z a ha hzK hcurve t ht
    change phaseEnergy g (z t) ≤ phaseEnergy g p
    rw [phaseEnergy_conserved g isOpen_Ioo ordConnected_Ioo hcurve ht
      (show (0:ℝ) ∈ Ioo (-a) a from ⟨by linarith,ha⟩)]
    exact hzK
  obtain ⟨z,hz0,hz⟩ := (geodesicEquation g).exists_global_of_compact_invariant
    (K := K) (isCompact_phaseEnergy g (phaseEnergy g p))
    (fun q _ => phaseGeodesic_local_existence g q) hinv
    (x := p) (show p ∈ K from (show phaseEnergy g p ≤ phaseEnergy g p from le_rfl))
  obtain ⟨hγ,he⟩ := phaseGeodesicOn_base g isOpen_univ (fun t _ => hz t)
  exact ⟨fun t => (z t).proj,(he (mem_univ 0)).symm.trans hz0,hγ⟩
end ThreeManifold.RiemannianCoordinates
end

section

open Set Filter Topology Manifold
open scoped ContDiff
namespace ThreeManifold.FlowContinuation
variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

lemma flow_contMDiff (F : X → ℝ → X)
    (h0 : ∀ x, F x 0 = x)
    (hadd : ∀ x s t, F (F x s) t = F x (s+t))
    (hc : ∀ x, Continuous (F x))
    (hloc : ∀ x, ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) I 1 (Function.uncurry F) (x,0)) :
    ContMDiff (I.prod 𝓘(ℝ,ℝ)) I 1 (Function.uncurry F) := by
  have htime (x : X) (t : ℝ) : ContMDiffAt I I 1 (fun y => F y t) x := by
    let Z := {s : ℝ | ContMDiffAt I I 1 (fun y => F y s) x}
    have hstep {s t : ℝ} (hs : s ∈ Z)
        (hl : ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) I 1 (Function.uncurry F) (F x s,t-s)) : t ∈ Z := by
      have hh := hl.comp x (hs.prodMk (contMDiffAt_const (c := t-s)))
      apply hh.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun y => by
        change F y t = F (F y s) (t-s)
        rw [hadd,add_sub_cancel])
    have hZc : IsClosed Z := by
      apply isClosed_of_closure_subset
      intro t ht
      have hh := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1:ℕ∞ω) ≠ ∞)).mp (hloc (F x t))
      have hd : ContinuousAt (fun s => (F x s,t-s)) t :=
        ((hc x).continuousAt).prodMk (continuousAt_const.sub continuousAt_id)
      have hn : {s : ℝ | ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) I 1
          (Function.uncurry F) (F x s,t-s)} ∈ 𝓝 t := by
        have hh' : ∀ᶠ q in 𝓝 (F x t,t-t), ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) I 1
            (Function.uncurry F) q := by simpa only [sub_self] using hh
        exact hd.eventually hh'
      obtain ⟨s,hs,hst⟩ := mem_closure_iff_nhds.mp ht _ hn
      exact hstep hst hs
    have hZo : IsOpen Z := by
      apply isOpen_iff_mem_nhds.mpr
      intro s hs
      have hh := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1:ℕ∞ω) ≠ ∞)).mp (hloc (F x s))
      have hd : ContinuousAt (fun t : ℝ => (F x s,t-s)) s :=
        continuousAt_const.prodMk (continuousAt_id.sub continuousAt_const)
      have hn : {t : ℝ | ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) I 1
          (Function.uncurry F) (F x s,t-s)} ∈ 𝓝 s := by
        have hh' : ∀ᶠ q in 𝓝 (F x s,s-s), ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) I 1
            (Function.uncurry F) q := by simpa only [sub_self] using hh
        exact hd.eventually hh'
      exact Filter.mem_of_superset hn (fun t ht => hstep hs ht)
    have h0Z : (0:ℝ) ∈ Z := contMDiffAt_id.congr_of_eventuallyEq
      (Filter.Eventually.of_forall h0)
    have he := (show IsClopen Z from ⟨hZc,hZo⟩).eq_univ ⟨0,h0Z⟩
    change t ∈ Z
    rw [he]
    trivial
  intro p
  have hfirst : ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) I 1 (fun q : X × ℝ => F q.1 p.2) p :=
    (htime p.1 p.2).comp p contMDiffAt_fst
  have hsecond : ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) 1
      (fun q : X × ℝ => q.2-p.2) p := contMDiffAt_snd.sub contMDiffAt_const
  have hl : ContMDiffAt (I.prod 𝓘(ℝ,ℝ)) I 1 (Function.uncurry F) (F p.1 p.2,p.2-p.2) := by
    simpa only [sub_self] using hloc (F p.1 p.2)
  apply (hl.comp p (hfirst.prodMk hsecond)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun q => by
    change F q.1 q.2 = F (F q.1 p.2) (q.2-p.2)
    rw [hadd,add_sub_cancel])
end ThreeManifold.FlowContinuation
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

def globalGeodesic (g : SmoothMetric M) (p : TangentBundle I3 M) : ℝ → M :=
  (exists_global_geodesic g p).choose
lemma globalGeodesic_initial (g : SmoothMetric M) (p : TangentBundle I3 M) :
    phaseLift (globalGeodesic g p) 0 = p := (exists_global_geodesic g p).choose_spec.1
lemma globalGeodesic_isGeodesic (g : SmoothMetric M) (p : TangentBundle I3 M) :
    IsGeodesicOn g (globalGeodesic g p) univ := (exists_global_geodesic g p).choose_spec.2

def geodesicFlow (g : SmoothMetric M) (p : TangentBundle I3 M) (t : ℝ) : TangentBundle I3 M :=
  phaseLift (globalGeodesic g p) t
lemma geodesicFlow_zero (g : SmoothMetric M) (p : TangentBundle I3 M) :
    geodesicFlow g p 0 = p := globalGeodesic_initial g p
lemma geodesicFlow_continuous (g : SmoothMetric M) (p : TangentBundle I3 M) :
    Continuous (geodesicFlow g p) := continuous_iff_continuousAt.mpr (fun t =>
      phaseLift_continuousAt isOpen_univ (globalGeodesic_isGeodesic g p).1 (mem_univ t))
lemma geodesicFlow_add (g : SmoothMetric M) (p : TangentBundle I3 M) (s t : ℝ) :
    geodesicFlow g (geodesicFlow g p s) t = geodesicFlow g p (s+t) := by
  have hγ := globalGeodesic_isGeodesic g p
  have hη := globalGeodesic_isGeodesic g (geodesicFlow g p s)
  have htrans : IsGeodesicOn g (fun r => globalGeodesic g p (r+s)) univ := by
    simpa using geodesic_translate g isOpen_univ hγ s
  have h0 : phaseLift (globalGeodesic g (geodesicFlow g p s)) 0 =
      phaseLift (fun r => globalGeodesic g p (r+s)) 0 := by
    rw [globalGeodesic_initial,phaseLift_translate (hγ.1.contMDiffAt (by simp)),zero_add]
    rfl
  have he := geodesic_unique g isOpen_univ ordConnected_univ hη htrans (mem_univ 0) h0
  have he' := phaseLift_eventuallyEq (t := t) (Filter.Eventually.of_forall (fun r => he (mem_univ r)))
  change phaseLift _ t = _
  rw [he'.eq_of_nhds,phaseLift_translate (hγ.1.contMDiffAt (by simp)),add_comm]
  rfl

lemma geodesicFlow_eq_chart (g : SmoothMetric M) (p : TangentBundle I3 M)
    {ε : ℝ} (hε : 0 < ε) {X : (E3 × E3) → ℝ → E3 × E3} {y : TangentBundle I3 M}
    (hy : y ∈ (chartAt (ModelProd E3 E3) p).source)
    (h0 : X (chartAt (ModelProd E3 E3) p y) 0 = chartAt (ModelProd E3 E3) p y)
    (hd : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (X (chartAt (ModelProd E3 E3) p y))
      (geodesicPhase g (chartAt E3 p.1) (X (chartAt (ModelProd E3 E3) p y) t)) t)
    (hXt : ∀ t ∈ Ioo (-ε) ε, (X (chartAt (ModelProd E3 E3) p y) t).1 ∈ (chartAt E3 p.1).target)
    {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    geodesicFlow g y t = (extChartAt I3.tangent p).symm (X (chartAt (ModelProd E3 E3) p y) t) := by
  let c := chartAt E3 p.1
  let C := chartAt (ModelProd E3 E3) p
  let γ : ℝ → M := fun r => c.symm (X (C y) r).1
  have hγ : IsGeodesicOn g γ (Ioo (-ε) ε) := chart_geodesic g (chart_mem_atlas E3 p.1) isOpen_Ioo hXt hd
  have hz : (0:ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  have hphase : ∀ r ∈ Ioo (-ε) ε, C (phaseLift γ r) = X (C y) r := by
    intro r hr
    rw [phaseLift_chart (hγ.1.contMDiffAt (isOpen_Ioo.mem_nhds hr)) (c.map_target (hXt r hr))]
    have he : c ∘ γ =ᶠ[𝓝 r] fun t => (X (C y) t).1 :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hr) (fun t ht => c.right_inv (hXt t ht))
    apply Prod.ext
    · exact he.eq_of_nhds
    · have hh : HasDerivAt (fun t => (X (C y) t).1) (X (C y) r).2 r := (hd r hr).fst
      exact he.deriv_eq.trans hh.deriv
  have hinit : phaseLift γ 0 = y := C.injOn
    ((TangentBundle.mem_chart_source_iff _ _).mpr (c.map_target (hXt 0 hz))) hy ((hphase 0 hz).trans h0)
  have he := geodesic_unique g isOpen_Ioo ordConnected_Ioo hγ
    (show IsGeodesicOn g (globalGeodesic g y) (Ioo (-ε) ε) from
      ⟨(globalGeodesic_isGeodesic g y).1.mono (subset_univ _),
       fun c hc t ht hct => (globalGeodesic_isGeodesic g y).2 c hc t (mem_univ t) hct⟩) hz
    (hinit.trans (globalGeodesic_initial g y).symm)
  have het : phaseLift γ t = geodesicFlow g y t := (phaseLift_eventuallyEq
    (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun r hr => he hr))).eq_of_nhds
  rw [← het,← hphase t ht]
  exact (C.left_inv ((TangentBundle.mem_chart_source_iff _ _).mpr (c.map_target (hXt t ht)))).symm

lemma geodesicFlow_contMDiffAt_zero (g : SmoothMetric M) (p : TangentBundle I3 M) :
    ContMDiffAt (I3.tangent.prod 𝓘(ℝ,ℝ)) I3.tangent 1 (Function.uncurry (geodesicFlow g)) (p,0) := by
  let c := chartAt E3 p.1
  let C := chartAt (ModelProd E3 E3) p
  let e := extChartAt I3.tangent p
  have hp : p ∈ C.source := mem_chart_source _ p
  obtain ⟨r,hr,ε,hε,X,h0,hγ,hd,hXt,hXs⟩ := exists_geodesic_local_flow g (z := e p)
    (chart_mem_atlas E3 p.1) (c.map_source (mem_chart_source E3 p.1))
  have hz : (0:ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  have hXp : ContDiffAt ℝ 1 (Function.uncurry X) (e p,0) :=
    hXs.contDiffAt ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨Metric.mem_ball_self hr,hz⟩)
  have he : ContMDiffAt I3.tangent 𝓘(ℝ,E3 × E3) 1 e p := contMDiffAt_extChartAt
  have harg : ContMDiffAt (I3.tangent.prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,(E3 × E3) × ℝ) 1
      (fun q : TangentBundle I3 M × ℝ => (e q.1,q.2)) (p,0) :=
    (he.comp (p,0) contMDiffAt_fst).prodMk_space contMDiffAt_snd
  have hOut : ContMDiffAt 𝓘(ℝ,E3 × E3) I3.tangent 1 e.symm (X (e p) 0) := by
    have hh := contMDiffWithinAt_extChartAt_symm_target (I := I3.tangent) (n := 1) p
      (show X (e p) 0 ∈ e.target from by rw [h0 _ (Metric.mem_ball_self hr)]; exact e.map_source (mem_extChartAt_source p))
    apply hh.contMDiffAt
    rw [h0 _ (Metric.mem_ball_self hr)]
    exact extChartAt_target_mem_nhds p
  apply (hOut.comp (p,0) (hXp.contMDiffAt.comp (p,0) harg)).congr_of_eventuallyEq
  have hn : {y : TangentBundle I3 M | y ∈ C.source ∧ e y ∈ Metric.ball (e p) r} ∈ 𝓝 p :=
    inter_mem (C.open_source.mem_nhds hp)
      (he.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)))
  have ht : Ioo (-ε) ε ∈ 𝓝 (0:ℝ) := isOpen_Ioo.mem_nhds hz
  have hnh := prod_mem_nhds hn ht
  filter_upwards [hnh] with q hq
  exact geodesicFlow_eq_chart g p hε hq.1.1 (h0 _ hq.1.2) (hd _ hq.1.2) (hXt _ hq.1.2) hq.2

theorem geodesicFlow_contMDiff (g : SmoothMetric M) :
    ContMDiff (I3.tangent.prod 𝓘(ℝ,ℝ)) I3.tangent 1 (Function.uncurry (geodesicFlow g)) :=
  FlowContinuation.flow_contMDiff (geodesicFlow g) (geodesicFlow_zero g)
    (geodesicFlow_add g) (geodesicFlow_continuous g) (geodesicFlow_contMDiffAt_zero g)
end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

theorem exists_geodesic_local_variation (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {z : E3 × E3} (hz : z.1 ∈ c.target) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ X : (E3 × E3) → ℝ → E3 × E3,
      (∀ y ∈ Metric.ball z r, X y 0 = y) ∧
      (∀ y ∈ Metric.ball z r, IsGeodesicOn g (fun t => c.symm (X y t).1) (Ioo (-ε) ε)) ∧
      (∀ y ∈ Metric.ball z r, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (X y) (geodesicPhase g c (X y t)) t) ∧
      (∀ y ∈ Metric.ball z r, ∀ t ∈ Ioo (-ε) ε, (X y t).1 ∈ c.target) ∧
      ContDiffOn ℝ 1 (Function.uncurry X) (Metric.ball z r ×ˢ Ioo (-ε) ε) ∧
      ∃ A : (E3 × E3) → ℝ → (E3 × E3) →L[ℝ] E3 × E3,
        (∀ y ∈ Metric.ball z r, A y 0 = ContinuousLinearMap.id ℝ (E3 × E3)) ∧
        (∀ y ∈ Metric.ball z r, ∀ t ∈ Ioo (-ε) ε, HasFDerivAt (fun w => X w t) (A y t) y) ∧
        (∀ y ∈ Metric.ball z r, ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt (A y) ((fderiv ℝ (geodesicPhase g c) (X y t)).comp (A y t)) t) := by
  obtain ⟨r,hr,ε,hε,X,h0,hd,hs,A,hA0,hdf,hAd⟩ :=
    ODEVariation.exists_contDiff_variation_flow (contDiffAt_infty.mp (geodesicPhase_smoothAt g hc hz) 2)
  have hO : IsOpen (Metric.ball z r ×ˢ Ioo (-ε) ε) := Metric.isOpen_ball.prod isOpen_Ioo
  have hp : (z,(0:ℝ)) ∈ Metric.ball z r ×ˢ Ioo (-ε) ε := ⟨Metric.mem_ball_self hr,by constructor <;> linarith⟩
  have hx : ContinuousAt (Function.uncurry X) (z,0) := hs.continuousOn.continuousAt (hO.mem_nhds hp)
  have hmem : {p : (E3 × E3) × ℝ | (X p.1 p.2).1 ∈ c.target} ∈ 𝓝 (z,0) := by
    apply hx.fst.preimage_mem_nhds
    simpa only [Function.uncurry_apply_pair,h0 z (Metric.mem_ball_self hr)] using c.open_target.mem_nhds hz
  obtain ⟨η,hη,hsmall⟩ := Metric.mem_nhds_iff.mp (inter_mem hmem (hO.mem_nhds hp))
  have hsub : ∀ y ∈ Metric.ball z (η/2), ∀ t ∈ Ioo (-(η/2)) (η/2),
      (X y t).1 ∈ c.target ∧ (y,t) ∈ Metric.ball z r ×ˢ Ioo (-ε) ε := by
    intro y hy t ht
    apply hsmall (a := (y,t))
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨lt_trans hy (half_lt_self hη),by rw [Real.dist_eq,sub_zero,abs_lt]; constructor <;> linarith [ht.1,ht.2]⟩
  refine ⟨η/2,half_pos hη,η/2,half_pos hη,X,?_,?_,?_,?_,?_⟩
  · intro y hy
    exact h0 y (hsub y hy 0 ⟨by linarith,by linarith⟩).2.1
  · intro y hy
    exact chart_geodesic g hc isOpen_Ioo (fun t ht => (hsub y hy t ht).1)
      (fun t ht => hd y (hsub y hy t ht).2.1 t (hsub y hy t ht).2.2)
  · intro y hy t ht
    exact hd y (hsub y hy t ht).2.1 t (hsub y hy t ht).2.2
  · exact fun y hy t ht => (hsub y hy t ht).1
  · refine ⟨hs.mono (fun p hp => (hsub p.1 hp.1 p.2 hp.2).2),A,?_,?_,?_⟩
    · intro y hy
      exact hA0 y (hsub y hy 0 ⟨by linarith,by linarith⟩).2.1
    · intro y hy t ht
      exact hdf y (hsub y hy t ht).2.1 t (hsub y hy t ht).2.2
    · intro y hy t ht
      exact hAd y (hsub y hy t ht).2.1 t (hsub y hy t ht).2.2

lemma geodesicPhase_fderiv_apply (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {z : E3 × E3} (hz : z.1 ∈ c.target) (w : E3 × E3) :
    fderiv ℝ (geodesicPhase g c) z w =
      (w.2,-(fderiv ℝ (connectionBilin g c) z.1 w.1 z.2 z.2 +
        connectionBilin g c z.1 w.2 z.2 + connectionBilin g c z.1 z.2 w.2)) := by
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  have hC := ((connectionBilin_smoothAt g hc hz).differentiableAt (by simp)).hasFDerivAt.comp z
    (hasFDerivAt_fst (p := z))
  have hh := (hasFDerivAt_snd (p := z)).prodMk
    (((hC.clm_apply (hasFDerivAt_snd (p := z))).clm_apply (hasFDerivAt_snd (p := z))).neg)
  have he : geodesicPhase g c = (fun q : E3 × E3 =>
      (q.2,-connectionBilin g c q.1 q.2 q.2)) := by
    funext q
    simp only [geodesicPhase,connectionBilin_apply]
  change HasFDerivAt (fun q : E3 × E3 => (q.2,-connectionBilin g c q.1 q.2 q.2)) _ z at hh
  rw [he,hh.fderiv]
  simp only [ContinuousLinearMap.prod_apply,
    _root_.neg_apply,_root_.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,Function.comp_apply]
  congr 1
  change -(connectionBilin g c z.1 z.2 w.2 + (connectionBilin g c z.1 w.2 z.2 +
    fderiv ℝ (connectionBilin g c) z.1 w.1 z.2 z.2)) = _
  abel

lemma geodesicPhase_variation_smooth (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {U : Set ℝ} (hU : IsOpen U) {z w : ℝ → E3 × E3}
    (hz : ∀ t ∈ U, (z t).1 ∈ c.target)
    (hdz : ∀ t ∈ U, HasDerivAt z (geodesicPhase g c (z t)) t)
    (hdw : ∀ t ∈ U, HasDerivAt w (fderiv ℝ (geodesicPhase g c) (z t) (w t)) t) :
    ContDiffOn ℝ ∞ (fun t => (z t,w t)) U := by
  apply ODEVariation.solution_smooth (f := fun q : (E3 × E3) × (E3 × E3) =>
      (geodesicPhase g c q.1,fderiv ℝ (geodesicPhase g c) q.1 q.2))
    (S := {q | q.1.1 ∈ c.target}) _ hU (fun t ht => hz t ht)
    (fun t ht => (hdz t ht).prodMk (hdw t ht))
  intro q hq
  have hf := geodesicPhase_smoothAt g hc hq
  exact ((hf.comp q contDiffAt_fst).prodMk
    ((hf.fderiv_right (m := ∞) (by simp)).comp q contDiffAt_fst |>.clm_apply contDiffAt_snd)).contDiffWithinAt

lemma linearized_geodesic_jacobi (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {U : Set ℝ} (hU : IsOpen U) {z w : ℝ → E3 × E3}
    (hz : ∀ t ∈ U, (z t).1 ∈ c.target)
    (hdz : ∀ t ∈ U, HasDerivAt z (geodesicPhase g c (z t)) t)
    (hdw : ∀ t ∈ U, HasDerivAt w (fderiv ℝ (geodesicPhase g c) (z t) (w t)) t)
    {s : ℝ} (hs : s ∈ U) :
    alongDerivative g c (fun t => (z t).1)
        (alongDerivative g c (fun t => (z t).1) (fun t => (w t).1)) s +
      curvatureTerm g c (z s).1 (w s).1 (z s).2 (z s).2 = 0 := by
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  let C := connectionBilin g c
  have hdw' (t : ℝ) (ht : t ∈ U) := (hdw t ht).congr_deriv
    (geodesicPhase_fderiv_apply g hc (hz t ht) (w t))
  have hx (t : ℝ) (ht : t ∈ U) : HasDerivAt (fun r => (z r).1) (z t).2 t := (hdz t ht).fst
  have hv (t : ℝ) (ht : t ∈ U) : HasDerivAt (fun r => (z r).2) (-C (z t).1 (z t).2 (z t).2) t := by
    have hh : HasDerivAt (fun r => (z r).2) (geodesicPhase g c (z t)).2 t := (hdz t ht).snd
    simpa only [C,connectionBilin_apply,geodesicPhase] using hh
  have hj (t : ℝ) (ht : t ∈ U) : HasDerivAt (fun r => (w r).1) (w t).2 t := (hdw' t ht).fst
  have hk (t : ℝ) (ht : t ∈ U) : HasDerivAt (fun r => (w r).2)
      (-(fderiv ℝ C (z t).1 (w t).1 (z t).2 (z t).2 + C (z t).1 (w t).2 (z t).2 + C (z t).1 (z t).2 (w t).2)) t := (hdw' t ht).snd
  let F : ℝ → E3 := fun t => (w t).2 + C (z t).1 (z t).2 (w t).1
  have he : alongDerivative g c (fun t => (z t).1) (fun t => (w t).1) =ᶠ[𝓝 s] F := by
    filter_upwards [hU.mem_nhds hs] with t ht
    rw [alongDerivative,(hx t ht).deriv,(hj t ht).deriv]
    exact (connectionBilin_apply g c (z t).1 (z t).2 (w t).1).symm ▸ rfl
  have hC := ((connectionBilin_smoothAt g hc (hz s hs)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s (hx s hs)
  have hF := (hk s hs).add ((hC.clm_apply (hv s hs)).clm_apply (hj s hs))
  change HasDerivAt F _ s at hF
  rw [along_congr g c Filter.EventuallyEq.rfl he,alongDerivative,(hx s hs).deriv,hF.deriv,
    curvature_connection g hc (hz s hs)]
  rw [← connectionBilin_apply]
  change -(fderiv ℝ C (z s).1 (w s).1 (z s).2 (z s).2 + C (z s).1 (w s).2 (z s).2 + C (z s).1 (z s).2 (w s).2) +
    ((fderiv ℝ C (z s).1 (z s).2 (z s).2 + C (z s).1 (-C (z s).1 (z s).2 (z s).2)) (w s).1 +
      C (z s).1 (z s).2 (w s).2) +
    C (z s).1 (z s).2 ((w s).2 + C (z s).1 (z s).2 (w s).1) +
    (fderiv ℝ C (z s).1 (w s).1 (z s).2 (z s).2 - fderiv ℝ C (z s).1 (z s).2 (w s).1 (z s).2 +
      C (z s).1 (w s).1 (C (z s).1 (z s).2 (z s).2) - C (z s).1 (z s).2 (C (z s).1 (w s).1 (z s).2)) = 0
  simp only [_root_.add_apply,map_neg,_root_.neg_apply,map_add]
  rw [connectionBilin_deriv_symm g hc (hz s hs) (z s).2 (z s).2 (w s).1,
    connectionBilin_symm g c (z s).1 (w s).2 (z s).2,
    connectionBilin_symm g c (z s).1 (C (z s).1 (z s).2 (z s).2) (w s).1,
    connectionBilin_symm g c (z s).1 (w s).1 (z s).2]
  abel
end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma geodesic_family_contMDiffAt (g : SmoothMetric M) {f : E → TangentBundle I3 M}
    {a : E} (hf : ContMDiffAt 𝓘(ℝ,E) I3.tangent 1 f a) (s : ℝ) :
    ContMDiffAt 𝓘(ℝ,E) I3.tangent 1 (fun y => geodesicFlow g (f y) s) a := by
  exact (geodesicFlow_contMDiff g).contMDiffAt.comp a (hf.prodMk contMDiffAt_const)

theorem geodesic_variation_representation (g : SmoothMetric M)
    {f : E → TangentBundle I3 M} {a : E}
    (hf : ContMDiffAt 𝓘(ℝ,E) I3.tangent 1 f a) (s : ℝ) :
    let p := geodesicFlow g (f a) s
    let e := extChartAt I3.tangent p
    let Z := fun y => e (geodesicFlow g (f y) s)
    ∃ ε > (0 : ℝ), ∃ X : (E3 × E3) → ℝ → E3 × E3,
      ∃ A : (E3 × E3) → ℝ → (E3 × E3) →L[ℝ] E3 × E3,
      (∀ t ∈ Ioo (-ε) ε, e (geodesicFlow g (f a) (s+t)) = X (Z a) t) ∧
      (∀ t ∈ Ioo (-ε) ε, HasDerivAt (X (Z a))
        (geodesicPhase g (chartAt E3 p.1) (X (Z a) t)) t) ∧
      (∀ t ∈ Ioo (-ε) ε, (X (Z a) t).1 ∈ (chartAt E3 p.1).target) ∧
      (∀ t ∈ Ioo (-ε) ε, HasFDerivAt
        (fun y => e (geodesicFlow g (f y) (s+t))) ((A (Z a) t).comp (fderiv ℝ Z a)) a) ∧
      (∀ t ∈ Ioo (-ε) ε, HasDerivAt (A (Z a))
        ((fderiv ℝ (geodesicPhase g (chartAt E3 p.1)) (X (Z a) t)).comp (A (Z a) t)) t) := by
  intro p e Z
  let c := chartAt E3 p.1
  let C := chartAt (ModelProd E3 E3) p
  have hp : p ∈ C.source := mem_chart_source _ p
  have hz : (e p).1 ∈ c.target := c.map_source (mem_chart_source E3 p.1)
  obtain ⟨r,hr,ε,hε,X,h0,hγ,hd,hXt,hXs,A,hA0,hdf,hAd⟩ :=
    exists_geodesic_local_variation g (chart_mem_atlas E3 p.1) hz
  have ha : Z a ∈ Metric.ball (e p) r := Metric.mem_ball_self hr
  have hFa := geodesic_family_contMDiffAt g hf s
  have he : ContMDiffAt I3.tangent 𝓘(ℝ,E3 × E3) 1 e p := contMDiffAt_extChartAt
  have hZ : ContDiffAt ℝ 1 Z a := contMDiffAt_iff_contDiffAt.mp (he.comp a hFa)
  have hZn : {y : E | geodesicFlow g (f y) s ∈ C.source ∧ Z y ∈ Metric.ball (e p) r} ∈ 𝓝 a :=
    inter_mem (hFa.continuousAt.preimage_mem_nhds (C.open_source.mem_nhds hp))
      (hZ.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds ha))
  have hrep (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      (fun y => e (geodesicFlow g (f y) (s+t))) =ᶠ[𝓝 a] fun y => X (Z y) t := by
    filter_upwards [hZn] with y hy
    rw [← geodesicFlow_add g (f y) s t,geodesicFlow_eq_chart g p hε hy.1
      (h0 _ hy.2) (hd _ hy.2) (hXt _ hy.2) ht]
    apply e.right_inv
    change X (Z y) t ∈ (extChartAt I3.tangent p).target
    rw [extChartAt_target]
    exact ⟨(TangentBundle.mem_chart_target_iff _ _).mpr (hXt _ hy.2 t ht),by simp⟩
  refine ⟨ε,hε,X,A,fun t ht => (hrep t ht).eq_of_nhds,hd _ ha,hXt _ ha,?_,hAd _ ha⟩
  intro t ht
  exact ((hdf _ ha t ht).comp a (hZ.differentiableAt (by simp)).hasFDerivAt).congr_of_eventuallyEq
    (hrep t ht)

theorem geodesic_family_linearization (g : SmoothMetric M)
    {f : E → TangentBundle I3 M} {a : E}
    (hf : ContMDiffAt 𝓘(ℝ,E) I3.tangent 1 f a) (s : ℝ) (b : E) :
    let p := geodesicFlow g (f a) s
    let e := extChartAt I3.tangent p
    let z := fun t => e (geodesicFlow g (f a) (s+t))
    let w := fun t => fderiv ℝ (fun y => e (geodesicFlow g (f y) (s+t))) a b
    ∃ ε > (0 : ℝ),
      (∀ t ∈ Ioo (-ε) ε, (z t).1 ∈ (chartAt E3 p.1).target) ∧
      (∀ t ∈ Ioo (-ε) ε, HasDerivAt z (geodesicPhase g (chartAt E3 p.1) (z t)) t) ∧
      (∀ t ∈ Ioo (-ε) ε, HasDerivAt w (fderiv ℝ (geodesicPhase g (chartAt E3 p.1)) (z t) (w t)) t) := by
  intro p e z w
  obtain ⟨ε,hε,X,A,hX,hd,hXt,hdf,hAd⟩ := geodesic_variation_representation g hf s
  let Z := fun y => e (geodesicFlow g (f y) s)
  have hew : ∀ t ∈ Ioo (-ε) ε, w t = A (Z a) t (fderiv ℝ Z a b) := by
    intro t ht
    exact congrArg (fun L => L b) (hdf t ht).fderiv
  have hen (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : z =ᶠ[𝓝 t] X (Z a) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun r hr => hX r hr)
  have hwen (t : ℝ) (ht : t ∈ Ioo (-ε) ε) : w =ᶠ[𝓝 t] fun r => A (Z a) r (fderiv ℝ Z a b) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun r hr => hew r hr)
  refine ⟨ε,hε,?_,?_,?_⟩
  · intro t ht
    rw [show z t = X (Z a) t from hX t ht]
    exact hXt t ht
  · intro t ht
    rw [(hen t ht).eq_of_nhds]
    exact (hd t ht).congr_of_eventuallyEq (hen t ht)
  · intro t ht
    rw [(hen t ht).eq_of_nhds,(hwen t ht).eq_of_nhds]
    have hh := ((hAd t ht).clm_apply (hasDerivAt_const t (fderiv ℝ Z a b))).congr_of_eventuallyEq (hwen t ht)
    simpa only [map_zero,add_zero,ContinuousLinearMap.comp_apply] using hh

lemma geodesic_family_linearization_at (g : SmoothMetric M)
    {f : E → TangentBundle I3 M} {a : E}
    (hf : ContMDiffAt 𝓘(ℝ,E) I3.tangent 1 f a) (s : ℝ) (b : E) :
    let p := geodesicFlow g (f a) s
    let e := extChartAt I3.tangent p
    let z := fun t => e (geodesicFlow g (f a) t)
    let w := fun t => fderiv ℝ (fun y => e (geodesicFlow g (f y) t)) a b
    ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧
      (∀ t ∈ U, (z t).1 ∈ (chartAt E3 p.1).target) ∧
      (∀ t ∈ U, HasDerivAt z (geodesicPhase g (chartAt E3 p.1) (z t)) t) ∧
      (∀ t ∈ U, HasDerivAt w (fderiv ℝ (geodesicPhase g (chartAt E3 p.1)) (z t) (w t)) t) := by
  intro p e z w
  obtain ⟨ε,hε,hz,hdz,hdw⟩ := geodesic_family_linearization g hf s b
  have hh (t : ℝ) (ht : t ∈ Ioo (s-ε) (s+ε)) : t-s ∈ Ioo (-ε) ε := by
    constructor <;> linarith [ht.1,ht.2]
  refine ⟨Ioo (s-ε) (s+ε),isOpen_Ioo,by constructor <;> linarith,?_,?_,?_⟩
  · intro t ht
    simpa only [add_sub_cancel] using hz (t-s) (hh t ht)
  · intro t ht
    have hd := (hdz (t-s) (hh t ht)).scomp t ((hasDerivAt_id t).sub_const s)
    simpa only [Function.comp_def,add_sub_cancel,mul_one,one_smul,id_eq,z,w,p,e] using hd
  · intro t ht
    have hd := (hdw (t-s) (hh t ht)).scomp t ((hasDerivAt_id t).sub_const s)
    simpa only [Function.comp_def,add_sub_cancel,mul_one,one_smul,id_eq,z,w,p,e] using hd
end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma smoothField_of_local_coordinates {γ : ℝ → M} {J : ∀ s, TangentSpace I3 (γ s)}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (h : ∀ s ∈ U, ∃ c : OpenPartialHomeomorph M E3, c ∈ atlas E3 M ∧ γ s ∈ c.source ∧
      ContDiffAt ℝ ∞ (fieldCoordinates γ J c) s) : SmoothFieldOn γ J U := by
  intro d hd s hs
  obtain ⟨c,hc,hsc,hF⟩ := h s hs.1
  have hγs := hγ.contMDiffAt (hU.mem_nhds hs.1)
  have fsm := transition_smoothAt hc hd (c.map_source hsc)
    (show c.symm (c (γ s)) ∈ d.source by rw [c.left_inv hsc]; exact hs.2)
  have hx := curve_coordinates_smoothAt hU hγ hc hs.1 hsc
  have he : fieldCoordinates γ J d =ᶠ[𝓝 s] fun r =>
      fderiv ℝ (d ∘ c.symm) (c (γ r)) (fieldCoordinates γ J c r) := by
    filter_upwards [hγs.continuousAt.preimage_mem_nhds
      ((c.open_source.inter d.open_source).mem_nhds ⟨hsc,hs.2⟩)] with r hr
    exact (field_coordinates_change hc hd hr.1 hr.2).symm
  exact (((fsm.fderiv_right (m := ∞) (by simp)).comp s hx).clm_apply hF).congr_of_eventuallyEq he |>.contDiffWithinAt

lemma jacobi_of_local_coordinates (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (h : ∀ s ∈ U, ∃ c : OpenPartialHomeomorph M E3, c ∈ atlas E3 M ∧ γ s ∈ c.source ∧
      ContDiffAt ℝ ∞ (fieldCoordinates γ J c) s ∧
      alongDerivative g c (c ∘ γ) (alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c)) s +
        curvatureTerm g c (c (γ s)) (fieldCoordinates γ J c s) (deriv (c ∘ γ) s) (deriv (c ∘ γ) s) = 0) :
    IsJacobiFieldOn g γ J U := by
  have hJ : SmoothFieldOn γ J U := smoothField_of_local_coordinates hU hγ
    (fun s hs => by obtain ⟨c,hc,hsc,hcs,_⟩ := h s hs; exact ⟨c,hc,hsc,hcs⟩)
  have hi (s : ℝ) (hs : s ∈ U) :
      covariantDerivative g γ (covariantDerivative g γ J) s + curvatureAlong g γ J s = 0 := by
    obtain ⟨c,hc,hsc,_,he⟩ := h s hs
    apply (mdifferentiable_of_mem_atlas (I := I3) hc).mfderiv_injective hsc
    rw [map_add,map_zero]
    change fieldCoordinates γ (covariantDerivative g γ (covariantDerivative g γ J)) c s +
      fieldCoordinates γ (curvatureAlong g γ J) c s = 0
    rw [covariantDerivative_iterate_coordinates g hU hγ hJ hs hc hsc,
      curvatureAlong_coordinates g J (hγ.contMDiffAt (hU.mem_nhds hs)) hc hsc]
    exact he
  intro c hc
  refine ⟨hJ c hc,?_⟩
  intro s hs hsc
  rw [← covariantDerivative_iterate_coordinates g hU hγ hJ hs hc hsc,
    ← curvatureAlong_coordinates g J (hγ.contMDiffAt (hU.mem_nhds hs)) hc hsc]
  change mfderiv I3 I3 c (γ s) (covariantDerivative g γ (covariantDerivative g γ J) s) +
    mfderiv I3 I3 c (γ s) (curvatureAlong g γ J s) = 0
  rw [← map_add,hi s hs,map_zero]
end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def geodesicFamily (g : SmoothMetric M) (f : E → TangentBundle I3 M) (a : E) (t : ℝ) : M :=
  (geodesicFlow g (f a) t).proj

def geodesicVariation (g : SmoothMetric M) (f : E → TangentBundle I3 M) (a b : E)
    (t : ℝ) : TangentSpace I3 (geodesicFamily g f a t) :=
  mfderiv 𝓘(ℝ,E) I3 (fun y => geodesicFamily g f y t) a b

lemma geodesicFamily_isGeodesic (g : SmoothMetric M) (f : E → TangentBundle I3 M) (a : E) :
    IsGeodesicOn g (geodesicFamily g f a) univ := by
  let _ : NormedAddCommGroup E := inferInstance
  let _ : NormedSpace ℝ E := inferInstance
  exact globalGeodesic_isGeodesic g (f a)

lemma geodesicFamily_parameter_smooth (g : SmoothMetric M) {f : E → TangentBundle I3 M}
    {a : E} (hf : ContMDiffAt 𝓘(ℝ,E) I3.tangent 1 f a) (t : ℝ) :
    ContMDiffAt 𝓘(ℝ,E) I3 1 (fun y => geodesicFamily g f y t) a :=
  (contMDiff_proj (IB := I3) (F := E3) (E := TangentSpace I3)).contMDiffAt.comp a
    (geodesic_family_contMDiffAt g hf t)

lemma geodesicVariation_coordinates (g : SmoothMetric M) {f : E → TangentBundle I3 M}
    {a : E} (hf : ContMDiffAt 𝓘(ℝ,E) I3.tangent 1 f a) (b : E) (t : ℝ)
    {p : TangentBundle I3 M} (hp : geodesicFamily g f a t ∈ (chartAt E3 p.1).source) :
    fieldCoordinates (geodesicFamily g f a) (geodesicVariation g f a b) (chartAt E3 p.1) t =
      (fderiv ℝ (fun y => extChartAt I3.tangent p (geodesicFlow g (f y) t)) a b).1 := by
  let c := chartAt E3 p.1
  let e := extChartAt I3.tangent p
  have ha := geodesic_family_contMDiffAt g hf t
  have hb := geodesicFamily_parameter_smooth g hf t
  have he : ContMDiffAt I3.tangent 𝓘(ℝ,E3 × E3) 1 e (geodesicFlow g (f a) t) :=
    contMDiffAt_extChartAt' ((TangentBundle.mem_chart_source_iff _ _).mpr hp)
  have hs : ContDiffAt ℝ 1 (fun y => e (geodesicFlow g (f y) t)) a :=
    contMDiffAt_iff_contDiffAt.mp (he.comp a ha)
  have hd : HasFDerivAt (fun y => (e (geodesicFlow g (f y) t)).1)
      ((ContinuousLinearMap.fst ℝ E3 E3).comp (fderiv ℝ (fun y => e (geodesicFlow g (f y) t)) a)) a :=
    (hs.differentiableAt (by simp)).hasFDerivAt.fst
  have hm := mfderiv_comp a ((mdifferentiable_of_mem_atlas (I := I3) (chart_mem_atlas E3 p.1)).mdifferentiableAt hp)
    (hb.mdifferentiableAt (by simp))
  have hv := congrArg (fun L => L b) hm
  rw [mfderiv_eq_fderiv] at hv
  change fderiv ℝ (fun y => c (geodesicFamily g f y t)) a b =
    fieldCoordinates (geodesicFamily g f a) (geodesicVariation g f a b) c t at hv
  rw [← hv]
  change fderiv ℝ (fun y => (e (geodesicFlow g (f y) t)).1) a b = _
  rw [hd.fderiv]
  rfl

theorem geodesicVariation_isJacobi (g : SmoothMetric M) {f : E → TangentBundle I3 M}
    {a : E} (hf : ContMDiffAt 𝓘(ℝ,E) I3.tangent 1 f a) (b : E) :
    IsJacobiFieldOn g (geodesicFamily g f a) (geodesicVariation g f a b) univ := by
  let γ := geodesicFamily g f a
  let J := geodesicVariation g f a b
  have hγ := geodesicFamily_isGeodesic g f a
  apply jacobi_of_local_coordinates g isOpen_univ hγ.1
  intro s _
  let p := geodesicFlow g (f a) s
  let c := chartAt E3 p.1
  let e := extChartAt I3.tangent p
  let z := fun t => e (geodesicFlow g (f a) t)
  let w := fun t => fderiv ℝ (fun y => e (geodesicFlow g (f y) t)) a b
  have hc : c ∈ atlas E3 M := chart_mem_atlas E3 p.1
  have hsc : γ s ∈ c.source := mem_chart_source E3 p.1
  obtain ⟨U,hU,hs,hz,hdz,hdw⟩ := geodesic_family_linearization_at g hf s b
  have hsmooth : ContDiffOn ℝ ∞ (fun t => (z t,w t)) U :=
    geodesicPhase_variation_smooth g hc hU hz hdz hdw
  have he : fieldCoordinates γ J c =ᶠ[𝓝 s] fun t => (w t).1 := by
    filter_upwards [(hγ.1.contMDiffAt (by simp)).continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds hsc)] with t ht
    exact geodesicVariation_coordinates g hf b t ht
  have hw : ContDiffAt ℝ ∞ (fun t => (w t).1) s := (hsmooth.contDiffAt (hU.mem_nhds hs)).snd.fst
  refine ⟨c,hc,hsc,hw.congr_of_eventuallyEq he,?_⟩
  have hde : alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c) =ᶠ[𝓝 s]
      alongDerivative g c (fun t => (z t).1) (fun t => (w t).1) := by
    filter_upwards [he.eventuallyEq_nhds] with t ht
    exact along_congr g c Filter.EventuallyEq.rfl ht
  rw [along_congr g c Filter.EventuallyEq.rfl hde,he.eq_of_nhds]
  have hx : deriv (c ∘ γ) s = (z s).2 := by
    exact (show HasDerivAt (fun t => (z t).1) (z s).2 s from (hdz s hs).fst).deriv
  rw [hx]
  exact linearized_geodesic_jacobi g hc hU hz hdz hdw hs
end ThreeManifold.RiemannianCoordinates
end

section

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma curvatureAlong_pairing_nonpos (g : SmoothMetric M) {γ : ℝ → M}
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) (hn : NonpositiveAt g (γ s)) :
    g.inner (γ s) (curvatureAlong g γ J s) (J s) ≤ 0 := by
  have hc := chart_mem_atlas E3 (γ s)
  have hsc := mem_chart_source E3 (γ s)
  rw [← metric_field_coordinates g (curvatureAlong g γ J) J hc hsc,
    curvatureAlong_coordinates g J hγ hc hsc]
  exact hn _ hc hsc _ _

lemma npc_noConjugatePoints (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) :
    NoConjugatePoints g := by
  apply noConjugatePoints_of_intrinsic_index g
  intro U hU hUc γ hγ J hJ hJc hJU
  apply integral_nonneg
  intro s
  by_cases hs : s ∈ U
  · exact indexPairDensity_nonneg_of_nonpositiveAt g J
      (hγ.1.contMDiffAt (hU.mem_nhds hs)) (nonpositiveAt_of_nonpositive g hn _)
  · have hz := notMem_subset hJU hs
    have hz' : indexPairDensity g γ J J s = 0 :=
      Function.notMem_support.mp (notMem_subset (indexPairDensity_support g γ J J) hz)
    exact hz'.ge

def jacobiNormSq (g : SmoothMetric M) (γ : ℝ → M)
    (J : ∀ s, TangentSpace I3 (γ s)) (s : ℝ) : ℝ := g.inner (γ s) (J s) (J s)
def jacobiNormSqSlope (g : SmoothMetric M) (γ : ℝ → M)
    (J : ∀ s, TangentSpace I3 (γ s)) (s : ℝ) : ℝ :=
  2 * g.inner (γ s) (covariantDerivative g γ J s) (J s)

lemma jacobiNormSq_hasDerivAt (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U)
    {s : ℝ} (hs : s ∈ U) :
    HasDerivAt (jacobiNormSq g γ J) (jacobiNormSqSlope g γ J s) s := by
  change HasDerivAt (fun r => g.inner (γ r) (J r) (J r))
    (2 * g.inner (γ s) (covariantDerivative g γ J s) (J s)) s
  have hd := intrinsic_pairing_hasDerivAt g hU hγ hJ hJ hs
  rw [g.symm (γ s) (J s) (covariantDerivative g γ J s)] at hd
  rw [two_mul]
  exact hd

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]

def fiberPhase (x : M) (v : E3) : TangentBundle I3 M := ⟨x,v⟩

lemma fiberPhase_contMDiff (x : M) : ContMDiff 𝓘(ℝ,E3) I3.tangent ∞ (fiberPhase x) := by
  let _ : CompactSpace M := inferInstance
  let _ : T2Space M := inferInstance
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_const,?_⟩
  let e := trivializationAt E3 (TangentSpace I3) x
  have hmem : x ∈ e.baseSet := mem_baseSet_trivializationAt E3 (TangentSpace I3) x
  have he : (fun w : E3 => (e (fiberPhase x w)).2) = e.continuousLinearMapAt ℝ x := by
    funext w
    exact (e.continuousLinearMapAt_apply_of_mem ℝ hmem w).symm
  change ContMDiffAt 𝓘(ℝ,E3) 𝓘(ℝ,E3) ∞ (fun w => (e (fiberPhase x w)).2) v
  rw [he]
  exact (show E3 →L[ℝ] E3 from e.continuousLinearMapAt ℝ x).contDiff.contMDiff.contMDiffAt

lemma fiberPhase_extChart (x : M) (v w : E3) :
    extChartAt I3.tangent (fiberPhase x v) (fiberPhase x w) =
      (chartAt E3 x x,mfderiv I3 I3 (chartAt E3 x) x w) := by
  let _ : CompactSpace M := inferInstance
  let _ : T2Space M := inferInstance
  apply Prod.ext
  · rfl
  · exact (congrArg (fun q : TangentBundle I3 E3 => q.2)
      (tangentMap_chart (I := I3) (p := fiberPhase x v) (q := fiberPhase x w) (mem_chart_source E3 x))).symm

def exponential (g : SmoothMetric M) (x : M) (v : E3) : M :=
  geodesicFamily g (fiberPhase x) v 1

lemma exponential_contMDiff (g : SmoothMetric M) (x : M) :
    ContMDiff 𝓘(ℝ,E3) I3 1 (exponential g x) := by
  intro v
  exact geodesicFamily_parameter_smooth g ((fiberPhase_contMDiff x).of_le (by simp)).contMDiffAt 1

lemma exponentialFamily_zero (g : SmoothMetric M) (x : M) (v : E3) :
    geodesicFamily g (fiberPhase x) v 0 = x := by
  change (geodesicFlow g (fiberPhase x v) 0).proj = x
  rw [geodesicFlow_zero]
  rfl

lemma exponentialVariation_zero (g : SmoothMetric M) (x : M) (v w : E3) :
    geodesicVariation g (fiberPhase x) v w 0 = 0 := by
  unfold geodesicVariation
  have he : (fun y : E3 => geodesicFamily g (fiberPhase x) y 0) = fun _ => x := by
    funext y; exact exponentialFamily_zero g x y
  rw [he,mfderiv_const]
  rfl

lemma fiberPhase_extChart_fderiv (x : M) (v b : E3) :
    fderiv ℝ (fun w => extChartAt I3.tangent (fiberPhase x v) (fiberPhase x w)) v b =
      (0,mfderiv I3 I3 (chartAt E3 x) x b) := by
  let L : E3 →L[ℝ] E3 := mfderiv I3 I3 (chartAt E3 x) x
  have hd : HasFDerivAt (fun w => (chartAt E3 x x,L w))
      ((0 : E3 →L[ℝ] E3).prod L) v := (hasFDerivAt_const (chartAt E3 x x) v).prodMk L.hasFDerivAt
  have he : (fun w => extChartAt I3.tangent (fiberPhase x v) (fiberPhase x w)) =
      fun w => (chartAt E3 x x,L w) := funext (fiberPhase_extChart x v)
  rw [he,hd.fderiv]
  rfl

theorem exponential_mfderiv_injective (g : SmoothMetric M) (hn : NoConjugatePoints g)
    (x : M) (v : E3) : Function.Injective (mfderiv 𝓘(ℝ,E3) I3 (exponential g x) v) := by
  suffices h : ∀ b : E3, mfderiv 𝓘(ℝ,E3) I3 (exponential g x) v b = 0 → b = 0 by
    intro a b hab
    have hz : mfderiv 𝓘(ℝ,E3) I3 (exponential g x) v (a-b) = 0 := by
      rw [map_sub,hab,sub_self]
    exact sub_eq_zero.mp (h (a-b) hz)
  intro b hb
  let f := fiberPhase x
  let γ := geodesicFamily g f v
  let J := geodesicVariation g f v b
  have hf : ContMDiffAt 𝓘(ℝ,E3) I3.tangent 1 f v :=
    ((fiberPhase_contMDiff x).of_le (by simp)).contMDiffAt
  have hγ := geodesicFamily_isGeodesic g f v
  have hJ := geodesicVariation_isJacobi g hf b
  have hz : ∀ t : ℝ, J t = 0 := fun t => hn univ isOpen_univ ordConnected_univ γ hγ J hJ
    0 (mem_univ 0) 1 (mem_univ 1) (by norm_num) (exponentialVariation_zero g x v b) hb t (mem_univ t)
  let c := chartAt E3 x
  let e := extChartAt I3.tangent (fiberPhase x v)
  let z := fun t => e (geodesicFlow g (f v) t)
  let w := fun t => fderiv ℝ (fun y => e (geodesicFlow g (f y) t)) v b
  have hlin := geodesic_family_linearization_at g hf 0 b
  simp only [geodesicFlow_zero] at hlin
  obtain ⟨U,hU,h0,hzt,hdz,hdw⟩ := hlin
  have he : (fun t => (w t).1) =ᶠ[𝓝 (0:ℝ)] fun _ => (0:E3) := by
    have hbase : γ 0 = x := exponentialFamily_zero g x v
    have hsource : γ 0 ∈ c.source := hbase ▸ mem_chart_source E3 x
    filter_upwards [(hγ.1.contMDiffAt (by simp)).continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds hsource)] with t ht
    have hc := geodesicVariation_coordinates g hf b t (p := fiberPhase x v) ht
    rw [← hc]
    change mfderiv I3 I3 c (γ t) (J t) = 0
    rw [hz t,map_zero]
  have hd : HasDerivAt (fun t => (w t).1) (w 0).2 0 := by
    have hd' := (hdw 0 h0).congr_deriv
      (geodesicPhase_fderiv_apply g (chart_mem_atlas E3 x) (hzt 0 h0) (w 0))
    exact hd'.fst
  have hw0 : (w 0).2 = 0 := by
    have hh := hd.congr_of_eventuallyEq he.symm
    exact hh.unique (hasDerivAt_const 0 (0:E3))
  have hi : w 0 = (0,mfderiv I3 I3 c x b) := by
    dsimp only [w]
    simp only [geodesicFlow_zero]
    exact fiberPhase_extChart_fderiv x v b
  rw [hi] at hw0
  exact (mdifferentiable_of_mem_atlas (I := I3) (chart_mem_atlas E3 x)).mfderiv_injective
    (mem_chart_source E3 x) (hw0.trans (map_zero _).symm)
end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma isLocalHomeomorph_of_mfderiv_injective {f : E3 → M}
    (hf : ContMDiff 𝓘(ℝ,E3) I3 1 f)
    (hi : ∀ a, Function.Injective (mfderiv 𝓘(ℝ,E3) I3 f a)) :
    IsLocalHomeomorph f := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro a
  let c := chartAt E3 (f a)
  let F : E3 → E3 := c ∘ f
  have hc : c ∈ atlas E3 M := chart_mem_atlas E3 (f a)
  have hca : f a ∈ c.source := mem_chart_source E3 (f a)
  have hC : ContMDiffAt I3 I3 1 c (f a) := contMDiffAt_extChartAt' hca
  have hF : ContDiffAt ℝ 1 F a := contMDiffAt_iff_contDiffAt.mp (hC.comp a hf.contMDiffAt)
  have hd : fderiv ℝ F a = (mfderiv I3 I3 c (f a)).comp (mfderiv 𝓘(ℝ,E3) I3 f a) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp a (hC.mdifferentiableAt (by simp)) (hf.mdifferentiable (by simp) a)
  have hdi : Function.Injective (fderiv ℝ F a) := by
    rw [hd]
    exact ((mdifferentiable_of_mem_atlas (I := I3) hc).mfderiv_injective hca).comp (hi a)
  let L : E3 ≃L[ℝ] E3 := (LinearEquiv.ofInjectiveEndo (fderiv ℝ F a).toLinearMap hdi).toContinuousLinearEquiv
  have hL : (L : E3 →L[ℝ] E3) = fderiv ℝ F a := rfl
  have hFd : HasFDerivAt F (L : E3 →L[ℝ] E3) a := by
    rw [hL]
    exact (hF.differentiableAt (by simp)).hasFDerivAt
  let e := hF.toOpenPartialHomeomorph F hFd (by simp)
  have hea : a ∈ e.source := hF.mem_toOpenPartialHomeomorph_source hFd (by simp)
  let U := e.source ∩ f ⁻¹' c.source
  have hU : IsOpen U := e.open_source.inter (c.open_source.preimage hf.continuous)
  have ha : a ∈ U := ⟨hea,hca⟩
  let d := (e.trans c.symm).restr U
  have heq : d.source = U := by
    simp only [d,OpenPartialHomeomorph.restr_source,OpenPartialHomeomorph.trans_source,
      hU.interior_eq]
    ext y
    constructor
    · exact fun h => h.2
    · intro hy
      exact ⟨⟨hy.1,c.map_source hy.2⟩,hy⟩
  have hequ : U.domRestrict f = d.source.domRestrict d ∘ (Homeomorph.setCongr heq.symm) := by
    funext y
    change f y.1 = c.symm (c (f y.1))
    exact (c.left_inv y.2.2).symm
  refine ⟨U,hU.mem_nhds ha,?_⟩
  rw [hequ]
  exact d.isOpenEmbedding_restrict.comp (Homeomorph.setCongr heq.symm).isOpenEmbedding

variable [CompactSpace M] [T2Space M]

theorem exponential_isLocalHomeomorph (g : SmoothMetric M)
    (hn : NoConjugatePoints g) (x : M) : IsLocalHomeomorph (exponential g x) :=
  isLocalHomeomorph_of_mfderiv_injective (exponential_contMDiff g x)
    (exponential_mfderiv_injective g hn x)

theorem npc_exponential_isLocalHomeomorph (g : SmoothMetric M)
    (hn : NonpositiveSectionalCurvature g) (x : M) : IsLocalHomeomorph (exponential g x) :=
  exponential_isLocalHomeomorph g (npc_noConjugatePoints g hn) x
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold MeasureTheory
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma metric_cauchy_schwarz (g : SmoothMetric M) (p : M)
    (v w : TangentSpace I3 p) : g.inner p v w ^ 2 ≤ g.inner p v v * g.inner p w w := by
  have h (t : ℝ) := inner_self_nonneg g p (v + t • w)
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul] at h
  rw [g.symm p w v] at h
  have hd := discrim_le_zero (a := g.inner p w w) (b := 2*g.inner p v w)
    (c := g.inner p v v) (fun t => by nlinarith only [h t])
  unfold discrim at hd
  nlinarith only [hd]

def jacobiNorm (g : SmoothMetric M) (γ : ℝ → M) (J : ∀ t, TangentSpace I3 (γ t)) : ℝ → ℝ :=
  fun t => Real.sqrt (jacobiNormSq g γ J t)

def jacobiRadialPairing (g : SmoothMetric M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I3 (γ t)) (t : ℝ) : ℝ :=
  g.inner (γ t) (covariantDerivative g γ J t) (J t)

lemma jacobiNorm_hasDerivAt (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ t, TangentSpace I3 (γ t)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : IsJacobiFieldOn g γ J U)
    {s : ℝ} (hs : s ∈ U) (hJs : J s ≠ 0) :
    HasDerivAt (jacobiNorm g γ J)
      (jacobiRadialPairing g γ J s / jacobiNorm g γ J s) s := by
  have hp : 0 < jacobiNormSq g γ J s := g.pos _ _ hJs
  have hd := (jacobiNormSq_hasDerivAt g hU hγ (jacobi_smoothField g hJ) hs).sqrt (ne_of_gt hp)
  change HasDerivAt (fun t => Real.sqrt (jacobiNormSq g γ J t)) _ s
  apply hd.congr_deriv
  dsimp only [jacobiNormSqSlope,jacobiRadialPairing,jacobiNorm]
  ring

lemma npc_jacobiNormSlope_hasDerivAt (g : SmoothMetric M)
    (hn : NonpositiveSectionalCurvature g) {γ : ℝ → M}
    {J : ∀ t, TangentSpace I3 (γ t)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : IsJacobiFieldOn g γ J U)
    {s : ℝ} (hs : s ∈ U) (hJs : J s ≠ 0) :
    ∃ a : ℝ, 0 ≤ a ∧ HasDerivAt (fun t => jacobiRadialPairing g γ J t / jacobiNorm g γ J t) a s := by
  let A := jacobiRadialPairing g γ J s
  let Q := jacobiNormSq g γ J s
  let N := jacobiNorm g γ J s
  let K := indexPairDensity g γ J J s
  have hQ : 0 < Q := g.pos _ _ hJs
  have hN : 0 < N := Real.sqrt_pos.mpr hQ
  have hN2 : N^2 = Q := Real.sq_sqrt hQ.le
  have hdA : HasDerivAt (jacobiRadialPairing g γ J) K s :=
    jacobi_indexPairDensity_hasDerivAt g hU hγ hJ (jacobi_smoothField g hJ) hs
  have hdN := jacobiNorm_hasDerivAt g hU hγ hJ hs hJs
  refine ⟨(K*N-A*(A/N))/N^2,?_,hdA.div hdN (ne_of_gt hN)⟩
  apply div_nonneg _ (sq_nonneg N)
  have hcs := metric_cauchy_schwarz g (γ s) (covariantDerivative g γ J s) (J s)
  have hc := curvatureAlong_pairing_nonpos g J (hγ.contMDiffAt (hU.mem_nhds hs))
    (nonpositiveAt_of_nonpositive g hn _)
  have hK : g.inner (γ s) (covariantDerivative g γ J s) (covariantDerivative g γ J s) ≤ K := by
    dsimp [K,indexPairDensity]
    linarith only [hc]
  have hmul := mul_le_mul_of_nonneg_right hK hQ.le
  have hmain : A^2 ≤ K*Q := hcs.trans hmul
  have he : (K*N-A*(A/N))*N = K*Q-A^2 := by
    rw [← hN2]
    field_simp
   
  exact (mul_nonneg_iff_of_pos_right hN).mp (by rw [he]; linarith only [hmain])

theorem npc_jacobiNorm_convex_Ici (g : SmoothMetric M)
    (hn : NonpositiveSectionalCurvature g) {γ : ℝ → M}
    {J : ∀ t, TangentSpace I3 (γ t)} (hγ : ContMDiff 𝓘(ℝ,ℝ) I3 ∞ γ)
    (hJ : IsJacobiFieldOn g γ J univ) (hpos : ∀ t > 0, J t ≠ 0) :
    ConvexOn ℝ (Ici 0) (jacobiNorm g γ J) := by
  classical
  have hc : Continuous (jacobiNorm g γ J) := by
    apply Real.continuous_sqrt.comp
    apply continuousOn_univ.mp
    exact (intrinsic_pairing_smooth g isOpen_univ hγ.contMDiffOn
      (jacobi_smoothField g hJ) (jacobi_smoothField g hJ)).continuousOn
  have hd (s : ℝ) (hs : s ∈ interior (Ici (0:ℝ))) :=
    npc_jacobiNormSlope_hasDerivAt g hn isOpen_univ hγ.contMDiffOn hJ
      (mem_univ s) (hpos s (by simpa only [interior_Ici,mem_Ioi] using hs))
  choose a ha hda using hd
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0) hc.continuousOn
    (f' := fun t => jacobiRadialPairing g γ J t / jacobiNorm g γ J t)
    (f'' := fun s => if hs : s ∈ interior (Ici (0:ℝ)) then a s hs else 0)
  · intro s hs
    exact (jacobiNorm_hasDerivAt g isOpen_univ hγ.contMDiffOn hJ (mem_univ s)
      (hpos s (by simpa only [interior_Ici,mem_Ioi] using hs))).hasDerivWithinAt
  · intro s hs
    simpa only [dite_eq_left hs] using (hda s hs).hasDerivWithinAt (s := interior (Ici (0:ℝ)))
  · intro s hs
    simpa only [dite_eq_left hs] using ha s hs

lemma connectionTerm_zero_right (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x v : E3) : connectionTerm g c x v 0 = 0 := by
  ext i
  simp only [connectionTerm,Pi.zero_apply,mul_zero,Finset.sum_const_zero]

lemma jacobiNorm_initial_rightDerivative (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ t, TangentSpace I3 (γ t)} (hγ : ContMDiff 𝓘(ℝ,ℝ) I3 ∞ γ)
    (hJ : SmoothFieldOn γ J univ) (h0 : J 0 = 0) :
    HasDerivWithinAt (jacobiNorm g γ J)
      (Real.sqrt (g.inner (γ 0) (covariantDerivative g γ J 0) (covariantDerivative g γ J 0)))
      (Ioi 0) 0 := by
  let c := chartAt E3 (γ 0)
  let j := fieldCoordinates γ J c
  let v := deriv j 0
  have hc : c ∈ atlas E3 M := chart_mem_atlas E3 (γ 0)
  have hsc : γ 0 ∈ c.source := mem_chart_source E3 (γ 0)
  have hjs : ContDiffAt ℝ ∞ j 0 := smoothField_coordinatesAt isOpen_univ hγ.contMDiffOn hJ hc (mem_univ 0) hsc
  have hz : j 0 = 0 := by simp only [j,fieldCoordinates,h0,map_zero]; rfl
  have hdj : HasDerivAt j v 0 := (hjs.differentiableAt (by simp)).hasDerivAt
  have hlimj : Tendsto (fun t : ℝ => t⁻¹ • j t) (𝓝[>] 0) (𝓝 v) := by
    simpa only [zero_add,hz,sub_zero] using hdj.tendsto_slope_zero_right
  have hcov : fieldCoordinates γ (covariantDerivative g γ J) c 0 = v := by
    rw [covariantDerivative_coordinates g hγ.contMDiffAt
      (hjs.differentiableAt (by simp)) hc hsc]
    change deriv j 0 + connectionTerm g c (c (γ 0)) (deriv (c ∘ γ) 0) (j 0) = v
    rw [hz,connectionTerm_zero_right,add_zero]
  have hB : ContinuousAt (fun t : ℝ => chartBilin g c (c (γ t))) 0 := by
    change ContinuousAt (chartBilin g c ∘ (c ∘ γ)) 0
    exact ContinuousAt.comp (f := c ∘ γ)
      (chartBilin_smoothAt g hc (c.map_source hsc)).continuousAt
      ((c.continuousAt hsc).comp hγ.continuous.continuousAt)
  have hlimB := hB.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hcont₁ : Continuous (fun p : (E3 →L[ℝ] E3 →L[ℝ] ℝ) × E3 => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hlim₁ := hcont₁.tendsto (chartBilin g c (c (γ 0)),v) |>.comp (hlimB.prodMk_nhds hlimj)
  have hcont₂ : Continuous (fun p : (E3 →L[ℝ] ℝ) × E3 => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hlim₂ := hcont₂.tendsto (chartBilin g c (c (γ 0)) v,v) |>.comp (hlim₁.prodMk_nhds hlimj)
  have hlim := Real.continuous_sqrt.tendsto (chartBilin g c (c (γ 0)) v v) |>.comp hlim₂
  have hbase : chartBilin g c (c (γ 0)) v v =
      g.inner (γ 0) (covariantDerivative g γ J 0) (covariantDerivative g γ J 0) := by
    rw [← hcov]
    exact metric_field_coordinates g _ _ hc hsc
  rw [hbase] at hlim
  apply (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mpr
  apply hlim.congr'
  have hnorm0 : jacobiNorm g γ J 0 = 0 := by
    simp only [jacobiNorm,jacobiNormSq,h0,map_zero,Real.sqrt_zero]
  have hsource : γ ⁻¹' c.source ∈ 𝓝[>] (0:ℝ) :=
    nhdsWithin_le_nhds (hγ.continuous.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hsc))
  filter_upwards [self_mem_nhdsWithin,hsource] with t ht htc
  change Real.sqrt (chartBilin g c (c (γ t)) (t⁻¹ • j t) (t⁻¹ • j t)) = slope (jacobiNorm g γ J) 0 t
  have hm : chartBilin g c (c (γ t)) (j t) (j t) = jacobiNormSq g γ J t :=
    metric_field_coordinates g J J hc htc
  simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  rw [← mul_assoc,← sq,hm,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (inv_nonneg.mpr ht.le)]
  rw [slope_def_field,hnorm0,sub_zero,sub_zero]
  simp only [jacobiNorm,div_eq_mul_inv,mul_comm]

theorem npc_jacobiNorm_lower (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    {γ : ℝ → M} {J : ∀ t, TangentSpace I3 (γ t)}
    (hγ : IsGeodesicOn g γ univ) (hJ : IsJacobiFieldOn g γ J univ) (h0 : J 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    t * Real.sqrt (g.inner (γ 0) (covariantDerivative g γ J 0) (covariantDerivative g γ J 0)) ≤
      jacobiNorm g γ J t := by
  by_cases hd : covariantDerivative g γ J 0 = 0
  · simp only [hd,map_zero,Real.sqrt_zero,mul_zero]
    exact Real.sqrt_nonneg _
  have hpos : ∀ s > (0:ℝ), J s ≠ 0 := by
    intro s hs hsz
    have hzero : ∀ z : ℝ, J z = 0 := fun z => npc_noConjugatePoints g hn univ isOpen_univ ordConnected_univ
      γ hγ J hJ 0 (mem_univ 0) s (mem_univ s) (ne_of_lt hs) h0 hsz z (mem_univ z)
    apply hd
    dsimp only [covariantDerivative,alongDerivative]
    have hz : fieldCoordinates γ J (chartAt E3 (γ 0)) = fun _ => 0 := by
      funext r; simp only [fieldCoordinates,hzero r,map_zero]; rfl
    rw [hz,deriv_const,connectionTerm_zero_right,add_zero]
    exact map_zero _
  have hγ' : ContMDiff 𝓘(ℝ,ℝ) I3 ∞ γ := contMDiffOn_univ.mp hγ.1
  have hc := npc_jacobiNorm_convex_Ici g hn hγ' hJ hpos
  have hnorm0 : jacobiNorm g γ J 0 = 0 := by
    simp only [jacobiNorm,jacobiNormSq,h0,map_zero,Real.sqrt_zero]
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [zero_mul,hnorm0] using (le_refl (0:ℝ))
  have he := hc.le_slope_of_hasDerivWithinAt_Ioi (show (0:ℝ) ∈ Ici 0 by simp)
    ht.le ht (jacobiNorm_initial_rightDerivative g hγ' (jacobi_smoothField g hJ) h0)
  simp only [slope_def_field,hnorm0,sub_zero] at he
  simpa only [mul_comm] using (le_div_iff₀ ht).mp he
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]

lemma exponentialVariation_initial_covariantDerivative (g : SmoothMetric M)
    (x : M) (v b : E3) :
    covariantDerivative g (geodesicFamily g (fiberPhase x) v)
      (geodesicVariation g (fiberPhase x) v b) 0 = b := by
  let f := fiberPhase x
  let γ := geodesicFamily g f v
  let J := geodesicVariation g f v b
  let c := chartAt E3 x
  let e := extChartAt I3.tangent (fiberPhase x v)
  let z := fun t => e (geodesicFlow g (f v) t)
  let w := fun t => fderiv ℝ (fun y => e (geodesicFlow g (f y) t)) v b
  have hf : ContMDiffAt 𝓘(ℝ,E3) I3.tangent 1 f v :=
    ((fiberPhase_contMDiff x).of_le (by simp)).contMDiffAt
  have hγ := geodesicFamily_isGeodesic g f v
  have hJ := geodesicVariation_isJacobi g hf b
  have hbase : γ 0 = x := exponentialFamily_zero g x v
  have hsource : γ 0 ∈ c.source := hbase ▸ mem_chart_source E3 x
  have hlin := geodesic_family_linearization_at g hf 0 b
  simp only [geodesicFlow_zero] at hlin
  obtain ⟨U,hU,h0,hzt,hdz,hdw⟩ := hlin
  have he : fieldCoordinates γ J c =ᶠ[𝓝 (0:ℝ)] fun t => (w t).1 := by
    filter_upwards [(hγ.1.contMDiffAt (by simp)).continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds hsource)] with t ht
    exact geodesicVariation_coordinates g hf b t (p := fiberPhase x v) ht
  have hd : HasDerivAt (fieldCoordinates γ J c) (w 0).2 0 := by
    have hd' := (hdw 0 h0).congr_deriv
      (geodesicPhase_fderiv_apply g (chart_mem_atlas E3 x) (hzt 0 h0) (w 0))
    have hh : HasDerivAt (fun t => (w t).1) (w 0).2 0 := hd'.fst
    exact hh.congr_of_eventuallyEq he
  have hi : w 0 = (0,mfderiv I3 I3 c x b) := by
    dsimp only [w]
    simp only [geodesicFlow_zero]
    exact fiberPhase_extChart_fderiv x v b
  have hcov := covariantDerivative_coordinates g (hγ.1.contMDiffAt (by simp))
    ((smoothField_coordinatesAt isOpen_univ hγ.1 (jacobi_smoothField g hJ)
      (chart_mem_atlas E3 (γ 0)) (mem_univ 0) (mem_chart_source E3 (γ 0))).differentiableAt (by simp))
    (chart_mem_atlas E3 x) hsource
  have hz : fieldCoordinates γ J c 0 = 0 := by
    change mfderiv I3 I3 c (γ 0) (J 0) = 0
    rw [show J 0 = 0 from exponentialVariation_zero g x v b,map_zero]
  change mfderiv I3 I3 c (γ 0) (covariantDerivative g γ J 0) = _ at hcov
  rw [alongDerivative,hd.deriv,hi,hz,connectionTerm_zero_right,add_zero,hbase] at hcov
  exact (mdifferentiable_of_mem_atlas (I := I3) (chart_mem_atlas E3 x)).mfderiv_injective
    (mem_chart_source E3 x) hcov

theorem npc_exponential_differential_expanding (g : SmoothMetric M)
    (hn : NonpositiveSectionalCurvature g) (x : M) (v b : E3) :
    g.inner x b b ≤ g.inner (exponential g x v)
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g x) v b)
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g x) v b) := by
  have hf : ContMDiffAt 𝓘(ℝ,E3) I3.tangent 1 (fiberPhase x) v :=
    ((fiberPhase_contMDiff x).of_le (by simp)).contMDiffAt
  have h := npc_jacobiNorm_lower g hn (geodesicFamily_isGeodesic g (fiberPhase x) v)
    (geodesicVariation_isJacobi g hf b) (exponentialVariation_zero g x v b) (t := 1) (by norm_num)
  rw [exponentialVariation_initial_covariantDerivative,exponentialFamily_zero,one_mul] at h
  change Real.sqrt (g.inner x b b) ≤ Real.sqrt (g.inner (exponential g x v)
    (mfderiv 𝓘(ℝ,E3) I3 (exponential g x) v b) (mfderiv 𝓘(ℝ,E3) I3 (exponential g x) v b)) at h
  exact (Real.sqrt_le_sqrt_iff (inner_self_nonneg g _ _)).mp h
end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
lemma deriv_comp_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {k t : ℝ} (hf : DifferentiableAt ℝ f (k*t)) :
    deriv (fun r => f (k*r)) t = k • deriv f (k*t) := by
  simpa only [Function.comp_def,mul_one] using (hf.hasDerivAt.scomp t ((hasDerivAt_id t).const_mul k)).deriv

lemma geodesic_scale (g : SmoothMetric M) {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : IsGeodesicOn g γ U) (k : ℝ) :
    IsGeodesicOn g (fun r => γ (k*r)) ((fun r => k*r) ⁻¹' U) := by
  have htA : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun r : ℝ => k*r) :=
    contMDiff_iff_contDiff.mpr (contDiff_const.mul contDiff_id)
  refine ⟨hγ.1.comp htA.contMDiffOn (fun _ h => h),?_⟩
  intro c hc t ht hct
  have hs := chartPhase_contDiffAt (hγ.1.contMDiffAt (hU.mem_nhds ht)) hc hct
  have hn : ∀ᶠ r in 𝓝 t, k*r ∈ U ∧ γ (k*r) ∈ c.source :=
    continuousAt_const.mul continuousAt_id |>.preimage_mem_nhds
      (Filter.Eventually.and (hU.mem_nhds ht)
        ((hγ.1.contMDiffAt (hU.mem_nhds ht)).continuousAt.preimage_mem_nhds
          (c.open_source.mem_nhds hct)))
  have hd : deriv (c ∘ (fun r => γ (k*r))) =ᶠ[𝓝 t] fun r => k • deriv (c ∘ γ) (k*r) := by
    filter_upwards [hn] with r hr
    exact deriv_comp_mul ((chartPhase_contDiffAt
      (hγ.1.contMDiffAt (hU.mem_nhds hr.1)) hc hr.2).fst.differentiableAt (by simp))
  have hdd : deriv (deriv (c ∘ (fun r => γ (k*r)))) t = (k*k) • deriv (deriv (c ∘ γ)) (k*t) := by
    rw [hd.deriv_eq]
    change deriv (k • (fun r => deriv (c ∘ γ) (k*r))) t = _
    have hdγ : DifferentiableAt ℝ (deriv (c ∘ γ)) (k*t) := hs.snd.differentiableAt (by simp)
    rw [deriv_const_smul k,deriv_comp_mul hdγ,smul_smul]
    exact hdγ.comp t (((hasDerivAt_id t).const_mul k).differentiableAt)
  change _ + _ = 0
  rw [hdd,hd.eq_of_nhds]
  have hbil (u v : E3) : connectionTerm g c (c (γ (k*t))) (k • u) (k • v) =
      (k*k) • connectionTerm g c (c (γ (k*t))) u v := by
    simp only [← connectionBilin_apply,map_smul,_root_.smul_apply,smul_smul]
  simp only [Function.comp_apply] at *
  have hgeo := hγ.2 c hc (k*t) ht hct
  change deriv (deriv (c ∘ γ)) (k*t) + connectionTerm g c (c (γ (k*t)))
    (deriv (c ∘ γ) (k*t)) (deriv (c ∘ γ) (k*t)) = 0 at hgeo
  rw [hbil,← smul_add,hgeo,smul_zero]

lemma geodesic_const (g : SmoothMetric M) (x : M) : IsGeodesicOn g (fun _ : ℝ => x) univ := by
  refine ⟨contMDiff_const.contMDiffOn,?_⟩
  intro c hc t ht hxt
  simp only [Function.comp_def,alongDerivative,deriv_const]
  simp only [← connectionBilin_apply,map_zero]
  simp [deriv_const]

variable [CompactSpace M] [T2Space M]
lemma exponential_zero (g : SmoothMetric M) (x : M) : exponential g x 0 = x := by
  let γ := globalGeodesic g (fiberPhase x 0)
  have hγ := globalGeodesic_isGeodesic g (fiberPhase x 0)
  have he : phaseLift γ 0 = phaseLift (fun _ : ℝ => x) 0 := by
    rw [globalGeodesic_initial]
    unfold fiberPhase phaseLift velocity
    rw [mfderiv_const]
    rfl
  exact geodesic_unique g isOpen_univ ordConnected_univ hγ (geodesic_const g x)
    (mem_univ 0) he (mem_univ 1)

lemma exponential_scale (g : SmoothMetric M) (x : M) (v : E3) (k : ℝ) :
    exponential g x (k • v) = globalGeodesic g (fiberPhase x v) k := by
  let γ := globalGeodesic g (fiberPhase x v)
  have hγ := globalGeodesic_isGeodesic g (fiberPhase x v)
  have hk : IsGeodesicOn g (fun r => γ (k*r)) univ := by
    simpa only [preimage_univ] using geodesic_scale g isOpen_univ hγ k
  have he : phaseLift (globalGeodesic g (fiberPhase x (k • v))) 0 =
      phaseLift (fun r => γ (k*r)) 0 := by
    rw [globalGeodesic_initial]
    have hbase : γ (k*0) = x := by
      change globalGeodesic g (fiberPhase x v) (k*0) = x
      rw [mul_zero]
      exact congrArg Bundle.TotalSpace.proj (globalGeodesic_initial g (fiberPhase x v))
    apply Bundle.TotalSpace.ext hbase.symm
    apply heq_of_eq
    change k • v = mfderiv 𝓘(ℝ,ℝ) I3 (fun r => γ (k*r)) 0 1
    have hc := mfderiv_comp 0 ((hγ.1.contMDiffAt (by simp)).mdifferentiableAt (by simp))
      ((contMDiff_iff_contDiff.mpr (contDiff_const.mul contDiff_id) :
        ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun r : ℝ => k*r)).mdifferentiable (by simp) 0)
    have hmul : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun r : ℝ => k*r) 0 1 = k := by
      rw [mfderiv_eq_fderiv]
      change deriv (fun r : ℝ => k*r) 0 = k
      simpa only [mul_one,id_eq] using ((hasDerivAt_id (0:ℝ)).const_mul k).deriv
    have hv : (velocity γ 0 : E3) = v := congrArg
      (fun p : TangentBundle I3 M => (p.snd : E3)) (globalGeodesic_initial g (fiberPhase x v))
    have hh := congrArg (fun L : ℝ →L[ℝ] E3 => L 1) hc
    change mfderiv 𝓘(ℝ,ℝ) I3 (fun r => γ (k*r)) 0 1 =
      mfderiv 𝓘(ℝ,ℝ) I3 γ (k*0) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun r : ℝ => k*r) 0 1) at hh
    rw [hmul,mul_zero] at hh
    have hsm : (mfderiv 𝓘(ℝ,ℝ) I3 γ 0 k : E3) = k • (velocity γ 0 : E3) := by
      unfold velocity
      let L : ℝ →L[ℝ] E3 := mfderiv 𝓘(ℝ,ℝ) I3 γ 0
      change L k = k • L 1
      have hL := L.map_smul k (1:ℝ)
      simp only [smul_eq_mul,mul_one] at hL
      exact hL

    exact ((congrArg (fun w : E3 => k • w) hv).symm.trans hsm.symm).trans hh.symm

  have hh := geodesic_unique g isOpen_univ ordConnected_univ
    (globalGeodesic_isGeodesic g (fiberPhase x (k • v))) hk (mem_univ 0) he (mem_univ 1)
  change globalGeodesic g (fiberPhase x (k • v)) 1 = globalGeodesic g (fiberPhase x v) k
  simpa only [mul_one] using hh
end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]
end ThreeManifold.RiemannianCoordinates

end

end OAI


