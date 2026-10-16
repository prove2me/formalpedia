-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
-- name    : OAI_Geometry_ConjugatePoints_Curvature
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:43:47.94609+00:00
-- url     : https://prove2.me/theorems/3bad1316-13e8-4752-8ce7-bddda2d7bb1e
-- title:
--   Pointwise nonpositive curvature, recharted metrics, and local isometries onto warped-product models in $\mathbb{R}^3$
-- statement:
--   This file sets up the comparison machinery used to compute curvature on the glued three-manifold: a pointwise form of nonpositive curvature, a way to view metrics on manifolds modelled on other normed spaces as metrics in $\mathbb{R}^3$-charts, explicit model metrics on $\mathbb{R}^3$, and a list of local isometries from pieces of the compact manifold onto these models.
--
--   **Notation.** $M$, $M'$ are smooth manifolds modelled on $\mathbb{R}^3$ with smooth Riemannian metrics $g$, $h$. In a chart $c$ write $g_{ij}$ for the coordinate metric matrix, $\Gamma^l_{ij} = \tfrac12 \sum_m g^{lm}(\partial_i g_{mj} + \partial_j g_{mi} - \partial_m g_{ij})$ for the Christoffel symbols, $R^l_{kij} = \partial_i \Gamma^l_{jk} - \partial_j \Gamma^l_{ik} + \sum_a (\Gamma^l_{ia}\Gamma^a_{jk} - \Gamma^l_{ja}\Gamma^a_{ik})$, and $R(u, v)w = \big(\sum_{k,i,j} R^l_{kij}\, w^k u^i v^j\big)_l$ for $u, v, w \in \mathbb{R}^3$. A *local metric isometry* $f : (M, g) \to (M', h)$ consists of an open set $D \subseteq M$ such that $f$ is smooth on $D$ and $g_p(u, v) = h_{f(p)}(df_p u, df_p v)$ for all $p \in D$ and all tangent vectors $u, v$.
--
--   The file defines and establishes:
--
--   1. **Pointwise nonpositivity.** $g$ is *nonpositive at* $p$ if for every atlas chart $c$ whose source contains $p$ and all $u, v \in \mathbb{R}^3$,
--   $$
--   g^{c}_{c(p)}\big(R(u, v)v,\ u\big) \le 0,
--   $$
--   where $g^c$ is the metric expressed in the chart. Nonpositive sectional curvature in the global (chartwise) sense implies nonpositivity at every point; $g_p(v, v) \ge 0$ for every tangent vector; and if a curve $\gamma$ is smooth at $s$ and $g$ is nonpositive at $\gamma(s)$, then for every vector field $J$ along $\gamma$ the index density $g(D_sJ, D_sJ) - g\big(R(J, \dot\gamma)\dot\gamma, J\big)$ at $s$ is nonnegative ($D_s$ the covariant derivative along $\gamma$). The pushforward of a field $J$ along $\gamma$ by $f$ is $s \mapsto df_{\gamma(s)} J(s)$.
--
--   2. **Warped-product matrices.** For $r : \mathbb{R} \to \mathbb{R}$ and $c, t \in \mathbb{R}$: $Q = \operatorname{diag}(r(t)^2, c^2)$, $P = \operatorname{diag}(r(t)^{-2}, c^{-2})$, $A = \operatorname{diag}(2 r(t) r'(t), 0)$ and $B = \operatorname{diag}(2 r'(t)^2 + 2 r(t) r''(t), 0)$, the fibre metric of $dt^2 + r^2dx^2 + c^2dy^2$, its inverse and its first two $t$-derivatives.
--
--   3. **Recharting.** If $M$ is modelled on a real normed space $E$ and $e : E \to \mathbb{R}^3$ is a linear isomorphism, composing every chart with $e$ makes $M$ a manifold modelled on $\mathbb{R}^3$, and a metric on $M$ becomes a smooth metric for this atlas. If $f$ is smooth on an open set $U$ and $f^*h = g$ on $U$, then $f$ is a local metric isometry with domain $U$ between the recharted metrics (with variants where only the source or only the target is recharted).
--
--   4. **Model metrics on $\mathbb{R}^3$.** For smooth $r, s, c : \mathbb{R} \to \mathbb{R}$ with $r, s$ nowhere zero,
--   $$
--   g^{r,s,c} = dx_0^2 + r(x_0)^2\big(dx_1 - c(x_0)\,dx_2\big)^2 + s(x_0)^2\,dx_2^2 ,
--   $$
--   and the covering projection $\mathbb{R}^3 \to Z = \mathbb{R} \times (\mathbb{R}/6\mathbb{Z})^2$ is a local isometry (on all of $\mathbb{R}^3$) from $g^{r,s,c}$ to the corresponding cylinder metric. The warped model is $g^{r,b} = dx_0^2 + r(x_0)^2dx_1^2 + b^2dx_2^2$ ($b \neq 0$ constant).
--
--   5. **The neck and its right end.** For $\delta \in (0, \tfrac12]$ and $B > 0$ the neck model is $g^{r,s,c}$ with $r = \rho_1 = \frac{\delta^2 B}{6}\ell_\delta$, $s = \rho_2 = \frac{B}{6}\ell_\delta(1 - \cdot)$ and $c = \chi$, where $\ell_\delta$ is the collar profile and $\chi$ the smooth step ($\chi = 0$ on $(-\infty, \tfrac{5}{12}]$, $\chi = 1$ on $[\tfrac{7}{12}, \infty)$) of the neck construction. With $\tilde r(t) = \frac{B}{6}\ell_\delta(t)$, $w = \frac{\delta^2 B}{6}\ell_\delta(1)$ and the affine map $F(x_0, x_1, x_2) = (1 - x_0,\ x_2,\ x_1 - x_2)$, the map $F$ is a local isometry with domain $\{x_0 > \tfrac23\}$ from the neck model to the warped model $g^{\tilde r, w}$.
--
--   6. **The hyperbolic side.** On $\mathbb{H} \times \mathbb{R}$ the metric $\langle u_1, v_1\rangle/(\operatorname{Im} z)^2 + c^2u_2v_2$ ($c \neq 0$) is carried isometrically (on its whole domain) by $(z, s) \mapsto (\log \operatorname{Im} z, \operatorname{Re} z, s)$ onto the warped model with $r(t) = e^{-t}$ and width $c$, and the projection $(z, s) \mapsto (\pi(z), s \bmod 6)$ is a local isometry onto the core metric $g^\Sigma + c^2 d\theta^2$ of $\Sigma \times S^1_6$.
--
--   7. **Isometries inside the compact construction.** Each piece inclusion $Q \to N$ is a local isometry from the recharted piece metric to the recharted compact metric $g_\delta$; the covering projection is a local isometry from the neck model to the recharted neck metric; the radial map $R_L$ and the switch map are local isometries from the pulled-back cylinder metrics to the original ones; the inclusion $Q \subset W$ is a local isometry from the piece metric to the whole-piece metric. For a whole-piece metric built from a cylinder metric $g$ and $c \neq 0$ (whose lift equals $dt^2 + e^{-2t}dx^2 + c^2dy^2$ for $t < \tfrac14$), the logarithmic cusp map $(\pi(z), \theta) \mapsto (\log \operatorname{Im} z, \operatorname{Re} z \bmod 6, \theta)$ is a local isometry to $g$ on the cusp $\{h > \tfrac18\}$, and the identity is a local isometry to the core metric on $\{h < \tfrac14\}$. The open neck is the image of the collar under the left inclusion into $N$.
--
--   Together these reduce curvature and Jacobi-field computations on the compact manifold to explicit warped products in $\mathbb{R}^3$, where Christoffel symbols and curvature can be written down in closed form.
--
--   **Formalization Note** `LocalMetricIsometry` (from the coordinates module) is a structure with fields `domain`, `isOpen_domain`, `smooth`, `metric`; the recharting uses `Rechart.charts`/`Rechart.isManifold` with `Coordinates3.coordinates` ($(z, s) \mapsto (\operatorname{Re} z, \operatorname{Im} z, s)$) or the cylinder coordinates, installed as local instances. $P$ uses Lean's inverse, so an entry is $0$ if $r(t) = 0$ or $c = 0$; $A$ and $B$ use `deriv`, which is $0$ at points of non-differentiability. Several anonymous local instances and smoothness lemmas are plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Curvature.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Curvature.lean by skeleton subtraction
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

namespace OAI

noncomputable section

/-!
# Local isometries, warped curvature, and compact curvature estimates.
-/

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

def NonpositiveAt (g : SmoothMetric M) (p : M) : Prop :=
  ∀ c : OpenPartialHomeomorph M E3, c ∈ atlas E3 M → p ∈ c.source →
    ∀ u v : E3, chartBilin g c (c p) (curvatureTerm g c (c p) u v v) u ≤ 0

lemma nonpositiveAt_of_nonpositive (g : SmoothMetric M)
    (h : NonpositiveSectionalCurvature g) (p : M) : NonpositiveAt g p := by
  intro c hc hp u v
  rw [← bilin_matrix]
  exact h c hc (c p) (c.map_source hp) u v

lemma inner_self_nonneg (g : SmoothMetric M) (p : M) (v : TangentSpace I3 p) :
    0 ≤ g.inner p v v := by
  by_cases hv : v = 0
  · simp only [hv,map_zero,le_refl]
  · exact (g.pos p v hv).le

lemma indexPairDensity_nonneg_of_nonpositiveAt (g : SmoothMetric M) {γ : ℝ → M}
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) (hn : NonpositiveAt g (γ s)) :
    0 ≤ indexPairDensity g γ J J s := by
  apply sub_nonneg.mpr
  apply le_trans _ (inner_self_nonneg g _ _)
  have hc := chart_mem_atlas E3 (γ s)
  have hsc := mem_chart_source E3 (γ s)
  rw [← metric_field_coordinates g (curvatureAlong g γ J) J hc hsc,
    curvatureAlong_coordinates g J hγ hc hsc]
  exact hn _ hc hsc _ _

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)

def mapField (_P : LocalMetricIsometry g h f) (γ : ℝ → M) (J : ∀ s, TangentSpace I3 (γ s)) :
    ∀ s, TangentSpace I3 ((f ∘ γ) s) := fun s => mfderiv I3 I3 f (γ s) (J s)

end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry

namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.WarpedCurvature
open Neck RiemannianCoordinates

def diag (a b : ℝ) : TMat := !![a,0;0,b]
def Q (r : ℝ → ℝ) (c t : ℝ) := diag ((r t)^2) (c^2)
def P (r : ℝ → ℝ) (c t : ℝ) := diag ((r t)^2)⁻¹ (c^2)⁻¹
def A (r : ℝ → ℝ) (t : ℝ) := diag (2*r t*deriv r t) 0
def B (r : ℝ → ℝ) (t : ℝ) := diag (2*(deriv r t)^2+2*r t*deriv (deriv r) t) 0
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
end ThreeManifold.WarpedCurvature
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.Rechart
open MetricConstruction RiemannianCoordinates
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def realMetric (e : E ≃L[ℝ] E3) (g : Metric (E := E) M) :
    letI := charts (M := M) e
    letI := isManifold (M := M) e
    SmoothMetric M := by
  letI := charts (M := M) e
  letI := isManifold (M := M) e
  exact pullbackHomeomorph g (Homeomorph.refl M)
    (identity_smooth_backward e) (identity_smooth_forward e)

lemma map_smoothAt (e : E ≃L[ℝ] E3) (d : F ≃L[ℝ] E3) {f : M → N} {p : M}
    (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f p) :
    letI := charts (M := M) e
    letI := charts (M := N) d
    ContMDiffAt I3 I3 ∞ f p := by
  let := charts (M := M) e
  let := charts (M := N) d
  exact ((identity_smooth_forward d (f p)).comp p hf).comp p
    (identity_smooth_backward e p)

def realIsometry (e : E ≃L[ℝ] E3) (d : F ≃L[ℝ] E3)
    (g : Metric (E := E) M) (h : Metric (E := F) N) (f : M → N)
    (U : Set M) (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f U)
    (hm : ∀ p ∈ U, pullInner (E := E) h f p = g.inner p) :
    letI := charts (M := M) e
    letI := isManifold (M := M) e
    letI := charts (M := N) d
    letI := isManifold (M := N) d
    LocalMetricIsometry (realMetric e g) (realMetric d h) f := by
  letI := charts (M := M) e
  letI := isManifold (M := M) e
  letI := charts (M := N) d
  letI := isManifold (M := N) d
  have hs (p : M) (hp : p ∈ U) := hf.contMDiffAt (hU.mem_nhds hp)
  refine ⟨U,hU,fun p hp => (map_smoothAt e d (hs p hp)).contMDiffWithinAt,?_⟩
  intro p hp u v
  have h₁ := pull_composition h
    ((identity_smooth_backward e p).mdifferentiableAt (by simp))
    ((hs p hp).mdifferentiableAt (by simp))
  have h₂ := pull_composition h
    ((map_smoothAt e d (hs p hp)).mdifferentiableAt (by simp))
    ((identity_smooth_backward d (f p)).mdifferentiableAt (by simp))
  change pullInner (E := E3) h f p =
    pullBilin (E := E3) (F := E) (pullInner (E := E) h f p)
      (mfderiv I3 𝓘(ℝ,E) (id : M → M) p) at h₁
  rw [hm p hp] at h₁
  change pullInner (E := E3) h f p = _ at h₂
  have he := h₁.symm.trans h₂
  exact congrArg (fun b : E3 →L[ℝ] E3 →L[ℝ] ℝ => b u v) he

variable {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
def realTargetIsometry (d : F ≃L[ℝ] E3)
    (g : SmoothMetric X) (h : Metric (E := F) N) (f : X → N)
    (U : Set X) (hU : IsOpen U)
    (hf : ContMDiffOn I3 𝓘(ℝ,F) ∞ f U)
    (hm : ∀ p ∈ U, pullInner (E := E3) h f p = g.inner p) :
    letI := charts (M := N) d
    letI := isManifold (M := N) d
    LocalMetricIsometry g (realMetric d h) f := by
  letI := charts (M := N) d
  letI := isManifold (M := N) d
  have hs (p : X) (hp : p ∈ U) : ContMDiffAt I3 I3 ∞ f p :=
    (identity_smooth_forward d (f p)).comp p (hf.contMDiffAt (hU.mem_nhds hp))
  refine ⟨U,hU,fun p hp => (hs p hp).contMDiffWithinAt,?_⟩
  intro p hp u v
  have h₂ := pull_composition h ((hs p hp).mdifferentiableAt (by simp))
    ((identity_smooth_backward d (f p)).mdifferentiableAt (by simp))
  change pullInner (E := E3) h f p = _ at h₂
  rw [hm p hp] at h₂
  exact congrArg (fun b : E3 →L[ℝ] E3 →L[ℝ] ℝ => b u v) h₂
end ThreeManifold.Rechart

namespace ThreeManifold.CylinderConstruction
open MetricConstruction RiemannianCoordinates
local instance instChartedSpaceE3Cylinder : ChartedSpace E3 Cylinder := Rechart.charts coordinates
local instance instIsManifoldRealE3I3SomeENatTopCylinder : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates
variable {r s c : ℝ → ℝ}
    (h1 : ContDiff ℝ ∞ r) (h2 : ContDiff ℝ ∞ s) (h3 : ContDiff ℝ ∞ c)
    (hr : ∀ t, r t ≠ 0) (hs : ∀ t, s t ≠ 0)
def euclideanMetric : SmoothMetric E3 :=
  triangularMetric (h1.comp (contDiff_apply ℝ ℝ 0)) (h2.comp (contDiff_apply ℝ ℝ 0))
    (h3.comp (contDiff_apply ℝ ℝ 0)) (fun _ => hr _) (fun _ => hs _)
def realMetric : SmoothMetric Cylinder := Rechart.realMetric coordinates (metric h1 h2 h3 hr hs)
def euclideanProjection : E3 → Cylinder := projection ∘ coordinates.symm
lemma euclideanProjection_smooth :
    ContMDiff I3 𝓘(ℝ,P) ∞ euclideanProjection := by
  exact projection_smooth.comp coordinates.symm.contDiff.contMDiff
lemma euclideanProjection_metric (x : E3) :
    pullInner (E := E3) (metric h1 h2 h3 hr hs) euclideanProjection x =
      (euclideanMetric h1 h2 h3 hr hs).inner x := by
  rw [euclideanProjection,pull_composition _
    (((show ContMDiff I3 𝓘(ℝ,P) ∞ coordinates.symm from coordinates.symm.contDiff.contMDiff) x).mdifferentiableAt (by simp))
    ((projection_smooth _).mdifferentiableAt (by simp)),metric_projection]
  ext u v
  change (lifted h1 h2 h3 hr hs).inner (coordinates.symm x)
    (mfderiv I3 𝓘(ℝ,P) coordinates.symm x u)
    (mfderiv I3 𝓘(ℝ,P) coordinates.symm x v) = _
  rw [mfderiv_eq_fderiv,coordinates.symm.hasFDerivAt.fderiv,lifted_apply]
  exact (triangularMetric_apply (h1.comp (contDiff_apply ℝ ℝ 0))
    (h2.comp (contDiff_apply ℝ ℝ 0)) (h3.comp (contDiff_apply ℝ ℝ 0))
    (fun _ => hr _) (fun _ => hs _) x u v).symm

def projectionIsometry : LocalMetricIsometry (euclideanMetric h1 h2 h3 hr hs)
    (realMetric h1 h2 h3 hr hs) euclideanProjection :=
  Rechart.realTargetIsometry coordinates _ _ _ univ isOpen_univ
    euclideanProjection_smooth.contMDiffOn (fun x _ => euclideanProjection_metric h1 h2 h3 hr hs x)
end ThreeManifold.CylinderConstruction

namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.WarpedCurvature
open MetricConstruction CylinderConstruction RiemannianCoordinates
variable {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) {b : ℝ} (hb : b ≠ 0) (hr : ∀ t, r t ≠ 0)
def warpedModel : SmoothMetric E3 := euclideanMetric hs (contDiff_const (c := b))
  (contDiff_const (c := 0)) hr (fun _ => hb)
end ThreeManifold.WarpedCurvature

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates WarpedCurvature
def neckModel {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) : SmoothMetric E3 :=
  euclideanMetric (radius₁_smooth ⟨hδ.1.le,hδ.2⟩ B) (radius₂_smooth ⟨hδ.1.le,hδ.2⟩ B)
    Cometric.χ_smooth (fun t => (radius₁_pos hδ.1 hB t).ne') (fun t => (radius₂_pos hB t).ne')
lemma neckModel_apply {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) (x u v : E3) :
    (neckModel hδ hB).inner x u v = u 0*v 0 + radius₁ δ B (x 0)^2*
      (u 1-Cometric.χ (x 0)*u 2)*(v 1-Cometric.χ (x 0)*v 2)+radius₂ δ B (x 0)^2*u 2*v 2 :=
  by
    exact triangularMetric_apply
      ((radius₁_smooth ⟨hδ.1.le,hδ.2⟩ B).comp (contDiff_apply ℝ ℝ 0))
      ((radius₂_smooth ⟨hδ.1.le,hδ.2⟩ B).comp (contDiff_apply ℝ ℝ 0))
      (Cometric.χ_smooth.comp (contDiff_apply ℝ ℝ 0))
      (fun y => (radius₁_pos hδ.1 hB (y 0)).ne')
      (fun y => (radius₂_pos hB (y 0)).ne') x u v
lemma warpedModel_apply {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) {b : ℝ} (hb : b ≠ 0)
    (hr : ∀ t, r t ≠ 0) (x u v : E3) :
    (warpedModel hs hb hr).inner x u v = u 0*v 0 + r (x 0)^2*u 1*v 1+b^2*u 2*v 2 := by
  have he : (warpedModel hs hb hr).inner x u v = u 0*v 0+
      r (x 0)^2*(u 1-0*u 2)*(v 1-0*v 2)+b^2*u 2*v 2 := by
    exact triangularMetric_apply (hs.comp (contDiff_apply ℝ ℝ 0))
      ((contDiff_const (c := b)).comp (contDiff_apply ℝ ℝ 0))
      ((contDiff_const (c := (0:ℝ))).comp (contDiff_apply ℝ ℝ 0))
      (fun y : E3 => hr (y 0)) (fun _ : E3 => hb) x u v
  simpa only [zero_mul,sub_zero] using he

def rightRadius (δ B t : ℝ) := B/6*Collar.ell δ t
lemma rightRadius_smooth {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (B : ℝ) : ContDiff ℝ ∞ (rightRadius δ B) :=
  contDiff_const.mul (Collar.ell_smooth ⟨hδ.1.le,hδ.2⟩)
lemma rightRadius_pos (δ : ℝ) {B : ℝ} (hB : 0 < B) (t : ℝ) : 0 < rightRadius δ B t :=
  mul_pos (div_pos hB (by norm_num)) (Collar.ell_pos _ _)
def rightWidth (δ B : ℝ) := δ^2*B/6*Collar.ell δ 1
lemma rightWidth_pos {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) : 0 < rightWidth δ B := by
  unfold rightWidth
  exact mul_pos (div_pos (mul_pos (sq_pos_of_pos hδ) hB) (by norm_num)) (Collar.ell_pos _ _)

def neckFlipLinear : E3 →L[ℝ] E3 :=
  ContinuousLinearMap.pi fun i : Fin 3 => if i = 0 then -(ContinuousLinearMap.proj 0 : E3 →L[ℝ] ℝ)
    else if i = 1 then (ContinuousLinearMap.proj 2 : E3 →L[ℝ] ℝ)
    else (ContinuousLinearMap.proj 1 : E3 →L[ℝ] ℝ) - ContinuousLinearMap.proj 2
lemma neckFlipLinear_apply (u : E3) : neckFlipLinear u = ![-u 0,u 2,u 1-u 2] := by
  ext i; fin_cases i <;> simp [neckFlipLinear]
def neckFlip (x : E3) : E3 := neckFlipLinear x + ![1,0,0]
lemma neckFlip_apply (x : E3) : neckFlip x = ![1-x 0,x 2,x 1-x 2] := by
  rw [neckFlip,neckFlipLinear_apply]
  ext i; fin_cases i <;> simp; ring
lemma neckFlip_smooth : ContDiff ℝ ∞ neckFlip := neckFlipLinear.contDiff.add contDiff_const
lemma neckFlip_deriv (x : E3) : mfderiv I3 I3 neckFlip x = neckFlipLinear := by
  rw [mfderiv_eq_fderiv]
  exact (neckFlipLinear.hasFDerivAt.add_const _).fderiv

def rightWarpedModel {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) : SmoothMetric E3 :=
  warpedModel (rightRadius_smooth hδ B) (rightWidth_pos hδ.1 hB).ne'
    (fun t => (rightRadius_pos δ hB t).ne')
lemma neckRight_tensor {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B)
    (x u v : E3) (hx : 2/3 < x 0) :
    (neckModel hδ hB).inner x u v =
      (rightWarpedModel hδ hB).inner (neckFlip x) (neckFlipLinear u) (neckFlipLinear v) := by
  rw [neckModel_apply]
  have hc : Cometric.χ (x 0) = 1 := Cometric.χ_eq_one (by linarith)
  have hr : radius₁ δ B (x 0) = rightWidth δ B := by
    rw [radius₁,ell_plateau ⟨hδ.1.le,hδ.2⟩ hx.le]
    rfl
  rw [hc,hr]
  unfold rightWarpedModel
  rw [warpedModel_apply,neckFlip_apply,neckFlipLinear_apply,neckFlipLinear_apply]
  simp [radius₂,rightRadius]
  ring

def neckRightIsometry {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) :
    LocalMetricIsometry (neckModel hδ hB) (rightWarpedModel hδ hB) neckFlip where
  domain := {x | 2/3 < x 0}
  isOpen_domain := isOpen_lt continuous_const (continuous_apply 0)
  smooth := neckFlip_smooth.contMDiff.contMDiffOn
  metric := by
    intro x hx u v
    have hu := congrArg (fun A : E3 →L[ℝ] E3 => A u) (neckFlip_deriv x)
    have hv := congrArg (fun A : E3 →L[ℝ] E3 => A v) (neckFlip_deriv x)
    exact (neckRight_tensor hδ hB x u v hx).trans (congrArg₂
      (fun a b : E3 => (rightWarpedModel hδ hB).inner (neckFlip x) a b) hu.symm hv.symm)
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.Rechart
open MetricConstruction RiemannianCoordinates
variable {E M X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
def realSourceIsometry (e : E ≃L[ℝ] E3)
    (g : Metric (E := E) M) (h : SmoothMetric X) (f : M → X)
    (U : Set M) (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ,E) I3 ∞ f U)
    (hm : ∀ p ∈ U, pullInner (E := E) h f p = g.inner p) :
    letI := charts (M := M) e
    letI := isManifold (M := M) e
    LocalMetricIsometry (realMetric e g) h f := by
  letI := charts (M := M) e
  letI := isManifold (M := M) e
  have hs (p : M) (hp : p ∈ U) := hf.contMDiffAt (hU.mem_nhds hp)
  refine ⟨U,hU,fun p hp => ((hs p hp).comp p
    (identity_smooth_backward e p)).contMDiffWithinAt,?_⟩
  intro p hp u v
  have h₁ := pull_composition h
    ((identity_smooth_backward e p).mdifferentiableAt (by simp))
    ((hs p hp).mdifferentiableAt (by simp))
  change pullInner (E := E3) h f p =
    pullBilin (E := E3) (F := E) (pullInner (E := E) h f p)
      (mfderiv I3 𝓘(ℝ,E) (id : M → M) p) at h₁
  rw [hm p hp] at h₁
  exact congrArg (fun b : E3 →L[ℝ] E3 →L[ℝ] ℝ => b u v) h₁.symm
end ThreeManifold.Rechart
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff UpperHalfPlane RealInnerProductSpace
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates WarpedCurvature

def universalMetric (c : ℝ) (hc : c ≠ 0) : Metric (E := EP) UniversalPiece :=
  product hyperbolic (scaleSq (euclidean (V := ℝ)) (fun _ => c) contMDiff_const (fun _ => hc))
lemma universalMetric_apply (c : ℝ) (hc : c ≠ 0) (x : UniversalPiece) (u v : EP) :
    (universalMetric c hc).inner x u v = x.1.im⁻¹^2*inner ℝ u.1 v.1+c^2*u.2*v.2 := by
  apply (productInner_apply hyperbolic
    (scaleSq (euclidean (V := ℝ)) (fun _ => c) contMDiff_const (fun _ => hc)) x u v).trans
  change hyperbolic.inner x.1 u.1 v.1+c^2*inner ℝ u.2 v.2 = _
  have hh := hyperbolic_inner x.1 u.1 v.1
  rw [hh]
  have hi : inner ℝ u.2 v.2 = u.2*v.2 := by simp [mul_comm]
  rw [hi]
  ring

def exponentialRadius (t : ℝ) := Real.exp (-t)
lemma exponentialRadius_smooth : ContDiff ℝ ∞ exponentialRadius := contDiff_id.neg.exp
def hyperbolicWarped (c : ℝ) (hc : c ≠ 0) : SmoothMetric E3 :=
  warpedModel exponentialRadius_smooth hc (fun t => (Real.exp_pos (-t)).ne')
def universalLog : UniversalPiece → E3 := coordinates ∘ logarithmicLift
lemma universalLog_smooth : ContMDiff 𝓘(ℝ,EP) I3 ∞ universalLog :=
  coordinates.contDiff.contMDiff.comp logarithmicLift_smooth
lemma universalLog_deriv (x : UniversalPiece) :
    mfderiv 𝓘(ℝ,EP) I3 universalLog x = coordinates.toContinuousLinearMap.comp (logLinear x.1.im) := by
  have hs : ContMDiff 𝓘(ℝ,P) I3 ∞ coordinates := coordinates.contDiff.contMDiff
  rw [universalLog,mfderiv_comp x
    ((hs _).mdifferentiableAt (by simp))
    ((logarithmicLift_smooth x).mdifferentiableAt (by simp)),logarithmicLift_deriv,
    mfderiv_eq_fderiv,coordinates.hasFDerivAt.fderiv]
  rfl

lemma universalLog_tensor (c : ℝ) (hc : c ≠ 0) (x : UniversalPiece) (u v : EP) :
    (hyperbolicWarped c hc).inner (universalLog x)
      (coordinates (logLinear x.1.im u)) (coordinates (logLinear x.1.im v)) =
    (universalMetric c hc).inner x u v := by
  have hw := warpedModel_apply exponentialRadius_smooth hc
    (fun t => (Real.exp_pos (-t)).ne') (universalLog x)
    (coordinates (logLinear x.1.im u)) (coordinates (logLinear x.1.im v))
  apply hw.trans
  rw [universalMetric_apply]
  change (x.1.im⁻¹*u.1.im)*(x.1.im⁻¹*v.1.im)+
    Real.exp (-Real.log x.1.im)^2*u.1.re*v.1.re+c^2*u.2*v.2 = _
  rw [Real.exp_neg,Real.exp_log x.1.im_pos,Complex.inner]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

lemma universalLog_metric (c : ℝ) (hc : c ≠ 0) (x : UniversalPiece) :
    pullInner (E := EP) (hyperbolicWarped c hc) universalLog x = (universalMetric c hc).inner x := by
  ext u v
  change (hyperbolicWarped c hc).inner (universalLog x)
    ((mfderiv 𝓘(ℝ,EP) I3 universalLog x : EP →L[ℝ] E3) u)
    ((mfderiv 𝓘(ℝ,EP) I3 universalLog x : EP →L[ℝ] E3) v) = _
  rw [universalLog_deriv]
  change (hyperbolicWarped c hc).inner (universalLog x)
    (coordinates (logLinear x.1.im u)) (coordinates (logLinear x.1.im v)) = _
  exact universalLog_tensor c hc x u v

local instance instChartedSpaceE3UniversalPiece : ChartedSpace E3 UniversalPiece := Rechart.charts Coordinates3.coordinates
local instance instIsManifoldRealE3I3SomeENatTopUniversalPiece : IsManifold I3 ∞ UniversalPiece := Rechart.isManifold Coordinates3.coordinates
local instance instChartedSpaceE3WholePiece : ChartedSpace E3 WholePiece := Rechart.charts Coordinates3.coordinates
local instance instIsManifoldRealE3I3SomeENatTopWholePiece : IsManifold I3 ∞ WholePiece := Rechart.isManifold Coordinates3.coordinates

def realUniversalMetric (c : ℝ) (hc : c ≠ 0) : SmoothMetric UniversalPiece :=
  Rechart.realMetric Coordinates3.coordinates (universalMetric c hc)
def realCoreMetric (c : ℝ) (hc : c ≠ 0) : SmoothMetric WholePiece :=
  Rechart.realMetric Coordinates3.coordinates (coreMetric c hc)
def universalLogIsometry (c : ℝ) (hc : c ≠ 0) :
    LocalMetricIsometry (realUniversalMetric c hc) (hyperbolicWarped c hc) universalLog :=
  Rechart.realSourceIsometry Coordinates3.coordinates _ _ _ univ isOpen_univ
    universalLog_smooth.contMDiffOn (fun x _ => universalLog_metric c hc x)
def coreProjectionIsometry (c : ℝ) (hc : c ≠ 0) :
    LocalMetricIsometry (realUniversalMetric c hc) (realCoreMetric c hc) sourceProjection :=
  Rechart.realIsometry Coordinates3.coordinates Coordinates3.coordinates _ _ _ univ isOpen_univ
    sourceProjection_smooth.contMDiffOn (by
      intro x _
      ext u v
      exact (coreMetric_projection c hc x u v).trans (universalMetric_apply c hc x u v).symm)
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise UpperHalfPlane
namespace ThreeManifold.WarpedCurvature
open RiemannianCoordinates Neck
end ThreeManifold.WarpedCurvature
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates
local instance instChartedSpaceE3UniversalPiece_1 : ChartedSpace E3 UniversalPiece := Rechart.charts Coordinates3.coordinates
local instance instIsManifoldRealE3I3SomeENatTopUniversalPiece_1 : IsManifold I3 ∞ UniversalPiece := Rechart.isManifold Coordinates3.coordinates
local instance instChartedSpaceE3WholePiece_1 : ChartedSpace E3 WholePiece := Rechart.charts Coordinates3.coordinates
local instance instIsManifoldRealE3I3SomeENatTopWholePiece_1 : IsManifold I3 ∞ WholePiece := Rechart.isManifold Coordinates3.coordinates
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
local instance instChartedSpaceE3Piece : ChartedSpace E3 Piece := Rechart.charts Coordinates3.coordinates
local instance instIsManifoldRealE3I3SomeENatTopPiece : IsManifold I3 ∞ Piece := Rechart.isManifold Coordinates3.coordinates

def realPieceMetric {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool) : SmoothMetric Piece :=
  Rechart.realMetric Coordinates3.coordinates (pieceMetrics hδ i)

def pieceInclusionIsometry {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool) :
    LocalMetricIsometry (realPieceMetric hδ i) (realCompactMetric hδ) (inclusion i) :=
  Rechart.realIsometry Coordinates3.coordinates Coordinates3.coordinates
    (pieceMetrics hδ i) (compactMetric hδ) (inclusion i) univ isOpen_univ
    (inclusion_smooth i).contMDiffOn (fun x _ => compactMetric_local hδ i x)
end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
variable {M N X : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
  [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {k : SmoothMetric X}
  {f : M → N} {w : N → X}
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric

section
open MetricConstruction CylinderConstruction RiemannianCoordinates
local instance instChartedSpaceE3Cylinder : ChartedSpace E3 Cylinder := Rechart.charts coordinates
local instance instIsManifoldRealE3I3SomeENatTopCylinder : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates

def realNeck {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) : SmoothMetric Cylinder :=
  Rechart.realMetric coordinates (neck hδ hB)
def neckProjectionIsometry {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) :
    LocalMetricIsometry (neckModel hδ hB) (realNeck hδ hB) euclideanProjection :=
  projectionIsometry (radius₁_smooth ⟨hδ.1.le,hδ.2⟩ B) (radius₂_smooth ⟨hδ.1.le,hδ.2⟩ B)
    Cometric.χ_smooth (fun t => (radius₁_pos hδ.1 hB t).ne') (fun t => (radius₂_pos hB t).ne')
def radialIsometry (g : Metric (E := P) Cylinder) {L : ℝ} (hL : 4 ≤ L) :
    LocalMetricIsometry (Rechart.realMetric coordinates (radialPull g hL))
      (Rechart.realMetric coordinates g) (radial L) :=
  Rechart.realIsometry coordinates coordinates _ _ _ univ isOpen_univ
    (radial_smooth L).contMDiffOn (fun _ _ => rfl)
def switchIsometry (g : Metric (E := P) Cylinder) :
    LocalMetricIsometry (Rechart.realMetric coordinates (switched g))
      (Rechart.realMetric coordinates g) switch :=
  Rechart.realIsometry coordinates coordinates _ _ _ univ isOpen_univ
    switch_smooth.contMDiffOn (fun _ _ => rfl)
end

open MetricConstruction CylinderConstruction RiemannianCoordinates

def heightToLog (a : ℝ) (ha : 0 < a) : HeightCylinder a → Cylinder :=
  Subtype.val ∘ logCylinderHomeomorph a ha
lemma heightToLog_smooth (a : ℝ) (ha : 0 < a) :
    ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ (heightToLog a ha) :=
  (contMDiff_subtype_val (U := logDomain a)).comp (logCylinder_smooth a ha)
lemma heightToLog_metric (g : Metric (E := P) Cylinder) (a : ℝ) (ha : 0 < a)
    (x : HeightCylinder a) : pullInner g (heightToLog a ha) x = (heightMetric g a ha).inner x := by
  exact pull_composition g (((logCylinder_smooth a ha) x).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (U := logDomain a) (n := ∞) _).mdifferentiableAt (by simp))

def wholeCuspLog (a : ℝ) (ha : 1 < a) : WholePiece → Cylinder :=
  heightToLog a (by linarith) ∘ cuspChart a ha
lemma cuspChart_source (a : ℝ) (ha : 1 < a) : (cuspChart a ha).source = wholeCusp a := by
  ext x
  simp [cuspChart]
lemma wholeCuspLog_smooth {a : ℝ} (ha : 1 < a) {x : WholePiece} (hx : x ∈ wholeCusp a) :
    ContMDiffAt 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (wholeCuspLog a ha) x := by
  apply ((heightToLog_smooth a (by linarith)) _).comp x
  apply (cuspChart_smooth a ha).contMDiffAt
  rw [cuspChart_source]
  exact (wholeCusp a).isOpen.mem_nhds hx
lemma wholeCuspLog_metric (g : Metric (E := P) Cylinder) {a : ℝ} (ha : 1 < a)
    {x : WholePiece} (hx : x ∈ wholeCusp a) :
    pullInner g (wholeCuspLog a ha) x = (cuspMetric g a ha).inner x := by
  have hs := (cuspChart_smooth a ha).contMDiffAt (by
    rw [cuspChart_source]; exact (wholeCusp a).isOpen.mem_nhds hx)
  rw [wholeCuspLog,pull_composition _ (hs.mdifferentiableAt (by simp))
    (((heightToLog_smooth a (by linarith)) _).mdifferentiableAt (by simp)),heightToLog_metric]
  rfl
local instance instChartedSpaceE3WholePiece_2 : ChartedSpace E3 WholePiece := Rechart.charts Coordinates3.coordinates
local instance instIsManifoldRealE3I3SomeENatTopWholePiece_2 : IsManifold I3 ∞ WholePiece := Rechart.isManifold Coordinates3.coordinates
local instance instChartedSpaceE3Cylinder_1 : ChartedSpace E3 Cylinder := Rechart.charts coordinates
local instance instIsManifoldRealE3I3SomeENatTopCylinder_1 : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates
variable (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
  (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
    pullInner (E := P) g projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)
def wholeCuspIsometry : LocalMetricIsometry
    (Rechart.realMetric Coordinates3.coordinates (wholeMetric g c hc low))
    (Rechart.realMetric coordinates g) (wholeCuspLog cuspLevel cuspLevel_gt) :=
  Rechart.realIsometry Coordinates3.coordinates coordinates _ _ _ (wholeCusp cuspLevel)
    (wholeCusp cuspLevel).isOpen (fun _ hx => (wholeCuspLog_smooth cuspLevel_gt hx).contMDiffWithinAt)
    (fun _ hx => (wholeCuspLog_metric g cuspLevel_gt hx).trans (wholeMetric_cusp g c hc low hx).symm)

def wholeCoreIsometry : LocalMetricIsometry
    (Rechart.realMetric Coordinates3.coordinates (wholeMetric g c hc low))
    (realCoreMetric c hc) id :=
  Rechart.realIsometry Coordinates3.coordinates Coordinates3.coordinates _ _ _ coreRegion coreRegion.isOpen
    contMDiff_id.contMDiffOn (by
      intro x hx
      ext u v
      change (coreMetric c hc).inner x (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) id x u)
        (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) id x v) = _
      rw [mfderiv_id]
      exact congrArg (fun b => b u v) (wholeMetric_core g c hc low hx).symm)
end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates GluedConstruction
local instance instChartedSpaceE3WholePiece_3 : ChartedSpace E3 WholePiece := Rechart.charts Coordinates3.coordinates
local instance instIsManifoldRealE3I3SomeENatTopWholePiece_3 : IsManifold I3 ∞ WholePiece := Rechart.isManifold Coordinates3.coordinates
local instance instChartedSpaceE3Piece_1 : ChartedSpace E3 Piece := Rechart.charts Coordinates3.coordinates
local instance instIsManifoldRealE3I3SomeENatTopPiece_1 : IsManifold I3 ∞ Piece := Rechart.isManifold Coordinates3.coordinates

def pieceMapIsometry (g : Metric (E := EP) WholePiece) :
    LocalMetricIsometry (Rechart.realMetric Coordinates3.coordinates (pieceMetric g))
      (Rechart.realMetric Coordinates3.coordinates g) pieceMap :=
  Rechart.realIsometry Coordinates3.coordinates Coordinates3.coordinates _ _ _ univ isOpen_univ
    pieceMap_smooth.contMDiffOn (fun _ _ => rfl)
def openNeck : Set GluedConstruction.Manifold := inclusion false '' (collar : Set Piece)
end ThreeManifold.CompactMetric

end

end OAI


