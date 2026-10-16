-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
-- name    : OAI_Geometry_ConjugatePoints_Distance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:11:00.953438+00:00
-- url     : https://prove2.me/theorems/d6e95271-4e9c-49bb-bc58-30e64173a998
-- title:
--   Riemannian distance on the universal cover $\mathbb{R}^3$ of a nonpositively curved compact 3-manifold and its midpoint inequality
-- statement:
--   This file equips the domain $\mathbb{R}^3$ of the exponential map of a compact nonpositively curved three-manifold with the pulled-back Riemannian distance, shows that deck transformations and changes of base point act by isometries, and proves the midpoint (CN) inequality for midpoints of radial segments.
--
--   **Notation.** For a real normed space $E$ and a continuous Riemannian metric $g$ on $E$ (an inner product $g_x$ on each tangent space $T_xE = E$, depending continuously on $x$), the *length* of a $C^1$ path $\gamma$ is $\int \sqrt{g_{\gamma(t)}(\dot\gamma, \dot\gamma)}\,dt$ and the *Riemannian distance* $d_g(x, y)$ is the infimum of lengths of $C^1$ paths $[0,1] \to E$ from $x$ to $y$. $M$ is a compact Hausdorff smooth manifold modelled on $\mathbb{R}^3$ with smooth metric $g$ of nonpositive sectional curvature, and $\exp_p : \mathbb{R}^3 \to M$ is its exponential map at $p$.
--
--   The file contains:
--
--   1. **Riemannian distance on a normed space.** $d_g$ is finite (since $E$ is connected) and makes $E$ a metric space. A $C^1$ map $f : E \to F$ with $g^F_{f(x)}(df_x u, df_x v) = g_x(u, v)$ preserves lengths of $C^1$ paths and satisfies $d_{g^F}(f(x), f(y)) \le d_g(x, y)$; a bijection $f$ with $f, f^{-1}$ both $C^1$ and both preserving the metrics is an isometry of the distances.
--
--   2. **Lower bounds for the distance.** If a linear functional $L$ satisfies $|L(v)| \le \sqrt{g_x(v, v)}$ for all $x, v$, then $|L(y - x)| \le d_g(x, y)$. If $B$ is a symmetric positive-definite bilinear form with $B(v, v) \le g_x(v, v)$ for all $x, v$, then
--   $$
--   \sqrt{B(y - x,\, y - x)} \le d_g(x, y).
--   $$
--
--   3. **The pulled-back metric and its distance.** The pullback of a smooth metric along a $C^1$ map whose differentials are linear isomorphisms is a continuous Riemannian metric. Since $d(\exp_p)_v$ is injective, $\tilde g^p = \exp_p^* g$, i.e. $\tilde g^p_v(a, b) = g_{\exp_p v}\big(d(\exp_p)_v a,\ d(\exp_p)_v b\big)$, is a continuous Riemannian metric on $\mathbb{R}^3$, and it is expanding: $g_p(b, b) \le \tilde g^p_v(b, b)$. Let $D_p = d_{\tilde g^p}$ be its Riemannian distance on $\mathbb{R}^3$.
--
--   4. **Deck transformations.** For a map $\varpi : E \to X$ of topological spaces, $\operatorname{Deck}(\varpi)$ is the group of homeomorphisms $d$ of $E$ with $\varpi \circ d = \varpi$, acting on $E$. If $\varpi$ is a covering map: two deck transformations agreeing at one point are equal ($E$ preconnected); $\varpi$ is surjective ($E$ nonempty, $X$ path-connected); if $E$ is simply connected and locally path-connected, any two points of a fibre are related by a deck transformation; and if moreover $X$ is path-connected, $\varpi$ is a quotient covering map for $\operatorname{Deck}(\varpi)$ and $\pi_1(X, \varpi(z)) \cong \operatorname{Deck}(\varpi)^{\mathrm{op}}$. Two such universal coverings $E \to X$, $F \to X$ with $\varpi(a) = \varpi'(b)$ are related by a homeomorphism $e$ with $e(a) = b$ and $\varpi' \circ e = \varpi$.
--
--   5. **Isometries of $D_p$.** Continuous lifts of $C^1$ maps through $\exp_p$ are $C^1$. Every deck transformation of $\exp_p$ is $C^1$, preserves $\tilde g^p$, and is an isometry of $D_p$. If $\exp_p(a) = \exp_q(b)$, there is a homeomorphism $e$ of $\mathbb{R}^3$ with $e(a) = b$, $\exp_q \circ e = \exp_p$, $e$ and $e^{-1}$ of class $C^1$, and $e$ an isometry from $D_p$ to $D_q$.
--
--   6. **Radial geometry and the CN inequality.** The geodesic $\gamma = \gamma_{(p,v)}$ with initial point $p$ and velocity $v$ satisfies $g(\dot\gamma(t), \dot\gamma(t)) = g_p(v, v)$ for all $t$; $\tilde g^p_{tv}(v, v) = g_p(v, v)$, and the radial path $r \mapsto rv$ on $[a, b]$ has length $\sqrt{g_p(v, v)}\,\max(b - a, 0)$; $\sqrt{g_p(y - x, y - x)} \le D_p(x, y)$ and $D_p(0, v) = \sqrt{g_p(v, v)}$. Recentering along a geodesic, $\exp_{\gamma(t)}\big(s\,\dot\gamma(t)\big) = \exp_p\big((t + s)v\big)$ for $\gamma = \gamma_{(p,v)}$. Finally, for all $v, z \in \mathbb{R}^3$,
--   $$
--   D_p\big(\tfrac12 v,\ z\big)^2 \le \frac{D_p(0, z)^2 + D_p(v, z)^2}{2} - \frac{D_p(0, v)^2}{4}.
--   $$
--
--   The last inequality, transported by the base-point-changing isometries of item 5, shows that $(\mathbb{R}^3, D_p)$ admits midpoints satisfying the CN inequality, and the deck group acts on it by isometries; this is the metric input for the group-theoretic obstruction to nonpositively curved metrics.
--
--   **Formalization Note** Continuous Riemannian metrics are Mathlib's `ContinuousRiemannianMetric`, distances are built from `riemannianEDist` via `EMetricSpace.toMetricSpace` (`RiemannianDistance.metricSpace`), and $D_p$ is `universalMetric g hn p`, an alternative `MetricSpace` structure on `E3` that is passed explicitly with `@`. The deck group is a subgroup of `Equiv.Perm E`, and the fundamental-group isomorphism goes to its opposite group. `exponentialTangentEquiv` packages $d(\exp_p)_v$ as a linear isomorphism using injectivity; some continuity lemmas for bilinear maps are plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Distance.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Distance.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation

namespace OAI

noncomputable section

/-!
# Riemannian distance and the nonpositively curved universal-cover metric.
-/

section
open Set Filter Topology Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace ThreeManifold.RiemannianDistance

section

lemma edist_finite_of_preconnected {X : Type*} [PseudoEMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  let S := {z : X | edist x z ≠ ⊤}
  have hopen : IsOpen S := by
    apply EMetric.isOpen_iff.mpr
    intro z hz
    refine ⟨1,by norm_num,fun w hw => ?_⟩
    have hwz : edist z w ≠ ⊤ := ne_top_of_lt (by simpa only [edist_comm] using (Metric.mem_eball.mp hw))
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hz,hwz⟩) (edist_triangle x z w)
  have hcomp : IsOpen Sᶜ := by
    apply EMetric.isOpen_iff.mpr
    intro z hz
    refine ⟨1,by norm_num,fun w hw => ?_⟩
    intro hwS
    have hwz : edist w z ≠ ⊤ := ne_top_of_lt (Metric.mem_eball.mp hw)
    exact hz (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hwS,hwz⟩) (edist_triangle x w z))
  have he : S = univ := (show IsClopen S from ⟨by simpa only [compl_compl] using hcomp.isClosed_compl,hopen⟩).eq_univ
    ⟨x,by simp [S]⟩
  have : y ∈ S := he ▸ mem_univ y
  exact this

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "I" => 𝓘(ℝ,E)

abbrev metricSpace (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _)) : MetricSpace E :=
  letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  letI : EMetricSpace E := .ofRiemannianMetric I E
  EMetricSpace.toMetricSpace (edist_finite_of_preconnected)

variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

lemma tangent_enorm (x : E) (v : TangentSpace 𝓘(ℝ,E) x) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  rw [← ofReal_norm,norm_eq_sqrt_real_inner]
  rfl

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

lemma pathELength_comp_eq {f : E → E} (hf : ContDiff ℝ 1 f)
    (hi : ∀ (x u v : E), g.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    {γ : ℝ → E} {a b : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc a b)) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    pathELength 𝓘(ℝ,E) (f ∘ γ) a b = pathELength 𝓘(ℝ,E) γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  simp only [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hγt := (hγ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by simp)
  dsimp only
  rw [tangent_enorm g,tangent_enorm g]
  have hv : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (f ∘ γ) t 1 : E) =
      fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E) := by
    rw [mfderiv_eq_fderiv,mfderiv_eq_fderiv,fderiv_comp t
      (hf.differentiable (by simp) (γ t)) hγt]
    rfl
  apply congrArg (ENNReal.ofReal ∘ Real.sqrt)
  calc
    _ = g.inner (f (γ t))
        (fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E))
        (fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E)) :=
      congrArg₂ (fun u v : E => g.inner (f (γ t)) u v) hv hv
    _ = _ := hi _ _ _

lemma riemannianEDist_map_le {f : E → E} (hf : ContDiff ℝ 1 f)
    (hi : ∀ (x u v : E), g.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    (x y : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    riemannianEDist 𝓘(ℝ,E) (f x) (f y) ≤ riemannianEDist 𝓘(ℝ,E) x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ,h0,h1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hc := hf.contMDiff.comp_contMDiffOn hγ
  have hl := riemannianEDist_le_pathELength (I := 𝓘(ℝ,E)) hc rfl rfl (by norm_num : (0:ℝ) ≤ 1)
  simp only [Function.comp_apply,h0,h1] at hl
  rw [pathELength_comp_eq g hf hi (contMDiffOn_iff_contDiffOn.mp hγ)] at hl
  exact hl.trans_lt hlen

theorem isometry_of_inner (f : E ≃ E) (hf : ContDiff ℝ 1 f) (hfi : ContDiff ℝ 1 f.symm)
    (hi : ∀ (x u v : E), g.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    (hii : ∀ (x u v : E), g.inner (f.symm x) (fderiv ℝ f.symm x u) (fderiv ℝ f.symm x v) = g.inner x u v) :
    @Isometry E E (metricSpace g).toPseudoEMetricSpace (metricSpace g).toPseudoEMetricSpace f := by
  have hle := riemannianEDist_map_le g hf hi
  have hlei := riemannianEDist_map_le g hfi hii
  let : MetricSpace E := metricSpace g
  intro x y
  apply le_antisymm (hle x y)
  simpa only [Equiv.symm_apply_apply] using hlei (f x) (f y)
end ThreeManifold.RiemannianDistance
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.MetricConstruction
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
lemma flip_contAt {X G A B C : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace G] [ChartedSpace X G]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : G → A →L[ℝ] B →L[ℝ] C} {x : G}
    (hf : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,A →L[ℝ] B →L[ℝ] C) 0 f x) :
    ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,B →L[ℝ] A →L[ℝ] C) 0 (fun y => (f y).flip) x := by
  let : NormedAddCommGroup (B →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (B →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (A →L[ℝ] B →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (A →L[ℝ] B →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (A →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (A →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (B →L[ℝ] A →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (B →L[ℝ] A →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  have hc : ContDiff ℝ 0 (fun L : A →L[ℝ] B →L[ℝ] C => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ A B C).toContinuousLinearEquiv.contDiff
  exact hc.comp_contMDiffAt hf

lemma bilin_comp_contAt {X G H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace G] [ChartedSpace X G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {q : G → F →L[ℝ] F →L[ℝ] ℝ} {L : G → H →L[ℝ] F} {x : G}
    (hq : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,F →L[ℝ] F →L[ℝ] ℝ) 0 q x)
    (hL : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,H →L[ℝ] F) 0 L x) :
    ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,H →L[ℝ] H →L[ℝ] ℝ) 0
      (fun y => (q y).bilinearComp (L y) (L y)) x := by
  exact flip_contAt ((flip_contAt (hq.clm_comp hL)).clm_comp hL)

lemma pullback_inner_contAt (g : Metric (E := F) N) {f : M → N}
    {x : M} (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f x) :
    ContMDiffAt 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace 𝓘(ℝ,E) y →L[ℝ] TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ)
        x (pullInner g f x)) x := by
  rw [contMDiffAt_section]
  have hg := g.contMDiff (f x)
  rw [contMDiffAt_section] at hg
  simp only [hom_trivializationAt_apply] at hg ⊢
  have hgc := (hg.of_le (show (0:ℕ∞ω) ≤ ∞ by simp)).comp x (hf.of_le (by simp))
  have hL := hf.mfderiv_const (m := 0) (by simp)
  apply (bilin_comp_contAt hgc hL).congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace 𝓘(ℝ,E)) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ,E)) x),
    hf.continuousAt
      ((trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x)))] with y hy hy'
  exact pullback_coordinates g f x y hy hy'

def continuousPullback (g : Metric (E := F) N) {f : M → N}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f)
    (e : ∀ x, TangentSpace 𝓘(ℝ,E) x ≃L[ℝ] TangentSpace 𝓘(ℝ,F) (f x))
    (he : ∀ x, (e x : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,F) (f x)) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x) :
    ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : M → Type _) where
  inner x := pullInner g f x
  symm x u v := g.symm (f x) _ _
  pos x u hu := by
    rw [pullInner_apply,← he]
    apply g.pos
    intro hh
    apply hu
    apply (e x).injective
    rw [(e x).map_zero]
    exact hh
  isVonNBounded x := by
    have hb := (g.isVonNBounded (f x)).image (e x).symm.toContinuousLinearMap
    apply hb.subset
    intro u hu
    refine ⟨e x u,?_,by simp⟩
    change g.inner (f x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x u)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x u) < 1 at hu
    rw [← he] at hu
    exact hu
  continuous := continuous_iff_continuousAt.mpr (fun x => (pullback_inner_contAt g (hf x)).continuousAt)
end ThreeManifold.MetricConstruction

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

def exponentialTangentEquiv (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) : E3 ≃L[ℝ] TangentSpace I3 (exponential g p v) :=
  (LinearEquiv.ofInjectiveEndo (show E3 →ₗ[ℝ] E3 from
    (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v).toLinearMap)
      (exponential_mfderiv_injective g (npc_noConjugatePoints g hn) p v)).toContinuousLinearEquiv

def exponentialMetric (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M) :
    ContinuousRiemannianMetric E3 (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
  MetricConstruction.continuousPullback g (exponential_contMDiff g p)
    (exponentialTangentEquiv g hn p) (fun _ => rfl)

lemma exponentialMetric_inner (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v a b : E3) :
    (exponentialMetric g hn p).inner v a b = g.inner (exponential g p v)
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v a)
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v b) := rfl

lemma exponentialMetric_expanding (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v b : E3) :
    g.inner p b b ≤ (exponentialMetric g hn p).inner v b b :=
  npc_exponential_differential_expanding g hn p v b
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology
namespace ThreeManifold.UniversalDeck
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

def group (p : E → X) : Subgroup (Equiv.Perm E) where
  carrier := {d | Continuous d ∧ Continuous d.symm ∧ ∀ z, p (d z) = p z}
  one_mem' := ⟨continuous_id,continuous_id,fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha,hai,hap⟩ ⟨hb,hbi,hbp⟩
    exact ⟨ha.comp hb,hbi.comp hai,fun z => (hap (b z)).trans (hbp z)⟩
  inv_mem' := by
    rintro a ⟨ha,hai,hap⟩
    refine ⟨hai,ha,fun z => ?_⟩
    simpa using (hap (a.symm z)).symm

instance deckAction : MulAction (group p) E where
  smul d z := d.val z
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
instance deckContinuous : ContinuousConstSMul (group p) E :=
  ⟨fun d => d.property.1⟩
lemma map_smul (d : group p) (z : E) : p (d • z) = p z := by
  let _ : TopologicalSpace X := inferInstance
  exact d.property.2.2 z

lemma deck_ext [PreconnectedSpace E] (hp : IsCoveringMap p)
    {a b : group p} {z : E} (h : a • z = b • z) : a = b := by
  apply Subtype.ext
  apply Equiv.ext
  exact congr_fun (hp.eq_of_comp_eq a.property.1 b.property.1
    (funext (fun w => (map_smul a w).trans (map_smul b w).symm)) z h)

lemma covering_surjective [Nonempty E] [PathConnectedSpace X] (hp : IsCoveringMap p) :
    Function.Surjective p := by
  let e : E := Classical.choice inferInstance
  intro y
  let γ := PathConnectedSpace.somePath (p e) y
  obtain ⟨v,hv,hv0⟩ := hp.exists_path_lifts γ.toContinuousMap e γ.source
  exact ⟨v 1,(congr_fun hv 1).trans γ.target⟩

variable [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]

lemma exists_deck (hp : IsCoveringMap p) {a b : E} (hab : p a = p b) :
    ∃ d : group p, d • a = b := by
  obtain ⟨f,⟨hfa,hfp⟩,_⟩ := hp.existsUnique_continuousMap_lifts
    ⟨p,hp.continuous⟩ a b hab.symm
  obtain ⟨g,⟨hgb,hgp⟩,_⟩ := hp.existsUnique_continuousMap_lifts
    ⟨p,hp.continuous⟩ b a hab
  have hfg : Function.RightInverse g f := by
    have he : f ∘ g = id := hp.eq_of_comp_eq
      (f.continuous.comp g.continuous) continuous_id
      (funext (fun z => (congr_fun hfp (g z)).trans (congr_fun hgp z))) b (by simp [hgb,hfa])
    exact congr_fun he
  have hgf : Function.LeftInverse g f := by
    have he : g ∘ f = id := hp.eq_of_comp_eq
      (g.continuous.comp f.continuous) continuous_id
      (funext (fun z => (congr_fun hgp (f z)).trans (congr_fun hfp z))) a (by simp [hfa,hgb])
    exact congr_fun he
  let d : Equiv.Perm E := ⟨f,g,hgf,hfg⟩
  exact ⟨⟨d,f.continuous,g.continuous,fun z => congr_fun hfp z⟩,hfa⟩

theorem quotient_cover [PathConnectedSpace X] (hp : IsCoveringMap p) :
    IsQuotientCoveringMap p (group p) := by
  refine {
    toIsQuotientMap := hp.isQuotientMap (covering_surjective hp)
    continuous_const_smul := fun d => d.property.1
    apply_eq_iff_mem_orbit := ?_
    disjoint := ?_ }
  · intro a b
    constructor
    · intro h
      obtain ⟨d,hd⟩ := exists_deck hp h.symm
      exact ⟨d,hd⟩
    · rintro ⟨d,rfl⟩
      exact map_smul d b
  · intro z
    obtain ⟨U,hU,hz,hi⟩ := hp.isLocalHomeomorph.isLocallyInjective z
    refine ⟨U,hU.mem_nhds hz,?_⟩
    rintro d ⟨w,⟨y,hy,rfl⟩,hdy⟩
    apply deck_ext hp (z := y)
    exact hi hdy hy (map_smul d y)

def fundamentalGroupEquiv [PathConnectedSpace X] (hp : IsCoveringMap p) (z : E) :
    FundamentalGroup X (p z) ≃* (group p)ᵐᵒᵖ :=
  (quotient_cover hp).fundamentalGroupEquiv ⟨z,rfl⟩
end ThreeManifold.UniversalDeck
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma lift_contDiff {f : E3 → M} (hf : ContMDiff 𝓘(ℝ,E3) I3 1 f)
    (hi : ∀ a, Function.Injective (mfderiv 𝓘(ℝ,E3) I3 f a))
    (hl : IsLocalHomeomorph f) {d : E3 → E3} (hd : Continuous d)
    (he : ∀ x, f (d x) = f x) : ContDiff ℝ 1 d := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let i := hl.localInverseAt (d x)
  have hic := localInverseAt_contMDiffAt hf hi hl (d x)
  rw [he x] at hic
  have heq : d =ᶠ[𝓝 x] fun z => i (f z) := by
    filter_upwards [hd.continuousAt.preimage_mem_nhds
      (i.open_target.mem_nhds hl.self_mem_localInverseAt_target)] with z hz
    have hh := i.right_inv hz
    rw [hl.localInverseAt_symm,he z] at hh
    exact hh.symm
  exact (contMDiffAt_iff_contDiffAt.mp (hic.comp x hf.contMDiffAt)).congr_of_eventuallyEq heq

variable [CompactSpace M] [T2Space M]
lemma exponentialDeck_contDiff (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (d : UniversalDeck.group (exponential g p)) : ContDiff ℝ 1 (fun v : E3 => d • v) :=
  lift_contDiff (exponential_contMDiff g p)
    (exponential_mfderiv_injective g (npc_noConjugatePoints g hn) p)
    (npc_exponential_isLocalHomeomorph g hn p) d.property.1 (UniversalDeck.map_smul d)

lemma exponentialDeck_inner (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (d : UniversalDeck.group (exponential g p)) (x u v : E3) :
    (exponentialMetric g hn p).inner (d • x)
      (fderiv ℝ (fun z => d • z) x u) (fderiv ℝ (fun z => d • z) x v) =
    (exponentialMetric g hn p).inner x u v := by
  have hd := (exponentialDeck_contDiff g hn p d).differentiable (by simp)
  have heq : (exponential g p) ∘ (fun z => d • z) = exponential g p :=
    funext (UniversalDeck.map_smul d)
  have hdif := mfderiv_comp x ((exponential_contMDiff g p).mdifferentiable (by simp) (d • x))
    ((exponentialDeck_contDiff g hn p d).contMDiff.mdifferentiable (by simp) x)
  rw [heq,mfderiv_eq_fderiv] at hdif
  have hu := congrArg (fun L : E3 →L[ℝ] E3 => L u) hdif
  have hv := congrArg (fun L : E3 →L[ℝ] E3 => L v) hdif
  change mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u =
    mfderiv 𝓘(ℝ,E3) I3 (exponential g p) (d • x) (fderiv ℝ (fun z => d • z) x u) at hu
  change mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v =
    mfderiv 𝓘(ℝ,E3) I3 (exponential g p) (d • x) (fderiv ℝ (fun z => d • z) x v) at hv
  change g.inner (exponential g p (d • x)) _ _ = g.inner (exponential g p x) _ _
  calc
    _ = g.inner (exponential g p (d • x))
        (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u)
        (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v) :=
      congrArg₂ (fun a b : E3 => g.inner (exponential g p (d • x)) a b) hu.symm hv.symm
    _ = _ := congrArg (fun z : M => g.inner z
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u : E3)
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v : E3)) (UniversalDeck.map_smul d x)
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology
namespace ThreeManifold.QuotientCoverGeometry
variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G] [MulAction G E]
variable {p : E → X} (hp : IsQuotientCoveringMap p G)
include hp

end ThreeManifold.QuotientCoverGeometry
end

section

open Set Metric

namespace ThreeManifold.NoNPC

section Attainment
variable {G X : Type*} [Group G] [MetricSpace X] [ProperSpace X]
  [MulAction G X] [IsIsometricSMul G X] [ProperlyDiscontinuousSMul G X]

end Attainment

section ProductShift

end ProductShift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end ThreeManifold.NoNPC
end

section
open Set Filter Topology Bundle Manifold
open scoped ContDiff NNReal
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

abbrev universalMetric (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M) : MetricSpace E3 :=
  RiemannianDistance.metricSpace (exponentialMetric g hn p)

lemma universalMetric_deck_isometry (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (d : UniversalDeck.group (exponential g p)) :
    @Isometry E3 E3 (universalMetric g hn p).toPseudoEMetricSpace
      (universalMetric g hn p).toPseudoEMetricSpace (fun x => d • x) :=
  RiemannianDistance.isometry_of_inner (exponentialMetric g hn p) d.val
    (exponentialDeck_contDiff g hn p d) (exponentialDeck_contDiff g hn p d⁻¹)
    (exponentialDeck_inner g hn p d) (exponentialDeck_inner g hn p d⁻¹)

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace ThreeManifold.RiemannianDistance
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (h : ContinuousRiemannianMetric F (TangentSpace 𝓘(ℝ,F) : F → Type _))
variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

lemma pathELength_comp_eq_between {f : E → F} (hf : ContDiff ℝ 1 f)
    (hi : ∀ (x u v : E), h.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    {γ : ℝ → E} {a b : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc a b)) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,F) : F → Type _) := ⟨h.toRiemannianMetric⟩
    pathELength 𝓘(ℝ,F) (f ∘ γ) a b = pathELength 𝓘(ℝ,E) γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,F) : F → Type _) := ⟨h.toRiemannianMetric⟩
  simp only [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hγt := (hγ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by simp)
  dsimp only
  rw [tangent_enorm h,tangent_enorm g]
  have hv : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F) (f ∘ γ) t 1 : F) =
      fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E) := by
    rw [mfderiv_eq_fderiv,mfderiv_eq_fderiv,fderiv_comp t
      (hf.differentiable (by simp) (γ t)) hγt]
    rfl
  apply congrArg (ENNReal.ofReal ∘ Real.sqrt)
  calc
    _ = h.inner (f (γ t))
        (fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E))
        (fderiv ℝ f (γ t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E)) :=
      congrArg₂ (fun u v : F => h.inner (f (γ t)) u v) hv hv
    _ = _ := hi _ _ _

lemma riemannianEDist_map_le_between {f : E → F} (hf : ContDiff ℝ 1 f)
    (hi : ∀ (x u v : E), h.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    (x y : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,F) : F → Type _) := ⟨h.toRiemannianMetric⟩
    riemannianEDist 𝓘(ℝ,F) (f x) (f y) ≤ riemannianEDist 𝓘(ℝ,E) x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,F) : F → Type _) := ⟨h.toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ,h0,h1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hc := hf.contMDiff.comp_contMDiffOn hγ
  have hl := riemannianEDist_le_pathELength (I := 𝓘(ℝ,F)) hc rfl rfl (by norm_num : (0:ℝ) ≤ 1)
  simp only [Function.comp_apply,h0,h1] at hl
  rw [pathELength_comp_eq_between h g hf hi (contMDiffOn_iff_contDiffOn.mp hγ)] at hl
  exact hl.trans_lt hlen

theorem isometry_between (f : E ≃ F) (hf : ContDiff ℝ 1 f) (hfi : ContDiff ℝ 1 f.symm)
    (hi : ∀ (x u v : E), h.inner (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) = g.inner x u v)
    (hii : ∀ (x u v : F), g.inner (f.symm x) (fderiv ℝ f.symm x u) (fderiv ℝ f.symm x v) = h.inner x u v) :
    @Isometry E F (metricSpace g).toPseudoEMetricSpace (metricSpace h).toPseudoEMetricSpace f := by
  have hle := riemannianEDist_map_le_between h g hf hi
  have hlei := riemannianEDist_map_le_between g h hfi hii
  intro x y
  apply le_antisymm (hle x y)
  simpa only [Equiv.symm_apply_apply] using hlei (f x) (f y)
end ThreeManifold.RiemannianDistance
end

section
open Set Filter Topology
namespace ThreeManifold.UniversalCover
variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
  [SimplyConnectedSpace F] [LocallyPathConnectedSpace F]
  {p : E → X} {q : F → X}

theorem exists_based_homeomorph (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (a : E) (b : F) (hab : p a = q b) :
    ∃ e : E ≃ₜ F, e a = b ∧ ∀ z, q (e z) = p z := by
  obtain ⟨f,⟨hfa,hfp⟩,_⟩ := hq.existsUnique_continuousMap_lifts ⟨p,hp.continuous⟩ a b hab.symm
  obtain ⟨g,⟨hgb,hgp⟩,_⟩ := hp.existsUnique_continuousMap_lifts ⟨q,hq.continuous⟩ b a hab
  have hfg : Function.RightInverse g f := by
    have he : f ∘ g = id := hq.eq_of_comp_eq (f.continuous.comp g.continuous) continuous_id
      (funext (fun z => (congr_fun hfp (g z)).trans (congr_fun hgp z))) b (by simp [hgb,hfa])
    exact congr_fun he
  have hgf : Function.LeftInverse g f := by
    have he : g ∘ f = id := hp.eq_of_comp_eq (g.continuous.comp f.continuous) continuous_id
      (funext (fun z => (congr_fun hgp (f z)).trans (congr_fun hfp z))) a (by simp [hfa,hgb])
    exact congr_fun he
  exact ⟨⟨⟨f,g,hgf,hfg⟩,f.continuous,g.continuous⟩,hfa,fun z => congr_fun hfp z⟩
end ThreeManifold.UniversalCover
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma lift_map_contDiff {f k : E3 → M} (hf : ContMDiff 𝓘(ℝ,E3) I3 1 f)
    (hk : ContMDiff 𝓘(ℝ,E3) I3 1 k)
    (hi : ∀ a, Function.Injective (mfderiv 𝓘(ℝ,E3) I3 f a))
    (hl : IsLocalHomeomorph f) {d : E3 → E3} (hd : Continuous d)
    (he : ∀ x, f (d x) = k x) : ContDiff ℝ 1 d := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let i := hl.localInverseAt (d x)
  have hic := localInverseAt_contMDiffAt hf hi hl (d x)
  rw [he x] at hic
  have heq : d =ᶠ[𝓝 x] fun z => i (k z) := by
    filter_upwards [hd.continuousAt.preimage_mem_nhds
      (i.open_target.mem_nhds hl.self_mem_localInverseAt_target)] with z hz
    have hh := i.right_inv hz
    rw [hl.localInverseAt_symm,he z] at hh
    exact hh.symm
  exact (contMDiffAt_iff_contDiffAt.mp (hic.comp x hk.contMDiffAt)).congr_of_eventuallyEq heq

variable [CompactSpace M] [T2Space M]
lemma exponentialChange_contDiff (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    {p q : M} {e : E3 → E3} (hc : Continuous e)
    (he : ∀ v, exponential g q (e v) = exponential g p v) : ContDiff ℝ 1 e :=
  lift_map_contDiff (exponential_contMDiff g q) (exponential_contMDiff g p)
    (exponential_mfderiv_injective g (npc_noConjugatePoints g hn) q)
    (npc_exponential_isLocalHomeomorph g hn q) hc he

lemma exponentialChange_inner (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    {p q : M} {e : E3 → E3} (hc : Continuous e)
    (he : ∀ v, exponential g q (e v) = exponential g p v) (x u v : E3) :
    (exponentialMetric g hn q).inner (e x) (fderiv ℝ e x u) (fderiv ℝ e x v) =
      (exponentialMetric g hn p).inner x u v := by
  have heq : exponential g q ∘ e = exponential g p := funext he
  have hdif := mfderiv_comp x ((exponential_contMDiff g q).mdifferentiable (by simp) (e x))
    ((exponentialChange_contDiff g hn hc he).contMDiff.mdifferentiable (by simp) x)
  rw [heq,mfderiv_eq_fderiv] at hdif
  have hu := congrArg (fun L : E3 →L[ℝ] E3 => L u) hdif
  have hv := congrArg (fun L : E3 →L[ℝ] E3 => L v) hdif
  change mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u =
    mfderiv 𝓘(ℝ,E3) I3 (exponential g q) (e x) (fderiv ℝ e x u) at hu
  change mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v =
    mfderiv 𝓘(ℝ,E3) I3 (exponential g q) (e x) (fderiv ℝ e x v) at hv
  change g.inner (exponential g q (e x)) _ _ = g.inner (exponential g p x) _ _
  calc
    _ = g.inner (exponential g q (e x))
        (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u)
        (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v) :=
      congrArg₂ (fun a b : E3 => g.inner (exponential g q (e x)) a b) hu.symm hv.symm
    _ = _ := congrArg (fun z : M => g.inner z
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x u : E3)
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) x v : E3)) (he x)

theorem exists_exponential_coordinates (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    {p q : M} (a b : E3) (hab : exponential g p a = exponential g q b) :
    ∃ e : E3 ≃ₜ E3, e a = b ∧ (∀ z, exponential g q (e z) = exponential g p z) ∧
      ContDiff ℝ 1 e ∧ ContDiff ℝ 1 e.symm ∧
      @Isometry E3 E3 (universalMetric g hn p).toPseudoEMetricSpace
        (universalMetric g hn q).toPseudoEMetricSpace e := by
  obtain ⟨e,hea,he⟩ := UniversalCover.exists_based_homeomorph
    (npc_exponential_isCoveringMap g hn p) (npc_exponential_isCoveringMap g hn q) a b hab
  have hei (z : E3) : exponential g p (e.symm z) = exponential g q z := by
    simpa only [e.apply_symm_apply] using (he (e.symm z)).symm
  have hc := exponentialChange_contDiff g hn e.continuous he
  have hci := exponentialChange_contDiff g hn e.symm.continuous hei
  refine ⟨e,hea,he,hc,hci,?_⟩
  exact RiemannianDistance.isometry_between (exponentialMetric g hn q) (exponentialMetric g hn p)
    e.toEquiv hc hci (exponentialChange_inner g hn e.continuous he)
      (exponentialChange_inner g hn e.symm.continuous hei)
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace ThreeManifold.RiemannianDistance
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

lemma functional_le_pathELength (L : E →L[ℝ] ℝ)
    (hL : ∀ (x v : E), |L v| ≤ Real.sqrt (g.inner x v v))
    {γ : ℝ → E} {a b : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc a b)) (hab : a ≤ b) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal |L (γ b-γ a)| ≤ pathELength 𝓘(ℝ,E) γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (L.contDiff.comp_contDiffOn hγ) hab
  simp only [Function.comp_apply,← L.map_sub,← ofReal_norm,Real.norm_eq_abs] at h
  apply h.trans
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume)).symm]
  apply setLIntegral_mono' measurableSet_Ioo
  intro t ht
  have htγ := (hγ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by simp)
  have hd := L.hasFDerivAt.comp t htγ.hasDerivAt.hasFDerivAt
  have he : deriv (L ∘ γ) t = L (deriv γ t) := by
    rw [hd.hasDerivAt.deriv]
    simp
  have hv : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E) = deriv γ t := by
    rw [mfderiv_eq_fderiv]
    rfl
  rw [tangent_enorm g]
  rw [congrArg (fun v : E => g.inner (γ t) v v) hv,he]
  exact ENNReal.ofReal_le_ofReal (hL (γ t) (deriv γ t))

lemma functional_le_riemannianEDist (L : E →L[ℝ] ℝ)
    (hL : ∀ (x v : E), |L v| ≤ Real.sqrt (g.inner x v v)) (x y : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal |L (y-x)| ≤ riemannianEDist 𝓘(ℝ,E) x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ,h0,h1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hb := functional_le_pathELength g L hL (contMDiffOn_iff_contDiffOn.mp hγ) (by norm_num : (0:ℝ) ≤ 1)
  rw [h0,h1] at hb
  exact hb.trans_lt hlen

lemma positive_bilinear_cauchy_schwarz (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v, 0 ≤ B v v) (v w : E) :
    B v w ^ 2 ≤ B v v * B w w := by
  have h (t : ℝ) := hp (v + t • w)
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,
    smul_eq_mul] at h
  rw [hs w v] at h
  have hd := discrim_le_zero (a := B w w) (b := 2*B v w) (c := B v v)
    (fun t => by nlinarith only [h t])
  unfold discrim at hd
  nlinarith only [hd]

theorem bilinear_le_riemannianEDist (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v ≠ 0, 0 < B v v)
    (hB : ∀ (x v : E), B v v ≤ g.inner x v v) (x y : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal (Real.sqrt (B (y-x) (y-x))) ≤ riemannianEDist 𝓘(ℝ,E) x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  by_cases he : y-x = 0
  · simp [he]
  have hpn (v : E) : 0 ≤ B v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hp v hv).le
  let d := y-x
  let c := Real.sqrt (B d d)
  have hc : 0 < c := Real.sqrt_pos.mpr (hp d he)
  have hc2 : c^2 = B d d := Real.sq_sqrt (hpn d)
  let L : E →L[ℝ] ℝ := c⁻¹ • B d
  have hL (z v : E) : |L v| ≤ Real.sqrt (g.inner z v v) := by
    have hcs := positive_bilinear_cauchy_schwarz B hs hpn d v
    have hg : 0 ≤ g.inner z v v := (hpn v).trans (hB z v)
    have hh := mul_le_mul_of_nonneg_left (hB z v) (hpn d)
    have hsq := Real.sq_sqrt hg
    change |c⁻¹ * B d v| ≤ _
    rw [abs_mul,abs_of_pos (inv_pos.mpr hc)]
    apply (inv_mul_le_iff₀ hc).mpr
    have hab : |B d v|^2 = B d v^2 := sq_abs _
    nlinarith [abs_nonneg (B d v),Real.sqrt_nonneg (g.inner z v v),
      mul_nonneg hc.le (Real.sqrt_nonneg (g.inner z v v))]
  have hd : |L (y-x)| = c := by
    change |c⁻¹ * B d d| = c
    rw [← hc2]
    have hh : c⁻¹ * c^2 = c := by field_simp
    rw [hh,abs_of_pos hc]
  simpa only [hd] using functional_le_riemannianEDist g L hL x y
end ThreeManifold.RiemannianDistance
end

section
open Set Filter Topology Bundle Manifold IsManifold MeasureTheory
open scoped ContDiff ENNReal
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

lemma globalGeodesic_speed (g : SmoothMetric M) (p : M) (v : E3) (t : ℝ) :
    g.inner (globalGeodesic g (fiberPhase p v) t)
      (velocity (globalGeodesic g (fiberPhase p v)) t)
      (velocity (globalGeodesic g (fiberPhase p v)) t) = g.inner p v v := by
  let γ := globalGeodesic g (fiberPhase p v)
  have hγ := globalGeodesic_isGeodesic g (fiberPhase p v)
  let f : ℝ → ℝ := fun r => g.inner (γ r) (velocity γ r) (velocity γ r)
  have hd (r : ℝ) : HasDerivAt f 0 r := geodesic_speed_hasDerivAt g isOpen_univ hγ (mem_univ r)
  have he : f t = f 0 := isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun r _ => (hd r).differentiableAt.differentiableWithinAt)
    (fun r _ => (hd r).deriv) (mem_univ t) (mem_univ 0)
  refine he.trans ?_
  exact congrArg (phaseEnergy g) (globalGeodesic_initial g (fiberPhase p v))

lemma exponentialMetric_radial (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) (t : ℝ) :
    (exponentialMetric g hn p).inner (t • v) v v = g.inner p v v := by
  have hr : ContDiff ℝ 1 (fun r : ℝ => r • v) := contDiff_id.smul contDiff_const
  have hd : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) (fun r : ℝ => r • v) t 1 = v := by
    rw [mfderiv_eq_fderiv]
    change deriv (fun r : ℝ => r • v) t = v
    simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const v).deriv
  have heq : exponential g p ∘ (fun r : ℝ => r • v) = globalGeodesic g (fiberPhase p v) :=
    funext (exponential_scale g p v)
  have hc := mfderiv_comp t ((exponential_contMDiff g p).mdifferentiable (by simp) (t • v))
    (hr.contMDiff.mdifferentiable (by simp) t)
  rw [heq] at hc
  have hv := congrArg (fun L : ℝ →L[ℝ] E3 => L 1) hc
  change (velocity (globalGeodesic g (fiberPhase p v)) t : E3) =
    mfderiv 𝓘(ℝ,E3) I3 (exponential g p) (t • v)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) (fun r : ℝ => r • v) t 1) at hv
  rw [hd] at hv
  rw [exponentialMetric_inner]
  calc
    _ = g.inner (exponential g p (t • v))
      (velocity (globalGeodesic g (fiberPhase p v)) t : E3)
      (velocity (globalGeodesic g (fiberPhase p v)) t : E3) :=
        congrArg₂ (fun a b : E3 => g.inner (exponential g p (t • v)) a b) hv.symm hv.symm
    _ = g.inner (globalGeodesic g (fiberPhase p v) t)
      (velocity (globalGeodesic g (fiberPhase p v)) t : E3)
      (velocity (globalGeodesic g (fiberPhase p v)) t : E3) := by
        rw [exponential_scale]
    _ = _ := globalGeodesic_speed g p v t

lemma exponentialMetric_radial_length (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) (a b : ℝ) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
      ⟨(exponentialMetric g hn p).toRiemannianMetric⟩
    pathELength 𝓘(ℝ,E3) (fun r : ℝ => r • v) a b =
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) * ENNReal.ofReal (b-a) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
      ⟨(exponentialMetric g hn p).toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  have hh (t : ℝ) : ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) (fun r : ℝ => r • v) t 1‖ₑ =
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
    rw [RiemannianDistance.tangent_enorm (exponentialMetric g hn p)]
    have hd : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) (fun r : ℝ => r • v) t 1 : E3) = v := by
      rw [mfderiv_eq_fderiv]
      change deriv (fun r : ℝ => r • v) t = v
      simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const v).deriv
    rw [congrArg (fun w : E3 => (exponentialMetric g hn p).inner (t • v) w w) hd,
      exponentialMetric_radial]
  simp_rw [hh]
  simp [Real.volume_Icc]

lemma universalMetric_lower (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (x y : E3) :
    Real.sqrt (g.inner p (y-x) (y-x)) ≤
      @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist x y := by
  have hh := RiemannianDistance.bilinear_le_riemannianEDist (exponentialMetric g hn p)
    (show E3 →L[ℝ] E3 →L[ℝ] ℝ from g.inner p) (g.symm p) (g.pos p)
    (exponentialMetric_expanding g hn p) x y
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
      ⟨(exponentialMetric g hn p).toRiemannianMetric⟩
  change ENNReal.ofReal _ ≤ @edist E3 (universalMetric g hn p).toPseudoEMetricSpace.toEDist x y at hh
  rw [@edist_dist E3 (universalMetric g hn p).toPseudoMetricSpace] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (@dist_nonneg E3 (universalMetric g hn p).toPseudoMetricSpace x y)).mp hh

lemma universalMetric_radial_zero (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) :
    @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist 0 v = Real.sqrt (g.inner p v v) := by
  apply le_antisymm
  · let : RiemannianBundle (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
      ⟨(exponentialMetric g hn p).toRiemannianMetric⟩
    have hc : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) 1 (fun r : ℝ => r • v) :=
      (contDiff_id.smul contDiff_const).contMDiff
    have hh := riemannianEDist_le_pathELength hc.contMDiffOn (by simp : (0:ℝ) • v = 0)
      (by simp : (1:ℝ) • v = v) (by norm_num : (0:ℝ) ≤ 1)
    rw [exponentialMetric_radial_length] at hh
    simp only [sub_zero,ENNReal.ofReal_one,mul_one] at hh
    change @edist E3 (universalMetric g hn p).toPseudoEMetricSpace.toEDist 0 v ≤ _ at hh
    rw [@edist_dist E3 (universalMetric g hn p).toPseudoMetricSpace] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp hh
  · simpa only [sub_zero] using universalMetric_lower g hn p 0 v
end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

lemma exponential_recenter (g : SmoothMetric M) (p : M) (v : E3) (t s : ℝ) :
    exponential g (globalGeodesic g (fiberPhase p v) t)
      (s • (velocity (globalGeodesic g (fiberPhase p v)) t : E3)) =
        exponential g p ((t+s) • v) := by
  trans globalGeodesic g (fiberPhase (globalGeodesic g (fiberPhase p v) t)
    (velocity (globalGeodesic g (fiberPhase p v)) t : E3)) s
  · exact exponential_scale g _ _ s
  rw [exponential_scale]
  exact congrArg Bundle.TotalSpace.proj (geodesicFlow_add g (fiberPhase p v) t s)

lemma recenter_radial_line (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) (t : ℝ) {e : E3 ≃ₜ E3}
    (he0 : e (t • v) = 0)
    (he : ∀ z, exponential g (globalGeodesic g (fiberPhase p v) t) (e z) = exponential g p z)
    (s : ℝ) : e ((t+s) • v) = s • (velocity (globalGeodesic g (fiberPhase p v)) t : E3) := by
  let q := globalGeodesic g (fiberPhase p v) t
  let w : E3 := velocity (globalGeodesic g (fiberPhase p v)) t
  change e ((t+s) • v) = s • w
  have hh : (fun r : ℝ => e ((t+r) • v)) =
      (fun r : ℝ => r • w) := by
    refine (npc_exponential_isCoveringMap g hn q).eq_of_comp_eq
      (e.continuous.comp ((continuous_const.add continuous_id).smul continuous_const))
      (continuous_id.smul continuous_const) ?_ 0 ?_
    · funext r
      exact (he _).trans (exponential_recenter g p v t r).symm
    · simpa only [add_zero,zero_smul] using he0
  exact congrFun hh s

lemma positive_form_smul (g : SmoothMetric M) (p : M) (v : E3) (t : ℝ) :
    g.inner p (t • v) (t • v) = t^2 * g.inner p v v := by
  let _ : CompactSpace M := inferInstance
  let _ : T2Space M := inferInstance
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner p
  change B (t • v) (t • v) = t^2 * B v v
  simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  ring

lemma positive_form_parallelogram (g : SmoothMetric M) (p : M) (u v : E3) :
    g.inner p (u+v) (u+v) + g.inner p (u-v) (u-v) =
      2*g.inner p u u + 2*g.inner p v v := by
  let _ : CompactSpace M := inferInstance
  let _ : T2Space M := inferInstance
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner p
  change B (u+v) (u+v) + B (u-v) (u-v) = 2*B u u + 2*B v v
  simp only [map_add,map_sub,_root_.add_apply,_root_.sub_apply]
  ring

lemma universalMetric_lower_sq (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (x y : E3) :
    g.inner p (y-x) (y-x) ≤
      (@dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist x y)^2 := by
  have h := universalMetric_lower g hn p x y
  have hs := Real.sq_sqrt (inner_self_nonneg g p (y-x))
  have hd := @dist_nonneg E3 (universalMetric g hn p).toPseudoMetricSpace x y
  nlinarith [Real.sqrt_nonneg (g.inner p (y-x) (y-x))]

lemma universalMetric_distance_zero_sq (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (x : E3) :
    (@dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist 0 x)^2 =
      g.inner p x x := by
  rw [universalMetric_radial_zero,Real.sq_sqrt (inner_self_nonneg g p x)]

theorem universalMetric_radial_CN (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v z : E3) :
    let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
    D ((1/2:ℝ) • v) z ^2 ≤ (D 0 z ^2 + D v z ^2)/2 - D 0 v ^2/4 := by
  let m := (1/2:ℝ) • v
  let q := globalGeodesic g (fiberPhase p v) (1/2)
  let w : E3 := velocity (globalGeodesic g (fiberPhase p v)) (1/2)
  have hbase : exponential g p m = exponential g q 0 := by
    rw [exponential_zero]
    exact exponential_scale g p v (1/2)
  obtain ⟨e,he0,he,hc,hci,hi⟩ := exists_exponential_coordinates g hn m 0 hbase
  have heA : e 0 = (-1/2:ℝ) • w := by
    have hh : e (((1/2:ℝ)+(-1/2)) • v) = (-1/2:ℝ) • w :=
      recenter_radial_line g hn p v (1/2) he0 he (-1/2)
    norm_num only [show (1/2:ℝ)+(-1/2)=0 by norm_num,zero_smul] at hh
    simpa only [neg_div] using hh
  have heB : e v = (1/2:ℝ) • w := by
    have hh : e (((1/2:ℝ)+(1/2)) • v) = (1/2:ℝ) • w :=
      recenter_radial_line g hn p v (1/2) he0 he (1/2)
    norm_num only [show (1/2:ℝ)+(1/2)=1 by norm_num,one_smul] at hh
    exact hh
  let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
  let Q := @dist E3 (universalMetric g hn q).toPseudoMetricSpace.toDist
  have hid (a b : E3) : Q (e a) (e b) = D a b := by
    exact @Isometry.dist_eq E3 E3 (universalMetric g hn p).toPseudoMetricSpace
      (universalMetric g hn q).toPseudoMetricSpace e hi a b
  have hmid : D m z ^2 = g.inner q (e z) (e z) := by
    rw [← hid,he0]
    exact universalMetric_distance_zero_sq g hn q (e z)
  have ha : g.inner q (e z + (1/2:ℝ) • w) (e z + (1/2:ℝ) • w) ≤ D 0 z ^2 := by
    have hh := universalMetric_lower_sq g hn q (e 0) (e z)
    change g.inner q (e z - e 0) (e z - e 0) ≤ Q (e 0) (e z) ^2 at hh
    rw [hid,heA] at hh
    simpa only [neg_div,neg_smul,sub_neg_eq_add] using hh
  have hb : g.inner q (e z - (1/2:ℝ) • w) (e z - (1/2:ℝ) • w) ≤ D v z ^2 := by
    have hh := universalMetric_lower_sq g hn q (e v) (e z)
    change g.inner q (e z - e v) (e z - e v) ≤ Q (e v) (e z) ^2 at hh
    rwa [hid,heB] at hh
  have hp := positive_form_parallelogram g q (e z) ((1/2:ℝ) • w)
  rw [positive_form_smul] at hp
  have hw : g.inner q w w = g.inner p v v := globalGeodesic_speed g p v (1/2)
  have hv : D 0 v ^2 = g.inner p v v := universalMetric_distance_zero_sq g hn p v
  change D m z ^2 ≤ _
  nlinarith only [ha,hb,hp,hw,hv,hmid]
end ThreeManifold.RiemannianCoordinates

end

end OAI


