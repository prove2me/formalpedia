-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
-- name    : OAI_Geometry_ConjugatePoints_Metric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:07:24.129276+00:00
-- url     : https://prove2.me/theorems/0629c819-ec89-4000-8212-cdf7b91a71e1
-- title:
--   Pullback, quotient, product and warped-cylinder Riemannian metrics
-- statement:
--   This file provides general constructions of smooth Riemannian metrics on $C^\infty$ manifolds without boundary modelled on real normed spaces, and uses them to build an explicit family of metrics on the three-dimensional cylinder $\mathbb{R} \times (\mathbb{R}/6\mathbb{Z})^2$.
--
--   Throughout, a *smooth Riemannian metric* $g$ on a $C^\infty$ manifold $M$ modelled on $E$ assigns to each $x \in M$ a continuous bilinear form $g_x$ on the tangent space $T_xM \cong E$ that is symmetric, positive definite ($g_x(v,v) > 0$ for $v \neq 0$), has a von Neumann bounded unit ball $\{v : g_x(v,v) < 1\}$, and depends $C^\infty$ on $x$ as a section of the bundle of bilinear forms. For a differentiable map $f : M \to N$ and a metric $g$ on $N$, the pulled-back bilinear form is
--   $$
--   (f^*g)_x(u, v) = g_{f(x)}\bigl(df_x\, u,\ df_x\, v\bigr).
--   $$
--
--   1. **Pullback metrics.** If $f : M \to N$ is $C^\infty$ and every differential $df_x$ is a linear isomorphism (supplied as data), then $f^*g$ is a smooth Riemannian metric on $M$. In particular, a homeomorphism $f$ such that $f$ and $f^{-1}$ are both $C^\infty$ pulls metrics back to metrics. Variant for quotients: if $p : M \to Q$ is a quotient covering map for a group action (see item 2) that is $C^\infty$, has $C^\infty$ local inverse branches and admits a section, $f : Q \to Q$ is $C^\infty$, and $f$ has a $C^\infty$ lift $\ell : M \to M$ with $f \circ p = p \circ \ell$ whose differentials are linear isomorphisms, then $f^*g$ is a smooth Riemannian metric on $Q$ for every smooth metric $g$ on $Q$.
--
--   2. **Descent to a covering quotient.** Let a group $G$ act on $M$, and let $p : M \to Q$ be a quotient covering map for this action (a continuous surjective quotient map whose fibres are exactly the $G$-orbits and such that each point has a neighbourhood moved off itself by every $k \neq 1$), where $Q$ is also a $C^\infty$ manifold modelled on $E$. Assume $p$ is $C^\infty$, each map $x \mapsto k \cdot x$ is $C^\infty$, every local inverse branch of $p$ is $C^\infty$ on its domain, and $\sigma : Q \to M$ is a section of $p$. If $g$ is a $G$-invariant metric on $M$, i.e. $(x \mapsto k\cdot x)^* g = g$ for all $k \in G$, then
--   $$
--   \bar g_q = \bigl(p^{-1}_{\sigma(q)}\bigr)^* g \quad (\text{pullback along the local inverse of } p \text{ through } \sigma(q))
--   $$
--   defines a smooth Riemannian metric $\bar g$ on $Q$. At each $q$ it agrees with the pullback of $g$ along any local inverse branch whose domain contains $q$, and $p^*\bar g = g$. Local inverse branches are automatically $C^\infty$ when $p$ admits $C^\infty$ local sections around every point.
--
--   3. **Elementary metrics.** For a $C^\infty$ nowhere-vanishing function $r : M \to \mathbb{R}$, the rescaling $r^2 g$ is a smooth metric. On a real inner product space $V$ the Euclidean metric is $\langle u, v \rangle$ at every point. On the circle $\mathbb{R}/b\mathbb{Z}$ (for any real $b$) the circle metric is the descent of the Euclidean metric of $\mathbb{R}$, which is invariant under the deck translations, so the projection $\mathbb{R} \to \mathbb{R}/b\mathbb{Z}$ pulls it back to the Euclidean metric. For metrics $g$ on $M$ and $h$ on $N$ the product metric on $M \times N$ is
--   $$
--   (g \oplus h)_{(x,y)}\bigl((u_1,u_2),(v_1,v_2)\bigr) = g_x(u_1, v_1) + h_y(u_2, v_2).
--   $$
--
--   4. **Metrics on a model space.** On a real normed space $V$ (viewed as a manifold with one chart), a $C^\infty$ field $x \mapsto q(x)$ of symmetric positive definite bilinear forms with bounded unit balls is a smooth metric. On $\mathbb{R}^\iota$, $\iota$ finite, with dot product $u \cdot v = \sum_i u_i v_i$, a $C^\infty$ family $x \mapsto K(x)$ of linear isomorphisms gives the twisted metric $(u, v) \mapsto K(x)u \cdot K(x)v$. For $r, s \neq 0$ and $c \in \mathbb{R}$ the triangular isomorphism of $\mathbb{R}^3$ is $T_{r,s,c}(v) = (v_0,\ r(v_1 - c v_2),\ s v_2)$; for $C^\infty$ functions $r, s, c : \mathbb{R}^3 \to \mathbb{R}$ with $r, s$ nowhere zero, the triangular metric is the twisted metric of $x \mapsto T_{r(x),s(x),c(x)}$, explicitly
--   $$
--   u_0 v_0 + r(x)^2\,(u_1 - c(x) u_2)(v_1 - c(x) v_2) + s(x)^2\, u_2 v_2 .
--   $$
--
--   5. **The warped cylinder.** Let $\mathcal{C} = \mathbb{R} \times (\mathbb{R}/6\mathbb{Z})^2$, covered by $\mathbb{R}^3$ through $(t, x, y) \mapsto (t,\ x \bmod 6,\ y \bmod 6)$; the deck group $6\mathbb{Z} \times 6\mathbb{Z}$ acts by translating the last two coordinates, and the projection is a $C^\infty$ quotient covering with $C^\infty$ local sections. For $C^\infty$ functions $r, s, c : \mathbb{R} \to \mathbb{R}$ with $r$ and $s$ nowhere zero, the lifted metric on $\mathbb{R}^3$,
--   $$
--   dt^2 + r(t)^2\,\bigl(dx - c(t)\,dy\bigr)^2 + s(t)^2\,dy^2,
--   $$
--   is deck-invariant and descends to a smooth Riemannian metric on $\mathcal{C}$ whose pullback to $\mathbb{R}^3$ is exactly the lifted metric.
--
--   These constructions are the metric toolkit of the three-manifold construction: warped cylinder metrics of item 5 model the neck regions, and pullback, descent and products move metrics between charts, coverings and quotients. Items 1 to 4 are reusable whenever a Riemannian metric has to be built on a quotient by a free properly discontinuous action or assembled from local models.
--
--   **Formalization Note** Metrics are Mathlib's `ContMDiffRiemannianMetric` on the tangent bundle (abbreviation `MetricConstruction.Metric`), whose fields are `inner`, `symm`, `pos`, `isVonNBounded` and `contMDiff`; the bilinear form $(f^*g)_x$ is `pullInner g f x`, defined with `mfderiv` for any map. The constructor `pullback g hf e he` takes the isomorphisms `e x` together with a proof that they coincide with `mfderiv f x`, and `descend` takes the section $\sigma$ used to choose the local inverse at each point. The product charted space is installed with low priority (`metricProductCharts`, model `E × F`). The cylinder is `ℝ × (AddCircle 6 × AddCircle 6)`, its cover is `P = ℝ × (ℝ × ℝ)`, identified with `V3 = Fin 3 → ℝ` by `CylinderConstruction.coordinates`; the trivial `PUnit` action on the first factor is plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Metric.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Metric.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ConjugatePoints mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing

namespace OAI

noncomputable section

/-!
# Pullback Riemannian metrics and smooth cylinder coordinates.
-/

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.MetricConstruction

section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

abbrev Metric (M : Type*) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] :=
  ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _)

def pullBilin (q : F →L[ℝ] F →L[ℝ] ℝ) (L : E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ :=
  q.bilinearComp L L

@[simp] lemma pullBilin_apply (q : F →L[ℝ] F →L[ℝ] ℝ) (L : E →L[ℝ] F) (u v : E) :
    pullBilin q L u v = q (L u) (L v) := rfl

lemma flip_smoothAt {X G A B C : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace G] [ChartedSpace X G]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : G → A →L[ℝ] B →L[ℝ] C} {x : G}
    (hf : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,A →L[ℝ] B →L[ℝ] C) ∞ f x) :
    ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,B →L[ℝ] A →L[ℝ] C) ∞ (fun y => (f y).flip) x := by
  let : NormedAddCommGroup (B →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (B →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (A →L[ℝ] B →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (A →L[ℝ] B →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (A →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (A →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (B →L[ℝ] A →L[ℝ] C) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (B →L[ℝ] A →L[ℝ] C) := ContinuousLinearMap.toNormedSpace
  have hc : ContDiff ℝ ∞ (fun L : A →L[ℝ] B →L[ℝ] C => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ A B C).toContinuousLinearEquiv.contDiff
  exact hc.comp_contMDiffAt hf

lemma bilin_comp_smoothAt {X G H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace G] [ChartedSpace X G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {q : G → F →L[ℝ] F →L[ℝ] ℝ} {L : G → H →L[ℝ] F} {x : G}
    (hq : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,F →L[ℝ] F →L[ℝ] ℝ) ∞ q x)
    (hL : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,H →L[ℝ] F) ∞ L x) :
    ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,H →L[ℝ] H →L[ℝ] ℝ) ∞
      (fun y => (q y).bilinearComp (L y) (L y)) x := by
  exact flip_smoothAt ((flip_smoothAt (hq.clm_comp hL)).clm_comp hL)

def pullInner (g : Metric (E := F) N) (f : M → N) (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ :=
  pullBilin (E := E) (F := F) (g.inner (f x)) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] lemma pullInner_apply (g : Metric (E := F) N) (f : M → N) (x : M)
    (u v : TangentSpace 𝓘(ℝ,E) x) :
    pullInner g f x u v = g.inner (f x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x u)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x v) := rfl

lemma pullback_coordinates (g : Metric (E := F) N) (f : M → N) (x y : M)
    (hx : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x).baseSet)
    (hy : f y ∈ (trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x)).baseSet) :
    ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ,E))
      (E →L[ℝ] ℝ) (fun y => TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ) x y x y
      (pullInner g f y) =
      (ContinuousLinearMap.inCoordinates F (TangentSpace 𝓘(ℝ,F))
        (F →L[ℝ] ℝ) (fun z => TangentSpace 𝓘(ℝ,F) z →L[ℝ] ℝ)
        (f x) (f y) (f x) (f y) (g.inner (f y))).bilinearComp
        (inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,F) id f
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f) x y)
        (inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,F) id f
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f) x y) := by
  ext u v
  rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := fun _ => ℝ) hx hx (mem_univ _)]
  simp only [pullInner_apply,ContinuousLinearMap.bilinearComp_apply]
  rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := fun _ => ℝ) hy hy (mem_univ _)]
  simp only [inTangentCoordinates,id_eq]
  rw [ContinuousLinearMap.inCoordinates_eq hx hy]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  simp only [Trivialization.symm_continuousLinearEquivAt_eq,
    Trivialization.coe_continuousLinearEquivAt_eq]
  simp only [Trivialization.symmL_apply _ hx]
  simp only [Trivial.fiberBundle_trivializationAt',Trivial.linearMapAt_trivialization, LinearMap.id_coe,id_eq]
  apply congrArg₂ (fun a b : TangentSpace 𝓘(ℝ,F) (f y) => g.inner (f y) a b)
  · exact ((trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x)).symm_linearMapAt
      (R := ℝ) hy _).symm
  · exact ((trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x)).symm_linearMapAt
      (R := ℝ) hy _).symm

lemma pullback_inner_smoothAt (g : Metric (E := F) N) {f : M → N}
    {x : M} (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f x) :
    ContMDiffAt 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace 𝓘(ℝ,E) y →L[ℝ] TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ)
        x (pullInner g f x)) x := by
  rw [contMDiffAt_section]
  have hg := g.contMDiff (f x)
  rw [contMDiffAt_section] at hg
  simp only [hom_trivializationAt_apply] at hg ⊢
  have hgc := hg.comp x hf
  have hL := hf.mfderiv_const (m := ∞) (by simp)
  apply (bilin_comp_smoothAt hgc hL).congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace 𝓘(ℝ,E)) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ,E)) x),
    hf.continuousAt
      ((trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x)))] with y hy hy'
  exact pullback_coordinates g f x y hy hy'

lemma pullback_inner_smooth (g : Metric (E := F) N) {f : M → N}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace 𝓘(ℝ,E) y →L[ℝ] TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ)
        x (pullInner g f x)) := fun x => pullback_inner_smoothAt g (hf x)

variable {P H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold 𝓘(ℝ,H) ∞ P]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma pullInner_comp (g : Metric (E := H) P) {f : M → N} {h : N → P} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f x)
    (hh : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,H) h (f x))
    (q : Metric (E := F) N) (hq : ∀ u v, pullInner g h (f x) u v = q.inner (f x) u v) :
    pullInner (E := E) g (h ∘ f) x = pullInner (E := E) q f x := by
  ext u v
  simp only [pullInner_apply, Function.comp_apply]
  rw [mfderiv_comp x hh hf]
  exact hq _ _

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma pullInner_congr (g : Metric (E := F) N) {f h : M → N} {x : M}
    (he : f =ᶠ[nhds x] h) : pullInner (E := E) g f x = pullInner (E := E) g h x := by
  ext u v
  simp only [pullInner_apply]
  rw [he.mfderiv_eq, he.eq_of_nhds]

def pullback (g : Metric (E := F) N) {f : M → N}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (e : ∀ x, TangentSpace 𝓘(ℝ,E) x ≃L[ℝ] TangentSpace 𝓘(ℝ,F) (f x))
    (he : ∀ x, (e x : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,F) (f x)) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x) : Metric (E := E) M where
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
  contMDiff := pullback_inner_smooth g hf
end

open QuotientConstruction
variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ,E) ∞ Q]
  [Group G] [MulAction G M] {p : M → Q}
  (hp : IsQuotientCoveringMap p G)
  (hps : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ p)
  (hact : ∀ k : G, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : M => k • x))
  (hls : ∀ (b : M) {q : Q}, q ∈ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b).source →
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b) q)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,E) ∞ Q] in
include hps hls in
lemma covering_inverse_mdifferentiable (b : M) :
    (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b).MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,E) := by
  constructor
  · intro q hq
    exact (hls b hq).mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
  · rw [hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm]
    exact hps.mdifferentiable (by simp) |>.mdifferentiableOn

variable (g : Metric (E := E) M)
  (hinv : ∀ (k : G) (x : M), pullInner (E := E) g (fun y => k • y) x = g.inner x)
  {σ : Q → M} (hσ : Function.RightInverse σ p)

omit [IsManifold 𝓘(ℝ,E) ∞ Q] in
include hact hls hinv in
lemma inverse_pullInner_independent (a b : M) {q : Q}
    (ha : q ∈ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt a).source)
    (hb : q ∈ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b).source) :
    pullInner (E := E) g (hp.isCoveringMap.isLocalHomeomorph.localInverseAt a) q =
    pullInner (E := E) g (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b) q := by
  let l := hp.isCoveringMap.isLocalHomeomorph
  let f := l.localInverseAt a
  let h := l.localInverseAt b
  have he : p (f q) = p (h q) :=
    (l.apply_localInverseAt_of_mem ha).trans (l.apply_localInverseAt_of_mem hb).symm
  obtain ⟨k,hk⟩ := hp.apply_eq_iff_mem_orbit.mp he
  have hsm := (hact k (h q)).comp q (hls b hb)
  have heq : (f : Q → M) =ᶠ[nhds q] (fun y => k • h y) := by
    apply lifts_eventuallyEq l (f.continuousAt ha) hsm.continuousAt hk.symm
    filter_upwards [f.open_source.mem_nhds ha, h.open_source.mem_nhds hb] with r hr hr'
    change p (f r) = p (k • h r)
    rw [hp.map_smul]
    exact (l.apply_localInverseAt_of_mem hr).trans (l.apply_localInverseAt_of_mem hr').symm
  rw [pullInner_congr g heq]
  apply pullInner_comp g ((hls b hb).mdifferentiableAt (by simp))
    ((hact k _).mdifferentiableAt (by simp)) g
  intro u v
  exact congrArg (fun L => L u v) (hinv k (h q))

def descendInner (q : Q) : TangentSpace 𝓘(ℝ,E) q →L[ℝ] TangentSpace 𝓘(ℝ,E) q →L[ℝ] ℝ :=
  pullInner g (hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ q)) q

include hact hls hinv hσ in
lemma descendInner_eq (b : M) {q : Q}
    (hq : q ∈ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b).source) :
    descendInner hp g (σ := σ) q =
      pullInner (E := E) g (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b) q := by
  let _ : IsManifold 𝓘(ℝ, E) ∞ Q := inferInstance
  apply inverse_pullInner_independent hp hact hls g hinv _ b _ hq
  simpa only [hσ q] using hp.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
    (x := σ q)

include hact hls hinv hσ in
lemma descendInner_smooth :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace 𝓘(ℝ,E) y →L[ℝ] TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ)
        q (descendInner hp g (σ := σ) q)) := by
  intro q
  have hq : q ∈ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ q)).source := by
    simpa only [hσ q] using hp.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
      (x := σ q)
  apply (pullback_inner_smoothAt g (hls (σ q) hq)).congr_of_eventuallyEq
  filter_upwards [(hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ q)).open_source.mem_nhds hq]
    with r hr
  exact congrArg (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) r)
    (descendInner_eq hp hact hls g hinv hσ (σ q) hr)

omit [IsManifold 𝓘(ℝ,E) ∞ Q] in
lemma descendInner_symm (q : Q) (u v : TangentSpace 𝓘(ℝ,E) q) :
    descendInner hp g (σ := σ) q u v = descendInner hp g (σ := σ) q v u := by
  simp only [descendInner,pullInner_apply]
  exact g.symm _ _ _

omit [IsManifold 𝓘(ℝ,E) ∞ Q] in
include hps hls hσ in
lemma descendInner_pos (q : Q) (u : TangentSpace 𝓘(ℝ,E) q) (hu : u ≠ 0) :
    0 < descendInner hp g (σ := σ) q u u := by
  let l := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ q)
  have hq : q ∈ l.source := by
    simpa only [hσ q] using hp.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
      (x := σ q)
  let e := (covering_inverse_mdifferentiable hp hps hls (σ q)).mfderiv hq
  simp only [descendInner,pullInner_apply]
  apply g.pos
  intro hh
  apply hu
  exact e.injective (hh.trans e.map_zero.symm)

omit [IsManifold 𝓘(ℝ,E) ∞ Q] in
include hps hls hσ in
lemma descendInner_bounded (q : Q) :
    IsVonNBounded ℝ {u : TangentSpace 𝓘(ℝ,E) q | descendInner hp g (σ := σ) q u u < 1} := by
  let l := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ q)
  have hq : q ∈ l.source := by
    simpa only [hσ q] using hp.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
      (x := σ q)
  let e := (covering_inverse_mdifferentiable hp hps hls (σ q)).mfderiv hq
  have hb := (g.isVonNBounded (l q)).image e.symm.toContinuousLinearMap
  apply hb.subset
  intro u hu
  exact ⟨e u,hu,e.symm_apply_apply u⟩

def descend : Metric (E := E) Q where
  inner := descendInner hp g (σ := σ)
  symm := descendInner_symm hp g
  pos := descendInner_pos hp hps hls g hσ
  isVonNBounded := descendInner_bounded hp hps hls g hσ
  contMDiff := descendInner_smooth hp hact hls g hinv hσ

lemma descend_local (b : M) {q : Q}
    (hq : q ∈ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b).source) :
    (descend hp hps hact hls g hinv hσ).inner q =
      pullInner (E := E) g (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b) q :=
  descendInner_eq hp hact hls g hinv hσ b hq

lemma descend_projection (x : M) :
    pullInner (E := E) (descend hp hps hact hls g hinv hσ) p x = g.inner x := by
  let l := hp.isCoveringMap.isLocalHomeomorph.localInverseAt x
  have hq : p x ∈ l.source := hp.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
  have hlx : l (p x) = x := hp.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self
  have he : (fun y => l (p y)) =ᶠ[nhds x] id := by
    filter_upwards [l.open_target.mem_nhds
      hp.isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target] with y hy
    simpa only [l,hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm,id_eq] using l.right_inv hy
  have hd : (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) l (p x)).comp (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) p x) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ,E) x) := by
    rw [← mfderiv_comp x ((hls x hq).mdifferentiableAt (by simp))
      ((hps x).mdifferentiableAt (by simp))]
    exact he.mfderiv_eq.trans mfderiv_id
  ext u v
  rw [pullInner_apply, descend_local hp hps hact hls g hinv hσ x hq,pullInner_apply]
  have hdu := congrArg (fun L : E →L[ℝ] E => L u) hd
  have hdv := congrArg (fun L : E →L[ℝ] E => L v) hd
  calc
    _ = g.inner (l (p x)) u v := congrArg₂ (fun a b : E => g.inner (l (p x)) a b) hdu hdv
    _ = g.inner x u v := congrArg (fun y : M => (g.inner y : E →L[ℝ] E →L[ℝ] ℝ) u v) hlx

end ThreeManifold.MetricConstruction
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff RealInnerProductSpace
namespace ThreeManifold.MetricConstruction
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

lemma metric_nonneg (g : Metric (E := E) M) (x : M) (v : TangentSpace 𝓘(ℝ,E) x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

def scaleSq (g : Metric (E := E) M) (r : M → ℝ)
    (hr : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ r) (hne : ∀ x, r x ≠ 0) : Metric (E := E) M where
  inner x := (r x)^2 • g.inner x
  symm x v w := by
    change (r x)^2 * g.inner x v w = (r x)^2 * g.inner x w v
    rw [g.symm x]
  pos x v hv := mul_pos (sq_pos_of_ne_zero (hne x)) (g.pos x v hv)
  isVonNBounded x := by
    have hb := (g.isVonNBounded x).image
      ((r x)⁻¹ • ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ,E) x))
    apply hb.subset
    intro v hv
    refine ⟨(r x) • v,?_,?_⟩
    · change g.inner x ((r x) • v) ((r x) • v) < 1
      change (r x)^2 * g.inner x v v < 1 at hv
      simpa only [map_smul,_root_.smul_apply,smul_eq_mul,pow_two,mul_assoc] using hv
    · simp [smul_smul,hne x]
  contMDiff := by
    let : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
      fun point => inferInstanceAs (ContinuousAdd (E →L[ℝ] ℝ))
    exact (hr.pow 2).smul_section g.contMDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
def flatBilin : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ (E := V)

def euclideanInner (x : V) :
    TangentSpace 𝓘(ℝ,V) x →L[ℝ] TangentSpace 𝓘(ℝ,V) x →L[ℝ] ℝ := flatBilin

lemma euclidean_inner_smooth :
    ContMDiff 𝓘(ℝ,V) (𝓘(ℝ,V).prod 𝓘(ℝ,V →L[ℝ] V →L[ℝ] ℝ)) ∞
      (fun x : V => TotalSpace.mk' (V →L[ℝ] V →L[ℝ] ℝ)
        (E := fun y => TangentSpace 𝓘(ℝ,V) y →L[ℝ] TangentSpace 𝓘(ℝ,V) y →L[ℝ] ℝ)
        x (euclideanInner x)) := by
  intro x
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  apply (contMDiffAt_const (c := flatBilin (V := V))).congr_of_eventuallyEq
  filter_upwards [] with y
  ext u v
  have hy : y ∈ (trivializationAt V (TangentSpace 𝓘(ℝ,V)) x).baseSet := by
    change y ∈ (univ : Set V)
    trivial
  rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := fun _ => ℝ) hy hy (mem_univ _)]
  rw [← Trivialization.symmL_apply (R := ℝ) _ hy, ← Trivialization.symmL_apply (R := ℝ) _ hy]
  simp only [TangentBundle.symmL_model_space,
    Trivial.fiberBundle_trivializationAt',Trivial.linearMapAt_trivialization, LinearMap.id_coe,id_eq]
  rfl

def euclidean : Metric (E := V) V where
  inner := euclideanInner
  symm x u v := real_inner_comm (v : V) (u : V)
  pos _ v hv := real_inner_self_pos.mpr hv
  isVonNBounded _ := by
    change IsVonNBounded ℝ {v : V | inner ℝ v v < 1}
    apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
    refine ⟨1,fun v hv => ?_⟩
    change inner ℝ v v < 1 at hv
    rw [real_inner_self_eq_norm_sq] at hv
    nlinarith [norm_nonneg v]
  contMDiff := euclidean_inner_smooth
end ThreeManifold.MetricConstruction
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.MetricConstruction

section
open QuotientConstruction CircleConstruction
lemma circle_action_deriv (b : ℝ) (k : Deck b) (r : ℝ) :
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun x : ℝ => k • x) r = ContinuousLinearMap.id ℝ ℝ := by
  change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun x : ℝ => (Multiplicative.toAdd k).val + x) r = _
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (fun x : ℝ => (Multiplicative.toAdd k).val + x) r =
    (ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ)
  simpa using ((hasFDerivAt_id r).const_add (Multiplicative.toAdd k).val).fderiv

lemma circle_action_invariant (b : ℝ) (k : Deck b) (r : ℝ) :
    pullInner (E := ℝ) (euclidean (V := ℝ)) (fun x : ℝ => k • x) r =
      (euclidean (V := ℝ)).inner r := by
  change pullBilin (flatBilin (V := ℝ))
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun x : ℝ => k • x) r) = flatBilin
  rw [circle_action_deriv]
  rfl

def circle (b : ℝ) : Metric (E := ℝ) (AddCircle b) :=
  descend (projection_cover b) (projection_smooth b) (action_smooth b)
    (fun a _ h => local_lift_smoothAt (projection_cover b) (section_spec b) (action_smooth b) a h)
    euclidean (circle_action_invariant b) (section_spec b)

lemma circle_projection (b r : ℝ) :
    pullInner (E := ℝ) (circle b) ((↑) : ℝ → AddCircle b) r =
      (euclidean (V := ℝ)).inner r :=
  descend_projection (projection_cover b) (projection_smooth b) (action_smooth b)
    (fun a _ h => local_lift_smoothAt (projection_cover b) (section_spec b) (action_smooth b) a h)
    euclidean (circle_action_invariant b) (section_spec b) r
end

section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
instance (priority := 50) metricProductCharts : ChartedSpace (E × F) (M × N) :=
  prodChartedSpace E M F N
instance (priority := 50) metricProductManifold : IsManifold 𝓘(ℝ,E × F) ∞ (M × N) := by
  simpa only [← modelWithCornersSelf_prod] using
    (inferInstance : IsManifold ((𝓘(ℝ,E)).prod 𝓘(ℝ,F)) ∞ (M × N))

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma projection_fst_smooth : ContMDiff 𝓘(ℝ,E × F) 𝓘(ℝ,E) ∞ (Prod.fst : M × N → M) := by
  simpa only [modelWithCornersSelf_prod] using
    (contMDiff_fst (I := 𝓘(ℝ,E)) (J := 𝓘(ℝ,F)) (n := ∞))
omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma projection_snd_smooth : ContMDiff 𝓘(ℝ,E × F) 𝓘(ℝ,F) ∞ (Prod.snd : M × N → N) := by
  simpa only [modelWithCornersSelf_prod] using
    (contMDiff_snd (I := 𝓘(ℝ,E)) (J := 𝓘(ℝ,F)) (n := ∞))

def productInner (g : Metric (E := E) M) (h : Metric (E := F) N) (x : M × N) :
    TangentSpace 𝓘(ℝ,E × F) x →L[ℝ] TangentSpace 𝓘(ℝ,E × F) x →L[ℝ] ℝ :=
  pullInner g Prod.fst x + pullInner h Prod.snd x

lemma productInner_apply (g : Metric (E := E) M) (h : Metric (E := F) N) (x : M × N)
    (u v : TangentSpace 𝓘(ℝ,E × F) x) :
    productInner g h x u v = g.inner x.1 u.1 v.1 + h.inner x.2 u.2 v.2 := by
  simp only [productInner,_root_.add_apply,pullInner_apply]
  have hf : mfderiv 𝓘(ℝ,E × F) 𝓘(ℝ,E) (Prod.fst : M × N → M) x =
      ContinuousLinearMap.fst ℝ E F := by
    convert! (mfderiv_fst (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,F)) (x := x)) using 1
  have hs : mfderiv 𝓘(ℝ,E × F) 𝓘(ℝ,F) (Prod.snd : M × N → N) x =
      ContinuousLinearMap.snd ℝ E F := by
    convert! (mfderiv_snd (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,F)) (x := x)) using 1
  rw [hf,hs]
  rfl

lemma bilin_product_bounded (q : E →L[ℝ] E →L[ℝ] ℝ) (r : F →L[ℝ] F →L[ℝ] ℝ)
    (hq : IsVonNBounded ℝ {v | q v v < 1}) (hr : IsVonNBounded ℝ {v | r v v < 1})
    (qp : ∀ v, 0 ≤ q v v) (rp : ∀ v, 0 ≤ r v v) :
    IsVonNBounded ℝ {v : E × F | q v.1 v.1 + r v.2 v.2 < 1} := by
  obtain ⟨C,hC⟩ := (NormedSpace.isVonNBounded_iff' ℝ).mp hq
  obtain ⟨D,hD⟩ := (NormedSpace.isVonNBounded_iff' ℝ).mp hr
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  refine ⟨max C D,fun u hu => ?_⟩
  change q u.1 u.1 + r u.2 u.2 < 1 at hu
  change max ‖u.1‖ ‖u.2‖ ≤ max C D
  apply max_le_max
  · exact hC u.1 (show q u.1 u.1 < 1 by linarith [rp u.2])
  · exact hD u.2 (show r u.2 u.2 < 1 by linarith [qp u.1])

def product (g : Metric (E := E) M) (h : Metric (E := F) N) : Metric (E := E × F) (M × N) where
  inner := productInner g h
  symm x u v := by
    rw [productInner_apply,productInner_apply]
    exact congrArg₂ (· + ·) (g.symm x.1 u.1 v.1) (h.symm x.2 u.2 v.2)
  pos x u hu := by
    rw [productInner_apply]
    by_cases he : u.1 = 0
    · have hn : u.2 ≠ 0 := fun hn => hu (Prod.ext he hn)
      have hz : g.inner x.1 u.1 u.1 = 0 := by
        calc
          _ = g.inner x.1 (0 : TangentSpace 𝓘(ℝ,E) x.1) 0 :=
            congrArg (fun v : TangentSpace 𝓘(ℝ,E) x.1 => g.inner x.1 v v) he
          _ = 0 := by simp
      rw [hz,zero_add]
      exact h.pos x.2 u.2 hn
    · exact add_pos_of_pos_of_nonneg (g.pos x.1 u.1 he) (metric_nonneg h x.2 u.2)
  isVonNBounded x := by
    have hb := bilin_product_bounded (E := E) (F := F) (g.inner x.1) (h.inner x.2)
      (g.isVonNBounded x.1) (h.isVonNBounded x.2) (metric_nonneg g x.1) (metric_nonneg h x.2)
    convert! hb using 1
    ext u
    exact (congrArg (· < 1) (productInner_apply g h x u u)).to_iff
  contMDiff := by
    let : ∀ x : M × N, ContinuousAdd (TangentSpace 𝓘(ℝ,E × F) x →L[ℝ] ℝ) :=
      fun x => inferInstanceAs (ContinuousAdd ((E × F) →L[ℝ] ℝ))
    exact (pullback_inner_smooth g projection_fst_smooth).add_section
      (pullback_inner_smooth h projection_snd_smooth)
end

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def modelInner (q : V → V →L[ℝ] V →L[ℝ] ℝ) (x : V) :
    TangentSpace 𝓘(ℝ,V) x →L[ℝ] TangentSpace 𝓘(ℝ,V) x →L[ℝ] ℝ := q x

lemma model_inner_smooth {q : V → V →L[ℝ] V →L[ℝ] ℝ} (hq : ContDiff ℝ ∞ q) :
    ContMDiff 𝓘(ℝ,V) (𝓘(ℝ,V).prod 𝓘(ℝ,V →L[ℝ] V →L[ℝ] ℝ)) ∞
      (fun x : V => TotalSpace.mk' (V →L[ℝ] V →L[ℝ] ℝ)
        (E := fun y => TangentSpace 𝓘(ℝ,V) y →L[ℝ] TangentSpace 𝓘(ℝ,V) y →L[ℝ] ℝ)
        x (modelInner q x)) := by
  intro x
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  apply (hq.contMDiff x).congr_of_eventuallyEq
  filter_upwards [] with y
  ext u v
  have hy : y ∈ (trivializationAt V (TangentSpace 𝓘(ℝ,V)) x).baseSet := by
    change y ∈ (univ : Set V)
    trivial
  rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := fun _ => ℝ) hy hy (mem_univ _)]
  rw [← Trivialization.symmL_apply (R := ℝ) _ hy, ← Trivialization.symmL_apply (R := ℝ) _ hy]
  simp only [TangentBundle.symmL_model_space,
    Trivial.fiberBundle_trivializationAt',Trivial.linearMapAt_trivialization, LinearMap.id_coe,id_eq]
  rfl

def modelMetric (q : V → V →L[ℝ] V →L[ℝ] ℝ) (hq : ContDiff ℝ ∞ q)
    (hs : ∀ x u v, q x u v = q x v u)
    (hp : ∀ x u, u ≠ 0 → 0 < q x u u)
    (hb : ∀ x, IsVonNBounded ℝ {u : V | q x u u < 1}) : Metric (E := V) V where
  inner := modelInner q
  symm := hs
  pos := hp
  isVonNBounded := hb
  contMDiff := model_inner_smooth hq

variable {ι : Type*} [Fintype ι]
def piBilin : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)
lemma piBilin_apply (u v : ι → ℝ) : piBilin u v = ∑ i, u i * v i := by
  simp [piBilin]
lemma piBilin_symm (u v : ι → ℝ) : piBilin u v = piBilin v u := by
  simp only [piBilin_apply,mul_comm]
lemma piBilin_pos (u : ι → ℝ) (hu : u ≠ 0) : 0 < piBilin u u := by
  rw [piBilin_apply]
  obtain ⟨i,hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hh
    apply hu
    ext i
    exact not_not.mp (not_exists.mp hh i)
  exact Finset.sum_pos' (fun _ _ => mul_self_nonneg _) ⟨i,Finset.mem_univ i,mul_self_pos.mpr hi⟩
lemma piBilin_bounded : IsVonNBounded ℝ {u : ι → ℝ | piBilin u u < 1} := by
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  refine ⟨1,fun u hu => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  have his : u i * u i ≤ ∑ j, u j * u j :=
    Finset.single_le_sum (fun _ _ => mul_self_nonneg _) (Finset.mem_univ i)
  change piBilin u u < 1 at hu
  rw [piBilin_apply] at hu
  rw [Real.norm_eq_abs,abs_le]
  constructor <;> nlinarith

lemma twistedPi_smooth (K : (ι → ℝ) → ((ι → ℝ) ≃L[ℝ] (ι → ℝ)))
    (hK : ContDiff ℝ ∞ (fun x => (K x : (ι → ℝ) →L[ℝ] (ι → ℝ)))) :
    ContDiff ℝ ∞ (fun x => pullBilin (piBilin (ι := ι)) (K x).toContinuousLinearMap) := by
  apply contDiff_clm_apply_iff.mpr
  intro u
  apply contDiff_clm_apply_iff.mpr
  intro v
  simp only [pullBilin_apply,piBilin_apply]
  apply ContDiff.sum
  intro i _
  exact ((contDiff_apply ℝ ℝ i).comp (hK.clm_apply contDiff_const)).mul
    ((contDiff_apply ℝ ℝ i).comp (hK.clm_apply contDiff_const))

lemma twistedPi_bounded (K : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    IsVonNBounded ℝ {u : ι → ℝ | pullBilin (piBilin (ι := ι)) K.toContinuousLinearMap u u < 1} := by
  apply (piBilin_bounded.image K.symm.toContinuousLinearMap).subset
  intro u hu
  exact ⟨K u,hu,K.symm_apply_apply u⟩

def twistedPi (K : (ι → ℝ) → ((ι → ℝ) ≃L[ℝ] (ι → ℝ)))
    (hK : ContDiff ℝ ∞ (fun x => (K x : (ι → ℝ) →L[ℝ] (ι → ℝ)))) :
    Metric (E := ι → ℝ) (ι → ℝ) :=
  modelMetric (fun x => pullBilin (piBilin (ι := ι)) (K x).toContinuousLinearMap)
    (twistedPi_smooth K hK)
    (fun _ _ _ => piBilin_symm (ι := ι) _ _)
    (fun x _ hu => piBilin_pos _ (fun hh => hu ((K x).injective (hh.trans (K x).map_zero.symm))))
    (fun x => twistedPi_bounded (K x))
end

abbrev V3 := Fin 3 → ℝ

def triangular (r s c : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) : V3 ≃L[ℝ] V3 :=
  { toFun := fun v => ![v 0,r * (v 1 - c * v 2),s * v 2]
    invFun := fun w => ![w 0,w 1 / r + c * w 2 / s,w 2 / s]
    left_inv := by
      intro v
      funext i
      fin_cases i <;> simp
      · field_simp
        ring
      · field_simp
    right_inv := by
      intro w
      funext i
      fin_cases i <;> simp
      · field_simp
        ring
      · field_simp
    map_add' := by intro v w; funext i; fin_cases i <;> simp <;> ring
    map_smul' := by intro a v; funext i; fin_cases i <;> simp <;> ring }

@[simp] lemma triangular_apply (r s c : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (v : V3) :
    triangular r s c hr hs v = ![v 0,r * (v 1-c*v 2),s*v 2] := rfl

lemma triangular_smooth {r s c : V3 → ℝ}
    (h1 : ContDiff ℝ ∞ r) (h2 : ContDiff ℝ ∞ s) (h3 : ContDiff ℝ ∞ c)
    (hr : ∀ x, r x ≠ 0) (hs : ∀ x, s x ≠ 0) :
    ContDiff ℝ ∞ (fun x => (triangular (r x) (s x) (c x) (hr x) (hs x) : V3 →L[ℝ] V3)) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact h1.mul (contDiff_const.sub (h3.mul contDiff_const))
  · exact h2.mul contDiff_const

def triangularMetric {r s c : V3 → ℝ}
    (h1 : ContDiff ℝ ∞ r) (h2 : ContDiff ℝ ∞ s) (h3 : ContDiff ℝ ∞ c)
    (hr : ∀ x, r x ≠ 0) (hs : ∀ x, s x ≠ 0) : Metric (E := V3) V3 :=
  twistedPi (fun x => triangular (r x) (s x) (c x) (hr x) (hs x))
    (triangular_smooth h1 h2 h3 hr hs)

lemma triangularMetric_apply {r s c : V3 → ℝ}
    (h1 : ContDiff ℝ ∞ r) (h2 : ContDiff ℝ ∞ s) (h3 : ContDiff ℝ ∞ c)
    (hr : ∀ x, r x ≠ 0) (hs : ∀ x, s x ≠ 0)
    (x : V3) (u v : TangentSpace 𝓘(ℝ,V3) x) :
    (triangularMetric h1 h2 h3 hr hs).inner x u v =
      u 0*v 0 + (r x)^2*(u 1-c x*u 2)*(v 1-c x*v 2) + (s x)^2*u 2*v 2 := by
  change piBilin (triangular (r x) (s x) (c x) (hr x) (hs x) u)
    (triangular (r x) (s x) (c x) (hr x) (hs x) v) = _
  simp only [piBilin_apply,Fin.sum_univ_three]
  change u 0*v 0 + (r x*(u 1-c x*u 2))*(r x*(v 1-c x*v 2)) +
    (s x*u 2)*(s x*v 2) = _
  ring

open QuotientConstruction

lemma inverse_smooth_of_sections {E M Q G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ,E) ∞ Q]
    [Group G] [MulAction G M] {p : M → Q}
    (hp : IsQuotientCoveringMap p G)
    (hact : ∀ k : G, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : M => k • x))
    (sec : ∀ q : Q, ∃ s : Q → M, ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ s q ∧
      (p ∘ s) =ᶠ[nhds q] id)
    (a : M) {q : Q} (hq : q ∈ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt a).source) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt a) q := by
  let l := hp.isCoveringMap.isLocalHomeomorph
  let f := l.localInverseAt a
  obtain ⟨s,hs,hps⟩ := sec q
  have he : p (f q) = p (s q) := (l.apply_localInverseAt_of_mem hq).trans hps.eq_of_nhds.symm
  obtain ⟨k,hk⟩ := hp.apply_eq_iff_mem_orbit.mp he
  have hsm := (hact k (s q)).comp q hs
  apply hsm.congr_of_eventuallyEq
  apply lifts_eventuallyEq l (f.continuousAt hq) hsm.continuousAt hk.symm
  filter_upwards [f.open_source.mem_nhds hq,hps] with y hy hpy
  change p (f y) = p (k • s y)
  rw [l.apply_localInverseAt_of_mem hy,hp.map_smul]
  exact hpy.symm
end ThreeManifold.MetricConstruction

namespace ThreeManifold.CylinderConstruction
open QuotientConstruction MetricConstruction
abbrev P := ℝ × (ℝ × ℝ)
abbrev Cylinder := ℝ × (AddCircle (6:ℝ) × AddCircle (6:ℝ))
abbrev Deck := PUnit.{1} × (CircleConstruction.Deck 6 × CircleConstruction.Deck 6)
instance identity_action : MulAction PUnit.{1} ℝ where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
lemma identity_cover : IsQuotientCoveringMap (id : ℝ → ℝ) PUnit.{1} where
  __ := Homeomorph.refl ℝ |>.isQuotientMap
  continuous_const_smul _ := continuous_id
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro h; exact ⟨PUnit.unit,h.symm⟩
    · rintro ⟨k,h⟩; exact h.symm
  disjoint _ := ⟨univ,univ_mem,fun _ _ => Subsingleton.elim _ _⟩
instance torus_action : MulAction (CircleConstruction.Deck 6 × CircleConstruction.Deck 6) (ℝ × ℝ) :=
  productAction
instance cylinder_action : MulAction Deck P := productAction

def projection (x : P) : Cylinder := (x.1,(x.2.1 : AddCircle (6 : ℝ)),(x.2.2 : AddCircle (6 : ℝ)))
lemma projection_cover : IsQuotientCoveringMap projection Deck :=
  product_cover identity_cover (product_cover (CircleConstruction.projection_cover 6)
    (CircleConstruction.projection_cover 6))

lemma projection_smooth : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ projection := by
  have h0 : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ) ∞ (fun x : P => x.1) :=
    contDiff_fst.contMDiff
  have h1 : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ) ∞ (fun x : P => (x.2.1 : AddCircle (6:ℝ))) :=
    (CircleConstruction.projection_smooth 6).comp
      (contDiff_fst.comp contDiff_snd).contMDiff
  have h2 : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ) ∞ (fun x : P => (x.2.2 : AddCircle (6:ℝ))) :=
    (CircleConstruction.projection_smooth 6).comp
      (contDiff_snd.comp contDiff_snd).contMDiff
  convert! h0.prodMk (h1.prodMk h2) using 1
  simp only [← modelWithCornersSelf_prod]

lemma deck_formula (k : Deck) (x : P) : k • x =
    x + (0,(Multiplicative.toAdd k.2.1).val,(Multiplicative.toAdd k.2.2).val) := by
  apply Prod.ext
  · change x.1 = x.1 + 0
    ring
  · apply Prod.ext
    · change (Multiplicative.toAdd k.2.1).val + x.2.1 = x.2.1 + (Multiplicative.toAdd k.2.1).val
      ring
    · change (Multiplicative.toAdd k.2.2).val + x.2.2 = x.2.2 + (Multiplicative.toAdd k.2.2).val
      ring

lemma action_smooth (k : Deck) : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ (fun x : P => k • x) := by
  simp only [deck_formula]
  exact contMDiff_id.add contMDiff_const

lemma local_sections (q : Cylinder) : ∃ s : Cylinder → P,
    ContMDiffAt 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ s q ∧ (projection ∘ s) =ᶠ[nhds q] id := by
  let f := CircleConstruction.localLift 6 q.2.1
  let g := CircleConstruction.localLift 6 q.2.2
  refine ⟨fun y => (y.1,f y.2.1,g y.2.2),?_,?_⟩
  · have h1 := (CircleConstruction.localLift_smooth 6 q.2.1).comp q
      ((contMDiffAt_fst (I := 𝓘(ℝ,ℝ)) (J := 𝓘(ℝ,ℝ))).comp q
        (contMDiffAt_snd (I := 𝓘(ℝ,ℝ)) (J := 𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ))))
    have h2 := (CircleConstruction.localLift_smooth 6 q.2.2).comp q
      ((contMDiffAt_snd (I := 𝓘(ℝ,ℝ)) (J := 𝓘(ℝ,ℝ))).comp q
        (contMDiffAt_snd (I := 𝓘(ℝ,ℝ)) (J := 𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ))))
    convert! ((contMDiffAt_fst (I := 𝓘(ℝ,ℝ)) (J := 𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ))).prodMk_space
        (h1.prodMk_space h2)) using 1
    simp only [← modelWithCornersSelf_prod]
  · have h1 := (CircleConstruction.localLift_eventually 6 q.2.1).comp_tendsto
      (continuous_fst.comp continuous_snd).continuousAt
    have h2 := (CircleConstruction.localLift_eventually 6 q.2.2).comp_tendsto
      (continuous_snd.comp continuous_snd).continuousAt
    filter_upwards [h1,h2] with y hy1 hy2
    exact Prod.ext rfl (Prod.ext hy1 hy2)

lemma local_inverse_smooth (a : P) {q : Cylinder}
    (hq : q ∈ (projection_cover.isCoveringMap.isLocalHomeomorph.localInverseAt a).source) :
    ContMDiffAt 𝓘(ℝ,P) 𝓘(ℝ,P) ∞
      (projection_cover.isCoveringMap.isLocalHomeomorph.localInverseAt a) q :=
  inverse_smooth_of_sections projection_cover action_smooth local_sections a hq

def coordinates : P ≃L[ℝ] V3 :=
  { toFun := fun x => ![x.1,x.2.1,x.2.2]
    invFun := fun v => (v 0,v 1,v 2)
    left_inv := by intro x; rfl
    right_inv := by intro v; ext i; fin_cases i <;> rfl
    map_add' := by intro x y; ext i; fin_cases i <;> rfl
    map_smul' := by intro a x; ext i; fin_cases i <;> rfl }

def model {r s c : V3 → ℝ}
    (h1 : ContDiff ℝ ∞ r) (h2 : ContDiff ℝ ∞ s) (h3 : ContDiff ℝ ∞ c)
    (hr : ∀ x, r x ≠ 0) (hs : ∀ x, s x ≠ 0) : Metric (E := P) P :=
  pullback (triangularMetric h1 h2 h3 hr hs) coordinates.contDiff.contMDiff
    (fun _ => coordinates) (fun x => by
      rw [mfderiv_eq_fderiv]
      exact (coordinates.hasFDerivAt (x := x)).fderiv.symm)

lemma model_apply {r s c : V3 → ℝ}
    (h1 : ContDiff ℝ ∞ r) (h2 : ContDiff ℝ ∞ s) (h3 : ContDiff ℝ ∞ c)
    (hr : ∀ x, r x ≠ 0) (hs : ∀ x, s x ≠ 0)
    (x : P) (u v : TangentSpace 𝓘(ℝ,P) x) :
    (model h1 h2 h3 hr hs).inner x u v =
      u.1*v.1 + (r (coordinates x))^2*(u.2.1-c (coordinates x)*u.2.2)*
        (v.2.1-c (coordinates x)*v.2.2) + (s (coordinates x))^2*u.2.2*v.2.2 := by
  change (triangularMetric h1 h2 h3 hr hs).inner (coordinates x)
    (mfderiv 𝓘(ℝ,P) 𝓘(ℝ,V3) coordinates x u)
    (mfderiv 𝓘(ℝ,P) 𝓘(ℝ,V3) coordinates x v) = _
  rw [mfderiv_eq_fderiv,(coordinates.hasFDerivAt (x := x)).fderiv]
  exact triangularMetric_apply h1 h2 h3 hr hs _ _ _

lemma deck_deriv (k : Deck) (x : P) :
    mfderiv 𝓘(ℝ,P) 𝓘(ℝ,P) (fun y : P => k • y) x = ContinuousLinearMap.id ℝ P := by
  simp only [deck_formula,mfderiv_eq_fderiv]
  exact ((hasFDerivAt_id x).add_const _).fderiv

variable {r s c : ℝ → ℝ}
    (h1 : ContDiff ℝ ∞ r) (h2 : ContDiff ℝ ∞ s) (h3 : ContDiff ℝ ∞ c)
    (hr : ∀ t, r t ≠ 0) (hs : ∀ t, s t ≠ 0)

def lifted : Metric (E := P) P :=
  model (h1.comp (contDiff_apply ℝ ℝ 0)) (h2.comp (contDiff_apply ℝ ℝ 0))
    (h3.comp (contDiff_apply ℝ ℝ 0)) (fun _ => hr _) (fun _ => hs _)

lemma lifted_apply (x : P) (u v : TangentSpace 𝓘(ℝ,P) x) :
    (lifted h1 h2 h3 hr hs).inner x u v =
      u.1*v.1 + (r x.1)^2*(u.2.1-c x.1*u.2.2)*(v.2.1-c x.1*v.2.2) +
        (s x.1)^2*u.2.2*v.2.2 :=
  model_apply _ _ _ _ _ x u v

lemma lifted_invariant (k : Deck) (x : P) :
    pullInner (E := P) (lifted h1 h2 h3 hr hs) (fun y : P => k • y) x =
      (lifted h1 h2 h3 hr hs).inner x := by
  ext u v
  rw [pullInner_apply,deck_deriv,lifted_apply,lifted_apply]
  rfl

def sectionMap (q : Cylinder) : P :=
  (q.1,CircleConstruction.sectionMap 6 q.2.1,CircleConstruction.sectionMap 6 q.2.2)
lemma section_spec : Function.RightInverse sectionMap projection := by
  intro q
  exact Prod.ext rfl (Prod.ext (CircleConstruction.section_spec 6 q.2.1)
    (CircleConstruction.section_spec 6 q.2.2))

def metric : Metric (E := P) Cylinder :=
  descend projection_cover projection_smooth action_smooth local_inverse_smooth
    (lifted h1 h2 h3 hr hs) (lifted_invariant h1 h2 h3 hr hs) section_spec

lemma metric_projection (x : P) :
    pullInner (E := P) (metric h1 h2 h3 hr hs) projection x =
      (lifted h1 h2 h3 hr hs).inner x :=
  descend_projection projection_cover projection_smooth action_smooth local_inverse_smooth
    (lifted h1 h2 h3 hr hs) (lifted_invariant h1 h2 h3 hr hs) section_spec x

end ThreeManifold.CylinderConstruction

namespace ThreeManifold.MetricConstruction
variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def pullbackHomeomorph (g : Metric (E := F) N) (f : M ≃ₜ N)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hi : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ f.symm) : Metric (E := E) M :=
  pullback g hf
    (fun x => (show f.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,F) from
      ⟨hf.mdifferentiable (by simp) |>.mdifferentiableOn,
        hi.mdifferentiable (by simp) |>.mdifferentiableOn⟩).mfderiv (mem_univ x))
    (fun _ => rfl)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma bilin_eq_of_pull_eq {p : M → N} (x : M)
    (hp : Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) p x))
    (g h : TangentSpace 𝓘(ℝ,F) (p x) →L[ℝ] TangentSpace 𝓘(ℝ,F) (p x) →L[ℝ] ℝ)
    (he : pullBilin (E:=E) (F:=F) g (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) p x) =
      pullBilin (E:=E) (F:=F) h (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) p x)) : g = h := by
  ext u v
  obtain ⟨a,rfl⟩ := hp u
  obtain ⟨b,rfl⟩ := hp v
  exact congrArg (fun L => L a b) he

variable {Q G : Type*} [TopologicalSpace Q] [ChartedSpace E Q]
  [IsManifold 𝓘(ℝ,E) ∞ Q] [Group G] [MulAction G M] {p : M → Q}
  (hp : IsQuotientCoveringMap p G)
  (hps : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ p)
  (hls : ∀ (b : M) {q : Q}, q ∈ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b).source →
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b) q)

def coveringDerivative (x : M) : E ≃L[ℝ] E :=
  ((covering_inverse_mdifferentiable hp hps hls x).symm).mfderiv
    (hp.isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,E) ∞ Q] in
lemma coveringDerivative_eq (x : M) :
    (coveringDerivative hp hps hls x).toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) p x := by
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
    (hp.isCoveringMap.isLocalHomeomorph.localInverseAt x).symm x = _
  rw [hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm]

variable {f : Q → Q} {lift : M → M}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ f)
    (hl : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ lift)
    (comm : f ∘ p = p ∘ lift)
    (dl : M → E ≃L[ℝ] E)
    (hdl : ∀ x, (dl x).toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) lift x)
    {σ : Q → M} (hσ : Function.RightInverse σ p)

def liftedDerivative (q : Q) : E ≃L[ℝ] E :=
  ((coveringDerivative hp hps hls (σ q)).symm.trans (dl (σ q))).trans
    (coveringDerivative hp hps hls (lift (σ q)))

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,E) ∞ Q] in
include hf hl comm hdl hσ in
lemma liftedDerivative_eq (q : Q) :
    (liftedDerivative hp hps hls dl (σ := σ) (lift := lift) q).toContinuousLinearMap =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f q := by
  have hc := congrArg (fun w : M → Q => (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) w (σ q))) comm
  rw [mfderiv_comp _ ((hf _).mdifferentiableAt (by simp))
    ((hps _).mdifferentiableAt (by simp)), mfderiv_comp _
      ((hps _).mdifferentiableAt (by simp)) ((hl _).mdifferentiableAt (by simp)), hσ q] at hc
  have hc' (v : E) : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f q (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) p (σ q) v) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) p (lift (σ q)) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) lift (σ q) v) :=
    congrArg (fun L : E →L[ℝ] E => L v) hc
  apply ContinuousLinearMap.ext
  intro u
  have hh := hc' ((coveringDerivative hp hps hls (σ q)).symm u)
  rw [← coveringDerivative_eq hp hps hls (σ q)] at hh
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f q
    ((coveringDerivative hp hps hls (σ q)) ((coveringDerivative hp hps hls (σ q)).symm u)) = _ at hh
  rw [ContinuousLinearEquiv.apply_symm_apply] at hh
  change (coveringDerivative hp hps hls (lift (σ q)))
    (dl (σ q) ((coveringDerivative hp hps hls (σ q)).symm u)) = _
  have hd := congrArg (fun D : E →L[ℝ] E => D
    ((coveringDerivative hp hps hls (σ q)).symm u)) (hdl (σ q))
  have hd' := congrArg (fun D : E →L[ℝ] E => D
    (dl (σ q) ((coveringDerivative hp hps hls (σ q)).symm u)))
      (coveringDerivative_eq hp hps hls (lift (σ q)))
  exact hd'.trans ((congrArg (fun v : E =>
    (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) p (lift (σ q))) v) hd).trans hh.symm)

def pullbackFromLift (g : Metric (E := E) Q) : Metric (E := E) Q :=
  pullback g hf (liftedDerivative hp hps hls dl (σ := σ) (lift := lift))
    (liftedDerivative_eq hp hps hls hf hl comm dl hdl hσ)
end ThreeManifold.MetricConstruction
end

open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.MetricConstruction
variable {E F H M N Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold 𝓘(ℝ,H) ∞ Q]
lemma pull_composition (g : Metric (E := H) Q) {f : M → N} {h : N → Q} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f x)
    (hh : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,H) h (f x)) :
    pullInner (E := E) g (h ∘ f) x =
      pullBilin (E := E) (F := F) (pullInner g h (f x)) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x) := by
  ext u v
  simp only [pullInner_apply,Function.comp_apply]
  rw [mfderiv_comp x hh hf]
  rfl
end ThreeManifold.MetricConstruction

end

end OAI


