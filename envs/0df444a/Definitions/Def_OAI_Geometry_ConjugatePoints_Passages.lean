-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Passages
-- name    : OAI_Geometry_ConjugatePoints_Passages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:49:12.609104+00:00
-- url     : https://prove2.me/theorems/027aabec-cead-4dd9-b464-7b4096d5b8c4
-- title:
--   Neck position maps, normalized neck metrics and reflection and cut-off operations for geodesic passages
-- statement:
--   This file builds the coordinate map that places the neck region of the glued manifold $M$ inside a model cylinder, shows it is a local isometry onto a model neck metric, rescales that model to a normalized metric on $\mathbb{R}^3$ (in two frames), and defines the elementary reflection and cut-off operations used to extend functions and vector fields along geodesic passages through the neck.
--
--   **Setting.** $\Sigma=\mathbb{H}/\bar\Gamma$ is the cusped hyperbolic surface with projection $\pi$ and height $h$ (as in the companion files), $S^1=\mathbb{R}/6\mathbb{Z}$, $W=\Sigma\times S^1$, $X=\{x\in\Sigma:h(x)<\log8\}\times S^1$ is the piece, $C\subset X$ the collar, $\Phi:C\to C$ the gluing map and $M=X_0\cup_\Phi X_1$ the glued manifold with inclusions $\iota_0,\iota_1$. The cylinder is $\mathcal{C}=\mathbb{R}\times(S^1\times S^1)$. Throughout $\delta\in(0,1/2]$; $\ell_\delta(t)=\exp\big(-\int_0^t k_\delta\big)>0$ is the collar profile of the cometric construction and $\chi(t)=S(6(t-5/12))$, where $S$ is the standard smooth step function ($S=0$ on $(-\infty,0]$, $S=1$ on $[1,\infty)$). Points of $\mathbb{R}^3$ are written $x=(x_0,x_1,x_2)$.
--
--   1. **Descending maps through the gluing.** For a two-piece gluing $Y_0\cup_e Y_1$ of two copies of a space $Y$ along a homeomorphism $e$ of an open set $O\subset Y$, and $f_0,f_1:Y\to Z$, the map $\operatorname{desc}(f)$ evaluates $f_i(y)$ at a chosen representative $(i,y)$ of a point. If $f_0(y)=f_1(e(y))$ for all $y\in O$, then $\operatorname{desc}(f)(\iota_i(y))=f_i(y)$ for all $i$ and $y$.
--
--   2. **Logarithmic cusp coordinates.** For $a>1$, $\Lambda_a:W\to\mathcal{C}$ sends $(\pi(z),u)$ with $\operatorname{Im}z>a$ to $(\log\operatorname{Im}z,(\operatorname{Re}z\bmod6,u))$ (its values outside this cusp region play no role). For $1<a\le b$, $\Lambda_a=\Lambda_b$ on the cusp region of level $b$.
--
--   3. **Piece and neck positions.** With $L_\delta=4-2\log\delta$, $q=e^{1/8}$, the radial reparametrization $\rho_L(r,w)=(\varrho_L(r),w)$, where $\varrho_L(r)=(1-\kappa(r))(r-L-1)+\kappa(r)\frac{r-\log2}{\log4}$ and $\kappa(r)=S(4r-1)$, and the switch $\mathrm{sw}(t,(\theta_1,\theta_2))=(1-t,(\theta_1+\theta_2,\theta_1))$, the piece positions $X\to\mathcal{C}$ are
--   $$
--   P^\delta_0=\rho_{L_\delta}\circ\Lambda_q\circ j,\qquad P^\delta_1=\mathrm{sw}\circ\rho_4\circ\Lambda_q\circ j,
--   $$
--   where $j(x,u)=(x,u)\in W$ forgets the height bound. On the collar they satisfy $P^\delta_0(c)=P^\delta_1(\Phi(c))$, so they descend to the neck position $N_\delta:M\to\mathcal{C}$ with $N_\delta\circ\iota_i=P^\delta_i$.
--
--   4. **Extended neck.** $X^{+}=\{(x,u)\in X:h(x)>1/2\}$ is open and lies in the cusp region of level $q$; $M^{+}=\iota_0(X^{+})\cup\iota_1(X^{+})$ is open in $M$. On $X^{+}$ the maps $P^\delta_i$ are $C^\infty$, and $N_\delta$ is $C^\infty$ on $M^{+}$. The interface band is $\{(x,u)\in X:\log2\le h(x)\le\log4\}$.
--
--   5. **Metric identities.** Let $\mathfrak n_{\delta,B}$ be the neck metric on $\mathcal{C}$ induced from the metric on $\mathbb{R}^3$ given below with radii $r_1=\frac{\delta^2B}{6}\ell_\delta(t)$, $r_2=\frac{B}{6}\ell_\delta(1-t)$, and let $B=p_\delta=6/(e^4\ell_\delta(-1))$. Then on $X^{+}$ the pull-back of $\mathfrak n_{\delta,p_\delta}$ under $P^\delta_i$ equals the metric of the $i$-th piece (the metric on the $i$-th copy of $X$ from which $g_\delta$ is glued), and on $M^{+}$
--   $$
--   N_\delta^{*}\,\mathfrak n_{\delta,p_\delta}=g_\delta ,
--   $$
--   where $g_\delta$ is the compact glued metric on $M$. Hence $N_\delta$ is a local metric isometry from $(M,g_\delta)$ to $(\mathcal{C},\mathfrak n_{\delta,p_\delta})$ with domain $M^{+}$: a map that is smooth on an open domain and satisfies $g_p(u,v)=\mathfrak n_{N(p)}(dN\,u,dN\,v)$ there.
--
--   6. **Normalized neck.** The normalized neck metric on $\mathbb{R}^3$ is
--   $$
--   \langle u,v\rangle_x=u_0v_0+\ell_\delta(x_0)^2\,(u_1-\delta^2\chi(x_0)u_2)(v_1-\delta^2\chi(x_0)v_2)+\ell_\delta(1-x_0)^2\,u_2v_2 .
--   $$
--   For $B>0$, the linear map $\nu(x)=(x_0,\tfrac{\delta^2B}{6}x_1,\tfrac{B}{6}x_2)$ is a global isometry from the model metric $u_0v_0+r_1^2(u_1-\chi u_2)(v_1-\chi v_2)+r_2^2u_2v_2$ (with $r_1,r_2$ as in item 5, evaluated at $x_0$) to the normalized neck metric.
--
--   7. **Right frame.** $F_\delta(y)=(-y_0,\ \delta^2y_1+y_2,\ y_1)$ is a linear isomorphism of $\mathbb{R}^3$, the affine map $y\mapsto F_\delta(y)+(1,0,0)$ is smooth with derivative $F_\delta$, the right-normalized metric is the pull-back of the normalized neck metric under this affine map (which is then a global isometry), and the framed neck metric is the right-normalized metric for the right frame and the normalized metric for the left frame.
--
--   8. **Reflections and cut-offs.** For $c\in\mathbb{R}$ and $f:\mathbb{R}\to\mathbb{R}$, the even and odd reflections are $f(s)$ for $s\le c$ and, for $s>c$, $f(2c-s)$, respectively $-f(2c-s)$. For a vector-valued $V$ and $b\in\mathbb{R}$, the cut-off is $V(s)$ for $s\le b$ and $0$ for $s>b$. For a local metric isometry $f:M\to N$, a curve $\gamma$ in $M$ and a field $J$ along $f\circ\gamma$, the pulled-back field is $s\mapsto(df_{\gamma(s)})^{-1}J(s)$.
--
--   These objects transfer the analysis of geodesics and Jacobi fields that cross the neck of $(M,g_\delta)$ to explicit metrics on $\mathbb{R}^3$, where the passage estimates are carried out.
--
--   **Formalization Note** The neck position is `neckPosition` (built with `TwoGluing.descend`) and the local isometry is `neckPositionIsometry`, which uses $\mathbb{R}^3$-valued charts on $M$ and $\mathcal{C}$ (`realCompactMetric`, `realNeck`). The inverse $(df)^{-1}$ in `unmapField` is `ContinuousLinearMap.inverse`, which is $0$ when $df$ is not invertible. Members recorded as `null` in the packet are auxiliary instances or lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Passages.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Passage supports, extension, and compact metric estimates.
-/

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X Y : Type} [TopologicalSpace X] (O : TopologicalSpace.Opens X) (e : O ≃ₜ O)
def descend (f : Bool → X → Y) : Space O e → Y :=
  fun p => f (representative O e p).1 (representative O e p).2
lemma descend_inclusion (f : Bool → X → Y)
    (hf : ∀ x : O, f false x.1 = f true (e x).1) (i : Bool) (x : X) :
    descend O e f (inclusion O e i x) = f i x := by
  let p := representative O e (inclusion O e i x)
  have he : inclusion O e p.1 p.2 = inclusion O e i x := representative_spec O e _
  change f p.1 p.2 = f i x
  rcases p with ⟨j,y⟩
  cases j <;> cases i
  · exact congrArg (f false) ((inclusion_openEmbedding O e false).injective he)
  · obtain ⟨hy,hxy⟩ := (inclusion_mixed_eq O e _ _).mp he
    exact (hf ⟨y,hy⟩).trans (congrArg (f true) hxy)
  · obtain ⟨hx,hxy⟩ := (inclusion_mixed_eq O e _ _).mp he.symm
    exact (congrArg (f true) hxy.symm).trans (hf ⟨x,hx⟩).symm
  · exact congrArg (f true) ((inclusion_openEmbedding O e true).injective he)
end ThreeManifold.TwoGluing
namespace ThreeManifold.CompactMetric

section
open MetricConstruction CylinderConstruction GluedConstruction
lemma logCuspMap_change (a b : ℝ) (ha : 1 < a) (hb : 1 < b) (hab : a ≤ b)
    {q : WholePiece} (hq : q ∈ wholeCusp b) :
    logCuspMap a ha q = logCuspMap b hb q := by
  obtain ⟨z,hz,hzq⟩ := hq
  let r := CircleConstruction.sectionMap 6 q.2
  have he : sourceProjection (z,r) = q := Prod.ext hzq (CircleConstruction.section_spec 6 q.2)
  rw [← he,logCusp_projection_apply a ha (z,r) (hab.trans_lt hz),logCusp_projection_apply b hb (z,r) hz]

def piecePosition (δ : ℝ) (i : Bool) : Piece → Cylinder :=
  if i then switch ∘ radial 4 ∘ logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap
  else radial (leftLength δ) ∘ logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap
lemma piecePosition_collar (δ : ℝ) (x : collar) :
    piecePosition δ false x.1 = leftPosition δ x ∧
    piecePosition δ true x.1 = rightPosition x := by
  have he := logCuspMap_change cuspLevel 2 cuspLevel_gt (by norm_num) cuspLevel_lt_two.le
    (q := pieceMap x.1) (show pieceMap x.1 ∈ wholeCusp 2 from x.2)
  constructor <;> dsimp [piecePosition,leftPosition,rightPosition,collarLog] <;> rw [he]
lemma piecePosition_match (δ : ℝ) (x : collar) :
    piecePosition δ false x.1 = piecePosition δ true (gluingMap x).1 := by
  rw [(piecePosition_collar δ x).1,(piecePosition_collar δ (gluingMap x)).2]
  exact (congrFun (position_match δ) x).symm

def neckPosition (δ : ℝ) : GluedConstruction.Manifold → Cylinder :=
  TwoGluing.descend collar gluingMap (piecePosition δ)
lemma neckPosition_inclusion (δ : ℝ) (i : Bool) (x : Piece) :
    neckPosition δ (inclusion i x) = piecePosition δ i x :=
  TwoGluing.descend_inclusion collar gluingMap _ (piecePosition_match δ) i x

def extendedPiece : Set Piece := {x | (1/2:ℝ) < HyperbolicCore.height x.1.1}
lemma extendedPiece_isOpen : IsOpen extendedPiece :=
  isOpen_lt continuous_const ((HyperbolicCore.height_continuous.comp continuous_subtype_val).comp continuous_fst)
lemma extendedPiece_cusp {x : Piece} (hx : x ∈ extendedPiece) : pieceMap x ∈ wholeCusp cuspLevel := by
  apply (HyperbolicCore.mem_cusp_iff_height cuspLevel_gt x.1.1).mpr
  rw [log_cuspLevel]
  change (1/2:ℝ) < HyperbolicCore.height x.1.1 at hx
  linarith

def extendedNeck : Set GluedConstruction.Manifold :=
  inclusion false '' extendedPiece ∪ inclusion true '' extendedPiece
lemma extendedNeck_isOpen : IsOpen extendedNeck :=
  ((TwoGluing.inclusion_openEmbedding collar gluingMap false).isOpenMap _ extendedPiece_isOpen).union
    ((TwoGluing.inclusion_openEmbedding collar gluingMap true).isOpenMap _ extendedPiece_isOpen)
lemma extendedNeck_representative {p : GluedConstruction.Manifold} (hp : p ∈ extendedNeck) :
    ∃ i x, x ∈ extendedPiece ∧ inclusion i x = p := by
  rcases hp with ⟨x,hx,rfl⟩|⟨x,hx,rfl⟩
  · exact ⟨false,x,hx,rfl⟩
  · exact ⟨true,x,hx,rfl⟩
lemma neckPosition_germ (δ : ℝ) (i : Bool) {p : GluedConstruction.Manifold}
    (hp : p ∈ (pieceOpenMap i).target) :
    neckPosition δ =ᶠ[𝓝 p] piecePosition δ i ∘ (pieceOpenMap i).symm := by
  filter_upwards [(pieceOpenMap i).open_target.mem_nhds hp] with q hq
  calc neckPosition δ q = neckPosition δ (inclusion i ((pieceOpenMap i).symm q)) :=
        congrArg (neckPosition δ) ((pieceOpenMap i).right_inv hq).symm
    _ = _ := neckPosition_inclusion δ i _
lemma piecePosition_smooth {δ : ℝ} (i : Bool) {x : Piece} (hx : x ∈ extendedPiece) :
    ContMDiffAt 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (piecePosition δ i) x := by
  have hs := (logCuspMap_smoothAt cuspLevel cuspLevel_gt (extendedPiece_cusp hx)).comp x (pieceMap_smooth x)
  cases i
  · exact ((radial_smooth (leftLength δ)) _).comp x hs
  · exact (switch_smooth _).comp x (((radial_smooth 4) _).comp x hs)
lemma neckPosition_smooth (δ : ℝ) {p : GluedConstruction.Manifold} (hp : p ∈ extendedNeck) :
    ContMDiffAt 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (neckPosition δ) p := by
  obtain ⟨i,x,hx,rfl⟩ := extendedNeck_representative hp
  have ht : inclusion i x ∈ (pieceOpenMap i).target := (pieceOpenMap i).map_source (mem_univ x)
  have hs : ContMDiffAt 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (piecePosition δ i) ((pieceOpenMap i).symm (inclusion i x)) := by
    rw [pieceOpenMap_inclusion]
    exact piecePosition_smooth i hx
  exact (hs.comp _ (pieceOpenMap_inverse_smooth i ht)).congr_of_eventuallyEq (neckPosition_germ δ i ht)
end

section
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
lemma pieceMetric_cusp (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
    (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
      pullInner (E := P) g projection x u v =
        u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)
    {x : Piece} (hx : x ∈ extendedPiece) :
    pullInner (E := EP) g (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap) x =
      (pieceMetric (wholeMetric g c hc low)).inner x := by
  rw [pull_composition _ ((pieceMap_smooth x).mdifferentiableAt (by simp))
    ((logCuspMap_smoothAt cuspLevel cuspLevel_gt (extendedPiece_cusp hx)).mdifferentiableAt (by simp)),
    ← cuspMetric_inner g cuspLevel cuspLevel_gt (extendedPiece_cusp hx),
    ← wholeMetric_cusp g c hc low (extendedPiece_cusp hx)]
  rfl
lemma piecePosition_metric {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool)
    {x : Piece} (hx : x ∈ extendedPiece) :
    pullInner (E := EP) (neck hδ (period_pos δ)) (piecePosition δ i) x =
      (pieceMetrics hδ i).inner x := by
  have hs := (logCuspMap_smoothAt cuspLevel cuspLevel_gt (extendedPiece_cusp hx)).comp x (pieceMap_smooth x)
  cases i
  · change pullInner (E := EP) (neck hδ (period_pos δ))
      (radial (leftLength δ) ∘ (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap)) x = _
    rw [pull_composition _ (hs.mdifferentiableAt (by simp))
      ((radial_smooth (leftLength δ) _).mdifferentiableAt (by simp))]
    change pullBilin (E := EP) (F := P) ((leftCylinder hδ).inner _)
      (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,P) (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap) x) = _
    exact pieceMetric_cusp _ _ _ (leftCylinder_low hδ) hx
  · change pullInner (E := EP) (neck hδ (period_pos δ))
      (switch ∘ (radial 4 ∘ (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap))) x = _
    rw [pull_composition _ (((radial_smooth 4 _).comp x hs).mdifferentiableAt (by simp))
      ((switch_smooth _).mdifferentiableAt (by simp))]
    change pullInner (E := EP) (switched (neck hδ (period_pos δ)))
      (radial 4 ∘ (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap)) x = _
    rw [pull_composition _ (hs.mdifferentiableAt (by simp))
      ((radial_smooth 4 _).mdifferentiableAt (by simp))]
    change pullInner (E := EP) (rightCylinder hδ) (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap) x = _
    exact pieceMetric_cusp _ _ _ (rightCylinder_low hδ) hx

lemma neckPosition_metric {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {p : GluedConstruction.Manifold} (hp : p ∈ extendedNeck) :
    pullInner (E := EP) (neck hδ (period_pos δ)) (neckPosition δ) p = (compactMetric hδ).inner p := by
  obtain ⟨i,x,hx,rfl⟩ := extendedNeck_representative hp
  apply bilin_eq_of_pull_eq (E := EP) (F := EP) x
    ((pieceOpenMap_mdifferentiable i).mfderiv_surjective (mem_univ x))
  have hd := pull_composition (neck hδ (period_pos δ))
    ((inclusion_smooth i x).mdifferentiableAt (by simp))
    ((neckPosition_smooth δ hp).mdifferentiableAt (by simp))
  have he : neckPosition δ ∘ inclusion i = piecePosition δ i := funext (neckPosition_inclusion δ i)
  exact hd.symm.trans ((congrArg (fun f => pullInner (E := EP) (neck hδ (period_pos δ)) f x) he).trans
    ((piecePosition_metric hδ i hx).trans (compactMetric_local hδ i x).symm))

local instance instChartedSpaceE3Cylinder_2 : ChartedSpace E3 Cylinder := Rechart.charts coordinates
local instance instIsManifoldRealE3I3SomeENatTopCylinder_2 : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates

def neckPositionIsometry {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) :
    LocalMetricIsometry (realCompactMetric hδ) (realNeck hδ (period_pos δ)) (neckPosition δ) :=
  Rechart.realIsometry Coordinates3.coordinates coordinates _ _ _ extendedNeck extendedNeck_isOpen
    (fun _ hp => (neckPosition_smooth δ hp).contMDiffWithinAt) (fun _ hp => neckPosition_metric hδ hp)
end

open MetricConstruction CylinderConstruction GluedConstruction
def interfaceBand : Set Piece := {x | Real.log 2 ≤ HyperbolicCore.height x.1.1 ∧
  HyperbolicCore.height x.1.1 ≤ Real.log 4}
end ThreeManifold.CompactMetric

namespace ThreeManifold.CylinderConstruction

section
open QuotientConstruction

end

local instance instChartedSpaceE3Cylinder_1 : ChartedSpace E3 Cylinder := Rechart.charts coordinates
local instance instIsManifoldRealE3I3SomeENatTopCylinder_1 : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates
end ThreeManifold.CylinderConstruction
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates Cometric Neck

def normalizedNeck {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : SmoothMetric E3 :=
  euclideanMetric (Collar.ell_smooth ⟨hδ.1.le,hδ.2⟩)
    ((Collar.ell_smooth ⟨hδ.1.le,hδ.2⟩).comp (contDiff_const.sub contDiff_id))
    ((contDiff_const (c := δ^2)).mul χ_smooth)
    (fun t => (Collar.ell_pos δ t).ne') (fun t => (Collar.ell_pos δ (1-t)).ne')

lemma normalizedNeck_apply {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (x u v : E3) :
    (normalizedNeck hδ).inner x u v = u 0*v 0 + (Collar.ell δ (x 0))^2 *
      (u 1-δ^2*χ (x 0)*u 2)*(v 1-δ^2*χ (x 0)*v 2) +
      (Collar.ell δ (1-x 0))^2*u 2*v 2 := by
  unfold normalizedNeck euclideanMetric
  apply triangularMetric_apply

def normalize (δ B : ℝ) : E3 →L[ℝ] E3 :=
  { toFun := fun x => ![x 0,δ^2*B/6*x 1,B/6*x 2]
    map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
    map_smul' := by intro a x; ext i; fin_cases i <;> simp <;> ring }

def normalizationIsometry {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) :
    LocalMetricIsometry (neckModel hδ hB) (normalizedNeck hδ) (normalize δ B) where
  domain := univ
  isOpen_domain := isOpen_univ
  smooth := (normalize δ B).contDiff.contMDiff.contMDiffOn
  metric := by
    intro x _ u v
    rw [mfderiv_eq_fderiv,(normalize δ B).hasFDerivAt.fderiv]
    change (neckModel hδ hB).inner x (show E3 from u) (show E3 from v) =
      (normalizedNeck hδ).inner (normalize δ B x) (normalize δ B u) (normalize δ B v)
    rw [neckModel_apply,normalizedNeck_apply]
    simp only [normalize,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,radius₁,radius₂]
    ring

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
def unmapField (_P : LocalMetricIsometry g h f) (γ : ℝ → M)
    (J : ∀ s, TangentSpace I3 ((f ∘ γ) s)) : ∀ s, TangentSpace I3 (γ s) :=
  fun s => (mfderiv I3 I3 f (γ s)).inverse (J s)
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
local instance instChartedSpaceE3Cylinder_3 : ChartedSpace E3 Cylinder := Rechart.charts coordinates
local instance instIsManifoldRealE3I3SomeENatTopCylinder_3 : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.FinitePassage

end ThreeManifold.FinitePassage
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
local instance instChartedSpaceE3Cylinder_4 : ChartedSpace E3 Cylinder := Rechart.charts coordinates
local instance instIsManifoldRealE3I3SomeENatTopCylinder_4 : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.PassageDynamics

def reflectEven (c : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ := if s ≤ c then f s else f (2*c-s)
def reflectOdd (c : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ := if s ≤ c then f s else -f (2*c-s)

end ThreeManifold.PassageDynamics

namespace ThreeManifold.SupportExtension
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def cut (b : ℝ) (V : ℝ → E) (s : ℝ) : E := if s ≤ b then V s else 0
end ThreeManifold.SupportExtension
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck
end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end

section
open RiemannianCoordinates MetricConstruction Cometric Neck LocalNeck ReturningPassage

def fromRightLinear (δ : ℝ) : E3 ≃L[ℝ] E3 :=
  { toLinearEquiv :=
      { toFun := fun y => ![-y 0,δ^2*y 1+y 2,y 1]
        invFun := fun x => ![-x 0,x 2,x 1-δ^2*x 2]
        left_inv := by intro y; ext i; fin_cases i <;> simp
        right_inv := by intro x; ext i; fin_cases i <;> simp
        map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
        map_smul' := by intro a x; ext i; fin_cases i <;> simp [mul_add,mul_left_comm] }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
def fromRight (δ : ℝ) (y : E3) : E3 := fromRightLinear δ y + ![1,0,0]
lemma fromRight_smooth (δ : ℝ) : ContDiff ℝ ∞ (fromRight δ) :=
  (fromRightLinear δ).contDiff.add contDiff_const
lemma fromRight_deriv (δ : ℝ) (y : E3) :
    mfderiv I3 I3 (fromRight δ) y = (fromRightLinear δ : E3 →L[ℝ] E3) := by
  rw [mfderiv_eq_fderiv]
  exact ((fromRightLinear δ).hasFDerivAt.add_const _).fderiv

def normalizedRight {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : SmoothMetric E3 :=
  pullback (normalizedNeck hδ) (fromRight_smooth δ).contMDiff
    (fun _ => fromRightLinear δ) (fun y => (fromRight_deriv δ y).symm)

def fromRightIsometry {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) :
    LocalMetricIsometry (normalizedRight hδ) (normalizedNeck hδ) (fromRight δ) where
  domain := univ
  isOpen_domain := isOpen_univ
  smooth := (fromRight_smooth δ).contMDiff.contMDiffOn
  metric := by intro x _ u v; rfl

def framedNeck (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : SmoothMetric E3 :=
  if right then normalizedRight hδ else normalizedNeck hδ

end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients
end ThreeManifold.CompactMetric

end

end OAI


