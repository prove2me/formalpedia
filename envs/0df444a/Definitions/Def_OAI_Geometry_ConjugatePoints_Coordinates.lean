-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
-- name    : OAI_Geometry_ConjugatePoints_Coordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:18:43.508831+00:00
-- url     : https://prove2.me/theorems/9b5b1875-ba1f-4c3b-b88a-1386db1aaba9
-- title:
--   Coordinate Riemannian calculus in dimension 3: Christoffel symbols, curvature, covariant derivatives and Jacobi fields
-- statement:
--   This file develops the local coordinate calculus of a Riemannian three-manifold: chart expressions of the metric, Christoffel symbols and curvature, their transformation laws, covariant derivatives and curvature along curves, Jacobi fields, and local isometries.
--
--   **Setting and background definitions.** $M$ is a $C^\infty$ manifold modelled on $\mathbb{R}^3$ and $g$ a smooth Riemannian metric on $M$. For a chart $c$ of the atlas, $x$ in its target and $u, v \in \mathbb{R}^3$, write $g^c_x(u, v) = g_{c^{-1}(x)}\bigl(D c^{-1}(x)\, u,\ D c^{-1}(x)\, v\bigr)$ for the chart expression of $g$, $g_{ij}(x) = g^c_x(e_i, e_j)$ for its matrix ($e_i$ the standard basis), $(g^{ij})$ for the inverse matrix and $\partial_k$ for the $k$-th partial derivative. The Christoffel symbols, connection term, curvature coefficients and curvature term are
--   $$
--   \Gamma^i_{jk} = \tfrac12 \sum_l g^{il}\bigl(\partial_j g_{lk} + \partial_k g_{lj} - \partial_l g_{jk}\bigr), \qquad \Gamma_x(u,v)^i = \sum_{j,k} \Gamma^i_{jk}\, u^j v^k,
--   $$
--   $$
--   R^l_{\ kij} = \partial_i \Gamma^l_{jk} - \partial_j \Gamma^l_{ik} + \sum_a \bigl(\Gamma^l_{ia}\Gamma^a_{jk} - \Gamma^l_{ja}\Gamma^a_{ik}\bigr), \qquad R_x(u,v)w^l = \sum_{k,i,j} R^l_{\ kij}\, w^k u^i v^j .
--   $$
--   For a curve $x(s)$ in a chart and a vector function $F(s)$, the derivative along the curve is $D_s F = F' + \Gamma_{x(s)}(x'(s), F(s))$. For a curve $\gamma : \mathbb{R} \to M$ and a field $J$ along it ($J(s) \in T_{\gamma(s)}M$), the coordinates of $J$ in $c$ are $F_c(s) = dc_{\gamma(s)} J(s)$. A geodesic on an open set $U \subseteq \mathbb{R}$ is a $C^\infty$ curve with $D_s (c \circ \gamma)' = 0$ in every atlas chart wherever defined; a Jacobi field on $U$ is a field whose coordinates are $C^\infty$ on $U \cap \gamma^{-1}(\operatorname{dom} c)$ and satisfy $D_s D_s F_c + R(F_c, (c\circ\gamma)')(c\circ\gamma)' = 0$ there, for every atlas chart $c$.
--
--   **Definitions of this file.**
--
--   1. The chart bilinear form $g^c_x$ above; the linear maps $w \mapsto \Gamma_x(v, w)$ and $w \mapsto R_x(w, v)v$; and $\Gamma_x$ viewed as a bilinear map $\mathbb{R}^3 \times \mathbb{R}^3 \to \mathbb{R}^3$.
--   2. The first-order form of the Jacobi equation: for linear maps $C, R$ of $\mathbb{R}^3$, the linear map $(F, D) \mapsto (D - CF,\ -CD - RF)$ of $\mathbb{R}^3 \times \mathbb{R}^3$.
--   3. A *coordinate metric isometry* between metrics $g$ on $M$ (chart $c$) and $h$ on $N$ (chart $d$) along $f : \mathbb{R}^3 \to \mathbb{R}^3$: an open set $\Omega$ contained in the target of $c$ such that $f$ maps $\Omega$ into the target of $d$, $f$ is $C^\infty$ on $\Omega$, $Df(x)$ is surjective and $g^c_x(u, v) = h^d_{f(x)}(Df(x)u, Df(x)v)$ for all $x \in \Omega$ and $u, v$.
--   4. A *local metric isometry* $f : M \to N$ from $g$ to $h$: an open set $W \subseteq M$ on which $f$ is $C^\infty$ and $g_p(u,v) = h_{f(p)}(df_p u, df_p v)$ for $p \in W$. For charts $c, d$ its coordinate domain is the set of $x$ in the target of $c$ with $c^{-1}(x) \in W$ and $f(c^{-1}(x))$ in the domain of $d$; on it $d \circ f \circ c^{-1}$ is a coordinate metric isometry.
--   5. Intrinsic objects along a curve $\gamma$: the velocity $\gamma'(s) = d\gamma_s(1)$; the covariant derivative $D_s J(s) = Dc^{-1}\bigl(c(\gamma(s))\bigr)\,(D_s F_c)(s)$ computed in the preferred chart $c$ at $\gamma(s)$; the curvature along $\gamma$, $s \mapsto R(J, \gamma')\gamma'$, obtained in the same way from $R_x(F_c, (c\circ\gamma)')(c\circ\gamma)'$; and *smooth fields on $U$*, whose coordinates in every atlas chart are $C^\infty$ on $U \cap \gamma^{-1}(\operatorname{dom} c)$.
--
--   **Main properties established.** In every chart: $g_{ij}$ is $C^\infty$ and positive definite; $\Gamma^i_{jk}$ is $C^\infty$ and symmetric in $j, k$; metric compatibility $\partial_k g_{ij} = \sum_l (g_{lj}\Gamma^l_{ki} + g_{il}\Gamma^l_{kj})$; $R(u,v)w = D\Gamma(u)(v,w) - D\Gamma(v)(u,w) + \Gamma(u, \Gamma(v,w)) - \Gamma(v, \Gamma(u,w))$; $R(u,v) = -R(v,u)$; the first Bianchi identity; $g(R(s,t)u, v) + g(u, R(s,t)v) = 0$; and $g(R(u,t)t, v) = g(R(v,t)t, u)$. Under a change of charts $f = d \circ c^{-1}$,
--   $$
--   D^2 f(u, v) + \Gamma^d\bigl(Df\,u, Df\,v\bigr) = Df\, \Gamma^c(u, v), \qquad R^d\bigl(Df\,u, Df\,v\bigr)(Df\,w) = Df\, R^c(u,v)w,
--   $$
--   so derivatives along curves, the covariant derivative and the curvature along $\gamma$ do not depend on the chart. Along a $C^\infty$ curve on an open set $U$: $\frac{d}{ds} g(J, H) = g(D_sJ, H) + g(J, D_sH)$ for smooth fields; $D_s$ is additive and satisfies $D_s(fJ) = f'J + f D_sJ$; a Jacobi field satisfies the intrinsic equation $D_s D_s J + R(J,\gamma')\gamma' = 0$; geodesics satisfy $D_s\gamma' = 0$, and their speed $g(\gamma', \gamma')$ has zero derivative on $U$. Finally, if $U$ is open and order-connected (an open interval), $J$ is a Jacobi field on $U$ along a $C^\infty$ curve, and $J(a) = 0$ and $D_s J(a) = 0$ for some $a \in U$, then $J(s) = 0$ for all $s \in U$.
--
--   This is the analytic foundation of the no-conjugate-points argument: it identifies the chartwise geodesic and Jacobi equations of the main statement with their intrinsic counterparts, proves the curvature symmetries needed for index forms, and gives uniqueness of Jacobi fields from initial data.
--
--   **Formalization Note** Charts are `OpenPartialHomeomorph M E3` in `atlas E3 M` with `E3 = Fin 3 → ℝ`; the background objects ($g_{ij}$, $\Gamma$, $R$, $D_s$, geodesics, Jacobi fields) are `metricMatrix`, `christoffel`, `connectionTerm`, `curvatureCoefficient`, `curvatureTerm`, `alongDerivative`, `IsGeodesicOn`, `IsJacobiFieldOn` from the mission's definition file, and this file's objects are `chartBilin`, `connectionLinear`, `curvatureLinear`, `connectionBilin`, `jacobiBlock`, `CoordinateMetricIsometry`, `LocalMetricIsometry` (with `coordinateDomain`, `coordinates`), `velocity`, `covariantDerivative`, `curvatureAlong` and `SmoothFieldOn`. Derivatives are `fderiv`/`deriv`, which return $0$ at points of non-differentiability, and the matrix inverse is Mathlib's (here applied only to positive definite matrices). The intrinsic covariant derivative and curvature use the chart `chartAt E3 (γ s)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Coordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Coordinates.lean by skeleton subtraction
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

namespace OAI

noncomputable section

/-!
# Riemannian coordinates, connections, curvature, and Jacobi fields.
-/

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates

section
open MetricConstruction
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

def chartBilin (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (x : E3) :
    E3 →L[ℝ] E3 →L[ℝ] ℝ := pullInner g c.symm x

lemma chartBilin_smoothAt (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) :
    ContDiffAt ℝ ∞ (chartBilin g c) x := by
  have hc' : ContMDiffAt I3 I3 ∞ c.symm x :=
    contMDiffAt_symm_of_mem_maximalAtlas (subset_maximalAtlas hc) hx
  have hs := pullback_inner_smoothAt g hc'
  rw [contMDiffAt_section] at hs
  simp only [hom_trivializationAt_apply] at hs
  apply contMDiffAt_iff_contDiffAt.mp
  apply hs.congr_of_eventuallyEq
  filter_upwards [] with y
  ext u v
  have hy : y ∈ (trivializationAt E3 (TangentSpace I3) x).baseSet := by
    change y ∈ (univ : Set E3)
    trivial
  rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := fun _ => ℝ) hy hy (mem_univ _)]
  rw [← Trivialization.symmL_apply (R := ℝ) _ hy, ← Trivialization.symmL_apply (R := ℝ) _ hy]
  simp only [TangentBundle.symmL_model_space,
    Trivial.fiberBundle_trivializationAt',Trivial.linearMapAt_trivialization, LinearMap.id_coe,id_eq]
  rfl

lemma matrix_smoothAt (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) :
    ContDiffAt ℝ ∞ (metricMatrix g c) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact ((chartBilin_smoothAt g hc hx).clm_apply contDiffAt_const).clm_apply contDiffAt_const

lemma vector_expansion (u : E3) : (∑ i : Fin 3, u i • basisVector i) = u := by
  ext j
  simp [basisVector, Pi.single_apply]

lemma bilin_matrix (q : E3 →L[ℝ] E3 →L[ℝ] ℝ) (u v : E3) :
    (∑ i : Fin 3, ∑ j : Fin 3, q (basisVector i) (basisVector j) * u i * v j) = q u v := by
  conv_rhs => rw [← vector_expansion u, ← vector_expansion v]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma matrix_posDef (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) :
    (metricMatrix g c x).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    exact g.symm _ _ _
  · intro u hu
    have hd := (mdifferentiable_of_mem_atlas (I := I3) hc).symm.mfderiv_injective hx
    have hne : mfderiv I3 I3 c.symm x u ≠ 0 := by
      intro he
      exact hu (hd (he.trans (map_zero _).symm))
    have hp := g.pos (c.symm x) _ hne
    have he := bilin_matrix (chartBilin g c x) u u
    change 0 < chartBilin g c x u u at hp
    rw [← he] at hp
    change 0 < ∑ i : Fin 3, ∑ j : Fin 3, metricMatrix g c x i j * u i * u j at hp
    simpa only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum,
      mul_comm,mul_left_comm,mul_assoc] using hp

section MatrixSmooth
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {n : Type*} [Fintype n] [DecidableEq n] {R : X → Matrix n n ℝ} {x : X}
lemma determinant_smoothAt (hR : ContDiffAt ℝ ∞ R x) :
    ContDiffAt ℝ ∞ (fun y => (R y).det) x := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul (contDiffAt_prod fun i _ =>
    contDiffAt_pi.mp (contDiffAt_pi.mp hR (σ i)) i)
lemma adjugate_smoothAt (hR : ContDiffAt ℝ ∞ R x) :
    ContDiffAt ℝ ∞ (fun y => (R y).adjugate) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply determinant_smoothAt
  apply contDiffAt_pi.mpr
  intro k
  apply contDiffAt_pi.mpr
  intro l
  by_cases hk : k = j
  · subst k
    simpa only [Matrix.updateRow_self] using (contDiffAt_const (c := (Pi.single i (1 : ℝ) : n → ℝ) l))
  · simpa only [Matrix.updateRow_ne hk] using (contDiffAt_pi.mp (contDiffAt_pi.mp hR k) l)
lemma inverse_smoothAt (hR : ContDiffAt ℝ ∞ R x) (hdet : (R x).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => (R y)⁻¹) x := by
  simp only [Matrix.inv_def,Ring.inverse_eq_inv']
  exact ((determinant_smoothAt hR).inv hdet).smul (adjugate_smoothAt hR)
end MatrixSmooth

lemma partial_smoothAt {f : E3 → ℝ} {x : E3} (hf : ContDiffAt ℝ ∞ f x) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => coordPartial f y i) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma christoffel_smoothAt (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (i j k : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => christoffel g c y i j k) x := by
  have hg := matrix_smoothAt g hc hx
  have hi := inverse_smoothAt hg (matrix_posDef g hc hx).det_pos.ne'
  unfold christoffel
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro l _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hi i) l).mul
    (((partial_smoothAt (contDiffAt_pi.mp (contDiffAt_pi.mp hg l) k) j).add
      (partial_smoothAt (contDiffAt_pi.mp (contDiffAt_pi.mp hg l) j) k)).sub
      (partial_smoothAt (contDiffAt_pi.mp (contDiffAt_pi.mp hg j) k) l))

lemma curvatureCoefficient_smoothAt (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (l k i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => curvatureCoefficient g c y l k i j) x := by
  unfold curvatureCoefficient
  exact ((partial_smoothAt (christoffel_smoothAt g hc hx l j k) i).sub
    (partial_smoothAt (christoffel_smoothAt g hc hx l i k) j)).add
      (ContDiffAt.sum fun a _ =>
        ((christoffel_smoothAt g hc hx l i a).mul (christoffel_smoothAt g hc hx a j k)).sub
        ((christoffel_smoothAt g hc hx l j a).mul (christoffel_smoothAt g hc hx a i k)))
end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma matrix_symm (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (x : E3) (i j : Fin 3) :
    metricMatrix g c x i j = metricMatrix g c x j i := g.symm _ _ _
lemma matrix_partial_symm (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x : E3) (i j k : Fin 3) :
    coordPartial (fun y => metricMatrix g c y i j) x k =
      coordPartial (fun y => metricMatrix g c y j i) x k := by
  congr 2
  funext y
  exact matrix_symm g c y i j
lemma chartBilin_symm (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (x u v : E3) :
    chartBilin g c x u v = chartBilin g c x v u := g.symm _ _ _
lemma christoffel_symm (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x : E3) (i j k : Fin 3) : christoffel g c x i j k = christoffel g c x i k j := by
  unfold christoffel
  simp only [matrix_partial_symm g c x j k,add_comm]

lemma lower_christoffel (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (a j k : Fin 3) :
    (∑ i : Fin 3, metricMatrix g c x a i * christoffel g c x i j k) =
    (1 / 2 : ℝ) * (coordPartial (fun y => metricMatrix g c y a k) x j +
      coordPartial (fun y => metricMatrix g c y a j) x k -
      coordPartial (fun y => metricMatrix g c y j k) x a) := by
  let G := metricMatrix g c x
  let D : Fin 3 → ℝ := fun l => coordPartial (fun y => metricMatrix g c y l k) x j +
    coordPartial (fun y => metricMatrix g c y l j) x k -
      coordPartial (fun y => metricMatrix g c y j k) x l
  have hi : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr (matrix_posDef g hc hx).det_pos.ne')
  change (∑ i : Fin 3, G a i * ((1/2:ℝ) * ∑ l : Fin 3, G⁻¹ i l * D l)) = (1/2:ℝ) * D a
  calc
    _ = (1/2:ℝ) * ∑ l : Fin 3, (∑ i : Fin 3, G a i * G⁻¹ i l) * D l := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (1/2:ℝ) * D a := by
      simp only [← Matrix.mul_apply,hi]
      simp [Matrix.one_apply]

lemma metric_coordinate_compatible (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (i j k : Fin 3) :
    coordPartial (fun y => metricMatrix g c y i j) x k =
    (∑ l : Fin 3, metricMatrix g c x l j * christoffel g c x l k i) +
    (∑ l : Fin 3, metricMatrix g c x i l * christoffel g c x l k j) := by
  simp only [matrix_symm g c x _ j,lower_christoffel g hc hx]
  rw [matrix_partial_symm g c x j i,matrix_partial_symm g c x k i,
    matrix_partial_symm g c x k j]
  ring

lemma fderiv_coordinate_expansion (f : E3 → ℝ) (x v : E3) :
    fderiv ℝ f x v = ∑ k : Fin 3, v k * coordPartial f x k := by
  conv_lhs => rw [← vector_expansion v]
  simp [coordPartial]

lemma connection_pairing (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (x t u v : E3) :
    chartBilin g c x (connectionTerm g c x t u) v =
      ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
        t k * u i * v j * (∑ l : Fin 3, metricMatrix g c x l j * christoffel g c x l k i) := by
  rw [← bilin_matrix]
  simp only [connectionTerm,Finset.mul_sum,Finset.sum_mul]
  change (∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      metricMatrix g c x l j * (christoffel g c x l k i * t k * u i) * v j) = _
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]; arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma connection_pairing_right (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (x t u v : E3) :
    chartBilin g c x u (connectionTerm g c x t v) =
      ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
        t k * u i * v j * (∑ l : Fin 3, metricMatrix g c x i l * christoffel g c x l k j) := by
  rw [chartBilin_symm,connection_pairing]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (∑ l : Fin 3, metricMatrix g c x l i * christoffel g c x l k j) =
      ∑ l : Fin 3, metricMatrix g c x i l * christoffel g c x l k j := by
    apply Finset.sum_congr rfl
    intro l _
    rw [matrix_symm g c x l i]
  rw [he]
  ring

lemma metric_directional_compatible (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (t u v : E3) :
    (∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun y => metricMatrix g c y i j) x t * u i * v j) =
      chartBilin g c x (connectionTerm g c x t u) v +
      chartBilin g c x u (connectionTerm g c x t v) := by
  simp only [fderiv_coordinate_expansion,Finset.sum_mul]
  rw [connection_pairing,connection_pairing_right,← Finset.sum_add_distrib]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [metric_coordinate_compatible g hc hx]
  ring

def connectionLinear (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (x v : E3) : E3 →L[ℝ] E3 :=
  ContinuousLinearMap.pi fun i => ∑ j : Fin 3, ∑ k : Fin 3,
    (christoffel g c x i j k * v j) • ContinuousLinearMap.proj k

@[simp] lemma connectionLinear_apply (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x v w : E3) : connectionLinear g c x v w = connectionTerm g c x v w := by
  ext i
  simp [connectionLinear,connectionTerm,ContinuousLinearMap.pi_apply]

def curvatureLinear (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (x v : E3) : E3 →L[ℝ] E3 :=
  ContinuousLinearMap.pi fun l => ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
    (curvatureCoefficient g c x l k i j * v k * v j) • ContinuousLinearMap.proj i

@[simp] lemma curvatureLinear_apply (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x v w : E3) : curvatureLinear g c x v w = curvatureTerm g c x w v v := by
  ext l
  simp only [curvatureLinear,curvatureTerm,ContinuousLinearMap.pi_apply,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma connection_smoothAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3} (hc : c ∈ atlas E3 M)
    {x v w : X → E3} {s : X} (hx : ContDiffAt ℝ ∞ x s) (hs : x s ∈ c.target)
    (hv : ContDiffAt ℝ ∞ v s) (hw : ContDiffAt ℝ ∞ w s) :
    ContDiffAt ℝ ∞ (fun r => connectionTerm g c (x r) (v r) (w r)) s := by
  apply contDiffAt_pi.mpr
  intro i
  unfold connectionTerm
  exact ContDiffAt.sum fun j _ => ContDiffAt.sum fun k _ =>
    (((christoffel_smoothAt g hc hs i j k).comp s hx).mul (contDiffAt_pi.mp hv j)).mul
      (contDiffAt_pi.mp hw k)

lemma curvature_smoothAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3} (hc : c ∈ atlas E3 M)
    {x u v w : X → E3} {s : X} (hx : ContDiffAt ℝ ∞ x s) (hs : x s ∈ c.target)
    (hu : ContDiffAt ℝ ∞ u s) (hv : ContDiffAt ℝ ∞ v s) (hw : ContDiffAt ℝ ∞ w s) :
    ContDiffAt ℝ ∞ (fun r => curvatureTerm g c (x r) (u r) (v r) (w r)) s := by
  apply contDiffAt_pi.mpr
  intro l
  unfold curvatureTerm
  exact ContDiffAt.sum fun k _ => ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    ((((curvatureCoefficient_smoothAt g hc hs l k i j).comp s hx).mul
      (contDiffAt_pi.mp hw k)).mul (contDiffAt_pi.mp hu i)).mul (contDiffAt_pi.mp hv j)

lemma curve_coordinates_smoothAt {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {s : ℝ} (hs : s ∈ U) (hsc : γ s ∈ c.source) :
    ContDiffAt ℝ ∞ (c ∘ γ) s :=
  contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (subset_maximalAtlas hc) hsc).comp s
      (hγ.contMDiffAt (hU.mem_nhds hs)))

lemma along_smoothAt (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3} (hc : c ∈ atlas E3 M)
    {x w : ℝ → E3} {s : ℝ} (hx : ContDiffAt ℝ ∞ x s) (hs : x s ∈ c.target)
    (hw : ContDiffAt ℝ ∞ w s) : ContDiffAt ℝ ∞ (alongDerivative g c x w) s := by
  have hd := hw.derivWithin (m := ∞) (by simp)
  have ht := hx.derivWithin (m := ∞) (by simp)
  exact hd.add (connection_smoothAt g hc hx hs ht hw)

lemma interval_enlargement {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    {a b : ℝ} (ha : a ∈ U) (hb : b ∈ U) :
    ∃ c d : ℝ, c < a ∧ b < d ∧ Icc c d ⊆ U := by
  obtain ⟨l, r, har, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds ha)
  obtain ⟨l', r', hbr, hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hb)
  have hc : (l+a)/2 ∈ U := hsub ⟨by linarith [har.1], by linarith [har.1,har.2]⟩
  have hd : (b+r')/2 ∈ U := hsub' ⟨by linarith [hbr.1,hbr.2], by linarith [hbr.2]⟩
  exact ⟨(l+a)/2, (b+r')/2, by linarith [har.1], by linarith [hbr.2], hUc.out hc hd⟩

lemma linear_ode_zero_on {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    {A : ℝ → V →L[ℝ] V} (hA : ContinuousOn A U)
    {f : ℝ → V} (hf : ∀ t ∈ U, HasDerivAt f (A t (f t)) t)
    {a : ℝ} (ha : a ∈ U) (hfa : f a = 0) : ∀ s ∈ U, f s = 0 := by
  intro s hs
  have hmin : min a s ∈ U := by
    rcases le_total a s with h | h
    · simpa [min_eq_left h] using ha
    · simpa [min_eq_right h] using hs
  have hmax : max a s ∈ U := by
    rcases le_total a s with h | h
    · simpa [max_eq_right h] using hs
    · simpa [max_eq_left h] using ha
  obtain ⟨l,r,hl,hr,hlrU⟩ := interval_enlargement hU hUc hmin hmax
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.mono hlrU)
  let K : NNReal := ⟨max C 0, le_max_right _ _⟩
  have hv : ∀ t ∈ Ioo l r, LipschitzOnWith K (fun x => A t x) univ := by
    intro t ht
    exact ((A t).lipschitz.weaken (show ‖A t‖₊ ≤ K from
      (hC t (Ioo_subset_Icc_self ht)).trans (le_max_left _ _))).lipschitzOnWith
  have hai : a ∈ Ioo l r := ⟨hl.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hr⟩
  have hsi : s ∈ Ioo l r := ⟨hl.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hr⟩
  have he := ODE_solution_unique_of_mem_Ioo hv hai
    (f := f) (g := fun _ => 0)
    (fun t ht => ⟨hf t (hlrU (Ioo_subset_Icc_self ht)), mem_univ _⟩)
    (fun t _ => ⟨by simpa using hasDerivAt_const t (0 : V), mem_univ _⟩) hfa
  exact he hsi

def jacobiBlock (C R : E3 →L[ℝ] E3) : E3 × E3 →L[ℝ] E3 × E3 :=
  ((ContinuousLinearMap.snd ℝ E3 E3) - C.comp (ContinuousLinearMap.fst ℝ E3 E3)).prod
    (-C.comp (ContinuousLinearMap.snd ℝ E3 E3) - R.comp (ContinuousLinearMap.fst ℝ E3 E3))
@[simp] lemma jacobiBlock_apply (C R : E3 →L[ℝ] E3) (x : E3 × E3) :
    jacobiBlock C R x = (x.2 - C x.1, -C x.2 - R x.1) := rfl

lemma jacobi_zero_in_chart (g : SmoothMetric M) {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    {J : ∀ s, TangentSpace I3 (γ s)} (hJ : IsJacobiFieldOn g γ J U)
    {c : OpenPartialHomeomorph M E3} (hc : c ∈ atlas E3 M) (hmap : ∀ s ∈ U, γ s ∈ c.source)
    {a : ℝ} (ha : a ∈ U) (hJa : J a = 0)
    (hDa : alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c) a = 0) :
    ∀ s ∈ U, J s = 0 := by
  let x := c ∘ γ
  let F := fieldCoordinates γ J c
  let D := alongDerivative g c x F
  let C := fun s => connectionLinear g c (x s) (deriv x s)
  let R := fun s => curvatureLinear g c (x s) (deriv x s)
  have hxs (s : ℝ) (hs : s ∈ U) : ContDiffAt ℝ ∞ x s :=
    curve_coordinates_smoothAt hU hγ hc hs (hmap s hs)
  have hFs (s : ℝ) (hs : s ∈ U) : ContDiffAt ℝ ∞ F s := by
    apply ((hJ c hc).1 s ⟨hs,hmap s hs⟩).contDiffAt
    exact inter_mem (hU.mem_nhds hs)
      ((hγ.contMDiffAt (hU.mem_nhds hs)).continuousAt.preimage_mem_nhds
        (c.open_source.mem_nhds (hmap s hs)))
  have hDs (s : ℝ) (hs : s ∈ U) : ContDiffAt ℝ ∞ D s :=
    along_smoothAt g hc (hxs s hs) (c.map_source (hmap s hs)) (hFs s hs)
  have hcont : ContinuousOn (fun s => jacobiBlock (C s) (R s)) U := by
    apply continuousOn_clm_apply.mpr
    intro z s hs
    have ht := (hxs s hs).derivWithin (m := ∞) (by simp)
    have hC (v : E3) : ContinuousAt (fun r => C r v) s := by
      simpa only [C,connectionLinear_apply] using
        (connection_smoothAt g hc (hxs s hs) (c.map_source (hmap s hs)) ht
          (contDiffAt_const (c := v))).continuousAt
    have hR (v : E3) : ContinuousAt (fun r => R r v) s := by
      simpa only [R,curvatureLinear_apply] using
        (curvature_smoothAt g hc (hxs s hs) (c.map_source (hmap s hs))
          (contDiffAt_const (c := v)) ht ht).continuousAt
    exact ((continuousAt_const.sub (hC z.1)).prodMk ((hC z.2).neg.sub (hR z.1))).continuousWithinAt
  have hstate (s : ℝ) (hs : s ∈ U) : HasDerivAt (fun r => (F r,D r))
      (jacobiBlock (C s) (R s) (F s,D s)) s := by
    have hFD : deriv F s = D s - C s (F s) := by
      change deriv F s = (deriv F s + connectionTerm g c (x s) (deriv x s) (F s)) -
        connectionTerm g c (x s) (deriv x s) (F s)
      abel
    have hDD : deriv D s = -C s (D s) - R s (F s) := by
      have he := (hJ c hc).2 s hs (hmap s hs)
      change deriv D s + connectionTerm g c (x s) (deriv x s) (D s) +
        curvatureTerm g c (x s) (F s) (deriv x s) (deriv x s) = 0 at he
      simp only [C,R,connectionLinear_apply,curvatureLinear_apply]
      linear_combination he
    have hh := ((hFs s hs).differentiableAt (by simp)).hasDerivAt.prodMk
      ((hDs s hs).differentiableAt (by simp)).hasDerivAt
    simpa only [hFD,hDD,jacobiBlock_apply] using hh
  have hFa : F a = 0 := by
    change mfderiv I3 I3 c (γ a) (J a) = 0
    rw [hJa]
    exact map_zero _
  have hz := linear_ode_zero_on hU hUc hcont hstate ha (Prod.ext hFa hDa)
  intro s hs
  have hF : F s = 0 := congrArg Prod.fst (hz s hs)
  have hinj := (mdifferentiable_of_mem_atlas (I := I3) hc).mfderiv_injective (hmap s hs)
  exact hinj (hF.trans (map_zero _).symm)

def connectionBilin (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (x : E3) :
    E3 →L[ℝ] E3 →L[ℝ] E3 :=
  ∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    christoffel g c x l j k • (ContinuousLinearMap.proj j).smulRight
      ((ContinuousLinearMap.proj k).smulRight (basisVector l))

lemma connectionBilin_apply (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) (x u v : E3) :
    connectionBilin g c x u v = connectionTerm g c x u v := by
  ext i
  simp only [connectionBilin,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,basisVector]
  change (∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    christoffel g c x l j k • u j • v k • (Pi.single l (1:ℝ) : E3)) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp [connectionTerm, mul_ite, mul_assoc]

lemma connectionBilin_smoothAt (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) :
    ContDiffAt ℝ ∞ (connectionBilin g c) x := by
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  exact ContDiffAt.sum fun l _ => ContDiffAt.sum fun j _ => ContDiffAt.sum fun k _ =>
    (christoffel_smoothAt g hc hx l j k).smul contDiffAt_const

lemma connectionBilin_deriv_apply (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (t u v : E3) (l : Fin 3) :
    fderiv ℝ (connectionBilin g c) x t u v l =
      ∑ j : Fin 3, ∑ k : Fin 3, fderiv ℝ (fun y => christoffel g c y l j k) x t * u j * v k := by
  have hf := ((connectionBilin_smoothAt g hc hx).differentiableAt (by simp)).hasFDerivAt
  have hF := (hf.clm_apply (hasFDerivAt_const u x)).clm_apply (hasFDerivAt_const v x)
  have he := (ContinuousLinearMap.proj l : E3 →L[ℝ] ℝ).hasFDerivAt.comp x hF
  have hΓ (j k : Fin 3) := ((christoffel_smoothAt g hc hx l j k).differentiableAt (by simp)).hasFDerivAt
  have hh := HasFDerivAt.sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    HasFDerivAt.sum fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) =>
      ((hΓ j k).mul_const (u j)).mul_const (v k)
  have he' : HasFDerivAt (fun y => connectionTerm g c y u v l)
      (ContinuousLinearMap.proj l |>.comp ((ContinuousLinearMap.apply ℝ E3 v).comp
        ((ContinuousLinearMap.apply ℝ (E3 →L[ℝ] E3) u).comp (fderiv ℝ (connectionBilin g c) x)))) x := by
    convert he using 1 <;> first
    | rfl
    | (funext y; exact (congrFun (connectionBilin_apply g c y u v) l).symm)
    | (ext z; simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
        ContinuousLinearMap.proj_apply,_root_.add_apply,
        _root_.zero_apply,ContinuousLinearMap.flip_apply,map_zero,zero_add])

  have hval := congrArg (fun L => L t) (he'.unique hh)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.apply_apply,_root_.sum_apply,_root_.smul_apply,
    smul_eq_mul] at hval
  rw [hval]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma deltaConnection_apply (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (t u v : E3) (l : Fin 3) :
    fderiv ℝ (connectionBilin g c) x t u v l =
      ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
        coordPartial (fun y => christoffel g c y l j k) x i * v k * t i * u j := by
  rw [connectionBilin_deriv_apply g hc hx]
  simp only [fderiv_coordinate_expansion, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma doubleConnection_apply (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x t u v : E3) (l : Fin 3) :
    connectionBilin g c x t (connectionBilin g c x u v) l =
      ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3,
        christoffel g c x l i a * christoffel g c x a j k * v k * t i * u j := by
  simp only [connectionBilin_apply, connectionTerm, Finset.mul_sum]
  change (∑ i : Fin 3, ∑ a : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    christoffel g c x l i a * t i * (christoffel g c x a j k * u j * v k)) = _
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma curvature_connection (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (u v w : E3) :
    curvatureTerm g c x u v w =
      fderiv ℝ (connectionBilin g c) x u v w - fderiv ℝ (connectionBilin g c) x v u w +
        connectionBilin g c x u (connectionBilin g c x v w) -
        connectionBilin g c x v (connectionBilin g c x u w) := by
  ext l
  simp only [Pi.add_apply, Pi.sub_apply, deltaConnection_apply g hc hx, doubleConnection_apply]
  have hswap : (∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
      coordPartial (fun y => christoffel g c y l j k) x i * w k * v i * u j) =
      ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
      coordPartial (fun y => christoffel g c y l i k) x j * w k * u i * v j := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hswap2 : (∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3,
      christoffel g c x l i a * christoffel g c x a j k * w k * v i * u j) =
      ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3,
      christoffel g c x l j a * christoffel g c x a i k * w k * u i * v j := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hswap,hswap2]
  simp only [curvatureTerm,curvatureCoefficient,add_mul,sub_mul,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,Finset.sum_mul]
  ring
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma metric_fields_hasDerivAt (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x F H : ℝ → E3} {s : ℝ} (hs : x s ∈ c.target)
    (hx : DifferentiableAt ℝ x s) (hF : DifferentiableAt ℝ F s) (hH : DifferentiableAt ℝ H s) :
    HasDerivAt (fun r => chartBilin g c (x r) (F r) (H r))
      (chartBilin g c (x s) (alongDerivative g c x F s) (H s) +
        chartBilin g c (x s) (F s) (alongDerivative g c x H s)) s := by
  let : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let q' := fderiv ℝ (chartBilin g c) (x s) (deriv x s)
  have hdq : DifferentiableAt ℝ (chartBilin g c) (x s) :=
    (chartBilin_smoothAt g hc hs).differentiableAt (by simp)
  have hdfq : HasFDerivAt (chartBilin g c) (fderiv ℝ (chartBilin g c) (x s)) (x s) := hdq.hasFDerivAt
  have hq : HasDerivAt (fun r => chartBilin g c (x r)) q' s :=
    hdfq.comp_hasDerivAt s hx.hasDerivAt
  have hentry (i j : Fin 3) : q' (basisVector i) (basisVector j) =
      fderiv ℝ (fun y => metricMatrix g c y i j) (x s) (deriv x s) := by
    have he := (hq.clm_apply (hasDerivAt_const s (basisVector i))).clm_apply
      (hasDerivAt_const s (basisVector j))
    simp only [map_zero,add_zero] at he
    change HasDerivAt (fun r => metricMatrix g c (x r) i j) (q' (basisVector i) (basisVector j)) s at he
    have hm := ((contDiffAt_pi.mp (contDiffAt_pi.mp (matrix_smoothAt g hc hs) i) j).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt s hx.hasDerivAt
    exact he.unique hm
  have hq' : q' (F s) (H s) =
      chartBilin g c (x s) (connectionTerm g c (x s) (deriv x s) (F s)) (H s) +
      chartBilin g c (x s) (F s) (connectionTerm g c (x s) (deriv x s) (H s)) := by
    rw [← bilin_matrix q']
    simp only [hentry]
    exact metric_directional_compatible g hc hs _ _ _
  have he := (hq.clm_apply hF.hasDerivAt).clm_apply hH.hasDerivAt
  apply he.congr_deriv
  simp only [alongDerivative,map_add,_root_.add_apply]
  rw [hq']
  ring

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates

section
open MetricConstruction
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma transition_smoothAt {c d : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M) {x : E3}
    (hx : x ∈ c.target) (hxd : c.symm x ∈ d.source) :
    ContDiffAt ℝ ∞ (d ∘ c.symm) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  exact (contMDiffAt_of_mem_maximalAtlas (subset_maximalAtlas hd) hxd).comp x
    (contMDiffAt_symm_of_mem_maximalAtlas (subset_maximalAtlas hc) hx)

omit [ChartedSpace E3 M] [IsManifold I3 ∞ M] in
lemma overlap_nhds {c d : OpenPartialHomeomorph M E3} {x : E3}
    (hx : x ∈ c.target) (hxd : c.symm x ∈ d.source) :
    ∀ᶠ y in 𝓝 x, y ∈ c.target ∧ c.symm y ∈ d.source :=
  inter_mem (c.open_target.mem_nhds hx)
    ((c.continuousAt_symm hx).preimage_mem_nhds (d.open_source.mem_nhds hxd))

lemma chart_metric_transform (g : SmoothMetric M) {c d : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M) {x : E3}
    (hx : x ∈ c.target) (hxd : c.symm x ∈ d.source) (u v : E3) :
    chartBilin g c x u v = chartBilin g d (d (c.symm x))
      (fderiv ℝ (d ∘ c.symm) x u) (fderiv ℝ (d ∘ c.symm) x v) := by
  have hf := (transition_smoothAt hc hd hx hxd).differentiableAt (by simp)
  have hh := (mdifferentiable_of_mem_atlas (I := I3) hd).mdifferentiableAt_symm (d.map_source hxd)
  have he : (d.symm ∘ (d ∘ c.symm)) =ᶠ[𝓝 x] c.symm := by
    filter_upwards [overlap_nhds hx hxd] with y hy
    exact d.left_inv hy.2
  have heq := pullInner_congr (E := E3) (F := E3) g he
  have hp := pull_composition (E := E3) (F := E3) (H := E3) g
    (mdifferentiableAt_iff_differentiableAt.mpr hf) hh
  have hp' := congrArg (fun q : E3 →L[ℝ] E3 →L[ℝ] ℝ => q u v) (heq.symm.trans hp)
  change chartBilin g c x u v = chartBilin g d (d (c.symm x))
    (mfderiv I3 I3 (d ∘ c.symm) x u) (mfderiv I3 I3 (d ∘ c.symm) x v) at hp'
  convert hp' using 1
  simp only [mfderiv_eq_fderiv]
  rfl

lemma connectionTerm_symm (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x u v : E3) : connectionTerm g c x u v = connectionTerm g c x v u := by
  ext i
  unfold connectionTerm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [christoffel_symm g c x i k j]
  ring

lemma chartBilin_pos (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) {u : E3} (hu : u ≠ 0) :
    0 < chartBilin g c x u u := by
  have hinj := (mdifferentiable_of_mem_atlas (I := I3) hc).symm.mfderiv_injective hx
  change 0 < g.inner (c.symm x) (mfderiv I3 I3 c.symm x u) (mfderiv I3 I3 c.symm x u)
  apply g.pos
  intro he
  exact hu (hinj (he.trans (map_zero _).symm))

lemma symmetric_skew_difference_zero {V : Type*} [Zero V]
    (q : V → V → ℝ) (hqs : ∀ u v, q u v = q v u)
    (hqp : ∀ v, v ≠ 0 → 0 < q v v) {A : E3 → V} (hA : Function.Surjective A)
    {B : E3 → E3 → V} (hBs : ∀ u v, B u v = B v u)
    (hBq : ∀ t u v, q (B t u) (A v) + q (A u) (B t v) = 0) :
    ∀ u v, B u v = 0 := by
  intro u v
  obtain ⟨w,hw⟩ := hA (B u v)
  have h1 := hBq u v w
  have h2 := hBq v w u
  have h3 := hBq w u v
  rw [hqs (A v) (B u w),hBs u w] at h1
  rw [hBs v u,hqs (A w) (B u v)] at h2
  rw [hBs w v,hqs (A u) (B v w)] at h3
  have hz' : q (B u v) (A w) = 0 := by linarith
  have hz : q (B u v) (B u v) = 0 := by simpa only [hw] using hz'
  by_contra hn
  have hp := hqp (B u v) hn
  linarith
end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma transition_metric_derivative (g : SmoothMetric M) {c d : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M) {x : E3}
    (hx : x ∈ c.target) (hxd : c.symm x ∈ d.source) (t u v : E3) :
    let f := d ∘ c.symm
    let A := fderiv ℝ f x
    let H := fderiv ℝ (fderiv ℝ f) x
    chartBilin g c x (connectionTerm g c x t u) v +
        chartBilin g c x u (connectionTerm g c x t v) =
      chartBilin g d (f x) (H t u + connectionTerm g d (f x) (A t) (A u)) (A v) +
        chartBilin g d (f x) (A u) (H t v + connectionTerm g d (f x) (A t) (A v)) := by
  intro f A H
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  let p : ℝ → E3 := fun s => x + s • t
  have hp : HasDerivAt p t 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const t).const_add x
  have hp0 : p 0 = x := by simp [p]
  have hs : ContDiffAt ℝ ∞ f x := transition_smoothAt hc hd hx hxd
  have hds : DifferentiableAt ℝ f x := hs.differentiableAt (by simp)
  have hAs : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hs.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hdf : HasFDerivAt f A (p 0) := hp0.symm ▸ hds.hasFDerivAt
  have hdA : HasFDerivAt (fderiv ℝ f) H (p 0) := hp0.symm ▸ hAs.hasFDerivAt
  have hfp : HasDerivAt (f ∘ p) (A t) 0 := by
    exact hdf.comp_hasDerivAt 0 hp
  have hAu : HasDerivAt (fun s => fderiv ℝ f (p s) u) (H t u) 0 := by
    have h := (hdA.comp_hasDerivAt 0 hp).clm_apply (hasDerivAt_const 0 u)
    convert h using 1 <;> first | rfl | simp only [map_zero,add_zero]
  have hAv : HasDerivAt (fun s => fderiv ℝ f (p s) v) (H t v) 0 := by
    have h := (hdA.comp_hasDerivAt 0 hp).clm_apply (hasDerivAt_const 0 v)
    convert h using 1 <;> first | rfl | simp only [map_zero,add_zero]
  have hq1 := metric_fields_hasDerivAt g hc (show p 0 ∈ c.target by rw [hp0]; exact hx) hp.differentiableAt
    (differentiableAt_const u) (differentiableAt_const v)
  have hq2 := metric_fields_hasDerivAt g hd (show (f ∘ p) 0 ∈ d.target by
    change f (p 0) ∈ d.target
    rw [hp0]
    exact d.map_source hxd) hfp.differentiableAt
      hAu.differentiableAt hAv.differentiableAt
  have he : (fun s => chartBilin g c (p s) u v) =ᶠ[𝓝 0]
      (fun s => chartBilin g d (f (p s)) (fderiv ℝ f (p s) u) (fderiv ℝ f (p s) v)) := by
    have ho := hp.continuousAt (hp0.symm ▸ overlap_nhds hx hxd)
    filter_upwards [ho] with s hs'
    exact chart_metric_transform g hc hd hs'.1 hs'.2 u v
  have heq := hq1.unique (hq2.congr_of_eventuallyEq he)
  simpa only [alongDerivative,deriv_const,zero_add,hp.deriv,hfp.deriv,hAu.deriv,hAv.deriv,
    Function.comp_apply,hp0] using heq

lemma transition_derivative_surjective {c d : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M) {x : E3}
    (hx : x ∈ c.target) (hxd : c.symm x ∈ d.source) :
    Function.Surjective (fderiv ℝ (d ∘ c.symm) x) := by
  have hs := ((mdifferentiable_of_mem_atlas (I := I3) hc).symm.trans
    (mdifferentiable_of_mem_atlas (I := I3) hd)).mfderiv_surjective ⟨hx,hxd⟩
  change Function.Surjective (mfderiv I3 I3 (d ∘ c.symm) x) at hs
  rw [mfderiv_eq_fderiv] at hs
  convert hs using 1 <;> rfl

lemma connection_change (g : SmoothMetric M) {c d : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M) {x : E3}
    (hx : x ∈ c.target) (hxd : c.symm x ∈ d.source) (u v : E3) :
    let f := d ∘ c.symm
    fderiv ℝ (fderiv ℝ f) x u v +
        connectionTerm g d (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) =
      fderiv ℝ f x (connectionTerm g c x u v) := by
  intro f
  let A := fderiv ℝ f x
  let H := fderiv ℝ (fderiv ℝ f) x
  let q := chartBilin g d (f x)
  let B := fun u v => H u v + connectionTerm g d (f x) (A u) (A v) - A (connectionTerm g c x u v)
  have hBs : ∀ u v, B u v = B v u := by
    intro u v
    have hH := ((transition_smoothAt hc hd hx hxd).isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).eq u v
    simp only [B,H,f,hH,connectionTerm_symm g d (f x) (A u) (A v),
      connectionTerm_symm g c x u v]
  have hBq : ∀ t u v, q (B t u) (A v) + q (A u) (B t v) = 0 := by
    intro t u v
    have he := transition_metric_derivative g hc hd hx hxd t u v
    dsimp only at he
    rw [chart_metric_transform g hc hd hx hxd (connectionTerm g c x t u) v,
      chart_metric_transform g hc hd hx hxd u (connectionTerm g c x t v)] at he
    change q (A (connectionTerm g c x t u)) (A v) +
      q (A u) (A (connectionTerm g c x t v)) =
        q (H t u + connectionTerm g d (f x) (A t) (A u)) (A v) +
        q (A u) (H t v + connectionTerm g d (f x) (A t) (A v)) at he
    dsimp only [B]
    simp only [map_sub,_root_.sub_apply]
    linarith
  have hz := symmetric_skew_difference_zero (fun u v => q u v)
    (chartBilin_symm g d (f x)) (fun _ hu => chartBilin_pos g hd (d.map_source hxd) hu)
    (transition_derivative_surjective hc hd hx hxd) hBs hBq u v
  exact sub_eq_zero.mp hz

lemma connection_change_derivative (g : SmoothMetric M) {c d : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M) {x : E3}
    (hx : x ∈ c.target) (hxd : c.symm x ∈ d.source) (t u v : E3) :
    let f := d ∘ c.symm
    let A := fderiv ℝ f x
    let H := fderiv ℝ (fderiv ℝ f) x
    let K := fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x
    K t u v + fderiv ℝ (connectionBilin g d) (f x) (A t) (A u) (A v) +
      connectionBilin g d (f x) (H t u) (A v) + connectionBilin g d (f x) (A u) (H t v) =
      H t (connectionBilin g c x u v) + A (fderiv ℝ (connectionBilin g c) x t u v) := by
  intro f A H K
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  let p : ℝ → E3 := fun s => x + s • t
  have hp : HasDerivAt p t 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const t).const_add x
  have hp0 : p 0 = x := by simp [p]
  have hs := transition_smoothAt hc hd hx hxd
  have hAs := hs.fderiv_right (m := ∞) (by simp)
  have hHs := hAs.fderiv_right (m := ∞) (by simp)
  have hdf : HasFDerivAt f A (p 0) := by
    rw [hp0]; exact (hs.differentiableAt (by simp)).hasFDerivAt
  have hdA : HasFDerivAt (fderiv ℝ f) H (p 0) := by
    rw [hp0]; exact (hAs.differentiableAt (by simp)).hasFDerivAt
  have hdH : HasFDerivAt (fderiv ℝ (fderiv ℝ f)) K (p 0) := by
    rw [hp0]; exact (hHs.differentiableAt (by simp)).hasFDerivAt
  have hdC : HasFDerivAt (connectionBilin g c) (fderiv ℝ (connectionBilin g c) x) (p 0) := by
    rw [hp0]; exact ((connectionBilin_smoothAt g hc hx).differentiableAt (by simp)).hasFDerivAt
  have hdD : HasFDerivAt (connectionBilin g d) (fderiv ℝ (connectionBilin g d) (f x)) (f (p 0)) := by
    rw [hp0]; exact ((connectionBilin_smoothAt g hd (d.map_source hxd)).differentiableAt (by simp)).hasFDerivAt
  have hf := hdf.comp_hasDerivAt 0 hp
  have hA := hdA.comp_hasDerivAt 0 hp
  have hH := hdH.comp_hasDerivAt 0 hp
  have hC := hdC.comp_hasDerivAt 0 hp
  have hD := hdD.comp_hasDerivAt 0 hf
  have hu := hA.clm_apply (hasDerivAt_const 0 u)
  have hv := hA.clm_apply (hasDerivAt_const 0 v)
  have hleft := ((hH.clm_apply (hasDerivAt_const 0 u)).clm_apply (hasDerivAt_const 0 v)).add
    ((hD.clm_apply hu).clm_apply hv)
  have hright := hA.clm_apply ((hC.clm_apply (hasDerivAt_const 0 u)).clm_apply (hasDerivAt_const 0 v))
  have he : (fun s => fderiv ℝ (fderiv ℝ f) (p s) u v +
      connectionBilin g d (f (p s)) (fderiv ℝ f (p s) u) (fderiv ℝ f (p s) v)) =ᶠ[𝓝 0]
      (fun s => fderiv ℝ f (p s) (connectionBilin g c (p s) u v)) := by
    filter_upwards [hp.continuousAt (hp0.symm ▸ overlap_nhds hx hxd)] with s hs'
    simp only [connectionBilin_apply]
    exact connection_change g hc hd hs'.1 hs'.2 u v
  have heq := hleft.unique (hright.congr_of_eventuallyEq he)
  simp only [map_zero,add_zero,Function.comp_apply,hp0,_root_.add_apply] at heq
  simpa only [A, add_assoc] using heq

lemma curvature_change (g : SmoothMetric M) {c d : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M) {x : E3}
    (hx : x ∈ c.target) (hxd : c.symm x ∈ d.source) (u v w : E3) :
    let f := d ∘ c.symm
    let A := fderiv ℝ f x
    curvatureTerm g d (f x) (A u) (A v) (A w) = A (curvatureTerm g c x u v w) := by
  intro f A
  let H := fderiv ℝ (fderiv ℝ f) x
  let K := fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x
  let C := connectionBilin g c x
  let D := connectionBilin g d (f x)
  let dC := fderiv ℝ (connectionBilin g c) x
  let dD := fderiv ℝ (connectionBilin g d) (f x)
  have hH : H u v = H v u := ((transition_smoothAt hc hd hx hxd).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).eq u v
  have hK : K u v = K v u := (((transition_smoothAt hc hd hx hxd).fderiv_right (m := ∞)
    (by simp)).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).eq u v
  have hconn (a b : E3) : A (C a b) = H a b + D (A a) (A b) := by
    simpa only [C,D,connectionBilin_apply] using (connection_change g hc hd hx hxd a b).symm
  have hdiff (a b e : E3) : A (dC a b e) =
      K a b e + dD (A a) (A b) (A e) + D (H a b) (A e) + D (A b) (H a e) - H a (C b e) := by
    apply (eq_sub_iff_add_eq).2
    simpa only [add_comm] using (connection_change_derivative g hc hd hx hxd a b e).symm
  rw [curvature_connection g hd (x := f x) (d.map_source hxd),curvature_connection g hc hx]
  change dD (A u) (A v) (A w) - dD (A v) (A u) (A w) +
    D (A u) (D (A v) (A w)) - D (A v) (D (A u) (A w)) =
    A (dC u v w - dC v u w + C u (C v w) - C v (C u w))
  simp only [map_sub,map_add]
  rw [hdiff,hdiff,hconn,hconn,hconn,hconn,hH,hK]
  simp only [map_add]
  abel

lemma along_change (g : SmoothMetric M) {c d : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M) {x F : ℝ → E3} {s : ℝ}
    (hx : DifferentiableAt ℝ x s) (hF : DifferentiableAt ℝ F s)
    (hxc : x s ∈ c.target) (hxd : c.symm (x s) ∈ d.source) :
    let f := d ∘ c.symm
    alongDerivative g d (f ∘ x) (fun r => fderiv ℝ f (x r) (F r)) s =
      fderiv ℝ f (x s) (alongDerivative g c x F s) := by
  intro f
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  have hfs : ContDiffAt ℝ ∞ f (x s) := transition_smoothAt hc hd hxc hxd
  have hdf := (hfs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hx.hasDerivAt
  have hdA := ((hfs.fderiv_right (m := ∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt s hx.hasDerivAt
  have hdF : HasDerivAt (fun r => fderiv ℝ f (x r) (F r))
      (fderiv ℝ (fderiv ℝ f) (x s) (deriv x s) (F s) +
        fderiv ℝ f (x s) (deriv F s)) s := by
    convert hdA.clm_apply hF.hasDerivAt using 1 <;> rfl
  have he := connection_change g hc hd hxc hxd (deriv x s) (F s)
  dsimp only at he
  rw [alongDerivative,hdF.deriv,hdf.deriv]
  change _ = fderiv ℝ f (x s) (deriv F s + connectionTerm g c (x s) (deriv x s) (F s))
  rw [map_add,← he]
  abel

lemma along_congr (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {x y F H : ℝ → E3} {s : ℝ} (hx : x =ᶠ[𝓝 s] y) (hF : F =ᶠ[𝓝 s] H) :
    alongDerivative g c x F s = alongDerivative g c y H s := by
  unfold alongDerivative
  rw [hx.eq_of_nhds,hF.eq_of_nhds,hx.deriv_eq,hF.deriv_eq]

lemma field_coordinates_change {γ : ℝ → M} {J : ∀ s, TangentSpace I3 (γ s)}
    {c d : OpenPartialHomeomorph M E3} (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M)
    {s : ℝ} (hsc : γ s ∈ c.source) (hsd : γ s ∈ d.source) :
    fderiv ℝ (d ∘ c.symm) (c (γ s)) (fieldCoordinates γ J c s) =
      fieldCoordinates γ J d s := by
  have hdc := mdifferentiable_of_mem_atlas (I := I3) hc
  have hdd := mdifferentiable_of_mem_atlas (I := I3) hd
  have he := mfderiv_comp (c (γ s)) (show MDifferentiableAt I3 I3 d (c.symm (c (γ s))) by
    rw [c.left_inv hsc]; exact hdd.mdifferentiableAt hsd)
    (hdc.mdifferentiableAt_symm (c.map_source hsc))
  have hi := congrArg (fun L => L (J s)) (hdc.symm_comp_deriv hsc)
  have he' := congrArg (fun L => L (fieldCoordinates γ J c s)) he
  rw [c.left_inv hsc] at he'
  change mfderiv I3 I3 (d ∘ c.symm) (c (γ s)) (fieldCoordinates γ J c s) =
    mfderiv I3 I3 d (γ s) (mfderiv I3 I3 c.symm (c (γ s)) (mfderiv I3 I3 c (γ s) (J s))) at he'
  change mfderiv I3 I3 c.symm (c (γ s)) (mfderiv I3 I3 c (γ s) (J s)) = J s at hi
  rw [hi,mfderiv_eq_fderiv] at he'
  convert he' using 1 ; rfl

lemma field_along_change (g : SmoothMetric M) {γ : ℝ → M} {J : ∀ s, TangentSpace I3 (γ s)}
    {c d : OpenPartialHomeomorph M E3} (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M)
    {s : ℝ} (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s)
    (hJ : DifferentiableAt ℝ (fieldCoordinates γ J c) s)
    (hsc : γ s ∈ c.source) (hsd : γ s ∈ d.source) :
    alongDerivative g d (d ∘ γ) (fieldCoordinates γ J d) s =
      fderiv ℝ (d ∘ c.symm) (c (γ s))
        (alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c) s) := by
  have hx := (contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (subset_maximalAtlas hc) hsc).comp s hγ)).differentiableAt (by simp)
  have ht := along_change g hc hd hx hJ (c.map_source hsc)
    (show c.symm (c (γ s)) ∈ d.source by rw [c.left_inv hsc]; exact hsd)
  have hn := hγ.continuousAt.preimage_mem_nhds ((c.open_source.inter d.open_source).mem_nhds ⟨hsc,hsd⟩)
  have hec : (d ∘ c.symm) ∘ (c ∘ γ) =ᶠ[𝓝 s] d ∘ γ := by
    filter_upwards [hn] with r hr
    simp only [Function.comp_apply,c.left_inv hr.1]
  have heF : (fun r => fderiv ℝ (d ∘ c.symm) ((c ∘ γ) r) (fieldCoordinates γ J c r))
      =ᶠ[𝓝 s] fieldCoordinates γ J d := by
    filter_upwards [hn] with r hr
    exact field_coordinates_change hc hd hr.1 hr.2
  dsimp only at ht
  rw [along_congr g d hec heF] at ht
  exact ht
end

variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

structure CoordinateMetricIsometry (g : SmoothMetric M) (h : SmoothMetric N)
    (c : OpenPartialHomeomorph M E3) (d : OpenPartialHomeomorph N E3) (f : E3 → E3) where
  domain : Set E3
  isOpen_domain : IsOpen domain
  source : domain ⊆ c.target
  target : MapsTo f domain d.target
  smooth : ContDiffOn ℝ ∞ f domain
  surjective : ∀ x ∈ domain, Function.Surjective (fderiv ℝ f x)
  metric : ∀ x ∈ domain, ∀ u v : E3,
    chartBilin g c x u v = chartBilin h d (f x) (fderiv ℝ f x u) (fderiv ℝ f x v)

namespace CoordinateMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N}
  {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3} {f : E3 → E3}
  (P : CoordinateMetricIsometry g h c d f)
end CoordinateMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N}
  {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3} {f : E3 → E3}
  (P : CoordinateMetricIsometry g h c d f)
end ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry

namespace ThreeManifold.RiemannianCoordinates

section
open MetricConstruction
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

structure LocalMetricIsometry (g : SmoothMetric M) (h : SmoothMetric N) (f : M → N) where
  domain : Set M
  isOpen_domain : IsOpen domain
  smooth : ContMDiffOn I3 I3 ∞ f domain
  metric : ∀ p ∈ domain, ∀ u v : TangentSpace I3 p,
    g.inner p u v = h.inner (f p) (mfderiv I3 I3 f p u) (mfderiv I3 I3 f p v)

namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
lemma smoothAt {p : M} (hp : p ∈ P.domain) : ContMDiffAt I3 I3 ∞ f p :=
  P.smooth.contMDiffAt (P.isOpen_domain.mem_nhds hp)

def coordinateDomain (c : OpenPartialHomeomorph M E3) (d : OpenPartialHomeomorph N E3) : Set E3 :=
  c.target ∩ c.symm ⁻¹' P.domain ∩ (f ∘ c.symm) ⁻¹' d.source

lemma coordinateDomain_open (c : OpenPartialHomeomorph M E3) (d : OpenPartialHomeomorph N E3) :
    IsOpen (P.coordinateDomain c d) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hc := c.continuousAt_symm hx.1.1
  exact inter_mem (inter_mem (c.open_target.mem_nhds hx.1.1)
    (hc.preimage_mem_nhds (P.isOpen_domain.mem_nhds hx.1.2)))
    (((P.smoothAt hx.1.2).continuousAt.comp hc).preimage_mem_nhds (d.open_source.mem_nhds hx.2))

lemma coordinate_smoothAt {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x : E3}
    (hx : x ∈ P.coordinateDomain c d) : ContDiffAt ℝ ∞ (d ∘ f ∘ c.symm) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  exact (contMDiffAt_of_mem_maximalAtlas (subset_maximalAtlas hd) hx.2).comp x
    ((P.smoothAt hx.1.2).comp x
      (contMDiffAt_symm_of_mem_maximalAtlas (subset_maximalAtlas hc) hx.1.1))

lemma coordinate_metric {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x : E3}
    (hx : x ∈ P.coordinateDomain c d) (u v : E3) :
    chartBilin g c x u v = chartBilin h d ((d ∘ f ∘ c.symm) x)
      (fderiv ℝ (d ∘ f ∘ c.symm) x u) (fderiv ℝ (d ∘ f ∘ c.symm) x v) := by
  have hcs := (mdifferentiable_of_mem_atlas (I := I3) hc).mdifferentiableAt_symm hx.1.1
  have hfs := (P.smoothAt hx.1.2).mdifferentiableAt (by simp)
  have hdi := (mdifferentiable_of_mem_atlas (I := I3) hd).mdifferentiableAt_symm (d.map_source hx.2)
  have hm : chartBilin g c x u v = pullInner (E := E3) h (f ∘ c.symm) x u v := by
    rw [pull_composition h hcs hfs]
    exact P.metric _ hx.1.2 _ _
  have he : (d.symm ∘ (d ∘ f ∘ c.symm)) =ᶠ[𝓝 x] (f ∘ c.symm) := by
    filter_upwards [(P.coordinateDomain_open c d).mem_nhds hx] with y hy
    exact d.left_inv hy.2
  rw [hm,← pullInner_congr (E := E3) (F := E3) h he,
    pull_composition h ((mdifferentiableAt_iff_differentiableAt).mpr
      ((P.coordinate_smoothAt hc hd hx).differentiableAt (by simp))) hdi]
  change chartBilin h d ((d ∘ f ∘ c.symm) x)
    (mfderiv I3 I3 (d ∘ f ∘ c.symm) x u) (mfderiv I3 I3 (d ∘ f ∘ c.symm) x v) = _
  rw [mfderiv_eq_fderiv]
  rfl

lemma coordinate_surjective {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x : E3}
    (hx : x ∈ P.coordinateDomain c d) : Function.Surjective (fderiv ℝ (d ∘ f ∘ c.symm) x) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) rfl).mp
  apply (injective_iff_map_eq_zero _).mpr
  intro u hu
  change fderiv ℝ (d ∘ f ∘ c.symm) x u = 0 at hu
  by_contra hne
  have hp := chartBilin_pos g hc hx.1.1 hne
  have he := P.coordinate_metric hc hd hx u u
  rw [hu,map_zero] at he
  change chartBilin g c x u u = 0 at he
  linarith

def coordinates {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) :
    CoordinateMetricIsometry g h c d (d ∘ f ∘ c.symm) where
  domain := P.coordinateDomain c d
  isOpen_domain := P.coordinateDomain_open c d
  source := fun _ hx => hx.1.1
  target := fun _ hx => d.map_source hx.2
  smooth := fun _ hx => (P.coordinate_smoothAt hc hd hx).contDiffWithinAt
  surjective := fun _ hx => P.coordinate_surjective hc hd hx
  metric := fun _ hx => P.coordinate_metric hc hd hx
end LocalMetricIsometry
end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

def covariantDerivative (g : SmoothMetric M) (γ : ℝ → M)
    (J : ∀ s, TangentSpace I3 (γ s)) (s : ℝ) : TangentSpace I3 (γ s) :=
  let c := chartAt E3 (γ s)
  mfderiv I3 I3 c.symm (c (γ s))
    (alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c) s)

lemma push_from_chart {p : M} {c d : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 M)
    (hpc : p ∈ c.source) (hpd : p ∈ d.source) (u : E3) :
    mfderiv I3 I3 d p (mfderiv I3 I3 c.symm (c p) u) =
      fderiv ℝ (d ∘ c.symm) (c p) u := by
  have hdc := mdifferentiable_of_mem_atlas (I := I3) hc
  have hdd := mdifferentiable_of_mem_atlas (I := I3) hd
  have he := mfderiv_comp (c p) (show MDifferentiableAt I3 I3 d (c.symm (c p)) by
    rw [c.left_inv hpc]; exact hdd.mdifferentiableAt hpd)
    (hdc.mdifferentiableAt_symm (c.map_source hpc))
  have he' := congrArg (fun L => L u) he
  rw [c.left_inv hpc,mfderiv_eq_fderiv] at he'
  convert he'.symm using 1 ; rfl

lemma covariantDerivative_coordinates (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s)
    (hJ : DifferentiableAt ℝ (fieldCoordinates γ J (chartAt E3 (γ s))) s)
    {c : OpenPartialHomeomorph M E3} (hc : c ∈ atlas E3 M) (hsc : γ s ∈ c.source) :
    fieldCoordinates γ (covariantDerivative g γ J) c s =
      alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c) s := by
  unfold fieldCoordinates covariantDerivative
  rw [push_from_chart (chart_mem_atlas E3 (γ s)) hc (mem_chart_source E3 (γ s)) hsc]
  exact (field_along_change g (chart_mem_atlas E3 (γ s)) hc hγ hJ
    (mem_chart_source E3 (γ s)) hsc).symm

lemma metric_field_coordinates (g : SmoothMetric M) {γ : ℝ → M}
    (J H : ∀ s, TangentSpace I3 (γ s)) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {s : ℝ} (hsc : γ s ∈ c.source) :
    chartBilin g c (c (γ s)) (fieldCoordinates γ J c s) (fieldCoordinates γ H c s) =
      g.inner (γ s) (J s) (H s) := by
  have hdc := mdifferentiable_of_mem_atlas (I := I3) hc
  have heJ := congrArg (fun L => L (J s)) (hdc.symm_comp_deriv hsc)
  have heH := congrArg (fun L => L (H s)) (hdc.symm_comp_deriv hsc)
  change mfderiv I3 I3 c.symm (c (γ s)) (fieldCoordinates γ J c s) = J s at heJ
  change mfderiv I3 I3 c.symm (c (γ s)) (fieldCoordinates γ H c s) = H s at heH
  change g.inner (c.symm (c (γ s)))
    (mfderiv I3 I3 c.symm (c (γ s)) (fieldCoordinates γ J c s))
    (mfderiv I3 I3 c.symm (c (γ s)) (fieldCoordinates γ H c s)) = _
  rw [c.left_inv hsc]
  exact congrArg₂ (fun a b => g.inner (γ s) a b) heJ heH

def SmoothFieldOn (γ : ℝ → M) (J : ∀ s, TangentSpace I3 (γ s)) (U : Set ℝ) : Prop :=
  ∀ c : OpenPartialHomeomorph M E3, c ∈ atlas E3 M →
    ContDiffOn ℝ ∞ (fieldCoordinates γ J c) (U ∩ γ ⁻¹' c.source)

lemma jacobi_smoothField (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hJ : IsJacobiFieldOn g γ J U) :
    SmoothFieldOn γ J U := fun c hc => (hJ c hc).1

lemma smoothField_coordinatesAt {γ : ℝ → M} {J : ∀ s, TangentSpace I3 (γ s)}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hJ : SmoothFieldOn γ J U) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {s : ℝ} (hs : s ∈ U) (hsc : γ s ∈ c.source) :
    ContDiffAt ℝ ∞ (fieldCoordinates γ J c) s := by
  let _ : IsManifold I3 ∞ M := inferInstance
  exact ((hJ c hc) s ⟨hs,hsc⟩).contDiffAt (inter_mem (hU.mem_nhds hs)
    ((hγ.contMDiffAt (hU.mem_nhds hs)).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hsc)))

lemma covariantDerivative_smooth (g : SmoothMetric M) {γ : ℝ → M} {J : ∀ s, TangentSpace I3 (γ s)}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hJ : SmoothFieldOn γ J U) : SmoothFieldOn γ (covariantDerivative g γ J) U := by
  intro c hc s hs
  apply ContDiffAt.contDiffWithinAt
  have he : fieldCoordinates γ (covariantDerivative g γ J) c =ᶠ[𝓝 s]
      alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c) := by
    have hn := inter_mem (hU.mem_nhds hs.1)
      ((hγ.contMDiffAt (hU.mem_nhds hs.1)).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hs.2))
    filter_upwards [hn] with r hr
    exact covariantDerivative_coordinates g (hγ.contMDiffAt (hU.mem_nhds hr.1))
      ((smoothField_coordinatesAt hU hγ hJ (chart_mem_atlas E3 (γ r)) hr.1
        (mem_chart_source E3 (γ r))).differentiableAt (by simp)) hc hr.2
  exact (along_smoothAt g hc (curve_coordinates_smoothAt hU hγ hc hs.1 hs.2)
    (c.map_source hs.2) (smoothField_coordinatesAt hU hγ hJ hc hs.1 hs.2)).congr_of_eventuallyEq he

lemma jacobi_mono (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U V : Set ℝ}
    (hJ : IsJacobiFieldOn g γ J U) (hVU : V ⊆ U) : IsJacobiFieldOn g γ J V := by
  intro c hc
  exact ⟨(hJ c hc).1.mono (inter_subset_inter_left _ hVU),
    fun s hs hsc => (hJ c hc).2 s (hVU hs) hsc⟩

lemma zero_germ_derivative (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {a : ℝ}
    (ha : ∀ᶠ s in 𝓝 a, J s = 0) (c : OpenPartialHomeomorph M E3) :
    alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c) a = 0 := by
  have he : fieldCoordinates γ J c =ᶠ[𝓝 a] (fun _ => 0) := by
    filter_upwards [ha] with s hs
    change mfderiv I3 I3 c (γ s) (J s) = 0
    rw [hs]
    exact map_zero _
  have hd := ((hasDerivAt_const a (0 : E3)).congr_of_eventuallyEq he).deriv
  rw [alongDerivative,hd,he.eq_of_nhds]
  change 0 + connectionLinear g c (c (γ a)) (deriv (c ∘ γ) a) 0 = 0
  rw [map_zero,add_zero]

omit [IsManifold I3 ∞ M] in
lemma chart_interval {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) {a : ℝ} (ha : a ∈ U)
    {c : OpenPartialHomeomorph M E3} (hca : γ a ∈ c.source) :
    ∃ l r : ℝ, a ∈ Ioo l r ∧ Ioo l r ⊆ U ∧ ∀ s ∈ Ioo l r, γ s ∈ c.source := by
  have hn : U ∩ γ ⁻¹' c.source ∈ 𝓝 a := inter_mem (hU.mem_nhds ha)
    ((hγ.contMDiffAt (hU.mem_nhds ha)).continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds hca))
  obtain ⟨l,r,har,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  exact ⟨l,r,har,fun s hs => (hsub hs).1,fun s hs => (hsub hs).2⟩

lemma jacobi_zero_of_initial (g : SmoothMetric M) {U : Set ℝ}
    (hU : IsOpen U) (hUc : OrdConnected U)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    {J : ∀ s, TangentSpace I3 (γ s)} (hJ : IsJacobiFieldOn g γ J U)
    {a : ℝ} (ha : a ∈ U) (hJa : J a = 0)
    {c : OpenPartialHomeomorph M E3} (hc : c ∈ atlas E3 M) (hca : γ a ∈ c.source)
    (hDa : alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c) a = 0) :
    ∀ s ∈ U, J s = 0 := by
  let Z : Set ℝ := {s | J s = 0}
  let B : Set U := Subtype.val ⁻¹' interior Z
  let : PreconnectedSpace U := Subtype.preconnectedSpace hUc.isPreconnected
  have hloc (d : OpenPartialHomeomorph M E3) (hd : d ∈ atlas E3 M)
      {l r t : ℝ} (hVU : Ioo l r ⊆ U) (hmap : ∀ s ∈ Ioo l r, γ s ∈ d.source)
      (ht : t ∈ Ioo l r) (htZ : t ∈ interior Z) : Ioo l r ⊆ interior Z := by
    have htJ : J t = 0 := by
      change t ∈ Z
      exact interior_subset htZ
    have htD := zero_germ_derivative g (mem_interior_iff_mem_nhds.mp htZ) d
    have hz := jacobi_zero_in_chart g isOpen_Ioo (ordConnected_Ioo)
      (hγ.mono hVU) (jacobi_mono g hJ hVU) hd hmap ht htJ htD
    intro s hs
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) hz
  have hB : IsClopen B := by
    refine ⟨?_, isOpen_interior.preimage continuous_subtype_val⟩
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    let d := chartAt E3 (γ s.val)
    obtain ⟨l,r,hsV,hVU,hmap⟩ := chart_interval hU hγ s.property (mem_chart_source E3 (γ s.val))
    have hVB : Subtype.val ⁻¹' Ioo l r ⊆ Bᶜ := by
      intro t ht htB
      exact hs (hloc d (chart_mem_atlas E3 (γ s.val)) hVU hmap ht htB hsV)
    exact Filter.mem_of_superset
      ((isOpen_Ioo.preimage continuous_subtype_val).mem_nhds hsV) hVB
  have haB : (⟨a,ha⟩ : U) ∈ B := by
    obtain ⟨l,r,haV,hVU,hmap⟩ := chart_interval hU hγ ha hca
    have hz := jacobi_zero_in_chart g isOpen_Ioo ordConnected_Ioo
      (hγ.mono hVU) (jacobi_mono g hJ hVU) hc hmap haV hJa hDa
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (isOpen_Ioo.mem_nhds haV) hz)
  have he := hB.eq_univ ⟨⟨a,ha⟩,haB⟩
  intro s hs
  have hsi : (⟨s,hs⟩ : U) ∈ B := by rw [he]; trivial
  change s ∈ Z
  exact interior_subset hsi
end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma intrinsic_pairing_hasDerivAt (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hJ : SmoothFieldOn γ J U) (hH : SmoothFieldOn γ H U) {s : ℝ} (hs : s ∈ U) :
    HasDerivAt (fun r => g.inner (γ r) (J r) (H r))
      (g.inner (γ s) (covariantDerivative g γ J s) (H s) +
        g.inner (γ s) (J s) (covariantDerivative g γ H s)) s := by
  let c := chartAt E3 (γ s)
  have hc := chart_mem_atlas E3 (γ s)
  have hsc := mem_chart_source E3 (γ s)
  have hx := curve_coordinates_smoothAt hU hγ hc hs hsc
  have hF := smoothField_coordinatesAt hU hγ hJ hc hs hsc
  have hG := smoothField_coordinatesAt hU hγ hH hc hs hsc
  have he := metric_fields_hasDerivAt g hc (c.map_source hsc)
    (hx.differentiableAt (by simp)) (hF.differentiableAt (by simp)) (hG.differentiableAt (by simp))
  have hn : ∀ᶠ r in 𝓝 s, γ r ∈ c.source :=
    (hγ.contMDiffAt (hU.mem_nhds hs)).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hsc)
  have hf : (fun r => g.inner (γ r) (J r) (H r)) =ᶠ[𝓝 s]
      (fun r => chartBilin g c ((c ∘ γ) r) (fieldCoordinates γ J c r) (fieldCoordinates γ H c r)) := by
    filter_upwards [hn] with r hr
    exact (metric_field_coordinates g J H hc hr).symm
  apply (he.congr_of_eventuallyEq hf).congr_deriv
  rw [← covariantDerivative_coordinates g (hγ.contMDiffAt (hU.mem_nhds hs))
    (hF.differentiableAt (by simp)) hc hsc,
    ← covariantDerivative_coordinates g (hγ.contMDiffAt (hU.mem_nhds hs))
    (hG.differentiableAt (by simp)) hc hsc]
  exact congrArg₂ (·+·) (metric_field_coordinates g _ _ hc hsc) (metric_field_coordinates g _ _ hc hsc)

lemma jacobi_zero_of_intrinsic_initial (g : SmoothMetric M) {U : Set ℝ}
    (hU : IsOpen U) (hUc : OrdConnected U) {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    {J : ∀ s, TangentSpace I3 (γ s)} (hJ : IsJacobiFieldOn g γ J U)
    {a : ℝ} (ha : a ∈ U) (hJa : J a = 0) (hDa : covariantDerivative g γ J a = 0) :
    ∀ s ∈ U, J s = 0 := by
  apply jacobi_zero_of_initial g hU hUc hγ hJ ha hJa (chart_mem_atlas E3 (γ a))
    (mem_chart_source E3 (γ a))
  rw [← covariantDerivative_coordinates g (hγ.contMDiffAt (hU.mem_nhds ha))
    ((smoothField_coordinatesAt hU hγ (jacobi_smoothField g hJ)
      (chart_mem_atlas E3 (γ a)) ha (mem_chart_source E3 (γ a))).differentiableAt (by simp))
    (chart_mem_atlas E3 (γ a)) (mem_chart_source E3 (γ a))]
  change mfderiv I3 I3 _ (γ a) (covariantDerivative g γ J a) = 0
  rw [hDa,map_zero]

def velocity (γ : ℝ → M) (s : ℝ) : TangentSpace I3 (γ s) :=
  mfderiv 𝓘(ℝ,ℝ) I3 γ s 1

lemma velocity_coordinates {γ : ℝ → M} {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hsc : γ s ∈ c.source) :
    fieldCoordinates γ (velocity γ) c s = deriv (c ∘ γ) s := by
  have he := mfderiv_comp s ((mdifferentiable_of_mem_atlas (I := I3) hc).mdifferentiableAt hsc)
    (hγ.mdifferentiableAt (by simp))
  have hv := congrArg (fun L => L 1) he
  rw [mfderiv_eq_fderiv] at hv
  change fderiv ℝ (c ∘ γ) s 1 = mfderiv I3 I3 c (γ s) (mfderiv 𝓘(ℝ,ℝ) I3 γ s 1) at hv
  exact hv.symm

lemma velocity_smooth {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) : SmoothFieldOn γ (velocity γ) U := by
  intro c hc s hs
  apply ContDiffAt.contDiffWithinAt
  have he : fieldCoordinates γ (velocity γ) c =ᶠ[𝓝 s] deriv (c ∘ γ) := by
    filter_upwards [hU.mem_nhds hs.1,
      (hγ.contMDiffAt (hU.mem_nhds hs.1)).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hs.2)] with r hr hrc
    exact velocity_coordinates (hγ.contMDiffAt (hU.mem_nhds hr)) hc hrc
  exact ((curve_coordinates_smoothAt hU hγ hc hs.1 hs.2).derivWithin (m := ∞) (by simp)).congr_of_eventuallyEq he

lemma geodesic_acceleration_zero (g : SmoothMetric M) {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : IsGeodesicOn g γ U) {s : ℝ} (hs : s ∈ U) :
    covariantDerivative g γ (velocity γ) s = 0 := by
  let c := chartAt E3 (γ s)
  have hc := chart_mem_atlas E3 (γ s)
  have hsc := mem_chart_source E3 (γ s)
  have he : fieldCoordinates γ (velocity γ) c =ᶠ[𝓝 s] deriv (c ∘ γ) := by
    filter_upwards [hU.mem_nhds hs,
      (hγ.1.contMDiffAt (hU.mem_nhds hs)).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hsc)] with r hr hrc
    exact velocity_coordinates (hγ.1.contMDiffAt (hU.mem_nhds hr)) hc hrc
  have hz : alongDerivative g c (c ∘ γ) (fieldCoordinates γ (velocity γ) c) s = 0 := by
    rw [along_congr g c Filter.EventuallyEq.rfl he]
    exact hγ.2 c hc s hs hsc
  exact (congrArg (fun v : E3 => mfderiv I3 I3 c.symm (c (γ s)) v) hz).trans (map_zero _)

lemma geodesic_speed_hasDerivAt (g : SmoothMetric M) {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : IsGeodesicOn g γ U) {s : ℝ} (hs : s ∈ U) :
    HasDerivAt (fun r => g.inner (γ r) (velocity γ r) (velocity γ r)) 0 s := by
  have he := intrinsic_pairing_hasDerivAt g hU hγ.1 (velocity_smooth hU hγ.1)
    (velocity_smooth hU hγ.1) hs
  simpa only [geodesic_acceleration_zero g hU hγ hs, map_zero, _root_.zero_apply, add_zero] using he

lemma covariantDerivative_iterate_coordinates (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U)
    {s : ℝ} (hs : s ∈ U) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) (hsc : γ s ∈ c.source) :
    fieldCoordinates γ (covariantDerivative g γ (covariantDerivative g γ J)) c s =
      alongDerivative g c (c ∘ γ) (alongDerivative g c (c ∘ γ) (fieldCoordinates γ J c)) s := by
  rw [covariantDerivative_coordinates g (hγ.contMDiffAt (hU.mem_nhds hs))
    ((smoothField_coordinatesAt hU hγ (covariantDerivative_smooth g hU hγ hJ)
      (chart_mem_atlas E3 (γ s)) hs (mem_chart_source E3 (γ s))).differentiableAt (by simp)) hc hsc]
  apply along_congr g c Filter.EventuallyEq.rfl
  filter_upwards [hU.mem_nhds hs,
    (hγ.contMDiffAt (hU.mem_nhds hs)).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hsc)] with r hr hrc
  exact covariantDerivative_coordinates g (hγ.contMDiffAt (hU.mem_nhds hr))
    ((smoothField_coordinatesAt hU hγ hJ (chart_mem_atlas E3 (γ r)) hr
      (mem_chart_source E3 (γ r))).differentiableAt (by simp)) hc hrc

def curvatureAlong (g : SmoothMetric M) (γ : ℝ → M)
    (J : ∀ s, TangentSpace I3 (γ s)) (s : ℝ) : TangentSpace I3 (γ s) :=
  let c := chartAt E3 (γ s)
  mfderiv I3 I3 c.symm (c (γ s)) (curvatureTerm g c (c (γ s))
    (fieldCoordinates γ J c s) (deriv (c ∘ γ) s) (deriv (c ∘ γ) s))

lemma curvatureAlong_coordinates (g : SmoothMetric M) {γ : ℝ → M}
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ} (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s)
    {c : OpenPartialHomeomorph M E3} (hc : c ∈ atlas E3 M) (hsc : γ s ∈ c.source) :
    fieldCoordinates γ (curvatureAlong g γ J) c s =
      curvatureTerm g c (c (γ s)) (fieldCoordinates γ J c s)
        (deriv (c ∘ γ) s) (deriv (c ∘ γ) s) := by
  let d := chartAt E3 (γ s)
  have hd := chart_mem_atlas E3 (γ s)
  have hsd := mem_chart_source E3 (γ s)
  have hcd : d.symm (d (γ s)) ∈ c.source := by rw [d.left_inv hsd]; exact hsc
  have he := curvature_change g hd hc (d.map_source hsd) hcd
    (fieldCoordinates γ J d s) (deriv (d ∘ γ) s) (deriv (d ∘ γ) s)
  dsimp only at he
  rw [← velocity_coordinates hγ hd hsd,field_coordinates_change hd hc hsd hsc,
    field_coordinates_change hd hc hsd hsc,velocity_coordinates hγ hc hsc,
    Function.comp_apply,d.left_inv hsd] at he
  change mfderiv I3 I3 c (γ s) (mfderiv I3 I3 d.symm (d (γ s))
    (curvatureTerm g d (d (γ s)) (fieldCoordinates γ J d s) (deriv (d ∘ γ) s) (deriv (d ∘ γ) s))) = _
  rw [push_from_chart hd hc hsd hsc]
  rw [velocity_coordinates hγ hd hsd] at he
  exact he.symm

lemma curvatureAlong_smooth (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U) :
    SmoothFieldOn γ (curvatureAlong g γ J) U := by
  intro c hc s hs
  apply ContDiffAt.contDiffWithinAt
  have hx := curve_coordinates_smoothAt hU hγ hc hs.1 hs.2
  have hF := smoothField_coordinatesAt hU hγ hJ hc hs.1 hs.2
  have he : fieldCoordinates γ (curvatureAlong g γ J) c =ᶠ[𝓝 s]
      (fun r => curvatureTerm g c (c (γ r)) (fieldCoordinates γ J c r)
        (deriv (c ∘ γ) r) (deriv (c ∘ γ) r)) := by
    filter_upwards [hU.mem_nhds hs.1,
      (hγ.contMDiffAt (hU.mem_nhds hs.1)).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hs.2)] with r hr hrc
    exact curvatureAlong_coordinates g J (hγ.contMDiffAt (hU.mem_nhds hr)) hc hrc
  refine ContDiffAt.congr_of_eventuallyEq ?_ he
  have hv := hx.derivWithin (m := ∞) (by simp)
  exact curvature_smoothAt g hc hx (c.map_source hs.2) hF hv hv

lemma jacobi_intrinsic_equation (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hJ : IsJacobiFieldOn g γ J U) {s : ℝ} (hs : s ∈ U) :
    covariantDerivative g γ (covariantDerivative g γ J) s + curvatureAlong g γ J s = 0 := by
  let c := chartAt E3 (γ s)
  have hc := chart_mem_atlas E3 (γ s)
  have hsc := mem_chart_source E3 (γ s)
  apply (mdifferentiable_of_mem_atlas (I := I3) hc).mfderiv_injective hsc
  rw [map_add,map_zero]
  change fieldCoordinates γ (covariantDerivative g γ (covariantDerivative g γ J)) c s +
    fieldCoordinates γ (curvatureAlong g γ J) c s = 0
  rw [covariantDerivative_iterate_coordinates g hU hγ (jacobi_smoothField g hJ) hs hc hsc,
    curvatureAlong_coordinates g J (hγ.contMDiffAt (hU.mem_nhds hs)) hc hsc]
  exact (hJ c hc).2 s hs hsc

omit [IsManifold I3 ∞ M] in
lemma fieldCoordinates_add (γ : ℝ → M) (J H : ∀ s, TangentSpace I3 (γ s))
    (c : OpenPartialHomeomorph M E3) :
    fieldCoordinates γ (fun s => J s + H s) c =
      fun s => fieldCoordinates γ J c s + fieldCoordinates γ H c s := by
  funext s
  exact map_add (mfderiv I3 I3 c (γ s)) (J s) (H s)
omit [IsManifold I3 ∞ M] in
lemma fieldCoordinates_smul (γ : ℝ → M) (J : ∀ s, TangentSpace I3 (γ s))
    (f : ℝ → ℝ) (c : OpenPartialHomeomorph M E3) :
    fieldCoordinates γ (fun s => f s • J s) c =
      fun s => f s • fieldCoordinates γ J c s := by
  funext s
  exact map_smul (mfderiv I3 I3 c (γ s)) (f s) (J s)
omit [IsManifold I3 ∞ M] in
lemma smoothField_add {γ : ℝ → M} {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hJ : SmoothFieldOn γ J U) (hH : SmoothFieldOn γ H U) :
    SmoothFieldOn γ (fun s => J s + H s) U := by
  intro c hc
  simpa only [fieldCoordinates_add] using (hJ c hc).add (hH c hc)

omit [IsManifold I3 ∞ M] in
lemma smoothField_smul {γ : ℝ → M} {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hJ : SmoothFieldOn γ J U) :
    SmoothFieldOn γ (fun s => f s • J s) U := by
  intro c hc
  rw [fieldCoordinates_smul]
  convert (hf.mono inter_subset_left).smul (hJ c hc) using 1
    <;> rfl

lemma covariantDerivative_add (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U)
    (hH : SmoothFieldOn γ H U) {s : ℝ} (hs : s ∈ U) :
    covariantDerivative g γ (fun r => J r + H r) s =
      covariantDerivative g γ J s + covariantDerivative g γ H s := by
  have hF := (smoothField_coordinatesAt hU hγ hJ (chart_mem_atlas E3 (γ s)) hs
    (mem_chart_source E3 (γ s))).differentiableAt (by simp)
  have hG := (smoothField_coordinatesAt hU hγ hH (chart_mem_atlas E3 (γ s)) hs
    (mem_chart_source E3 (γ s))).differentiableAt (by simp)
  let c := chartAt E3 (γ s)
  let P : E3 →L[ℝ] TangentSpace I3 (γ s) := mfderiv I3 I3 c.symm (c (γ s))
  change P (deriv (fieldCoordinates γ (fun r => J r + H r) c) s +
    connectionTerm g c (c (γ s)) (deriv (c ∘ γ) s) (fieldCoordinates γ (fun r => J r + H r) c s)) =
    P (deriv (fieldCoordinates γ J c) s + connectionTerm g c (c (γ s)) (deriv (c ∘ γ) s) (fieldCoordinates γ J c s)) +
    P (deriv (fieldCoordinates γ H c) s + connectionTerm g c (c (γ s)) (deriv (c ∘ γ) s) (fieldCoordinates γ H c s))
  have hd : deriv (fun r => fieldCoordinates γ J c r + fieldCoordinates γ H c r) s =
      deriv (fieldCoordinates γ J c) s + deriv (fieldCoordinates γ H c) s := by
    convert (hF.hasDerivAt.add hG.hasDerivAt).deriv using 1 <;> rfl
  rw [fieldCoordinates_add,hd]
  simp only [← connectionLinear_apply,map_add]
  abel

lemma covariantDerivative_smul (g : SmoothMetric M) {γ : ℝ → M}
    {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U)
    {f : ℝ → ℝ} {s : ℝ} (hs : s ∈ U) (hf : DifferentiableAt ℝ f s) :
    covariantDerivative g γ (fun r => f r • J r) s =
      deriv f s • J s + f s • covariantDerivative g γ J s := by
  let c := chartAt E3 (γ s)
  have hc := chart_mem_atlas E3 (γ s)
  have hsc := mem_chart_source E3 (γ s)
  have hF := (smoothField_coordinatesAt hU hγ hJ hc hs hsc).differentiableAt (by simp)
  have hγs := hγ.contMDiffAt (hU.mem_nhds hs)
  apply (mdifferentiable_of_mem_atlas (I := I3) hc).mfderiv_injective hsc
  rw [map_add,map_smul,map_smul]
  change fieldCoordinates γ (covariantDerivative g γ (fun r => f r • J r)) c s =
    deriv f s • fieldCoordinates γ J c s + f s • fieldCoordinates γ (covariantDerivative g γ J) c s
  have hscaled : DifferentiableAt ℝ (fieldCoordinates γ (fun r => f r • J r) c) s := by
    rw [fieldCoordinates_smul]
    convert hf.smul hF using 1 <;> rfl
  rw [covariantDerivative_coordinates g hγs hscaled hc hsc,
    covariantDerivative_coordinates g hγs hF hc hsc]
  unfold alongDerivative
  rw [fieldCoordinates_smul]
  have hd : deriv (fun r => f r • fieldCoordinates γ J c r) s =
      deriv f s • fieldCoordinates γ J c s + f s • deriv (fieldCoordinates γ J c) s := by
    convert (hf.hasDerivAt.smul hF.hasDerivAt).deriv using 1 <;> first | rfl | exact add_comm _ _
  rw [hd,← connectionLinear_apply,map_smul,
    connectionLinear_apply,smul_add]
  abel

lemma curvatureAlong_add (g : SmoothMetric M) (γ : ℝ → M)
    (J H : ∀ s, TangentSpace I3 (γ s)) (s : ℝ) :
    curvatureAlong g γ (fun r => J r + H r) s = curvatureAlong g γ J s + curvatureAlong g γ H s := by
  let c := chartAt E3 (γ s)
  let P : E3 →L[ℝ] TangentSpace I3 (γ s) := mfderiv I3 I3 c.symm (c (γ s))
  change P (curvatureTerm g c (c (γ s)) (fieldCoordinates γ (fun r => J r + H r) c s)
    (deriv (c ∘ γ) s) (deriv (c ∘ γ) s)) =
    P (curvatureTerm g c (c (γ s)) (fieldCoordinates γ J c s) (deriv (c ∘ γ) s) (deriv (c ∘ γ) s)) +
    P (curvatureTerm g c (c (γ s)) (fieldCoordinates γ H c s) (deriv (c ∘ γ) s) (deriv (c ∘ γ) s))
  rw [fieldCoordinates_add]
  simp only [← curvatureLinear_apply,map_add]

lemma curvatureAlong_smul (g : SmoothMetric M) (γ : ℝ → M)
    (J : ∀ s, TangentSpace I3 (γ s)) (f : ℝ → ℝ) (s : ℝ) :
    curvatureAlong g γ (fun r => f r • J r) s = f s • curvatureAlong g γ J s := by
  let c := chartAt E3 (γ s)
  let P : E3 →L[ℝ] TangentSpace I3 (γ s) := mfderiv I3 I3 c.symm (c (γ s))
  change P (curvatureTerm g c (c (γ s)) (fieldCoordinates γ (fun r => f r • J r) c s)
    (deriv (c ∘ γ) s) (deriv (c ∘ γ) s)) =
    f s • P (curvatureTerm g c (c (γ s)) (fieldCoordinates γ J c s) (deriv (c ∘ γ) s) (deriv (c ∘ γ) s))
  rw [fieldCoordinates_smul]
  simp only [← curvatureLinear_apply,map_smul]

lemma intrinsic_pairing_smooth (g : SmoothMetric M) {γ : ℝ → M}
    {J H : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U) (hH : SmoothFieldOn γ H U) :
    ContDiffOn ℝ ∞ (fun s => g.inner (γ s) (J s) (H s)) U := by
  intro s hs
  let c := chartAt E3 (γ s)
  have hc := chart_mem_atlas E3 (γ s)
  have hsc := mem_chart_source E3 (γ s)
  have hx := curve_coordinates_smoothAt hU hγ hc hs hsc
  have hF := smoothField_coordinatesAt hU hγ hJ hc hs hsc
  have hG := smoothField_coordinatesAt hU hγ hH hc hs hsc
  have hQ := ((chartBilin_smoothAt g hc (c.map_source hsc)).comp s hx).clm_apply hF |>.clm_apply hG
  have he : (fun r => g.inner (γ r) (J r) (H r)) =ᶠ[𝓝 s]
      (fun r => chartBilin g c ((c ∘ γ) r) (fieldCoordinates γ J c r) (fieldCoordinates γ H c r)) := by
    filter_upwards [(hγ.contMDiffAt (hU.mem_nhds hs)).continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds hsc)] with r hr
    exact (metric_field_coordinates g J H hc hr).symm
  exact (hQ.congr_of_eventuallyEq he).contDiffWithinAt
end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
lemma connectionBilin_symm (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x u v : E3) : connectionBilin g c x u v = connectionBilin g c x v u := by
  simp only [connectionBilin_apply,connectionTerm_symm g c x u v]
lemma connectionBilin_deriv_symm (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (t u v : E3) :
    fderiv ℝ (connectionBilin g c) x t u v = fderiv ℝ (connectionBilin g c) x t v u := by
  ext l
  rw [connectionBilin_deriv_apply g hc hx,connectionBilin_deriv_apply g hc hx,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun y => christoffel g c y l j k) = (fun y => christoffel g c y l k j) := by
    funext y; exact christoffel_symm g c y l j k
  rw [he]
  ring
lemma curvature_skew (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (u v w : E3) :
    curvatureTerm g c x u v w = -curvatureTerm g c x v u w := by
  rw [curvature_connection g hc hx,curvature_connection g hc hx]
  abel
lemma curvature_bianchi (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (u v w : E3) :
    curvatureTerm g c x u v w + curvatureTerm g c x v w u + curvatureTerm g c x w u v = 0 := by
  simp only [curvature_connection g hc hx]
  rw [connectionBilin_deriv_symm g hc hx u v w,
    connectionBilin_deriv_symm g hc hx v w u,connectionBilin_deriv_symm g hc hx w u v,
    connectionBilin_symm g c x v w,connectionBilin_symm g c x w u,connectionBilin_symm g c x u v]
  abel
end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

local instance instNormedAddCommGroupContinuousLinearMapRealIdE3 : NormedAddCommGroup (E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdE3 : NormedSpace ℝ (E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealIdE3_1 : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdE3_1 : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealIdE3_2 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdE3_2 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace

local instance instNormedAddCommGroupContinuousLinearMapRealIdE3_3 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdE3_3 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealIdE3_4 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdE3_4 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

lemma bilin_derivative_compatible (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (t u v : E3) :
    fderiv ℝ (chartBilin g c) x t u v =
      chartBilin g c x (connectionBilin g c x t u) v +
        chartBilin g c x u (connectionBilin g c x t v) := by
  let : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let p : ℝ → E3 := fun s => x + s • t
  have hp : HasDerivAt p t 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const t).const_add x
  have hp0 : p 0 = x := by simp [p]
  have hQ : HasFDerivAt (chartBilin g c) (fderiv ℝ (chartBilin g c) x) (p 0) := by
    rw [hp0]; exact ((chartBilin_smoothAt g hc hx).differentiableAt (by simp)).hasFDerivAt
  have he := (((hQ.comp_hasDerivAt 0 hp).clm_apply (hasDerivAt_const 0 u)).clm_apply
    (hasDerivAt_const 0 v)).unique
    (metric_fields_hasDerivAt g hc (by rw [hp0];exact hx) hp.differentiableAt
      (differentiableAt_const u) (differentiableAt_const v))
  simpa only [map_zero,add_zero,alongDerivative,deriv_const,zero_add,hp.deriv,hp0,
    connectionBilin_apply] using he

lemma bilin_derivative_line (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (s t u v : E3) :
    HasDerivAt (fun r : ℝ => fderiv ℝ (chartBilin g c) (x + r • s) t u v)
      (fderiv ℝ (fderiv ℝ (chartBilin g c)) x s t u v) 0 := by
  have hp : HasDerivAt (fun r : ℝ => x + r • s) s 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const s).const_add x
  have hDQ : HasFDerivAt (fderiv ℝ (chartBilin g c))
      (fderiv ℝ (fderiv ℝ (chartBilin g c)) x) x := (((chartBilin_smoothAt g hc hx).fderiv_right (m := ∞)
    (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hDQ' : HasFDerivAt (fderiv ℝ (chartBilin g c))
      (fderiv ℝ (fderiv ℝ (chartBilin g c)) x) (x + (0:ℝ) • s) := by
    simpa only [zero_smul,add_zero] using hDQ
  have hline : HasDerivAt (fun r : ℝ => fderiv ℝ (chartBilin g c) (x + r • s))
      (fderiv ℝ (fderiv ℝ (chartBilin g c)) x s) 0 := hDQ'.comp_hasDerivAt 0 hp
  have ht : HasDerivAt (fun r : ℝ => fderiv ℝ (chartBilin g c) (x + r • s) t)
      (fderiv ℝ (fderiv ℝ (chartBilin g c)) x s t) 0 := by
    simpa only [map_zero, add_zero] using hline.clm_apply (hasDerivAt_const 0 t)
  have hu : HasDerivAt (fun r : ℝ => fderiv ℝ (chartBilin g c) (x + r • s) t u)
      (fderiv ℝ (fderiv ℝ (chartBilin g c)) x s t u) 0 := by
    simpa only [map_zero, add_zero] using ht.clm_apply (hasDerivAt_const 0 u)
  simpa only [map_zero, add_zero] using hu.clm_apply (hasDerivAt_const 0 v)

lemma connectionBilin_line (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (s t u : E3) :
    HasDerivAt (fun r : ℝ => connectionBilin g c (x + r • s) t u)
      (fderiv ℝ (connectionBilin g c) x s t u) 0 := by
  have hp : HasDerivAt (fun r : ℝ => x + r • s) s 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const s).const_add x
  have hC := ((connectionBilin_smoothAt g hc hx).differentiableAt (by simp)).hasFDerivAt
  have hC' : HasFDerivAt (connectionBilin g c) (fderiv ℝ (connectionBilin g c) x)
      (x + (0:ℝ) • s) := by simpa only [zero_smul,add_zero] using hC
  have hh := ((hC'.comp_hasDerivAt 0 hp).clm_apply (hasDerivAt_const 0 t)).clm_apply
    (hasDerivAt_const 0 u)
  convert hh using 1 <;> first | rfl | simp only [map_zero,add_zero]

lemma bilin_connection_line (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (s t u v : E3) :
    HasDerivAt (fun r : ℝ => chartBilin g c (x + r • s)
      (connectionBilin g c (x + r • s) t u) v)
      (fderiv ℝ (chartBilin g c) x s (connectionBilin g c x t u) v +
        chartBilin g c x (fderiv ℝ (connectionBilin g c) x s t u) v) 0 := by
  have hp : HasDerivAt (fun r : ℝ => x + r • s) s 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const s).const_add x
  have hQ := ((chartBilin_smoothAt g hc hx).differentiableAt (by simp)).hasFDerivAt
  have hQ' : HasFDerivAt (chartBilin g c) (fderiv ℝ (chartBilin g c) x)
      (x + (0:ℝ) • s) := by simpa only [zero_smul,add_zero] using hQ
  have hh := (((hQ'.comp_hasDerivAt 0 hp).clm_apply (connectionBilin_line g hc hx s t u)).clm_apply
    (hasDerivAt_const 0 v))
  convert hh using 1 <;> first | rfl | simp only [map_zero,add_zero,zero_smul,Function.comp_apply,_root_.add_apply]

lemma bilin_second_compatible (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (s t u v : E3) :
    fderiv ℝ (fderiv ℝ (chartBilin g c)) x s t u v =
      fderiv ℝ (chartBilin g c) x s (connectionBilin g c x t u) v +
      chartBilin g c x (fderiv ℝ (connectionBilin g c) x s t u) v +
      fderiv ℝ (chartBilin g c) x s u (connectionBilin g c x t v) +
      chartBilin g c x u (fderiv ℝ (connectionBilin g c) x s t v) := by
  have hp : ContinuousAt (fun r : ℝ => x + r • s) 0 := by fun_prop
  have he : (fun r : ℝ => fderiv ℝ (chartBilin g c) (x + r • s) t u v) =ᶠ[𝓝 0]
      (fun r : ℝ => chartBilin g c (x + r • s) (connectionBilin g c (x + r • s) t u) v +
        chartBilin g c (x + r • s) (connectionBilin g c (x + r • s) t v) u) := by
    have hn : x + (0:ℝ) • s ∈ c.target := by simpa using hx
    filter_upwards [hp.preimage_mem_nhds (c.open_target.mem_nhds hn)] with r hr
    rw [bilin_derivative_compatible g hc hr,chartBilin_symm g c (x+r•s) u]
  have hd := ((bilin_connection_line g hc hx s t u v).add
    (bilin_connection_line g hc hx s t v u)).congr_of_eventuallyEq he
  have hh := (bilin_derivative_line g hc hx s t u v).unique hd
  have hsym : fderiv ℝ (chartBilin g c) x s (connectionBilin g c x t v) u =
      fderiv ℝ (chartBilin g c) x s u (connectionBilin g c x t v) := by
    rw [bilin_derivative_compatible g hc hx,bilin_derivative_compatible g hc hx]
    rw [chartBilin_symm g c x (connectionBilin g c x s (connectionBilin g c x t v)) u,
      chartBilin_symm g c x (connectionBilin g c x t v) (connectionBilin g c x s u)]
    exact add_comm _ _
  rw [hsym,chartBilin_symm g c x (fderiv ℝ (connectionBilin g c) x s t v) u] at hh
  simpa only [add_assoc] using hh

lemma curvature_pairing_skew (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (s t u v : E3) :
    chartBilin g c x (curvatureTerm g c x s t u) v +
      chartBilin g c x u (curvatureTerm g c x s t v) = 0 := by
  have hs := bilin_second_compatible g hc hx s t u v
  have ht := bilin_second_compatible g hc hx t s u v
  have hsym := ((chartBilin_smoothAt g hc hx).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).eq s t
  rw [hsym] at hs
  rw [ht] at hs
  simp only [bilin_derivative_compatible g hc hx] at hs
  simp only [curvature_connection g hc hx,map_add,map_sub,_root_.add_apply,_root_.sub_apply]
  linarith

lemma curvature_pairing_selfAdjoint (g : SmoothMetric M) {c : OpenPartialHomeomorph M E3}
    (hc : c ∈ atlas E3 M) {x : E3} (hx : x ∈ c.target) (u v t : E3) :
    chartBilin g c x (curvatureTerm g c x u t t) v =
      chartBilin g c x (curvatureTerm g c x v t t) u := by
  have hb := congrArg (fun z => chartBilin g c x z t) (curvature_bianchi g hc hx u t v)
  have hs := curvature_pairing_skew g hc hx u t t v
  have ht := curvature_pairing_skew g hc hx t v u t
  have hu := curvature_pairing_skew g hc hx v u t t
  rw [curvature_skew g hc hx t v t] at ht
  simp only [map_add,_root_.add_apply,map_zero,_root_.zero_apply,map_neg] at hb ht
  rw [chartBilin_symm g c x t (curvatureTerm g c x u t v)] at hs
  rw [chartBilin_symm g c x u (curvatureTerm g c x v t t)] at ht
  rw [chartBilin_symm g c x t (curvatureTerm g c x v u t)] at hu
  linarith
end ThreeManifold.RiemannianCoordinates

end

end OAI


