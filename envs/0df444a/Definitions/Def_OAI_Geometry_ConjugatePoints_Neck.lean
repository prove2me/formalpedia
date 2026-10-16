-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
-- name    : OAI_Geometry_ConjugatePoints_Neck
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:13:09.342892+00:00
-- url     : https://prove2.me/theorems/9d20fbd0-6712-44de-96f0-76e8c5177097
-- title:
--   Coordinate formulas for metrics $dt^2 + Q(t)$, the neck cometric matrices, and the flat torus neck
-- statement:
--   This file fixes the explicit coordinate formulas used to compute geodesics, curvature and index forms in the neck of the three-manifold construction, the explicit $2 \times 2$ cometric matrices of the neck, and the flat model of the neck as a quotient of a slab in $\mathbb{R}^3$.
--
--   Notation. Vectors of $\mathbb{R}^3$ are written $U = (U_1, U_2) \in \mathbb{R} \times \mathbb{R}^2$ (a "height" component and a "torus" component). For a real $2 \times 2$ matrix $A$ and $u, v \in \mathbb{R}^2$ put $\langle u, v \rangle_A = u \cdot (A v)$ (no symmetry is assumed). Let $\psi$ be the standard smooth transition function ($C^\infty$, nondecreasing, $0$ on $(-\infty,0]$, $1$ on $[1,\infty)$), and let $a(u) = e^{-1/(2/3-u)}$ for $u < 2/3$, $a(u) = 0$ otherwise, $A(u) = \int_0^u a$, and $\chi(t) = \psi(6(t - 5/12))$.
--
--   1. **Tensor contraction.** For a finite index set and $C = (C_{lij})$, $C(u, v)_l = \sum_{i,j} C_{lij}\, u_i v_j$.
--
--   2. **Coordinate formulas for metrics $dt^2 + Q(t)$.** For $2\times 2$ matrices $Q, P, A, B$ (in applications $Q$ is the torus metric at height $t$, $P = Q^{-1}$, $A = Q'$, $B = Q''$) and $T, U, V, W, \dot V \in \mathbb{R} \times \mathbb{R}^2$:
--      - metric: $\langle U, V \rangle_Q = U_1 V_1 + \langle U_2, V_2 \rangle_Q$;
--      - connection: $\Gamma(U, V) = \bigl(-\tfrac12 \langle U_2, V_2\rangle_A,\ \tfrac12 (U_1\, PA V_2 + V_1\, PA U_2)\bigr)$;
--      - its height derivative: $\Gamma'(U, V) = \bigl(-\tfrac12 \langle U_2, V_2\rangle_B,\ \tfrac12 (U_1 (PB - PAPA) V_2 + V_1 (PB - PAPA) U_2)\bigr)$;
--      - curvature: $R(U,V)W = U_1\, \Gamma'(V, W) - V_1\, \Gamma'(U, W) + \Gamma(U, \Gamma(V, W)) - \Gamma(V, \Gamma(U, W))$;
--      - energy density: $\dot V_1^2 + \langle \dot V_2, \dot V_2 \rangle_Q + 2 V_1 \langle \dot V_2, T_2 \rangle_A + \tfrac12 V_1^2 \langle T_2, T_2 \rangle_B$;
--      - boundary term: $-\tfrac12 T_1 \langle V_2, V_2 \rangle_A + V_1 \langle T_2, V_2 \rangle_A$;
--      - boundary jet:
--   $$
--   -\tfrac14 \langle T_2,T_2\rangle_A \langle V_2,V_2\rangle_A - T_1 \langle \dot V_2, V_2\rangle_A - \tfrac12 T_1^2 \langle V_2,V_2\rangle_B + \dot V_1 \langle V_2,T_2\rangle_A + V_1 \langle \dot V_2,T_2\rangle_A + V_1T_1\langle V_2,T_2\rangle_B - V_1T_1\langle V_2,T_2\rangle_{APA};
--   $$
--      - the identification $\mathbb{R}^3 \cong \mathbb{R} \times \mathbb{R}^2$, $x \mapsto (x_0, (x_1, x_2))$, and the block matrices $\operatorname{diag}(1, Q)$ and $\operatorname{diag}(0, A)$ of size $3 \times 3$.
--
--      With $P = Q^{-1}$, $A = Q'$, $B = Q''$ these are the Christoffel symbols, their height derivative and the curvature tensor of the metric $dt^2 + Q(t)$ written in the conventions of the coordinate curvature $R(u,v)w$ used throughout the project.
--
--   3. **The neck cometric.** For $\delta, t \in \mathbb{R}$ let $d_1 = 1 + \delta A(t)$, $d_2 = 1 + \delta A(1 - t)$, $\sigma = \delta^2 \chi(t)$ and
--   $$
--   P_\delta(t) = \begin{pmatrix} d_1 + d_2 \sigma^2 & d_2 \sigma \\ d_2 \sigma & d_2 \end{pmatrix} = \begin{pmatrix} 1 & \sigma \\ 0 & 1 \end{pmatrix}\begin{pmatrix} d_1 & 0 \\ 0 & d_2 \end{pmatrix}\begin{pmatrix} 1 & 0 \\ \sigma & 1 \end{pmatrix}, \qquad Q_\delta(t) = P_\delta(t)^{-1}.
--   $$
--   With $u_1 = \delta a(t)$, $u_2 = -\delta a(1-t)$, $v = \delta^2 \chi'(t)$, $w_1 = \delta a'(t)$, $w_2 = \delta a'(1-t)$, $z = \delta^2 \chi''(t)$ (the first and second $t$-derivatives of $d_1, d_2, \sigma$), the matrices
--   $$
--   P^{(1)}_\delta = \begin{pmatrix} u_1 + u_2 \sigma^2 + 2 d_2 \sigma v & u_2 \sigma + d_2 v \\ u_2 \sigma + d_2 v & u_2 \end{pmatrix}, \quad P^{(2)}_\delta = \begin{pmatrix} w_1 + w_2\sigma^2 + 4u_2\sigma v + 2d_2 v^2 + 2 d_2\sigma z & w_2\sigma + 2u_2 v + d_2 z \\ w_2\sigma + 2u_2 v + d_2 z & w_2 \end{pmatrix}
--   $$
--   are the matrices obtained from $P_\delta$ by differentiating its entries once and twice with the product rule (they are defined by these explicit formulas; the file does not state a derivative identity), and $N_1, N_2$ are the symmetric matrices with zero lower-right entry determined by $P^{(1)}_\delta = \operatorname{diag}(u_1, u_2) + \delta^2 N_1$ and $P^{(2)}_\delta = \operatorname{diag}(w_1, w_2) + \delta^2 N_2$; explicitly $N_1$ has entries $-\delta^3 a(1-t)\chi^2 + 2 d_2 \delta^2 \chi\chi'$ and $-\delta a(1-t)\chi + d_2 \chi'$, and $N_2$ has entries $\delta^3 a'(1-t)\chi^2 - 4\delta^3 a(1-t)\chi\chi' + 2 d_2\delta^2 \chi'^2 + 2 d_2 \delta^2 \chi\chi''$ and $\delta a'(1-t)\chi - 2\delta a(1-t)\chi' + d_2\chi''$ (diagonal, off-diagonal). Further,
--   $$
--   T_\delta = \begin{pmatrix} \delta^2 & 1 \\ 1 & 0 \end{pmatrix}, \qquad C_\delta = \begin{pmatrix} 0 & 1 \\ 1 & -\delta^2 \end{pmatrix}, \qquad P^{\mathrm{end}}_\delta(\tau) = C_\delta\, P_\delta(1 - \tau)\, C_\delta^{\mathsf T},
--   $$
--   ($T_\delta$ and $C_\delta$ are mutually inverse), and the coordinate cometric of the left end is $P_\delta$, that of the right end $P^{\mathrm{end}}_\delta$. Auxiliary: $|p|^2 = p_0^2 + p_1^2$ and $q_M(p) = p \cdot Mp$ for $p \in \mathbb{R}^2$, the constant $144\, e^{-12}$, and the congruence map $M \mapsto C M C^{\mathsf T}$ as a continuous linear map on $2 \times 2$ matrices.
--
--   4. **Slab and flat torus neck.** The slab $S = \{x \in \mathbb{R}^3 : 0 < x_0 < 1\}$ is an open subset of $\mathbb{R}^3$, made a $C^\infty$ manifold with the single chart given by the inclusion. For $B_0, B_1 \in \mathbb{R}$ the neck is $N_{B_0,B_1} = (0,1) \times \mathbb{R}/B_0\mathbb{Z} \times \mathbb{R}/B_1\mathbb{Z}$, and
--   $$
--   S \to N_{B_0,B_1}, \qquad (x_0, x_1, x_2) \mapsto (x_0,\ x_1 \bmod B_0,\ x_2 \bmod B_1)
--   $$
--   is a quotient covering map for the group $B_0\mathbb{Z} \times B_1\mathbb{Z}$ acting on $S$ by translating $x_1, x_2$. These translations are $C^\infty$, and $N_{B_0,B_1}$ receives the quotient $C^\infty$ structure modelled on $\mathbb{R}^3$.
--
--   These definitions turn the analysis of geodesics, Jacobi fields and index forms in the neck into explicit computations with $2 \times 2$ matrices: the neck carries metrics of the form $dt^2 + Q_\delta(t)$ with $Q_\delta = P_\delta^{-1}$, and the left and right coordinate cometrics describe the two ends of the neck in compatible torus coordinates.
--
--   **Formalization Note** Vectors are `Vec = ℝ × (Fin 2 → ℝ)` and matrices `TMat = Matrix (Fin 2) (Fin 2) ℝ`; the formulas of item 2 are `Neck.metric`, `gamma`, `gammaPrime`, `curvatureJet`, `coordinateEnergyDensity`, `boundaryTerm`, `boundaryJet`, `splitVector`/`joinVector`, `blockMatrix`, `blockJet`, and they are defined for arbitrary matrices without assuming $P = Q^{-1}$. In item 3 the names are `Cometric.d₁`, `d₂`, `shear`, `P`, `Q`, `u₁`, …, `P₁`, `P₂`, `N₁`, `N₂`, `T₂`, `C₂`, `PEnd`, `cutoffMargin`, `congruenceCLM`, and `coordinateCometric right δ` (with `right : Bool`); `Q δ t` uses Mathlib's matrix inverse, which returns $0$ for singular matrices, and the derivatives $a'$, $\chi'$, $\chi''$ are `deriv`. The slab is `LocalNeck.Slab` and the neck is `TorusNeck.Neck B₀ B₁` with charts `neckCharts`; the lemmas identifying slab tangent trivializations with the identity are plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Neck.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ConjugatePoints mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric

namespace OAI

noncomputable section

/-!
# Tensor identities and the local and torus neck metrics.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff

namespace ThreeManifold.Tensor
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

def contract (C : n → n → n → ℝ) (u v : n → ℝ) : n → ℝ :=
  fun l => ∑ i, ∑ j, C l i j * u i * v j

end ThreeManifold.Tensor

namespace ThreeManifold.Neck
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

abbrev TVec := Fin 2 → ℝ
abbrev TMat := Matrix (Fin 2) (Fin 2) ℝ
abbrev Vec := ℝ × TVec

def pairing (A : TMat) (u v : TVec) : ℝ := dotProduct u (A *ᵥ v)

def metric (Q : TMat) (U V : Vec) : ℝ := U.1 * V.1 + pairing Q U.2 V.2

def gamma (P A : TMat) (U V : Vec) : Vec :=
  (-(1 / 2 : ℝ) * pairing A U.2 V.2,
    (1 / 2 : ℝ) • (U.1 • (P *ᵥ (A *ᵥ V.2)) + V.1 • (P *ᵥ (A *ᵥ U.2))))

def gammaPrime (P A B : TMat) (U V : Vec) : Vec :=
  (-(1 / 2 : ℝ) * pairing B U.2 V.2,
    (1 / 2 : ℝ) •
      (U.1 • ((P * B - P * A * P * A) *ᵥ V.2) +
       V.1 • ((P * B - P * A * P * A) *ᵥ U.2)))

def curvatureJet (P A B : TMat) (U V W : Vec) : Vec :=
  U.1 • gammaPrime P A B V W - V.1 • gammaPrime P A B U W +
    gamma P A U (gamma P A V W) - gamma P A V (gamma P A U W)

def coordinateEnergyDensity (Q A B : TMat) (T V Vdot : Vec) : ℝ :=
  Vdot.1 ^ 2 + pairing Q Vdot.2 Vdot.2 +
    2 * V.1 * pairing A Vdot.2 T.2 + (1 / 2 : ℝ) * V.1 ^ 2 * pairing B T.2 T.2

def boundaryTerm (A : TMat) (T V : Vec) : ℝ :=
  -(1 / 2 : ℝ) * T.1 * pairing A V.2 V.2 + V.1 * pairing A T.2 V.2

def boundaryJet (P A B : TMat) (T V Vdot : Vec) : ℝ :=
  -(1 / 4 : ℝ) * pairing A T.2 T.2 * pairing A V.2 V.2 -
    T.1 * pairing A Vdot.2 V.2 - (1 / 2 : ℝ) * T.1 ^ 2 * pairing B V.2 V.2 +
    Vdot.1 * pairing A V.2 T.2 + V.1 * pairing A Vdot.2 T.2 +
    V.1 * T.1 * pairing B V.2 T.2 - V.1 * T.1 * pairing (A * P * A) V.2 T.2

def splitVector (x : E3) : Vec := (x 0, ![x 1, x 2])
def joinVector (u : Vec) : E3 := ![u.1, u.2 0, u.2 1]
def blockMatrix (Q : TMat) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Q 0 0, Q 0 1; 0, Q 1 0, Q 1 1]
def blockJet (A : TMat) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

abbrev V2 := Fin 2 → ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def sqnorm (p : V2) : ℝ := p 0 ^ 2 + p 1 ^ 2

def qform (M : Mat2) (p : V2) : ℝ := p ⬝ᵥ (M *ᵥ p)

def d₁ (δ t : ℝ) : ℝ := 1 + δ * A t
def d₂ (δ t : ℝ) : ℝ := 1 + δ * A (1 - t)
def shear (δ t : ℝ) : ℝ := δ ^ 2 * χ t
def P (δ t : ℝ) : Mat2 :=
  !![d₁ δ t + d₂ δ t * shear δ t ^ 2, d₂ δ t * shear δ t;
     d₂ δ t * shear δ t, d₂ δ t]

def Q (δ t : ℝ) : Mat2 := (P δ t)⁻¹

@[fun_prop] lemma d₁_smooth (δ : ℝ) : ContDiff ℝ ∞ (d₁ δ) := by
  unfold d₁
  fun_prop

@[fun_prop] lemma d₂_smooth (δ : ℝ) : ContDiff ℝ ∞ (d₂ δ) := by
  unfold d₂
  fun_prop

@[fun_prop] lemma shear_smooth (δ : ℝ) : ContDiff ℝ ∞ (shear δ) := by
  unfold shear
  fun_prop

def u₁ (δ t : ℝ) : ℝ := δ * a t
def u₂ (δ t : ℝ) : ℝ := -δ * a (1 - t)
def v (δ t : ℝ) : ℝ := δ ^ 2 * deriv χ t
def w₁ (δ t : ℝ) : ℝ := δ * deriv a t
def w₂ (δ t : ℝ) : ℝ := δ * deriv a (1 - t)
def z (δ t : ℝ) : ℝ := δ ^ 2 * deriv (deriv χ) t

def P₁ (δ t : ℝ) : Mat2 :=
  !![u₁ δ t + u₂ δ t * shear δ t ^ 2 + 2 * d₂ δ t * shear δ t * v δ t,
     u₂ δ t * shear δ t + d₂ δ t * v δ t;
     u₂ δ t * shear δ t + d₂ δ t * v δ t, u₂ δ t]

def P₂ (δ t : ℝ) : Mat2 :=
  !![w₁ δ t + w₂ δ t * shear δ t ^ 2 + 4 * u₂ δ t * shear δ t * v δ t +
       2 * d₂ δ t * v δ t ^ 2 + 2 * d₂ δ t * shear δ t * z δ t,
     w₂ δ t * shear δ t + 2 * u₂ δ t * v δ t + d₂ δ t * z δ t;
     w₂ δ t * shear δ t + 2 * u₂ δ t * v δ t + d₂ δ t * z δ t, w₂ δ t]

def T₂ (δ : ℝ) : Mat2 := !![δ ^ 2, 1; 1, 0]
def C₂ (δ : ℝ) : Mat2 := !![0, 1; 1, -δ ^ 2]

def PEnd (δ τ : ℝ) : Mat2 := C₂ δ * P δ (1 - τ) * (C₂ δ)ᵀ

def N₁ (δ t : ℝ) : Mat2 :=
  !![-δ ^ 3 * a (1 - t) * χ t ^ 2 + 2 * d₂ δ t * δ ^ 2 * χ t * deriv χ t,
      -δ * a (1 - t) * χ t + d₂ δ t * deriv χ t;
      -δ * a (1 - t) * χ t + d₂ δ t * deriv χ t, 0]

def N₂ (δ t : ℝ) : Mat2 :=
  !![δ ^ 3 * deriv a (1 - t) * χ t ^ 2 - 4 * δ ^ 3 * a (1 - t) * χ t * deriv χ t +
       2 * d₂ δ t * δ ^ 2 * deriv χ t ^ 2 +
       2 * d₂ δ t * δ ^ 2 * χ t * deriv (deriv χ) t,
      δ * deriv a (1 - t) * χ t - 2 * δ * a (1 - t) * deriv χ t +
       d₂ δ t * deriv (deriv χ) t;
      δ * deriv a (1 - t) * χ t - 2 * δ * a (1 - t) * deriv χ t +
       d₂ δ t * deriv (deriv χ) t, 0]

@[fun_prop] lemma a_deriv_smooth : ContDiff ℝ ∞ (deriv a) :=
  (contDiff_infty_iff_deriv.mp a_smooth).2

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

def cutoffMargin : ℝ := 144 * Real.exp (-12)

def congruenceCLM (C : Mat2) : Mat2 →L[ℝ] Mat2 :=
  ((mulRightLinearMap (Fin 2) ℝ Cᵀ).comp
    (mulLeftLinearMap (Fin 2) ℝ C)).toContinuousLinearMap

def coordinateCometric (right : Bool) (δ : ℝ) : ℝ → Mat2 :=
  if right then PEnd δ else P δ

end ThreeManifold.Cometric

namespace ThreeManifold.LocalNeck

section
open Manifold Bundle Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

abbrev Slab := {x : E3 // x 0 ∈ Ioo (0 : ℝ) 1}

instance : Nonempty Slab := ⟨⟨fun _ => 1 / 2, by norm_num⟩⟩

lemma slab_isOpen : IsOpen {x : E3 | x 0 ∈ Ioo (0 : ℝ) 1} :=
  isOpen_Ioo.preimage (continuous_apply 0)

theorem slabEmbedding : Topology.IsOpenEmbedding (Subtype.val : Slab → E3) :=
  slab_isOpen.isOpenEmbedding_subtypeVal

def slabChart : OpenPartialHomeomorph Slab E3 :=
  slabEmbedding.toOpenPartialHomeomorph Subtype.val

@[simp] lemma slabChart_source : slabChart.source = univ := by
  exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source _ _

@[simp] lemma slabChart_apply (x : Slab) : slabChart x = x.val := rfl

instance : ChartedSpace E3 Slab := slabChart.singletonChartedSpace slabChart_source
instance : IsManifold I3 ∞ Slab := slabChart.isManifold_singleton slabChart_source

@[simp] lemma chartAt_eq (x : Slab) : chartAt E3 x = slabChart := rfl

lemma achart_eq (x y : Slab) : achart E3 x = achart E3 y := by
  apply Subtype.ext
  rfl

@[simp] lemma slab_symmL (b b' : Slab) :
    (trivializationAt E3 (TangentSpace I3) b).symmL ℝ b' = (1 : E3 →L[ℝ] E3) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core]
  · rw [achart_eq b b']
    apply ContinuousLinearMap.ext
    intro v
    apply (tangentBundleCore I3 Slab).coordChange_self
    simp
  · simp

@[simp] lemma slab_linearMapAt (b b' : Slab) :
    (trivializationAt E3 (TangentSpace I3) b).continuousLinearMapAt ℝ b' =
      (1 : E3 →L[ℝ] E3) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core]
  · rw [achart_eq b b']
    apply ContinuousLinearMap.ext
    intro v
    apply (tangentBundleCore I3 Slab).coordChange_self
    simp
  · simp

lemma slab_val_smooth : ContMDiff I3 I3 ∞ (Subtype.val : Slab → E3) := by
  intro x
  convert! contMDiffAt_extChartAt (I := I3) (n := ∞) (x := x) using 1

open Cometric Neck

end

open Manifold Bundle Set Filter Cometric Neck Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end ThreeManifold.LocalNeck

namespace ThreeManifold.TorusNeck

section
open Set Filter Topology Manifold Bundle
open scoped ContDiff Matrix.Norms.Elementwise
open LocalNeck QuotientConstruction

abbrev Height := {t : ℝ // t ∈ Ioo (0 : ℝ) 1}
abbrev Neck (B₀ B₁ : ℝ) := Height × (AddCircle B₀ × AddCircle B₁)
abbrev Deck (B₀ B₁ : ℝ) := PUnit.{1} ×
  (Multiplicative (AddSubgroup.zmultiples B₀) × Multiplicative (AddSubgroup.zmultiples B₁))

instance : MulAction PUnit.{1} Height where
  smul _ t := t
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

lemma height_cover : IsQuotientCoveringMap (id : Height → Height) PUnit.{1} where
  __ := Homeomorph.refl Height |>.isQuotientMap
  continuous_const_smul _ := continuous_id
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro h
      exact ⟨PUnit.unit, h.symm⟩
    · rintro ⟨k, h⟩
      exact h.symm
  disjoint _ := ⟨univ, univ_mem, fun _ _ => Subsingleton.elim _ _⟩

instance torusProductAction (B₀ B₁ : ℝ) :
    MulAction (Multiplicative (AddSubgroup.zmultiples B₀) ×
      Multiplicative (AddSubgroup.zmultiples B₁)) (ℝ × ℝ) := productAction

instance neckProductAction (B₀ B₁ : ℝ) : MulAction (Deck B₀ B₁) (Height × (ℝ × ℝ)) :=
  productAction

def split : Slab ≃ₜ Height × (ℝ × ℝ) where
  toFun x := (⟨x.1 0, x.2⟩, x.1 1, x.1 2)
  invFun y := ⟨![y.1.1, y.2.1, y.2.2], y.1.2⟩
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv y := rfl
  continuous_toFun := by
    exact ((continuous_apply 0).comp continuous_subtype_val).subtype_mk _ |>.prodMk
      (((continuous_apply 1).comp continuous_subtype_val).prodMk
        ((continuous_apply 2).comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp
    · exact continuous_subtype_val.comp continuous_fst
    · exact continuous_fst.comp continuous_snd
    · exact continuous_snd.comp continuous_snd

instance deckAction (B₀ B₁ : ℝ) : MulAction (Deck B₀ B₁) Slab :=
  split.toEquiv.mulAction (Deck B₀ B₁)

def projection (B₀ B₁ : ℝ) (x : Slab) : Neck B₀ B₁ :=
  (⟨x.1 0, x.2⟩, (x.1 1 : AddCircle B₀), (x.1 2 : AddCircle B₁))

lemma projection_cover (B₀ B₁ : ℝ) :
    IsQuotientCoveringMap (projection B₀ B₁) (Deck B₀ B₁) := by
  have h0 := (AddCircle.isAddQuotientCoveringMap_coe B₀).toMultiplicative _
  have h1 := (AddCircle.isAddQuotientCoveringMap_coe B₁).toMultiplicative _
  have ht := product_cover h0 h1
  have hn := product_cover height_cover ht
  exact cover_precomp hn split (fun _ _ => split.apply_symm_apply _)

lemma deck_val (B₀ B₁ : ℝ) (k : Deck B₀ B₁) (x : Slab) :
    (k • x).val = x.val + ![0, (Multiplicative.toAdd k.2.1).val,
      (Multiplicative.toAdd k.2.2).val] := by
  ext i
  fin_cases i
  · change x.val 0 = x.val 0 + 0
    ring
  · change (Multiplicative.toAdd k.2.1).val + x.val 1 =
      x.val 1 + (Multiplicative.toAdd k.2.1).val
    ring
  · change (Multiplicative.toAdd k.2.2).val + x.val 2 =
      x.val 2 + (Multiplicative.toAdd k.2.2).val
    ring

lemma deck_smooth (B₀ B₁ : ℝ) (k : Deck B₀ B₁) :
    ContMDiff I3 I3 ∞ (fun x : Slab => k • x) := by
  intro x
  rw [contMDiffAt_iff_target_of_mem_source (mem_chart_source E3 (k • x))]
  refine ⟨(projection_cover B₀ B₁).continuous_const_smul k |>.continuousAt, ?_⟩
  have hv : (fun y : Slab => slabChart (k • y)) = fun y => y.val +
      ![0, (Multiplicative.toAdd k.2.1).val, (Multiplicative.toAdd k.2.2).val] := by
    funext y
    exact deck_val B₀ B₁ k y
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_def, id_eq,
    chartAt_eq]
  rw [hv]
  exact (slab_val_smooth.contMDiffAt).add contMDiffAt_const

noncomputable def sectionMap (B₀ B₁ : ℝ) : Neck B₀ B₁ → Slab :=
  Function.surjInv (projection_cover B₀ B₁).surjective

lemma sectionMap_rightInverse (B₀ B₁ : ℝ) :
    Function.RightInverse (sectionMap B₀ B₁) (projection B₀ B₁) :=
  Function.rightInverse_surjInv (projection_cover B₀ B₁).surjective

instance neckCharts (B₀ B₁ : ℝ) : ChartedSpace E3 (Neck B₀ B₁) :=
  manifoldCharts (E := E3) (projection_cover B₀ B₁) (sectionMap_rightInverse B₀ B₁)

instance neckSmooth (B₀ B₁ : ℝ) : IsManifold I3 ∞ (Neck B₀ B₁) :=
  manifold_quotient_isManifold (projection_cover B₀ B₁) (sectionMap_rightInverse B₀ B₁)
    (deck_smooth B₀ B₁)

open Cometric Neck
end

open Set Filter Manifold Bundle Neck Cometric LocalNeck Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.TorusNeck

end

end OAI


