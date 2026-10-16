-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
-- name    : OAI_Geometry_ConjugatePoints_Continuation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:00:48.481678+00:00
-- url     : https://prove2.me/theorems/4169964e-92a0-4687-ab96-22a8a55185a0
-- title:
--   Path lifting through the exponential map and the covering property of $\exp_p$ under nonpositive curvature
-- statement:
--   This file proves that, on a compact Riemannian three-manifold of nonpositive sectional curvature, the exponential map at any point is a covering map (the Cartan–Hadamard theorem in this setting). The argument lifts $C^1$ curves through $\exp_p$ by solving an ordinary differential equation and continuing its solutions globally; the file also contains a general covering criterion and a few objects used later for loops in the glued manifold.
--
--   **Notation.** $M$ is a smooth manifold modelled on $\mathbb{R}^3$ with smooth Riemannian metric $g$, and $\exp_p : \mathbb{R}^3 \to M$ is the exponential map at $p$ (defined when $M$ is compact and Hausdorff). An *equation* on a space $X$ is a predicate on (curve $z : \mathbb{R} \to X$, time $t$) that depends only on the germ of $z$ at $t$, is invariant under time translation, and has unique solutions on open intervals given one common value; $z$ *solves it on* $U$ if the predicate holds at every $t \in U$.
--
--   The file contains:
--
--   1. **Global continuation criteria.** For an equation on $X$ and a point $x$: (a) if some solution through $x$ exists on a neighbourhood of time $0$, and for every $A > 0$ there is $\delta > 0$ such that from every point of every solution $z$ with $z(0) = x$ on $(-a, a)$, $0 < a \le A$, a new solution can be started on $(-\delta, \delta)$, then there is a solution $z$ with $z(0) = x$ defined for all times; (b) the same conclusion holds if solutions exist locally on a uniform time interval near every point of $X$ and, for each $A > 0$, all solutions with $z(0) = x$ on $(-a, a)$, $0 < a \le A$, take values in a fixed compact set $K_A$.
--
--   2. **The lifting equation.** For a map $f : E \to Y$ from a normed space and a curve $\gamma : \mathbb{R} \to Y$, the state space is
--   $$
--   \mathcal{S}(f, \gamma) = \{(t, v) \in \mathbb{R} \times E : f(v) = \gamma(t)\},
--   $$
--   and a curve $z(r) = (t(r), v(r))$ in $\mathcal{S}$ solves the lifting equation at $r$ if it is differentiable there with derivative of the form $(1, w)$. When $f$ is a local homeomorphism this is an equation in the sense above, and along any solution on $(-a, a)$ the time component is $t(r) = r + t(0)$.
--
--   3. **Smooth local lifts.** If $f : \mathbb{R}^3 \to M$ is $C^1$, has injective differential everywhere and is a local homeomorphism, its local inverses are $C^1$; for a $C^1$ curve $\gamma$ the lifting equation has local solutions near every state, uniformly on a neighbourhood; along solutions $df_{v(r)}\,\dot v(r) = \dot\gamma(t(r))$; and every continuous lift $v$ of $\gamma$ (i.e. $f \circ v = \gamma$) is $C^1$. Also, for a positive-definite bilinear form $B$ on a nontrivial finite-dimensional normed space there is $C > 0$ with $\|v\|^2 \le C\,B(v, v)$.
--
--   4. **Compact bounds and global lifts.** Let $M$ be compact and Hausdorff and $g$ of nonpositive sectional curvature. For a $C^1$ curve $\gamma : \mathbb{R} \to M$, a state $x$ and $A > 0$ there is a compact set of states containing every solution of the lifting equation through $\exp_p$ with $z(0) = x$ on $(-a, a)$, $0 < a \le A$. Consequently, for every $v_0$ with $\exp_p(v_0) = \gamma(0)$ there is a $C^1$ curve $v : \mathbb{R} \to \mathbb{R}^3$ with
--   $$
--   v(0) = v_0, \qquad \exp_p(v(t)) = \gamma(t) \quad \text{for all } t \in \mathbb{R}.
--   $$
--
--   5. **A covering criterion.** For a local homeomorphism $p : E \to X$ with $E$ Hausdorff, fibres are discrete. If a point $x$ has an open neighbourhood $U$ and a homotopy $H : [0,1] \times U \to X$ with $H(0, b) = x$, $H(1, b) = b$, such that every path $t \mapsto H(t, b)$ lifts from every point of $p^{-1}(x)$, and every point $z \in p^{-1}(U)$ is the endpoint of a lift of $t \mapsto H(t, p(z))$, then $p$ is evenly covered at $x$. Every point of $M$ has such a neighbourhood whose radial paths extend to $C^1$ curves $\mathbb{R} \to M$, so a local homeomorphism $f : \mathbb{R}^3 \to M$ through which every $C^1$ curve lifts from every initial point is a covering map. In particular, if $M$ is compact and Hausdorff and $g$ has nonpositive sectional curvature, then $\exp_p$ is a covering map for every $p \in M$.
--
--   6. **Auxiliary objects.** The radius $\sqrt{g_p(v, v) + 1}$; the loop based at $\gamma(0)$ given by a continuous curve with $\gamma(1) = \gamma(0)$ restricted to $[0, 1]$; the point $z_0 = \tfrac98 i \in \mathbb{H}$, whose image in the cusped surface $\Sigma = \mathbb{H}/\Gamma$ has height $< \log 8$; and, for $z$ with $h(\pi(z)) < \log 8$, the circle-fibre curve $t \mapsto (\pi(z),\ 6t \bmod 6)$ in the piece $\Sigma_8 \times \mathbb{R}/6\mathbb{Z}$, which runs once around the fibre as $t$ goes from $0$ to $1$.
--
--   The covering property of $\exp_p$ identifies $\mathbb{R}^3$ with the universal cover of a nonpositively curved compact $M$; this is the first step of the argument that the glued manifold carries no metric of nonpositive curvature.
--
--   **Formalization Note** Solutions of the lifting equation live in the subtype `State f γ` of $\mathbb{R} \times E$; the predicate `Holds` asks for a derivative `(1, v)` at the given time, and `equation f γ hf` packages it as a `FlowContinuation.Equation`. Curves are $C^1$ (`ContMDiff 𝓘(ℝ,ℝ) I3 1`), paths are parametrised by the unit interval, and covering maps are Mathlib's `IsCoveringMap`/`IsEvenlyCovered`. The private `ite_eq_left` and `dite_eq_left` are plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Continuation.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Continuation.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

/-!
# Geodesic continuation and the covering exponential map.
-/

section
open Set Filter Topology
namespace ThreeManifold.FlowContinuation.Equation
variable {X : Type*} (P : Equation X)

theorem exists_global_of_finite_time_extensions {x : X}
    (hstart : ∃ ε > (0:ℝ), ∃ z, z 0 = x ∧ P.CurveOn z (Ioo (-ε) ε))
    (hext : ∀ A > (0:ℝ), ∃ δ > (0:ℝ), ∀ z a, 0 < a → a ≤ A → z 0 = x →
      P.CurveOn z (Ioo (-a) a) → ∀ t ∈ Ioo (-a) a,
      ∃ w, w 0 = z t ∧ P.CurveOn w (Ioo (-δ) δ)) :
    ∃ z, z 0 = x ∧ ∀ t, P.Holds z t := by
  classical
  let S := {a : ℝ | ∃ z, z 0 = x ∧ P.CurveOn z (Ioo (-a) a)}
  obtain ⟨ε,hε,z,hz0,hz⟩ := hstart
  have hεS : ε ∈ S := ⟨z,hz0,hz⟩
  apply P.global_of_arbitrarily_long
  suffices hnb : ¬ BddAbove S by
    intro a
    obtain ⟨b,hb,hab⟩ := not_bddAbove_iff.mp hnb a
    obtain ⟨z,hz0,hz⟩ := hb
    exact ⟨z,hz0,hz.mono P (Ioo_subset_Ioo (neg_le_neg hab.le) hab.le)⟩
  intro hbdd
  let A := sSup S
  have hεA : ε ≤ A := le_csSup hbdd hεS
  obtain ⟨δ,hδ,hloc⟩ := hext A (lt_of_lt_of_le hε hεA)
  let ε := min δ (A/2)
  have hε : 0 < ε := lt_min hδ (half_pos (lt_of_lt_of_le hε hεA))
  have hεA : ε ≤ A := (min_le_right _ _).trans (by linarith)
  obtain ⟨a,⟨z,hz0,hz⟩,ha⟩ := Real.add_neg_lt_sSup (⟨_,hεS⟩ : S.Nonempty)
    (ε := -(ε/2)) (by linarith)
  change A + -(ε/2) < a at ha
  have ha0 : 0 < a := by linarith
  have hleft : -(A-ε/2) ∈ Ioo (-a) a := ⟨by linarith,by linarith⟩
  have hright : A-ε/2 ∈ Ioo (-a) a := ⟨by linarith,by linarith⟩
  have haA : a ≤ A := le_csSup hbdd ⟨z,hz0,hz⟩
  obtain ⟨z1,h10,h1'⟩ := hloc z a ha0 haA hz0 hz (-(A-ε/2)) hleft
  obtain ⟨z2,h20,h2'⟩ := hloc z a ha0 haA hz0 hz (A-ε/2) hright
  have h1 := h1'.mono P (Ioo_subset_Ioo (neg_le_neg (min_le_left δ (A/2))) (min_le_left δ (A/2)))
  have h2 := h2'.mono P (Ioo_subset_Ioo (neg_le_neg (min_le_left δ (A/2))) (min_le_left δ (A/2)))
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

theorem exists_global_of_compact_bounds [TopologicalSpace X] {x : X}
    (hloc : ∀ y : X, ∃ U ∈ 𝓝 y, ∃ ε > (0:ℝ), ∀ w ∈ U,
      ∃ z, z 0 = w ∧ P.CurveOn z (Ioo (-ε) ε))
    (hbounds : ∀ A > (0:ℝ), ∃ K : Set X, IsCompact K ∧ ∀ z a,
      0 < a → a ≤ A → z 0 = x → P.CurveOn z (Ioo (-a) a) →
      MapsTo z (Ioo (-a) a) K) :
    ∃ z, z 0 = x ∧ ∀ t, P.Holds z t := by
  classical
  apply P.exists_global_of_finite_time_extensions
  · obtain ⟨U,hU,ε,hε,hsol⟩ := hloc x
    obtain ⟨z,hz0,hz⟩ := hsol x (mem_of_mem_nhds hU)
    exact ⟨ε,hε,z,hz0,hz⟩
  · intro A hA
    obtain ⟨K,hK,hbound⟩ := hbounds A hA
    choose U hUn ε hε hsol using hloc
    obtain ⟨T,hcover⟩ := hK.elim_nhds_subcover' (fun i _ => U i) (fun i _ => hUn i)
    let V := insert (1:ℝ) (T.image (fun i : K => ε i))
    have hV : V.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
    let δ := V.min' hV
    have hδ : 0 < δ := by
      apply (Finset.lt_min'_iff V hV).mpr
      intro r hr
      rcases Finset.mem_insert.mp hr with hr | hr
      · rw [hr]; norm_num
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
        exact hε i
    refine ⟨δ,hδ,fun z a ha haA hz0 hz t ht => ?_⟩
    obtain ⟨i,hi,hti⟩ := mem_iUnion₂.mp (hcover (hbound z a ha haA hz0 hz ht))
    obtain ⟨w,hw0,hw⟩ := hsol i (z t) hti
    have hδε : (δ:ℝ) ≤ ε i := by
      apply Finset.min'_le V (ε i)
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
    exact ⟨w,hw0,hw.mono P (Ioo_subset_Ioo (neg_le_neg hδε) hδε)⟩
end ThreeManifold.FlowContinuation.Equation

namespace ThreeManifold.PathContinuation
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace Y]
variable (f : E → Y) (γ : ℝ → Y)
abbrev State := {p : ℝ × E // f p.2 = γ p.1}

def Holds (z : ℝ → State f γ) (t : ℝ) : Prop :=
  ∃ v : E, HasDerivAt (fun r => (z r).val) (1,v) t

lemma holds_shift (z : ℝ → State f γ) (a t : ℝ) :
    Holds f γ (fun r => z (r+a)) t ↔ Holds f γ z (t+a) := by
  let _ : TopologicalSpace Y := inferInstance
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v,?_⟩
    have hv' : HasDerivAt (fun r => (z (r+a)).val) (1,v) ((t+a)+(-a)) := by simpa using hv
    have h := hv'.comp_add_const (t+a) (-a)
    simpa using h
  · rintro ⟨v,hv⟩
    exact ⟨v,hv.comp_add_const t a⟩

lemma holds_time_derivative {z : ℝ → State f γ} {t : ℝ} (h : Holds f γ z t) :
    HasDerivAt (fun r => (z r).val.1) 1 t := by
  let _ : TopologicalSpace Y := inferInstance
  exact h.choose_spec.fst

lemma holds_space_derivative {z : ℝ → State f γ} {t : ℝ} (h : Holds f γ z t) :
    DifferentiableAt ℝ (fun r => (z r).val.2) t := by
  let _ : TopologicalSpace Y := inferInstance
  have hd : HasDerivAt (fun r => (z r).val.2) h.choose t := h.choose_spec.snd
  exact hd.differentiableAt

lemma holds_unique (hf : IsLocalHomeomorph f) {z w : ℝ → State f γ} {a b t : ℝ}
    (hz : ∀ r ∈ Ioo a b, Holds f γ z r) (hw : ∀ r ∈ Ioo a b, Holds f γ w r)
    (ht : t ∈ Ioo a b) (he : z t = w t) : EqOn z w (Ioo a b) := by
  have htime : EqOn (fun r => (z r).val.1) (fun r => (w r).val.1) (Ioo a b) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo a b).isPreconnected
      (fun r hr => (holds_time_derivative f γ (hz r hr)).differentiableAt.differentiableWithinAt)
      (fun r hr => (holds_time_derivative f γ (hw r hr)).differentiableAt.differentiableWithinAt)
      (fun r hr => ?_) ht (congrArg (fun q => q.val.1) he)
    rw [(holds_time_derivative f γ (hz r hr)).deriv,(holds_time_derivative f γ (hw r hr)).deriv]
  have hspace : EqOn (fun r => (z r).val.2) (fun r => (w r).val.2) (Ioo a b) := by
    apply (T2Space.isSeparatedMap f).eqOn_of_comp_eqOn hf.isLocallyInjective
      (convex_Ioo a b).isPreconnected
      (fun r hr => (holds_space_derivative f γ (hz r hr)).continuousAt.continuousWithinAt)
      (fun r hr => (holds_space_derivative f γ (hw r hr)).continuousAt.continuousWithinAt)
      (fun r hr => ?_) ht (congrArg (fun q => q.val.2) he)
    exact (z r).property.trans ((congrArg γ (htime hr)).trans (w r).property.symm)
  intro r hr
  exact Subtype.ext (Prod.ext (htime hr) (hspace hr))

def equation (hf : IsLocalHomeomorph f) : FlowContinuation.Equation (State f γ) where
  Holds := Holds f γ
  germ := by
    intro z w t he hz
    obtain ⟨v,hv⟩ := hz
    exact ⟨v,hv.congr_of_eventuallyEq (he.mono (fun r hr => congrArg Subtype.val hr.symm))⟩
  shift := holds_shift f γ
  unique := holds_unique f γ hf

lemma time_affine (hf : IsLocalHomeomorph f) {z : ℝ → State f γ} {a : ℝ}
    (ha : 0 < a) (hz : (equation f γ hf).CurveOn z (Ioo (-a) a)) :
    EqOn (fun t => (z t).val.1) (fun t => t+(z 0).val.1) (Ioo (-a) a) := by
  apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-a) a).isPreconnected
    (fun t ht => (holds_time_derivative f γ (hz t ht)).differentiableAt.differentiableWithinAt)
    (differentiable_id.add_const _).differentiableOn (fun t ht => ?_)
    ⟨neg_lt_zero.mpr ha,ha⟩ (by simp)
  rw [(holds_time_derivative f γ (hz t ht)).deriv]
  simp
end ThreeManifold.PathContinuation
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma localInverseAt_contMDiffAt {f : E3 → M}
    (hf : ContMDiff 𝓘(ℝ,E3) I3 1 f)
    (hi : ∀ a, Function.Injective (mfderiv 𝓘(ℝ,E3) I3 f a))
    (hl : IsLocalHomeomorph f) (a : E3) :
    ContMDiffAt I3 𝓘(ℝ,E3) 1 (hl.localInverseAt a) (f a) := by
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
  have hFd : HasFDerivAt F (L : E3 →L[ℝ] E3) a :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  let e := hF.toOpenPartialHomeomorph F hFd (by simp)
  have hea : a ∈ e.source := hF.mem_toOpenPartialHomeomorph_source hFd (by simp)
  have hei : ContDiffAt ℝ 1 e.symm (F a) := hF.to_localInverse hFd (by simp)
  have hj : ContMDiffAt I3 𝓘(ℝ,E3) 1 (fun y => e.symm (c y)) (f a) :=
    hei.contMDiffAt.comp (f a) hC
  let i := hl.localInverseAt a
  have hic : ContinuousAt i (f a) := i.continuousAt hl.apply_self_mem_localInverseAt_source
  have hie : i (f a) = a := hl.localInverseAt_apply_self
  have heq : (fun y => e.symm (c y)) =ᶠ[𝓝 (f a)] i := by
    filter_upwards [i.open_source.mem_nhds hl.apply_self_mem_localInverseAt_source,
      hic.preimage_mem_nhds (hie ▸ e.open_source.mem_nhds hea)] with y hy hyi
    have hh : f (i y) = y := hl.apply_localInverseAt_of_mem hy
    calc e.symm (c y) = e.symm (c (f (i y))) := congrArg (fun q => e.symm (c q)) hh.symm
      _ = i y := e.left_inv hyi
  exact hj.congr_of_eventuallyEq heq.symm

lemma localInverseAt_contMDiffOn {f : E3 → M}
    (hf : ContMDiff 𝓘(ℝ,E3) I3 1 f)
    (hi : ∀ a, Function.Injective (mfderiv 𝓘(ℝ,E3) I3 f a))
    (hl : IsLocalHomeomorph f) (a : E3) :
    ContMDiffOn I3 𝓘(ℝ,E3) 1 (hl.localInverseAt a) (hl.localInverseAt a).source := by
  intro y hy
  let i := hl.localInverseAt a
  let j := hl.localInverseAt (i y)
  have hfy : f (i y) = y := hl.apply_localInverseAt_of_mem hy
  have hj := localInverseAt_contMDiffAt hf hi hl (i y)
  rw [hfy] at hj
  have hji : j y = i y := by
    calc j y = j (f (i y)) := congrArg j hfy.symm
      _ = i y := hl.localInverseAt_apply_self
  have hyj : y ∈ j.source := hfy ▸ hl.apply_self_mem_localInverseAt_source
  have heq : i =ᶠ[𝓝 y] j := by
    filter_upwards [i.open_source.mem_nhds hy, j.open_source.mem_nhds hyj,
      hj.continuousAt.preimage_mem_nhds (hji ▸ i.open_target.mem_nhds (i.map_source hy))]
      with z hzi hzj hzt
    exact hl.injOn_localInverseAt_target (i.map_source hzi) hzt
      ((hl.apply_localInverseAt_of_mem hzi).trans (hl.apply_localInverseAt_of_mem hzj).symm)
  exact (hj.congr_of_eventuallyEq heq).contMDiffWithinAt
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable {f : E3 → M} {γ : ℝ → M}
open RiemannianCoordinates

theorem local_lift_exists
    (hf : ContMDiff 𝓘(ℝ,E3) I3 1 f)
    (hi : ∀ a, Function.Injective (mfderiv 𝓘(ℝ,E3) I3 f a))
    (hl : IsLocalHomeomorph f) (hγ : ContMDiff 𝓘(ℝ,ℝ) I3 1 γ)
    (x : State f γ) :
    ∃ U ∈ 𝓝 x, ∃ ε > (0:ℝ), ∀ y ∈ U,
      ∃ z, z 0 = y ∧ (equation f γ hl).CurveOn z (Ioo (-ε) ε) := by
  classical
  let i := hl.localInverseAt x.val.2
  have hxg : γ x.val.1 ∈ i.source := x.property ▸ hl.apply_self_mem_localInverseAt_source
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    (hγ.continuous.continuousAt.preimage_mem_nhds (i.open_source.mem_nhds hxg))
  let ε := δ/3
  have hε : 0 < ε := by dsimp [ε]; positivity
  let U : Set (State f γ) := {y | y.val.1 ∈ Metric.ball x.val.1 ε ∧ y.val.2 ∈ i.target}
  have hU : IsOpen U :=
    (Metric.isOpen_ball.preimage (continuous_fst.comp continuous_subtype_val)).inter
      (i.open_target.preimage (continuous_snd.comp continuous_subtype_val))
  have hxU : x ∈ U := ⟨Metric.mem_ball_self hε,hl.self_mem_localInverseAt_target⟩
  refine ⟨U,hU.mem_nhds hxU,ε,hε,fun y hy => ?_⟩
  have hmap : ∀ t ∈ Ioo (-ε) ε, γ (y.val.1+t) ∈ i.source := by
    intro t ht
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    have hys : |y.val.1-x.val.1| < ε := by simpa only [Metric.mem_ball,Real.dist_eq] using hy.1
    have hts : |t| < ε := abs_lt.mpr ht
    calc |y.val.1+t-x.val.1| = |(y.val.1-x.val.1)+t| := by congr 1; ring
      _ ≤ |y.val.1-x.val.1|+|t| := abs_add_le _ _
      _ < ε+ε := add_lt_add hys hts
      _ < δ := by dsimp [ε]; linarith
  let z : ℝ → State f γ := fun t => if ht : t ∈ Ioo (-ε) ε then
    ⟨(y.val.1+t,i (γ (y.val.1+t))),hl.apply_localInverseAt_of_mem (hmap t ht)⟩ else y
  have heq {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
      (fun r => (z r).val) =ᶠ[𝓝 t] fun r => (y.val.1+r,i (γ (y.val.1+r))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    simp only [z,dite_eq_left hr]
  have hz0 : z 0 = y := by
    apply Subtype.ext
    rw [(heq ⟨neg_lt_zero.mpr hε,hε⟩).eq_of_nhds]
    apply Prod.ext
    · simp
    · simp only [add_zero]
      rw [← y.property,← congrFun (hl.localInverseAt_symm x.val.2) y.val.2]
      exact i.right_inv hy.2
  refine ⟨z,hz0,fun t ht => ?_⟩
  have his := (localInverseAt_contMDiffOn hf hi hl x.val.2).contMDiffAt
    (i.open_source.mem_nhds (hmap t ht))
  have hshift : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) 1 (fun r => y.val.1+r) t :=
    (contDiff_const.add contDiff_id).contMDiff.contMDiffAt
  have hs : ContDiffAt ℝ 1 (fun r => i (γ (y.val.1+r))) t :=
    contMDiffAt_iff_contDiffAt.mp (his.comp t (hγ.contMDiffAt.comp t hshift))
  refine ⟨deriv (fun r => i (γ (y.val.1+r))) t,?_⟩
  have hd := ((hasDerivAt_id t).const_add y.val.1).prodMk
    (hs.differentiableAt (by simp)).hasDerivAt
  exact hd.congr_of_eventuallyEq (heq ht)
end ThreeManifold.PathContinuation
end

section
open Set Filter Topology
namespace ThreeManifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]

theorem positive_bilinear_norm_bound (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v ≠ 0, 0 < B v v) :
    ∃ C > (0:ℝ), ∀ v, ‖v‖^2 ≤ C * B v v := by
  have hc : Continuous (fun v => B v v) := B.continuous.clm_apply continuous_id
  obtain ⟨u,hu,hmin⟩ := (isCompact_sphere (0:E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1)) hc.continuousOn
  have hun : ‖u‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hu
  have hu0 : u ≠ 0 := by intro he; simp [he] at hun
  have hp : 0 < B u u := hB u hu0
  refine ⟨(B u u)⁻¹,inv_pos.mpr hp,fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hn0 : ‖v‖ ≠ 0 := ne_of_gt hn
  have hvu : ‖v‖⁻¹ • v ∈ Metric.sphere (0:E) 1 := by
    simp [norm_smul,hn0]
  have h := hmin hvu
  change B u u ≤ B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) at h
  simp only [map_smul,_root_.smul_apply,smul_eq_mul] at h
  have h' : B u u * ‖v‖^2 ≤ B v v := by
    calc
      B u u * ‖v‖^2 ≤ (‖v‖⁻¹ * (‖v‖⁻¹ * B v v)) * ‖v‖^2 :=
        mul_le_mul_of_nonneg_right h (sq_nonneg _)
      _ = B v v := by field_simp
  calc
    ‖v‖^2 = (B u u)⁻¹ * (B u u * ‖v‖^2) := by field_simp
    _ ≤ (B u u)⁻¹ * B v v := mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hp.le)
end ThreeManifold
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.PathContinuation
open RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable {f : E3 → M} {γ : ℝ → M}

lemma lift_derivative_eq (hf : ContMDiff 𝓘(ℝ,E3) I3 1 f)
    (hγ : ContMDiff 𝓘(ℝ,ℝ) I3 1 γ) {z : ℝ → State f γ} {t : ℝ}
    (hz : Holds f γ z t) :
    mfderiv 𝓘(ℝ,E3) I3 f (z t).val.2 (deriv (fun r => (z r).val.2) t) =
      velocity γ (z t).val.1 := by
  let _ : IsManifold I3 ∞ M := inferInstance
  obtain ⟨b,hb⟩ := hz
  have h1 : HasDerivAt (fun r => (z r).val.1) 1 t := hb.fst
  have h2 : HasDerivAt (fun r => (z r).val.2) b t := hb.snd
  have hcomp : (f ∘ fun r => (z r).val.2) = (γ ∘ fun r => (z r).val.1) :=
    funext (fun r => (z r).property)
  have he := congrArg (fun L : ℝ →L[ℝ] E3 => L 1)
    (congrArg (fun F : ℝ → M => mfderiv 𝓘(ℝ,ℝ) I3 F t) hcomp)
  rw [mfderiv_comp t (hf.contMDiffAt.mdifferentiableAt (by simp)) h2.differentiableAt.mdifferentiableAt,
    mfderiv_comp t (hγ.contMDiffAt.mdifferentiableAt (by simp)) h1.differentiableAt.mdifferentiableAt] at he
  simp only [mfderiv_eq_fderiv] at he
  change mfderiv 𝓘(ℝ,E3) I3 f (z t).val.2 (deriv (fun r => (z r).val.2) t) =
    mfderiv 𝓘(ℝ,ℝ) I3 γ (z t).val.1 (deriv (fun r => (z r).val.1) t) at he
  exact he.trans (congrArg (fun w : ℝ => mfderiv 𝓘(ℝ,ℝ) I3 γ (z t).val.1 w) h1.deriv)

lemma continuous_phaseLift_C1 (hγ : ContMDiff 𝓘(ℝ,ℝ) I3 1 γ) :
    Continuous (phaseLift γ) := by
  have h := hγ.continuous_tangentMap (by simp)
  have hc : Continuous (fun t : ℝ => (⟨t,1⟩ : TangentBundle 𝓘(ℝ,ℝ) ℝ)) := by
    exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ,ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  exact h.comp hc

variable [CompactSpace M] [T2Space M]

theorem exponential_lift_compact_bounds (g : SmoothMetric M)
    (hn : NonpositiveSectionalCurvature g) (p : M)
    (hγ : ContMDiff 𝓘(ℝ,ℝ) I3 1 γ) (x : State (exponential g p) γ)
    (A : ℝ) (_hA : 0 < A) :
    ∃ K : Set (State (exponential g p) γ), IsCompact K ∧ ∀ z a,
      0 < a → a ≤ A → z 0 = x →
      (equation (exponential g p) γ (npc_exponential_isLocalHomeomorph g hn p)).CurveOn z (Ioo (-a) a) →
      MapsTo z (Ioo (-a) a) K := by
  classical
  let f := exponential g p
  have hf := exponential_contMDiff g p
  let hl := npc_exponential_isLocalHomeomorph g hn p
  obtain ⟨C,hC,hCb⟩ := positive_bilinear_norm_bound (E := E3)
    (show E3 →L[ℝ] E3 →L[ℝ] ℝ from g.inner p) (fun v hv => g.pos p v hv)
  have hec : Continuous (fun s => g.inner (γ s) (velocity γ s) (velocity γ s)) :=
    (continuous_phaseEnergy g).comp (continuous_phaseLift_C1 hγ)
  obtain ⟨D,hD⟩ := ((isCompact_Icc : IsCompact (Icc (x.val.1-A) (x.val.1+A))).image hec).bddAbove
  let R := Real.sqrt (C * max D 0)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  let K0 := Icc (x.val.1-A) (x.val.1+A) ×ˢ Metric.closedBall x.val.2 (R*A)
  let K : Set (State f γ) := Subtype.val ⁻¹' K0
  have hclosed : IsClosed {q : ℝ × E3 | f q.2 = γ q.1} :=
    isClosed_eq (hf.continuous.comp continuous_snd) (hγ.continuous.comp continuous_fst)
  have hK : IsCompact K := by
    apply hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    exact isCompact_Icc.prod (isCompact_closedBall _ _)
  refine ⟨K,hK,fun z a ha haA hz0 hz t ht => ?_⟩
  have htime := time_affine f γ hl ha hz
  have htime' : ∀ s ∈ Ioo (-a) a, (z s).val.1 = s+x.val.1 := by
    intro s hs; simpa only [hz0] using htime hs
  have hst : ∀ s ∈ Ioo (-a) a, (z s).val.1 ∈ Icc (x.val.1-A) (x.val.1+A) := by
    intro s hs
    rw [htime' s hs]
    constructor <;> linarith [hs.1,hs.2]
  have hdb : ∀ s ∈ Ioo (-a) a, ‖deriv (fun r => (z r).val.2) s‖ ≤ R := by
    intro s hs
    let b := deriv (fun r => (z r).val.2) s
    have hde : (show E3 →L[ℝ] E3 from mfderiv 𝓘(ℝ,E3) I3 f (z s).val.2) b =
        (show E3 from velocity γ (z s).val.1) := lift_derivative_eq hf hγ (hz s hs)
    have h := npc_exponential_differential_expanding g hn p (z s).val.2 b
    change (show E3 →L[ℝ] E3 →L[ℝ] ℝ from g.inner p) b b ≤
      (show E3 →L[ℝ] E3 →L[ℝ] ℝ from g.inner (f (z s).val.2))
        ((show E3 →L[ℝ] E3 from mfderiv 𝓘(ℝ,E3) I3 f (z s).val.2) b)
        ((show E3 →L[ℝ] E3 from mfderiv 𝓘(ℝ,E3) I3 f (z s).val.2) b) at h
    rw [hde] at h
    have hbase := congrArg (fun q : M =>
      (show E3 →L[ℝ] E3 →L[ℝ] ℝ from g.inner q)
        (show E3 from velocity γ (z s).val.1) (show E3 from velocity γ (z s).val.1))
      (z s).property
    have h' := h.trans_eq hbase
    have hD' : g.inner (γ (z s).val.1) (velocity γ (z s).val.1) (velocity γ (z s).val.1) ≤ D :=
      hD (mem_image_of_mem _ (hst s hs))
    have hb : ‖b‖^2 ≤ C * max D 0 :=
      (hCb b).trans (mul_le_mul_of_nonneg_left (h'.trans (hD'.trans (le_max_left _ _))) hC.le)
    exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg hC.le (le_max_right _ _))).mpr hb
  change (z t).val.1 ∈ _ ∧ (z t).val.2 ∈ _
  refine ⟨hst t ht,?_⟩
  rw [Metric.mem_closedBall,dist_eq_norm]
  have hder : ∀ s ∈ Ioo (-a) a, DifferentiableAt ℝ (fun r => (z r).val.2) s :=
    fun s hs => holds_space_derivative f γ (hz s hs)
  have hnorm := Convex.norm_image_sub_le_of_norm_deriv_le hder hdb (convex_Ioo (-a) a)
    (show (0:ℝ) ∈ Ioo (-a) a from ⟨by linarith,ha⟩) ht
  simp only [hz0,sub_zero,Real.norm_eq_abs] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left (le_trans (abs_le.mpr ⟨ht.1.le,ht.2.le⟩) haA) hR)
end ThreeManifold.PathContinuation

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

def regularRadius (g : SmoothMetric M) (p : M) (v : E3) : ℝ :=
  Real.sqrt (g.inner p v v + 1)

variable [CompactSpace M] [T2Space M]
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.PathContinuation
open RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M] {γ : ℝ → M}

end ThreeManifold.PathContinuation

namespace ThreeManifold.RiemannianCoordinates
open PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma contDiff_lift_of_localHomeomorph {f : E3 → M} {γ : ℝ → M} {v : ℝ → E3}
    (hf : ContMDiff 𝓘(ℝ,E3) I3 1 f)
    (hi : ∀ a, Function.Injective (mfderiv 𝓘(ℝ,E3) I3 f a))
    (hl : IsLocalHomeomorph f) (hγ : ContMDiff 𝓘(ℝ,ℝ) I3 1 γ)
    (hv : Continuous v) (he : ∀ t, f (v t) = γ t) : ContDiff ℝ 1 v := by
  rw [contDiff_iff_contDiffAt]
  intro t
  let i := hl.localInverseAt (v t)
  have hev : v =ᶠ[𝓝 t] i ∘ γ := by
    filter_upwards [hv.continuousAt.preimage_mem_nhds
      (i.open_target.mem_nhds hl.self_mem_localInverseAt_target)] with s hs
    rw [Function.comp_apply,← he s]
    simpa only [i,hl.localInverseAt_symm] using (i.right_inv hs).symm
  apply ContDiffAt.congr_of_eventuallyEq _ hev
  apply contMDiffAt_iff_contDiffAt.mp
  have h := localInverseAt_contMDiffAt hf hi hl (v t)
  rw [he t] at h
  exact h.comp t hγ.contMDiffAt

variable [CompactSpace M] [T2Space M]

theorem npc_exponential_path_lift (g : SmoothMetric M)
    (hn : NonpositiveSectionalCurvature g) (p : M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ,ℝ) I3 1 γ)
    (v0 : E3) (hv0 : exponential g p v0 = γ 0) :
    ∃ v : ℝ → E3, ContDiff ℝ 1 v ∧ v 0 = v0 ∧ ∀ t, exponential g p (v t) = γ t := by
  let f := exponential g p
  have hf := exponential_contMDiff g p
  have hncp := npc_noConjugatePoints g hn
  have hi := exponential_mfderiv_injective g hncp p
  let hl := npc_exponential_isLocalHomeomorph g hn p
  let x : State f γ := ⟨(0,v0),hv0⟩
  obtain ⟨z,hz0,hz⟩ := (equation f γ hl).exists_global_of_compact_bounds
    (fun y => local_lift_exists hf hi hl hγ y)
    (fun A hA => exponential_lift_compact_bounds g hn p hγ x A hA)
  have htime : ∀ t, (z t).val.1 = t := by
    have h := isOpen_univ.eqOn_of_deriv_eq (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected
      (fun t _ => (holds_time_derivative f γ (hz t)).differentiableAt.differentiableWithinAt)
      differentiable_id.differentiableOn
      (fun t _ => by rw [(holds_time_derivative f γ (hz t)).deriv]; simp)
      (mem_univ 0) (show (z 0).val.1 = (id 0 : ℝ) by rw [hz0]; rfl)
    exact fun t => h (mem_univ t)
  let v : ℝ → E3 := fun t => (z t).val.2
  have hvc : Continuous v := continuous_iff_continuousAt.mpr
    (fun t => (holds_space_derivative f γ (hz t)).continuousAt)
  have he : ∀ t, f (v t) = γ t := fun t => (z t).property.trans (congrArg γ (htime t))
  exact ⟨v,contDiff_lift_of_localHomeomorph hf hi hl hγ hvc he,
    show v 0 = v0 by change (z 0).val.2 = v0; rw [hz0],he⟩
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology unitInterval
namespace ThreeManifold
variable {E X : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
variable {p : E → X}

lemma localHomeomorph_discrete_fiber (hp : IsLocalHomeomorph p) (x : X) :
    DiscreteTopology (p ⁻¹' {x}) := by
  let _ : T2Space E := inferInstance
  let : Subsingleton (p '' (p ⁻¹' {x})) := ⟨by
    rintro ⟨a,⟨a',ha',rfl⟩⟩ ⟨b,⟨b',hb',rfl⟩⟩
    apply Subtype.ext
    exact ha'.trans hb'.symm⟩
  exact hp.isLocalHomeomorphOn.discreteTopology_of_image

theorem evenlyCovered_of_radial_lifts (hp : IsLocalHomeomorph p)
    {x : X} {U : Set X} (hx : x ∈ U) (hU : IsOpen U)
    (H : C(I × U,X)) (h0 : ∀ b, H (0,b) = x) (h1 : ∀ b, H (1,b) = b.val)
    (hforward : ∀ (b : U) (a : p ⁻¹' {x}),
      ∃ v : C(I,E), v 0 = a.val ∧ ∀ t, p (v t) = H (t,b))
    (hbackward : ∀ (z : p ⁻¹' U),
      ∃ v : C(I,E), v 1 = z.val ∧ ∀ t, p (v t) = H (t,⟨p z.val,z.property⟩)) :
    IsEvenlyCovered p x (p ⁻¹' {x}) := by
  classical
  let F := p ⁻¹' {x}
  let Z := p ⁻¹' U
  let : DiscreteTopology F := localHomeomorph_discrete_fiber hp x
  choose L hL0 hL using hforward
  choose R hR1 hR using hbackward
  have hLc : Continuous (fun q : I × (U × F) => L q.2.1 q.2.2 q.1) := by
    let f : C(I × (U × F),X) :=
      ⟨fun q => H (q.1,q.2.1),H.continuous.comp (continuous_fst.prodMk continuous_snd.fst)⟩
    apply hp.continuous_lift (T2Space.isSeparatedMap p) f
      (g := fun q : I × (U × F) => L q.2.1 q.2.2 q.1)
      (funext (fun q => hL q.2.1 q.2.2 q.1))
    · simpa only [Function.comp_def,hL0] using (continuous_subtype_val.comp continuous_snd :
        Continuous (fun q : U × F => q.2.val))
    · intro q
      exact (L q.1 q.2).continuous
  have hRc : Continuous (fun q : I × Z => R q.2 (unitInterval.symm q.1)) := by
    let f : C(I × Z,X) :=
      ⟨fun q => H (unitInterval.symm q.1,⟨p q.2.val,q.2.property⟩),
        H.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        ((hp.continuous.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _))⟩
    apply hp.continuous_lift (T2Space.isSeparatedMap p) f
      (g := fun q : I × Z => R q.2 (unitInterval.symm q.1))
      (funext (fun q => hR q.2 (unitInterval.symm q.1)))
    · simpa only [unitInterval.symm_zero,hR1] using (continuous_subtype_val : Continuous (fun z : Z => z.val))
    · intro z
      exact (R z).continuous.comp unitInterval.continuous_symm
  let forward : U × F → Z := fun q => ⟨L q.1 q.2 1,by change p (L q.1 q.2 1) ∈ U; rw [hL,h1]; exact q.1.property⟩
  let backward : Z → U × F := fun z =>
    (⟨p z.val,z.property⟩,⟨R z 0,by change p (R z 0) = x; rw [hR,h0]⟩)
  have hfc : Continuous forward :=
    (hLc.comp (continuous_const.prodMk continuous_id)).subtype_mk _
  have hbc : Continuous backward := by
    apply Continuous.prodMk
    · exact (hp.continuous.comp continuous_subtype_val).subtype_mk _
    · apply Continuous.subtype_mk
      simpa only [Function.comp_def,id_eq,unitInterval.symm_one] using hRc.comp ((continuous_const : Continuous (fun _ : Z => (1 : I))).prodMk continuous_id)
  have hleft : Function.LeftInverse backward forward := by
    rintro ⟨b,a⟩
    have hf : p (forward (b,a)).val = b.val := (hL b a 1).trans (h1 b)
    have hb : (⟨p (forward (b,a)).val,(forward (b,a)).property⟩ : U) = b := Subtype.ext hf
    have he : R (forward (b,a)) = L b a := by
      apply ContinuousMap.coe_injective
      apply (T2Space.isSeparatedMap p).eq_of_comp_eq hp.isLocallyInjective
        (R (forward (b,a))).continuous (L b a).continuous
        (funext (fun t => (hR (forward (b,a)) t).trans (by rw [hb]; exact (hL b a t).symm)))
        1
      exact hR1 (forward (b,a))
    apply Prod.ext hb
    apply Subtype.ext
    change R (forward (b,a)) 0 = a.val
    rw [he,hL0]
  have hright : Function.RightInverse backward forward := by
    intro z
    have he : L (backward z).1 (backward z).2 = R z := by
      apply ContinuousMap.coe_injective
      apply (T2Space.isSeparatedMap p).eq_of_comp_eq hp.isLocallyInjective
        (L (backward z).1 (backward z).2).continuous (R z).continuous
        (funext (fun t => (hL (backward z).1 (backward z).2 t).trans (hR z t).symm)) 0
      exact hL0 (backward z).1 (backward z).2
    apply Subtype.ext
    change L (backward z).1 (backward z).2 1 = z.val
    rw [he,hR1]
  let e : (U × F) ≃ₜ Z :=
    { toFun := forward, invFun := backward, left_inv := hleft, right_inv := hright,
      continuous_toFun := hfc, continuous_invFun := hbc }
  exact ⟨inferInstance,U,hx,hU,hU.preimage hp.continuous,e.symm,fun _ => rfl⟩
end ThreeManifold
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
local notation "𝕀" => unitInterval
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma smooth_radial_neighborhood (x : M) :
    ∃ U : Set M, x ∈ U ∧ IsOpen U ∧ ∃ H : C(𝕀 × U,M),
      (∀ b, H (0,b) = x) ∧ (∀ b, H (1,b) = b.val) ∧
      ∀ b : U, ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ,ℝ) I3 1 γ ∧
        ∀ t : 𝕀, γ t = H (t,b) := by
  let c := chartAt E3 x
  have hcx : c x ∈ c.target := c.map_source (mem_chart_source E3 x)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp c.open_target (c x) hcx
  let U := c.source ∩ c ⁻¹' Metric.ball (c x) r
  have hU : IsOpen U := c.continuousOn_toFun.isOpen_inter_preimage c.open_source Metric.isOpen_ball
  have hx : x ∈ U := ⟨mem_chart_source E3 x,Metric.mem_ball_self hr⟩
  let A : ℝ → U → E3 := fun t b =>
    (1 - Real.smoothTransition t) • c x + Real.smoothTransition t • c b.val
  have hA : ∀ t b, A t b ∈ c.target := by
    intro t b
    exact hball ((convex_ball (c x) r)
      (Metric.mem_ball_self hr) b.property.2
      (sub_nonneg.mpr (Real.smoothTransition.le_one t))
      (Real.smoothTransition.nonneg t) (sub_add_cancel 1 _))
  have hcU : Continuous (fun b : U => c b.val) :=
    c.continuousOn_toFun.comp_continuous continuous_subtype_val (fun b => b.property.1)
  have hAc : Continuous (fun q : 𝕀 × U => A q.1 q.2) := by
    exact ((continuous_const.sub (Real.smoothTransition.continuous.comp
      (continuous_subtype_val.comp continuous_fst))).smul continuous_const).add
      ((Real.smoothTransition.continuous.comp (continuous_subtype_val.comp continuous_fst)).smul
        (hcU.comp continuous_snd))
  let H : C(𝕀 × U,M) := ⟨fun q => c.symm (A q.1 q.2),
    c.continuousOn_invFun.comp_continuous hAc (fun q => hA q.1 q.2)⟩
  refine ⟨U,hx,hU,H,?_,?_,?_⟩
  · intro b
    change c.symm (A 0 b) = x
    simpa [A] using c.left_inv (mem_chart_source E3 x)
  · intro b
    change c.symm (A 1 b) = b.val
    simpa [A] using c.left_inv b.property.1
  · intro b
    refine ⟨fun t => c.symm (A t b),?_,fun _ => rfl⟩
    intro t
    have ha : ContDiff ℝ 1 (fun t => A t b) :=
      ((contDiff_const.sub Real.smoothTransition.contDiff).smul contDiff_const).add
        (Real.smoothTransition.contDiff.smul contDiff_const)
    have hc : ContMDiffAt I3 I3 1 c.symm (A t b) :=
      (contMDiffOn_chart_symm (I := I3) (n := 1)).contMDiffAt
        (c.open_target.mem_nhds (hA t b))
    exact hc.comp t (contMDiffAt_iff_contDiffAt.mpr ha.contDiffAt)

lemma covering_of_global_smooth_lifts {f : E3 → M} (hf : IsLocalHomeomorph f)
    (hlift : ∀ {γ : ℝ → M}, ContMDiff 𝓘(ℝ,ℝ) I3 1 γ →
      ∀ v0 : E3, f v0 = γ 0 → ∃ v : ℝ → E3,
        ContDiff ℝ 1 v ∧ v 0 = v0 ∧ ∀ t, f (v t) = γ t) : IsCoveringMap f := by
  intro x
  obtain ⟨U,hx,hU,H,h0,h1,hH⟩ := smooth_radial_neighborhood x
  apply ThreeManifold.evenlyCovered_of_radial_lifts hf hx hU H h0 h1
  · intro b a
    obtain ⟨γ,hγ,he⟩ := hH b
    obtain ⟨v,hv,hv0,hve⟩ := hlift hγ a.val
      (a.property.trans ((he 0).trans (h0 b)).symm)
    exact ⟨⟨fun t => v t,hv.continuous.comp continuous_subtype_val⟩,hv0,
      fun t => (hve t).trans (he t)⟩
  · intro z
    obtain ⟨γ,hγ,he⟩ := hH ⟨f z.val,z.property⟩
    have hrev : ContMDiff 𝓘(ℝ,ℝ) I3 1 (fun t : ℝ => γ (1-t)) :=
      hγ.comp (contMDiff_iff_contDiff.mpr (contDiff_const.sub contDiff_id))
    obtain ⟨v,hv,hv0,hve⟩ := hlift hrev z.val (by
      simpa using ((he 1).trans (h1 ⟨f z.val,z.property⟩)).symm)
    refine ⟨⟨fun t => v (1-t),hv.continuous.comp (continuous_const.sub continuous_subtype_val)⟩,?_,?_⟩
    · simpa using hv0
    · intro t
      change f (v (1-(t:ℝ))) = _
      exact (hve (1-t)).trans (by simp only [sub_sub_cancel]; exact he t)

variable [CompactSpace M] [T2Space M]

theorem npc_exponential_isCoveringMap (g : SmoothMetric M)
    (hn : NonpositiveSectionalCurvature g) (p : M) : IsCoveringMap (exponential g p) :=
  covering_of_global_smooth_lifts (npc_exponential_isLocalHomeomorph g hn p)
    (fun hγ v0 hv0 => npc_exponential_path_lift g hn p hγ v0 hv0)
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates

section
open PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]

end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

def closedCurvePath {γ : ℝ → M} (hc : Continuous γ) (he : γ 1 = γ 0) : Path (γ 0) (γ 0) where
  toFun t := γ t
  continuous_toFun := hc.comp continuous_subtype_val
  source' := rfl
  target' := he

end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
  {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates GluedConstruction HyperbolicCore
local instance instChartedSpaceE3UniversalPiece_2 : ChartedSpace E3 UniversalPiece := Rechart.charts Coordinates3.coordinates
local instance instIsManifoldRealE3I3SomeENatTopUniversalPiece_2 : IsManifold I3 ∞ UniversalPiece := Rechart.isManifold Coordinates3.coordinates
local instance instChartedSpaceE3WholePiece_4 : ChartedSpace E3 WholePiece := Rechart.charts Coordinates3.coordinates
local instance instIsManifoldRealE3I3SomeENatTopWholePiece_4 : IsManifold I3 ∞ WholePiece := Rechart.isManifold Coordinates3.coordinates
local instance instChartedSpaceE3Piece_2 : ChartedSpace E3 Piece := Rechart.charts Coordinates3.coordinates
local instance instIsManifoldRealE3I3SomeENatTopPiece_2 : IsManifold I3 ∞ Piece := Rechart.isManifold Coordinates3.coordinates
def lowPoint : ℍ := ⟨(9/8:ℂ)*Complex.I,by norm_num⟩
lemma lowPoint_core : height (projection lowPoint) < Real.log 8 := by
  rw [height_projection_high (by norm_num [lowPoint])]
  exact Real.log_lt_log (by norm_num [lowPoint]) (by norm_num [lowPoint])
def pieceFiber (z : ℍ) (hz : height (projection z) < Real.log 8) (t : ℝ) : Piece :=
  (⟨projection z,hz⟩,((6*t : ℝ) : GluedConstruction.Circle))
end ThreeManifold.CompactMetric

end

end OAI


