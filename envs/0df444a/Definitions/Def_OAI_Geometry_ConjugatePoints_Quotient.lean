-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
-- name    : OAI_Geometry_ConjugatePoints_Quotient
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:03:13.479152+00:00
-- url     : https://prove2.me/theorems/4f9d34b7-a2d5-47bf-a26b-d2cd32387111
-- title:
--   Smooth quotients by covering actions and the cusped hyperbolic surface $\mathbb{H}/\Gamma$ with its height function
-- statement:
--   This file sets up two pieces of infrastructure: a general recipe for putting a smooth manifold structure on the quotient of a manifold by a covering group action, and a concrete non-compact hyperbolic surface $\Sigma = \mathbb{H}/\Gamma$, where $\mathbb{H} = \{z \in \mathbb{C} : \operatorname{Im} z > 0\}$ is the upper half-plane and $\Gamma \le SL(2,\mathbb{Z})$ is an explicit finite-index subgroup acting by Möbius transformations $\begin{pmatrix} a & b \\ c & d\end{pmatrix} \cdot z = \frac{az+b}{cz+d}$. The surface is equipped with a continuous height function that splits it into a compact core and a single cusp.
--
--   Throughout, a *quotient covering map* for an action of a group $G$ on a space $X$ is a continuous surjective quotient map $p : X \to Y$ such that every $k \in G$ acts continuously, $p(x) = p(y)$ holds exactly when $x = k \cdot y$ for some $k \in G$, and every point has a neighbourhood $U$ with $kU \cap U = \emptyset$ for all $k \ne 1$.
--
--   1. **Product and pulled-back covering actions.** If $G$ acts on $X$ and $H$ acts on $Y$, then $G \times H$ acts on $X \times Y$ coordinatewise, $(g,h)\cdot(x,y) = (g x, h y)$. If $f : X \to Z$ and $g : Y \to W$ are quotient covering maps for $G$ and $H$, then $f \times g : X \times Y \to Z \times W$ is a quotient covering map for $G \times H$. If $f : X \to Z$ is a quotient covering map for $G$ and $e : A \to X$ is a $G$-equivariant homeomorphism, then $f \circ e$ is a quotient covering map for $G$.
--
--   2. **Smooth structure on a quotient.** Let $E$ be a real normed space, $M$ a $C^\infty$ manifold modelled on $E$ (without boundary), $G$ a group acting on $M$, $p : M \to Y$ a quotient covering map for this action, and $\sigma : Y \to M$ any map with $p \circ \sigma = \mathrm{id}_Y$. The atlas on $Y$ assigns to $q \in Y$ the chart obtained by composing the local inverse of $p$ through $\sigma(q)$ with the chart of $M$ at $\sigma(q)$. If every $k \in G$ acts by a $C^\infty$ map $x \mapsto k\cdot x$, then this atlas makes $Y$ a $C^\infty$ manifold modelled on $E$, the projection $p$ is $C^\infty$, and every local inverse branch of $p$ (through any point $b \in M$) is $C^\infty$ at every point of its domain.
--
--   3. **The group $\Gamma$.** Put
--   $$
--   \varphi = \begin{pmatrix} 1 & 1 \\ 1 & 2 \end{pmatrix}, \qquad \psi = \begin{pmatrix} 1 & -1 \\ -1 & 2 \end{pmatrix}, \qquad \Gamma = \langle \varphi, \psi, -I \rangle \le SL(2,\mathbb{Z}),
--   $$
--   and let $T = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$, $S = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$. Writing $\bar g$ for the reduction of $g$ modulo $n$, the auxiliary subgroups are $P_2 = \{1, \bar\varphi, \bar\varphi^2\} \le SL(2,\mathbb{Z}/2)$ and the eight-element subgroup $Q_3 = \{\pm 1, \pm\bar\varphi, \pm\bar\psi, \pm\bar\varphi\bar\psi\} \le SL(2,\mathbb{Z}/3)$; reduction maps $\Gamma$ into $P_2$ and into $Q_3$. The established properties are:
--      - every $g \in \Gamma$ has $\operatorname{tr} g \notin \{0, 1, -1\}$; hence no element of $\Gamma$ is elliptic, and an element of $\Gamma$ that fixes one point of $\mathbb{H}$ fixes every point of $\mathbb{H}$;
--      - $\Gamma$ is a normal subgroup of $SL(2,\mathbb{Z})$; one has $\psi^{-1}\varphi^{-1}\psi\varphi = -T^6$ and $S = -\varphi\psi T^3$;
--      - every $g \in SL(2,\mathbb{Z})$ can be written $g = T^n h$ with $n \in \{0,1,\dots,5\}$ and $h \in \Gamma$, and for $n \in \mathbb{Z}$ one has $T^n \in \Gamma$ if and only if $6 \mid n$.
--
--   4. **The surface $\Sigma$.** Since $-I \in \Gamma$ acts trivially, $\Gamma$ is replaced by its image $\overline{\Gamma}$ in the permutation group of $\mathbb{H}$; this image acts freely, continuously and properly discontinuously. The surface is the orbit space $\Sigma = \mathbb{H}/\overline{\Gamma}$ with projection $\pi : \mathbb{H} \to \Sigma$, which is a quotient covering map. Viewing $\mathbb{C} \cong \mathbb{R}^2$ as a real normed space and choosing a section $\sigma$ of $\pi$, item 2 makes $\Sigma$ a smooth surface modelled on $\mathbb{C}$ with $\pi$ smooth; $\Sigma$ is moreover Hausdorff, second countable and connected. Two points are identified, $\pi(z) = \pi(w)$, exactly when $z = g\cdot w$ for some $g \in \Gamma$.
--
--   5. **The cusp.** For $a \in \mathbb{R}$ let $C_a = \pi(\{z \in \mathbb{H} : \operatorname{Im} z > a\})$. Each $C_a$ is open and $\Sigma \setminus C_a$ is compact. For $a > 1$ and $\operatorname{Im} z, \operatorname{Im} w > a$,
--   $$
--   \pi(z) = \pi(w) \iff z = w + 6k \text{ for some } k \in \mathbb{Z},
--   $$
--   and $z \mapsto (\operatorname{Im} z, \operatorname{Re} z \bmod 6)$ induces a homeomorphism $C_a \cong (a,\infty) \times \mathbb{R}/6\mathbb{Z}$ (the cusp coordinates). A general lemma used here: if two quotient maps out of the same space have the same fibres, their targets are canonically homeomorphic.
--
--   6. **The height function.** For $z \in \mathbb{H}$ let $m(z) = \max_{g \in SL(2,\mathbb{Z})} \operatorname{Im}(g\cdot z) > 0$ (the maximum is attained). Then $m(g\cdot z) = m(z)$ for $g \in SL(2,\mathbb{Z})$, $m(z) = \operatorname{Im} z$ when $\operatorname{Im} z > 1$, and $z \mapsto \log m(z)$ is $1$-Lipschitz for the hyperbolic metric on $\mathbb{H}$. The height on $\Sigma$ is
--   $$
--   h(\pi(z)) = \log m(z),
--   $$
--   a well-defined continuous function with $h(\pi(z)) = \log \operatorname{Im} z$ whenever $\operatorname{Im} z > 1$. For $a > 1$: $x \in C_a$ if and only if $h(x) > \log a$, and the sublevel set $\{h \le \log a\}$ is compact.
--
--   7. **The open core and its connectedness.** For $b \in \mathbb{R}$ the open core is the open subspace $\Sigma_b = \{x \in \Sigma : h(x) < \log b\}$. For $1 < a < b$ the slice $\{x \in \Sigma_b : h(x) \le \log a\}$ is compact. For $1 < a < c$ the *clipping map* $\Sigma \to \Sigma$ is the identity outside $C_a$ and, in the cusp coordinates of $C_a$, replaces $(t, \theta)$ by $(\min(t,c), \theta)$; it is continuous, fixes every point with $h \le \log c$, and has image exactly $\{h \le \log c\}$. Consequently $\{h \le \log c\}$ is connected for every $c > 1$, and for every $b > 1$ the open core $\Sigma_b$ is nonempty and connected.
--
--   These constructions supply a concrete non-compact hyperbolic surface whose cusp region $C_a$ has the coordinates of item 5 and compact complement, together with an exhaustion by compact connected sublevel sets of a height function; the general quotient recipe of items 1 and 2 is reusable for any smooth manifold divided by a free, properly discontinuous action by diffeomorphisms.
--
--   **Formalization Note** In Lean the elements of $SL(2,\mathbb{Z})$ act on $\mathbb{H}$ through their images in $GL(2,\mathbb{R})$; the surface `Surface` is the orbit quotient of $\mathbb{H}$ by `effective`, the range of $\Gamma$ in `Equiv.Perm ℍ`. The charts on a quotient (`manifoldCharts`) depend on the chosen section, here `sectionMap := Function.surjInv`, and the height is defined as `logMaxIm (sectionMap x)`, which is shown to be independent of the choice of lift (`height_projection`). The maximizer in $m(z)$ is chosen with `Classical.choose`. The model is `𝓘(ℝ, ℂ)` with smoothness exponent $\infty$. The clipping map is `clipCusp a c` (with hypotheses $1 < a < c$), and the cusp, open core and compact slice are `cusp`, `OpenCore`, `compact_core_slice`. Two private `dite` rewriting lemmas are plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Quotient.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Quotient.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ConjugatePoints mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ConjugatePoints

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

noncomputable section

/-!
# Smooth quotient constructions and the hyperbolic core.
-/

section
open Set Filter Topology
namespace ThreeManifold.QuotientConstruction

variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace W]
    {G H : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]

@[instance_reducible]
def productAction : MulAction (G × H) (X × Y) where
  smul g x := (g.1 • x.1, g.2 • x.2)
  one_smul x := by
    change ((1 : G) • x.1, (1 : H) • x.2) = x
    simp
  mul_smul g h x := by
    change ((g.1 * h.1) • x.1, (g.2 * h.2) • x.2) =
      (g.1 • (h.1 • x.1), g.2 • (h.2 • x.2))
    simp [mul_smul]

lemma product_cover {f : X → Z} {g : Y → W}
    (hf : IsQuotientCoveringMap f G) (hg : IsQuotientCoveringMap g H) :
    let := productAction (X := X) (Y := Y) (G := G) (H := H)
    IsQuotientCoveringMap (Prod.map f g) (G × H) := by
  let := productAction (X := X) (Y := Y) (G := G) (H := H)
  refine {
    toIsQuotientMap := (hf.isOpenQuotientMap.isOpenMap.prodMap hg.isOpenQuotientMap.isOpenMap).isQuotientMap
      (hf.continuous.prodMap hg.continuous) (hf.surjective.prodMap hg.surjective)
    continuous_const_smul := ?_
    apply_eq_iff_mem_orbit := ?_
    disjoint := ?_ }
  · intro k
    exact (hf.continuous_const_smul k.1).prodMap (hg.continuous_const_smul k.2)
  · intro x y
    constructor
    · intro h
      obtain ⟨a, ha⟩ := hf.apply_eq_iff_mem_orbit.mp (congrArg Prod.fst h)
      obtain ⟨b, hb⟩ := hg.apply_eq_iff_mem_orbit.mp (congrArg Prod.snd h)
      exact ⟨(a, b), Prod.ext ha hb⟩
    · rintro ⟨k, rfl⟩
      exact Prod.ext (hf.map_smul k.1) (hg.map_smul k.2)
  · intro x
    obtain ⟨U, hU, hUd⟩ := hf.disjoint x.1
    obtain ⟨V, hV, hVd⟩ := hg.disjoint x.2
    refine ⟨U ×ˢ V, prod_mem_nhds hU hV, ?_⟩
    rintro k ⟨z, ⟨y, hy, hyz⟩, hz⟩
    exact Prod.ext (hUd k.1 ⟨z.1, ⟨y.1, hy.1, congrArg Prod.fst hyz⟩, hz.1⟩)
      (hVd k.2 ⟨z.2, ⟨y.2, hy.2, congrArg Prod.snd hyz⟩, hz.2⟩)

lemma cover_precomp {A : Type*} [TopologicalSpace A] [MulAction G A]
    {f : X → Z} (hf : IsQuotientCoveringMap f G) (e : A ≃ₜ X)
    (he : ∀ k : G, ∀ a : A, e (k • a) = k • e a) :
    IsQuotientCoveringMap (f ∘ e) G := by
  refine {
    toIsQuotientMap := hf.toIsQuotientMap.comp e.isQuotientMap
    continuous_const_smul := ?_
    apply_eq_iff_mem_orbit := ?_
    disjoint := ?_ }
  · intro k
    have h : (fun a : A => k • a) = e.symm ∘ (fun x : X => k • x) ∘ e := by
      funext a
      apply e.injective
      simp [he]
    rw [h]
    exact e.symm.continuous.comp ((hf.continuous_const_smul k).comp e.continuous)
  · intro a b
    change f (e a) = f (e b) ↔ _
    rw [hf.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, e.injective ((he k b).trans hk)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, (he k b).symm⟩
  · intro a
    obtain ⟨U, hU, hd⟩ := hf.disjoint (e a)
    refine ⟨e ⁻¹' U, e.continuous.continuousAt hU, ?_⟩
    rintro k ⟨z, ⟨y, hy, rfl⟩, hz⟩
    exact hd k ⟨e (k • y), ⟨e y, hy, (he k y).symm⟩, hz⟩

end ThreeManifold.QuotientConstruction
end

open Set Manifold Bundle
open scoped ContDiff
open Set Filter Topology Manifold
open scoped ContDiff

namespace ThreeManifold.QuotientConstruction

lemma lifts_eventuallyEq {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} (hf : IsLocalHomeomorph f)
    {u v : Z → X} {z : Z} (hu : ContinuousAt u z) (hv : ContinuousAt v z)
    (heq : u z = v z) (hcomp : (f ∘ u) =ᶠ[nhds z] (f ∘ v)) :
    u =ᶠ[nhds z] v := by
  let e := hf.localInverseAt (u z)
  have he : e.target ∈ nhds (u z) := e.open_target.mem_nhds hf.self_mem_localInverseAt_target
  have h1 : ∀ᶠ w in nhds z, u w ∈ e.target := hu he
  have h2 : ∀ᶠ w in nhds z, v w ∈ e.target := hv (heq ▸ he)
  filter_upwards [h1, h2, hcomp] with w hw hw' hww
  exact hf.injOn_localInverseAt_target hw hw' hww

lemma cover_lift_eventuallyEq_action
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {H : Type*} [Group H] [MulAction H X] {p : X → Y}
    (hp : IsQuotientCoveringMap p H)
    (hact : ∀ k : H, Continuous (fun x : X => k • x))
    (b : X) {x : X}
    (hx : p x ∈ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b).source) :
    ∃ k : H, (fun y => hp.isCoveringMap.isLocalHomeomorph.localInverseAt b (p y)) =ᶠ[nhds x]
      (fun y => k • y) := by
  let hlocal := hp.isCoveringMap.isLocalHomeomorph
  let d := hlocal.localInverseAt b
  have hdp : p (d (p x)) = p x := hlocal.apply_localInverseAt_of_mem hx
  obtain ⟨k, hk⟩ := hp.apply_eq_iff_mem_orbit.mp hdp
  refine ⟨k, lifts_eventuallyEq hlocal
    ((d.continuousAt hx).comp hp.continuous.continuousAt) (hact k).continuousAt hk.symm ?_⟩
  have hnear : ∀ᶠ y in nhds x, p y ∈ d.source :=
    hp.continuous.continuousAt (d.open_source.mem_nhds hx)
  filter_upwards [hnear] with y hy
  exact (hlocal.apply_localInverseAt_of_mem hy).trans (hp.map_smul k).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Type*} [TopologicalSpace Q]
    {G : Type*} [Group G] [MulAction G E]
    {f : E → Q} (hf : IsQuotientCoveringMap f G)

omit [MulAction G E]
open IsManifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [MulAction G M] {p : M → Q}
    (hp : IsQuotientCoveringMap p G)

@[instance_reducible]
def manifoldCharts {σ : Q → M} (hσ : Function.RightInverse σ p) : ChartedSpace E Q :=
  hp.isCoveringMap.isLocalHomeomorph.chartedSpaceOfRightInverse hσ

lemma manifold_quotient_isManifold {σ : Q → M} (hσ : Function.RightInverse σ p)
    (hact : ∀ k : G, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x : M => k • x)) :
    letI := manifoldCharts (E := E) hp hσ
    IsManifold 𝓘(ℝ, E) ∞ Q := by
  let := manifoldCharts (E := E) hp hσ
  apply isManifold_of_contDiffOn
  intro e d he hd
  obtain ⟨a, rfl⟩ := he
  obtain ⟨b, rfl⟩ := hd
  intro x hx
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, preimage_id_eq, range_id, inter_univ] at hx ⊢
  let ca := chartAt E (σ a)
  let cb := chartAt E (σ b)
  let la := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ a)
  let lb := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ b)
  have ha : x ∈ ca.target := hx.1.1
  have hb : p (ca.symm x) ∈ lb.source := by
    have hb := hx.2.1
    simpa only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.coe_trans_symm,
      hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm, Function.comp_def] using hb
  have hb' : lb (p (ca.symm x)) ∈ cb.source := by
    have hb := hx.2.2
    simp only [OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.coe_trans_symm,
      hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm, Function.comp_def, mem_preimage] at hb
    exact hb
  obtain ⟨k, hk⟩ := cover_lift_eventuallyEq_action hp (fun k => (hact k).continuous) (σ b) hb
  have hkeq : lb (p (ca.symm x)) = k • ca.symm x := hk.eq_of_nhds
  have hks : k • ca.symm x ∈ cb.source := hkeq ▸ hb'
  have hca : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ca.symm x :=
    contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas (σ a)) ha
  have hcb : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ cb (k • ca.symm x) :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (σ b)) hks
  have hsm := hcb.comp x ((hact k (ca.symm x)).comp x hca)
  apply ContDiffAt.contDiffWithinAt
  apply hsm.contDiffAt.congr_of_eventuallyEq
  have hcomp := hk.comp_tendsto hca.continuousAt
  filter_upwards [hcomp] with y hy
  simp only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_trans_symm,
    hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm, Function.comp_def]
  change cb (lb (p (ca.symm y))) = cb (k • ca.symm y)
  exact congrArg cb hy

lemma manifold_quotient_projection_smooth {σ : Q → M} (hσ : Function.RightInverse σ p)
    (hact : ∀ k : G, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x : M => k • x)) :
    letI := manifoldCharts (E := E) hp hσ
    letI := manifold_quotient_isManifold hp hσ hact
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ p := by
  let := manifoldCharts (E := E) hp hσ
  let := manifold_quotient_isManifold hp hσ hact
  intro x
  rw [contMDiffAt_iff_target_of_mem_source (mem_chart_source E (p x))]
  refine ⟨hp.continuous.continuousAt, ?_⟩
  let cb := chartAt E (σ (p x))
  let lb := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ (p x))
  have hx : p x ∈ (lb.trans cb).source := mem_chart_source E (p x)
  obtain ⟨k, hk⟩ := cover_lift_eventuallyEq_action hp (fun k => (hact k).continuous)
    (σ (p x)) hx.1
  have hkeq : lb (p x) = k • x := hk.eq_of_nhds
  have hks : k • x ∈ cb.source := hkeq ▸ hx.2
  have hcb : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ cb (k • x) :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (σ (p x))) hks
  apply (hcb.comp x (hact k x)).congr_of_eventuallyEq
  filter_upwards [hk] with y hy
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_def, id_eq]
  change cb (lb (p y)) = cb (k • y)
  exact congrArg cb hy

lemma chosen_lift_smoothAt {σ : Q → M} (hσ : Function.RightInverse σ p)
    (hact : ∀ k : G, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x : M => k • x)) (q : Q) :
    letI := manifoldCharts (E := E) hp hσ
    letI := manifold_quotient_isManifold hp hσ hact
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ q)) q := by
  let := manifoldCharts (E := E) hp hσ
  let := manifold_quotient_isManifold hp hσ hact
  let c := chartAt E (σ q)
  let d := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ q)
  have hq : q ∈ (d.trans c).source := mem_chart_source E q
  have hct : chartAt E q q ∈ c.target := c.map_source hq.2
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm (chartAt E q q) :=
    contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas (σ q)) hct
  have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E q) q :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas q) (mem_chart_source E q)
  apply (hc.comp q hchart).congr_of_eventuallyEq
  have hnear : ∀ᶠ r in nhds q, d r ∈ c.source :=
    (d.continuousAt hq.1) (c.open_source.mem_nhds hq.2)
  filter_upwards [hnear] with r hr
  change d r = c.symm (c (d r))
  exact (c.left_inv hr).symm

lemma local_lift_smoothAt {σ : Q → M} (hσ : Function.RightInverse σ p)
    (hact : ∀ k : G, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x : M => k • x))
    (b : M) {q : Q} (hq : q ∈ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b).source) :
    letI := manifoldCharts (E := E) hp hσ
    letI := manifold_quotient_isManifold hp hσ hact
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b) q := by
  let := manifoldCharts (E := E) hp hσ
  let := manifold_quotient_isManifold hp hσ hact
  let hlocal := hp.isCoveringMap.isLocalHomeomorph
  let d := hlocal.localInverseAt (σ q)
  let l := hlocal.localInverseAt b
  have hdq : q ∈ d.source := by
    simpa only [hσ q] using hlocal.apply_self_mem_localInverseAt_source (x := σ q)
  have heq : p (l q) = p (d q) :=
    (hlocal.apply_localInverseAt_of_mem hq).trans
      (hlocal.apply_localInverseAt_of_mem hdq).symm
  obtain ⟨k, hk⟩ := hp.apply_eq_iff_mem_orbit.mp heq
  have hd := chosen_lift_smoothAt hp hσ hact q
  have hsm := (hact k (d q)).comp q hd
  apply hsm.congr_of_eventuallyEq
  apply lifts_eventuallyEq hlocal (l.continuousAt hq) hsm.continuousAt hk.symm
  filter_upwards [l.open_source.mem_nhds hq, d.open_source.mem_nhds hdq] with r hr hdr
  dsimp only [Function.comp_def]
  rw [hp.map_smul k]
  exact (hlocal.apply_localInverseAt_of_mem hr).trans
    (hlocal.apply_localInverseAt_of_mem hdr).symm

end ThreeManifold.QuotientConstruction

open Matrix
open scoped MatrixGroups UpperHalfPlane
namespace ThreeManifold.HyperbolicCore

def phi : SL(2, ℤ) := ⟨!![1, 1; 1, 2], by norm_num [Matrix.det_fin_two]⟩
def psi : SL(2, ℤ) := ⟨!![1, -1; -1, 2], by norm_num [Matrix.det_fin_two]⟩
def Γ : Subgroup SL(2, ℤ) := Subgroup.closure {phi, psi, -1}

def red (n : ℕ) : SL(2, ℤ) →* SL(2, ZMod n) :=
  SpecialLinearGroup.map (Int.castRingHom (ZMod n))

def qset : Set SL(2, ZMod 3) :=
  {1, -1, red 3 phi, -(red 3 phi), red 3 psi, -(red 3 psi),
   red 3 phi * red 3 psi, -(red 3 phi * red 3 psi)}

def Q : Subgroup SL(2, ZMod 3) where
  carrier := qset
  one_mem' := by simp [qset]
  mul_mem' := by
    intro a b ha hb
    simp only [qset, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  inv_mem' := by
    intro a ha
    simp only [qset, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def pset : Set SL(2, ZMod 2) := {1, red 2 phi, red 2 phi * red 2 phi}

def P : Subgroup SL(2, ZMod 2) where
  carrier := pset
  one_mem' := by simp [pset]
  mul_mem' := by
    intro a b ha hb
    simp only [pset, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;> decide
  inv_mem' := by
    intro a ha
    simp only [pset, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl <;> decide

theorem red_two_mem {g : SL(2, ℤ)} (hg : g ∈ Γ) : red 2 g ∈ P := by
  have h : Γ ≤ P.comap (red 2) := by
    apply (Subgroup.closure_le _).2
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    change red 2 a ∈ pset
    simp only [pset, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases ha with rfl | rfl | rfl <;> decide
  exact h hg

theorem red_three_mem {g : SL(2, ℤ)} (hg : g ∈ Γ) : red 3 g ∈ Q := by
  have h : Γ ≤ Q.comap (red 3) := by
    apply (Subgroup.closure_le _).2
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    change red 3 a ∈ qset
    simp only [qset, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases ha with rfl | rfl | rfl <;> decide
  exact h hg

lemma P_trace_zero {g : SL(2, ZMod 2)} (hg : g ∈ P)
    (ht : g 0 0 + g 1 1 = 0) : g = 1 := by
  change g ∈ pset at hg
  simp only [pset, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rfl
  all_goals revert ht; decide

lemma Q_trace_one {g : SL(2, ZMod 3)} (hg : g ∈ Q)
    (ht : g 0 0 + g 1 1 = 1) : g = -1 := by
  change g ∈ qset at hg
  simp only [qset, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert ht <;> decide

lemma Q_trace_neg_one {g : SL(2, ZMod 3)} (hg : g ∈ Q)
    (ht : g 0 0 + g 1 1 = -1) : g = 1 := by
  change g ∈ qset at hg
  simp only [qset, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert ht <;> decide

lemma det_congruence_trace {a b c d N : ℤ}
    (hd : a*d-b*c = 1) (ha : N ∣ a-1) (hb : N ∣ b)
    (hc : N ∣ c) (he : N ∣ d-1) : N^2 ∣ a+d-2 := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  obtain ⟨z,hz⟩ := hc
  obtain ⟨w,hw⟩ := he
  refine ⟨y*z-x*w, ?_⟩
  have ha' : a = 1+N*x := by linarith
  have hd' : d = 1+N*w := by linarith
  subst a; subst d; subst b; subst c
  nlinarith [hd]

lemma red_one_trace {g : SL(2, ℤ)} {N : ℕ} (hg : red N g = 1) :
    (N:ℤ)^2 ∣ g 0 0 + g 1 1 - 2 := by
  apply det_congruence_trace (b := g 0 1) (c := g 1 0)
    (by simpa only [Matrix.det_fin_two] using g.property)
  all_goals apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
  · have hh := congrArg (fun m : SL(2, ZMod N) => m 0 0) hg
    simpa [red] using sub_eq_zero.mpr hh
  · have hh := congrArg (fun m : SL(2, ZMod N) => m 0 1) hg
    simpa [red] using hh
  · have hh := congrArg (fun m : SL(2, ZMod N) => m 1 0) hg
    simpa [red] using hh
  · have hh := congrArg (fun m : SL(2, ZMod N) => m 1 1) hg
    simpa [red] using sub_eq_zero.mpr hh

theorem trace_not_small {g : SL(2, ℤ)} (hg : g ∈ Γ) :
    g 0 0 + g 1 1 ≠ 0 ∧ g 0 0 + g 1 1 ≠ 1 ∧ g 0 0 + g 1 1 ≠ -1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    have hm := P_trace_zero (red_two_mem hg) (by
      change (g 0 0 : ZMod 2) + (g 1 1 : ZMod 2) = 0
      simpa using congrArg (fun t : ℤ => (t : ZMod 2)) ht)
    have hd := red_one_trace hm
    rw [ht] at hd
    norm_num at hd
  · intro ht
    have hm := Q_trace_one (red_three_mem hg) (by
      change (g 0 0 : ZMod 3) + (g 1 1 : ZMod 3) = 1
      simpa using congrArg (fun t : ℤ => (t : ZMod 3)) ht)
    have hn : red 3 (-g) = 1 := by simpa [red] using congrArg Neg.neg hm
    have hd := red_one_trace hn
    have hv : (-g) 0 0 + (-g) 1 1 = -1 := by
      change -g 0 0 + -g 1 1 = -1
      omega
    rw [hv] at hd
    norm_num at hd
  · intro ht
    have hm := Q_trace_neg_one (red_three_mem hg) (by
      change (g 0 0 : ZMod 3) + (g 1 1 : ZMod 3) = -1
      simpa using congrArg (fun t : ℤ => (t : ZMod 3)) ht)
    have hd := red_one_trace hm
    rw [ht] at hd
    norm_num at hd

lemma mapGL_det (g : SL(2, ℤ)) :
    ((SpecialLinearGroup.mapGL ℝ g).val).det = 1 := by
  rw [Matrix.det_fin_two]
  change (g 0 0 : ℝ)*(g 1 1 : ℝ)-(g 0 1 : ℝ)*(g 1 0 : ℝ)=1
  exact_mod_cast (show g 0 0*g 1 1-g 0 1*g 1 0=1 by
    simpa only [Matrix.det_fin_two] using g.property)

theorem not_elliptic {g : SL(2, ℤ)} (hg : g ∈ Γ) :
    ¬ (SpecialLinearGroup.mapGL ℝ g).IsElliptic := by
  intro he
  change ((SpecialLinearGroup.mapGL ℝ g).val).discr < 0 at he
  rw [Matrix.discr_fin_two, Matrix.trace_fin_two] at he
  have hd := mapGL_det g
  rw [hd] at he
  have htrace : ((g 0 0 : ℝ) + (g 1 1 : ℝ))^2 < 4 := by
    simpa [SpecialLinearGroup.mapGL_coe_matrix] using he
  have hint : (g 0 0 + g 1 1)^2 < 4 := by exact_mod_cast htrace
  obtain ⟨h0,h1,hn1⟩ := trace_not_small hg
  have hlo : -1 ≤ g 0 0 + g 1 1 := by nlinarith
  have hhi : g 0 0 + g 1 1 ≤ 1 := by nlinarith
  omega

theorem fixed_point_trivial {g : SL(2, ℤ)} (hg : g ∈ Γ) {z : ℍ}
    (hz : g • z = z) : ∀ w : ℍ, g • w = w := by
  have hcen : SpecialLinearGroup.mapGL ℝ g ∈ Subgroup.center (GL (Fin 2) ℝ) := by
    by_contra hn
    exact not_elliptic hg (UpperHalfPlane.isElliptic_of_exists_smul_eq_self
      (by rw [mapGL_det]; norm_num) hn ⟨z,hz⟩)
  exact UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mpr hcen

end ThreeManifold.HyperbolicCore

open Matrix
open scoped MatrixGroups UpperHalfPlane

open Set Pointwise
namespace ThreeManifold.HyperbolicCore

instance integer_proper : ProperlyDiscontinuousSMul SL(2, ℤ) ℍ := by
  rw [properlyDiscontinuousSMul_iff]
  intro K L hK hL
  have h := (Subgroup.properlyDiscontinuousSMul_iff 𝒮ℒ).mp
    (inferInstance : ProperlyDiscontinuousSMul 𝒮ℒ ℍ) hK hL
  have hp := h.preimage (SpecialLinearGroup.mapGL_injective (R := ℤ) (n := Fin 2) (S := ℝ)).injOn
  apply hp.subset
  intro g hg
  exact ⟨⟨g,rfl⟩,hg⟩

def effective : Subgroup (Equiv.Perm ℍ) := (MulAction.toPermHom Γ ℍ).range

def effect : Γ →* effective := (MulAction.toPermHom Γ ℍ).rangeRestrict

lemma effect_surjective : Function.Surjective effect :=
  MonoidHom.rangeRestrict_surjective _

instance effective_cancel : IsCancelSMul effective ℍ := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g z hz
  obtain ⟨a,rfl⟩ := effect_surjective g
  apply Subtype.ext
  apply Equiv.ext
  intro w
  exact fixed_point_trivial a.property hz w

instance effective_continuous : ContinuousConstSMul effective ℍ where
  continuous_const_smul g := by
    obtain ⟨a,rfl⟩ := effect_surjective g
    change Continuous (fun z : ℍ => SpecialLinearGroup.mapGL ℝ a.val • z)
    exact continuous_const_smul _

instance effective_proper : ProperlyDiscontinuousSMul effective ℍ := by
  rw [properlyDiscontinuousSMul_iff]
  intro K L hK hL
  have hg := finite_disjoint_inter_image (Γ := Γ) hK hL
  apply (hg.image effect).subset
  intro a ha
  obtain ⟨g,rfl⟩ := effect_surjective a
  exact ⟨g,ha,rfl⟩

def Surface := Quotient (MulAction.orbitRel effective ℍ)
instance : TopologicalSpace Surface := inferInstanceAs
  (TopologicalSpace (Quotient (MulAction.orbitRel effective ℍ)))
def projection : ℍ → Surface := Quotient.mk _

lemma projection_cover : IsQuotientCoveringMap projection effective :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

end ThreeManifold.HyperbolicCore

open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
namespace ThreeManifold.HyperbolicCore
open QuotientConstruction

instance halfplane_real_manifold : IsManifold 𝓘(ℝ, ℂ) ∞ ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.isManifold_singleton

lemma action_smooth (g : SL(2, ℤ)) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : ℍ => g • z) := by
  intro z
  have h := UpperHalfPlane.contMDiff_smul (n := ∞)
    (g := SpecialLinearGroup.mapGL ℝ g) (by
      change 0 < ((SpecialLinearGroup.mapGL ℝ g).val).det
      rw [mapGL_det]; norm_num) z
  rw [contMDiffAt_iff] at h ⊢
  exact ⟨h.1,h.2.restrict_scalars ℝ⟩

lemma effective_smooth (g : effective) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : ℍ => g • z) := by
  obtain ⟨a,rfl⟩ := effect_surjective g
  exact action_smooth a.val

def sectionMap : Surface → ℍ := Function.surjInv projection_cover.surjective
lemma sectionMap_rightInverse : Function.RightInverse sectionMap projection :=
  Function.rightInverse_surjInv projection_cover.surjective

instance surfaceCharts : ChartedSpace ℂ Surface :=
  manifoldCharts (E := ℂ) projection_cover sectionMap_rightInverse
instance surfaceSmooth : IsManifold 𝓘(ℝ, ℂ) ∞ Surface :=
  manifold_quotient_isManifold projection_cover sectionMap_rightInverse effective_smooth

lemma projection_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ projection :=
  manifold_quotient_projection_smooth projection_cover sectionMap_rightInverse effective_smooth

instance : TopologicalSpace effective := ⊥
instance : DiscreteTopology effective := ⟨rfl⟩
instance : ProperSMul effective ℍ :=
  properlyDiscontinuousSMul_iff_properSMul.mp inferInstance
instance surfaceT2 : T2Space Surface := inferInstanceAs
  (T2Space (Quotient (MulAction.orbitRel effective ℍ)))
instance surfaceSecondCountable : SecondCountableTopology Surface :=
  ContinuousConstSMul.secondCountableTopology
instance surfaceConnected : ConnectedSpace Surface :=
  projection_cover.surjective.connectedSpace projection_cover.continuous

end ThreeManifold.HyperbolicCore

open Matrix
open scoped MatrixGroups UpperHalfPlane

namespace ThreeManifold.HyperbolicCore
open ModularGroup

lemma phi_mem : phi ∈ Γ := Subgroup.subset_closure (by simp)
lemma psi_mem : psi ∈ Γ := Subgroup.subset_closure (by simp)
lemma neg_one_mem : (-1 : SL(2, ℤ)) ∈ Γ := Subgroup.subset_closure (by simp)

lemma conj_preserves (c : SL(2, ℤ))
    (hp : c*phi*c⁻¹ ∈ Γ) (hq : c*psi*c⁻¹ ∈ Γ) :
    ∀ g ∈ Γ, c*g*c⁻¹ ∈ Γ := by
  have hc : Γ ≤ Γ.comap (MulAut.conj c).toMonoidHom := by
    apply (Subgroup.closure_le _).2
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hp
    · exact hq
    · change c*(-1)*c⁻¹ ∈ Γ
      simpa using neg_one_mem
  exact hc

lemma S_preserves : ∀ g ∈ Γ, S*g*S⁻¹ ∈ Γ := by
  apply conj_preserves
  · have h : S*phi*S⁻¹ = phi⁻¹ := by decide
    rw [h]; exact Γ.inv_mem phi_mem
  · have h : S*psi*S⁻¹ = psi⁻¹ := by decide
    rw [h]; exact Γ.inv_mem psi_mem

lemma Sinv_preserves : ∀ g ∈ Γ, S⁻¹*g*(S⁻¹)⁻¹ ∈ Γ := by
  apply conj_preserves
  · have h : S⁻¹*phi*(S⁻¹)⁻¹ = phi⁻¹ := by decide
    rw [h]; exact Γ.inv_mem phi_mem
  · have h : S⁻¹*psi*(S⁻¹)⁻¹ = psi⁻¹ := by decide
    rw [h]; exact Γ.inv_mem psi_mem

lemma T_preserves : ∀ g ∈ Γ, T*g*T⁻¹ ∈ Γ := by
  apply conj_preserves
  · have h : T*phi*T⁻¹ = psi⁻¹ := by decide
    rw [h]; exact Γ.inv_mem psi_mem
  · have h : T*psi*T⁻¹ = phi*psi := by decide
    rw [h]; exact Γ.mul_mem phi_mem psi_mem

lemma Tinv_preserves : ∀ g ∈ Γ, T⁻¹*g*(T⁻¹)⁻¹ ∈ Γ := by
  apply conj_preserves
  · have h : T⁻¹*phi*(T⁻¹)⁻¹ = psi*phi := by decide
    rw [h]; exact Γ.mul_mem psi_mem phi_mem
  · have h : T⁻¹*psi*(T⁻¹)⁻¹ = phi⁻¹ := by decide
    rw [h]; exact Γ.inv_mem phi_mem

lemma normalizer_of_preserves {c : SL(2, ℤ)}
    (hc : ∀ g ∈ Γ, c*g*c⁻¹ ∈ Γ)
    (hi : ∀ g ∈ Γ, c⁻¹*g*(c⁻¹)⁻¹ ∈ Γ) : c ∈ Subgroup.normalizer Γ := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact hc g
  · intro hg
    simpa [mul_assoc] using hi _ hg

instance gamma_normal : Γ.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, ← SpecialLinearGroup.SL2Z_generators]
  apply le_antisymm (le_trans le_top (by rw [SpecialLinearGroup.SL2Z_generators]))
  apply (Subgroup.closure_le _).2
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact normalizer_of_preserves S_preserves Sinv_preserves
  · exact normalizer_of_preserves T_preserves Tinv_preserves

lemma peripheral_matrix : psi⁻¹*phi⁻¹*psi*phi = -(T^6) := by decide

lemma T_six_mem : T^6 ∈ Γ := by
  have hc := Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem psi_mem)
    (Γ.inv_mem phi_mem)) psi_mem) phi_mem
  rw [peripheral_matrix] at hc
  simpa using Γ.mul_mem neg_one_mem hc

lemma S_coset_relation : S = (-1)*phi*psi*T^3 := by decide

def qmap : SL(2, ℤ) →* SL(2, ℤ) ⧸ Γ := QuotientGroup.mk' Γ

lemma qmap_phi : qmap phi = 1 := (QuotientGroup.eq_one_iff _).2 phi_mem
lemma qmap_psi : qmap psi = 1 := (QuotientGroup.eq_one_iff _).2 psi_mem
lemma qmap_neg_one : qmap (-1) = 1 := (QuotientGroup.eq_one_iff _).2 neg_one_mem

lemma qmap_S : qmap S = qmap T ^ 3 := by
  conv_lhs => rw [S_coset_relation]
  simp only [map_mul, map_pow, qmap_phi, qmap_psi, qmap_neg_one, one_mul]

lemma qmap_T_six : qmap T ^ 6 = 1 := by
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).2 T_six_mem

lemma qmap_cyclic (g : SL(2, ℤ)) : qmap g ∈ Subgroup.zpowers (qmap T) := by
  have hc : (⊤ : Subgroup SL(2, ℤ)) ≤ (Subgroup.zpowers (qmap T)).comap qmap := by
    rw [← SpecialLinearGroup.SL2Z_generators]
    apply (Subgroup.closure_le _).2
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · change qmap S ∈ Subgroup.zpowers (qmap T)
      rw [qmap_S]
      exact (Subgroup.zpowers (qmap T)).pow_mem (Subgroup.mem_zpowers _) 3
    · exact Subgroup.mem_zpowers _
  exact hc (Subgroup.mem_top g)

lemma qmap_representative (g : SL(2, ℤ)) :
    ∃ n : Fin 6, qmap (T ^ n.val) = qmap g := by
  obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp (qmap_cyclic g)
  have hm : 0 ≤ k % 6 := Int.emod_nonneg _ (by norm_num)
  have hl : k % 6 < 6 := Int.emod_lt_of_pos _ (by norm_num)
  refine ⟨⟨(k%6).toNat,by omega⟩, ?_⟩
  rw [map_pow, ← hk]
  have h6 : qmap T ^ (6 : ℤ) = 1 := by simpa using qmap_T_six
  have hde : 6*(k/6)+k%6 = k := by omega
  calc
    qmap T ^ (k%6).toNat = qmap T ^ (k%6) := by
      rw [← zpow_natCast,Int.toNat_of_nonneg hm]
    _ = qmap T ^ (6*(k/6)+k%6) := by
      rw [_root_.zpow_add,_root_.zpow_mul,h6, _root_.one_zpow,one_mul]
    _ = qmap T ^ k := by rw [hde]

theorem coset_representative (g : SL(2, ℤ)) :
    ∃ n : Fin 6, ∃ h : SL(2, ℤ), h ∈ Γ ∧ T^n.val*h = g := by
  obtain ⟨n,hn⟩ := qmap_representative g
  exact ⟨n,((QuotientGroup.mk'_eq_mk' Γ).mp hn)⟩

end ThreeManifold.HyperbolicCore

open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
namespace ThreeManifold.HyperbolicCore
open ModularGroup

lemma T_zpow_mem_iff (n : ℤ) : T ^ n ∈ Γ ↔ 6 ∣ n := by
  constructor
  · intro hn
    have h2 := P_trace_zero (red_two_mem hn) (by
      change ((T ^ n) 0 0 : ZMod 2) + ((T ^ n) 1 1 : ZMod 2) = 0
      rw [show (T ^ n) 0 0 = 1 by simp [coe_T_zpow],
        show (T ^ n) 1 1 = 1 by simp [coe_T_zpow]]
      decide)
    have h3 := Q_trace_neg_one (red_three_mem hn) (by
      change ((T ^ n) 0 0 : ZMod 3) + ((T ^ n) 1 1 : ZMod 3) = -1
      rw [show (T ^ n) 0 0 = 1 by simp [coe_T_zpow],
        show (T ^ n) 1 1 = 1 by simp [coe_T_zpow]]
      decide)
    have hn2 : (2 : ℤ) ∣ n := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).mp
      have h := congrArg (fun m : SL(2, ZMod 2) => m 0 1) h2
      change ((T ^ n) 0 1 : ZMod 2) = 0 at h
      rwa [show (T ^ n) 0 1 = n by simp [coe_T_zpow]] at h
    have hn3 : (3 : ℤ) ∣ n := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd n 3).mp
      have h := congrArg (fun m : SL(2, ZMod 3) => m 0 1) h3
      change ((T ^ n) 0 1 : ZMod 3) = 0 at h
      rwa [show (T ^ n) 0 1 = n by simp [coe_T_zpow]] at h
    omega
  · rintro ⟨k, rfl⟩
    rw [_root_.zpow_mul]
    exact Γ.zpow_mem (by simpa using T_six_mem) k

lemma projection_smul (g : SL(2, ℤ)) (hg : g ∈ Γ) (z : ℍ) :
    projection (g • z) = projection z :=
  projection_cover.map_smul (effect ⟨g, hg⟩)

lemma projection_eq_iff (z w : ℍ) :
    projection z = projection w ↔ ∃ g : SL(2, ℤ), g ∈ Γ ∧ g • w = z := by
  rw [projection_cover.apply_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := effect_surjective g
    exact ⟨a.val, a.property, hg⟩
  · rintro ⟨g, hg, he⟩
    exact ⟨effect ⟨g,hg⟩, he⟩

lemma bottomLeft_eq_zero_of_high (g : SL(2, ℤ)) (z : ℍ)
    (hz : 1 < z.im) (hg : 1 < (g • z).im) : g 1 0 = 0 := by
  by_contra hc
  have hc2 : (1 : ℝ) ≤ (g 1 0 : ℝ) ^ 2 := by
    have h : (1 : ℤ) ≤ (g 1 0) ^ 2 := by
      have hpos := sq_pos_of_ne_zero hc
      omega
    exact_mod_cast h
  have hd := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (g := (g : GL (Fin 2) ℝ)) (z := z)
  change ((g 1 0 : ℝ) * z.im) ^ 2 ≤ _ at hd
  have hp := UpperHalfPlane.normSq_denom_pos (g : GL (Fin 2) ℝ) z.im_ne_zero
  rw [ModularGroup.im_smul_eq_div_normSq, lt_div_iff₀ hp] at hg
  have he : z.im ^ 2 ≤ ((g 1 0 : ℝ) * z.im) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg z.im)]
  nlinarith

lemma matrix_eq_T_zpow_of_c_eq_zero {g : SL(2, ℤ)} (hc : g 1 0 = 0) :
    ∃ n : ℤ, g = T ^ n ∨ g = -(T ^ n) := by
  have had := g.det_coe
  replace had : g 0 0 * g 1 1 = 1 := by rw [det_fin_two, hc] at had; lia
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · refine ⟨g 0 1, Or.inl ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
  · refine ⟨-(g 0 1), Or.inr ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]

theorem projection_high_eq_iff {a : ℝ} (ha : 1 < a) {z w : ℍ}
    (hz : a < z.im) (hw : a < w.im) :
    projection z = projection w ↔ ∃ k : ℤ, (z : ℂ) = (w : ℂ) + 6 * k := by
  rw [projection_eq_iff]
  constructor
  · rintro ⟨g, hg, he⟩
    have hc := bottomLeft_eq_zero_of_high g w (ha.trans hw) (he ▸ ha.trans hz)
    rcases matrix_eq_T_zpow_of_c_eq_zero hc with ⟨n, hn | hn⟩
    · rw [hn] at hg he
      obtain ⟨k,hk⟩ := (T_zpow_mem_iff n).mp hg
      refine ⟨k, ?_⟩
      rw [← he, coe_T_zpow_smul_eq, hk]
      push_cast
      rfl
    · rw [hn] at hg he
      have hg' : T ^ n ∈ Γ := by simpa using Γ.mul_mem neg_one_mem hg
      obtain ⟨k,hk⟩ := (T_zpow_mem_iff n).mp hg'
      refine ⟨k, ?_⟩
      rw [ModularGroup.SL_neg_smul] at he
      rw [← he, coe_T_zpow_smul_eq, hk]
      push_cast
      rfl
  · rintro ⟨k, hk⟩
    refine ⟨T ^ (6 * k), (T_zpow_mem_iff _).mpr (dvd_mul_right _ _), ?_⟩
    apply UpperHalfPlane.ext
    rw [coe_T_zpow_smul_eq, hk]
    push_cast
    rfl

def cusp (a : ℝ) : Set Surface := projection '' {z : ℍ | a < z.im}

lemma cusp_open (a : ℝ) : IsOpen (cusp a) :=
  projection_cover.isOpenQuotientMap.isOpenMap _ (isOpen_lt continuous_const UpperHalfPlane.continuous_im)

theorem cusp_complement_compact (a : ℝ) : IsCompact (cusp a)ᶜ := by
  let K : Set ℍ := ⋃ n : Fin 6,
    (fun z : ℍ => T ^ (-(n.val : ℤ)) • z) '' (ModularGroup.truncatedFundamentalDomain a)
  have hK : IsCompact K := isCompact_iUnion fun n =>
    (ModularGroup.isCompact_truncatedFundamentalDomain a).image (action_smooth _).continuous
  apply (hK.image projection_cover.continuous).of_isClosed_subset (cusp_open a).isClosed_compl
  intro x hx
  obtain ⟨z, rfl⟩ := projection_cover.surjective x
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  obtain ⟨n,h,hh,he⟩ := coset_representative g
  have hi : (g • z).im ≤ a := by
    by_contra hi
    have hzimage : projection z ∈ cusp a := by
      refine ⟨h • z, ?_, projection_smul h hh z⟩
      rw [← he, mul_smul] at hi
      have ht := ModularGroup.im_T_zpow_smul (h • z) (n.val : ℤ)
      rw [zpow_natCast] at ht
      change ¬ (T ^ n.val • (h • z)).im ≤ a at hi
      rwa [ht, not_le] at hi
    exact hx hzimage
  have hhz : h • z ∈ K := by
    apply mem_iUnion.mpr ⟨n, ?_⟩
    refine ⟨g • z, ⟨hg,hi⟩, ?_⟩
    dsimp only
    rw [← he, mul_smul, _root_.zpow_neg, zpow_natCast, inv_smul_smul]
  exact ⟨h • z, hhz, projection_smul h hh z⟩

end ThreeManifold.HyperbolicCore

open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
namespace ThreeManifold.HyperbolicCore

section

def highCoordinates (a : ℝ) (ha : 0 < a) :
    {z : ℍ // a < z.im} ≃ₜ (Ioi a × ℝ) where
  toFun z := (⟨z.1.im, z.2⟩, z.1.re)
  invFun p := ⟨⟨⟨p.2, p.1.1⟩, ha.trans p.1.2⟩, p.1.2⟩
  left_inv z := by apply Subtype.ext; apply UpperHalfPlane.ext; rfl
  right_inv p := by rfl
  continuous_toFun :=
    ((UpperHalfPlane.continuous_im.comp continuous_subtype_val).subtype_mk _).prodMk
      (UpperHalfPlane.continuous_re.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.upperHalfPlaneMk
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop

def highProjection (a : ℝ) : {z : ℍ // a < z.im} → cusp a :=
  fun z => ⟨projection z.1, ⟨z.1,z.2,rfl⟩⟩

lemma highProjection_openQuotient (a : ℝ) : IsOpenQuotientMap (highProjection a) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x,z,hz,rfl⟩
    exact ⟨⟨z,hz⟩, rfl⟩
  · exact (projection_cover.continuous.comp continuous_subtype_val).subtype_mk _
  · intro U hU
    have hv : IsOpen (Subtype.val '' U : Set ℍ) :=
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im).isOpenEmbedding_subtypeVal.isOpenMap U hU
    have he : highProjection a '' U =
        Subtype.val ⁻¹' (projection '' (Subtype.val '' U)) := by
      ext x
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact ⟨z.1,⟨z,hz,rfl⟩,rfl⟩
      · rintro ⟨z,⟨w,hw,rfl⟩,he⟩
        exact ⟨w,hw,Subtype.ext he⟩
    rw [he]
    exact (projection_cover.isOpenQuotientMap.isOpenMap _ hv).preimage continuous_subtype_val

def highCylinderProjection (a : ℝ) : {z : ℍ // a < z.im} → (Ioi a × AddCircle (6 : ℝ)) :=
  fun z => (⟨z.1.im,z.2⟩,(z.1.re : AddCircle (6 : ℝ)))

lemma highCylinderProjection_openQuotient (a : ℝ) (ha : 0 < a) :
    IsOpenQuotientMap (highCylinderProjection a) := by
  exact (IsOpenQuotientMap.id.prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (6 : ℝ)))).comp
      (highCoordinates a ha).isOpenQuotientMap

lemma circle_six_eq_iff (x y : ℝ) :
    (x : AddCircle (6 : ℝ)) = (y : AddCircle (6 : ℝ)) ↔ ∃ k : ℤ, x = y + 6 * k := by
  rw [← AddCommGroup.modEq_iff_eq_mod_zmultiples, AddCommGroup.modEq_iff_eq_add_zsmul]
  simp only [zsmul_eq_mul]
  constructor <;> rintro ⟨k,hk⟩ <;> refine ⟨-k, ?_⟩ <;> push_cast <;> linarith

lemma highProjection_sameFibers (a : ℝ) (ha : 1 < a) (z w : {z : ℍ // a < z.im}) :
    highProjection a z = highProjection a w ↔
    highCylinderProjection a z = highCylinderProjection a w := by
  rw [Subtype.ext_iff]
  change projection z.1 = projection w.1 ↔ _
  rw [projection_high_eq_iff ha z.2 w.2]
  constructor
  · rintro ⟨k,hk⟩
    apply Prod.ext
    · apply Subtype.ext
      have h := congrArg Complex.im hk
      simpa [highCylinderProjection] using h
    · apply (circle_six_eq_iff _ _).mpr
      exact ⟨k, by have h := congrArg Complex.re hk; simpa using h⟩
  · intro h
    have him : z.1.im = w.1.im := congrArg (fun p : Ioi a × AddCircle (6 : ℝ) => (p.1 : ℝ)) h
    obtain ⟨k,hk⟩ := (circle_six_eq_iff _ _).mp (congrArg Prod.snd h)
    refine ⟨k, Complex.ext ?_ ?_⟩
    · simpa using hk
    · simpa using him

section SameFibers
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {p : X → Y} {q : X → Z}

def fiberHomeomorph (hp : IsQuotientMap p) (hq : IsQuotientMap q)
    (he : ∀ x y, p x = p y ↔ q x = q y) : Y ≃ₜ Z := by
  let f : Y → Z := q ∘ Function.surjInv hp.surjective
  let g : Z → Y := p ∘ Function.surjInv hq.surjective
  have hf : ∀ x, f (p x) = q x := fun x => (he _ _).mp (Function.rightInverse_surjInv hp.surjective _)
  have hg : ∀ x, g (q x) = p x := fun x => (he _ _).mpr (Function.rightInverse_surjInv hq.surjective _)
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro y
    obtain ⟨x,rfl⟩ := hp.surjective y
    rw [hf,hg]
  · intro z
    obtain ⟨x,rfl⟩ := hq.surjective z
    rw [hg,hf]
  · apply hp.continuous_iff.mpr
    convert hq.continuous using 1
    exact funext hf
  · apply hq.continuous_iff.mpr
    convert hp.continuous using 1
    exact funext hg

lemma fiberHomeomorph_apply (hp : IsQuotientMap p) (hq : IsQuotientMap q)
    (he : ∀ x y, p x = p y ↔ q x = q y) (x : X) :
    fiberHomeomorph hp hq he (p x) = q x :=
  (he _ _).mp (Function.rightInverse_surjInv hp.surjective _)
end SameFibers

def cuspCoordinates (a : ℝ) (ha : 1 < a) : cusp a ≃ₜ (Ioi a × AddCircle (6 : ℝ)) :=
  fiberHomeomorph (highProjection_openQuotient a).isQuotientMap
    (highCylinderProjection_openQuotient a (by linarith)).isQuotientMap
    (highProjection_sameFibers a ha)

lemma cuspCoordinates_apply (a : ℝ) (ha : 1 < a) (z : ℍ) (hz : a < z.im) :
    cuspCoordinates a ha ⟨projection z, ⟨z,hz,rfl⟩⟩ =
      (⟨z.im,hz⟩,(z.re : AddCircle (6 : ℝ))) :=
  fiberHomeomorph_apply (highProjection_openQuotient a).isQuotientMap
    (highCylinderProjection_openQuotient a (by linarith)).isQuotientMap
    (highProjection_sameFibers a ha) ⟨z,hz⟩

open Matrix ModularGroup

lemma integer_action_isometry (g : SL(2, ℤ)) : Isometry (fun z : ℍ => g • z) := by
  exact isometry_smul ℍ (SpecialLinearGroup.map (Int.castRingHom ℝ) g)

def maxIm (z : ℍ) : ℝ := (Classical.choose (exists_max_im z) • z).im
lemma maxIm_pos (z : ℍ) : 0 < maxIm z := UpperHalfPlane.im_pos _
lemma im_smul_le_maxIm (z : ℍ) (g : SL(2, ℤ)) : (g • z).im ≤ maxIm z :=
  Classical.choose_spec (exists_max_im z) g
lemma im_le_maxIm (z : ℍ) : z.im ≤ maxIm z := by
  simpa using im_smul_le_maxIm z 1

lemma maxIm_smul (g : SL(2, ℤ)) (z : ℍ) : maxIm (g • z) = maxIm z := by
  apply le_antisymm
  · exact (show ((Classical.choose (exists_max_im (g • z))) • g • z).im ≤ maxIm z by
      rw [← mul_smul]; exact im_smul_le_maxIm _ _)
  · have h := im_smul_le_maxIm (g • z) (Classical.choose (exists_max_im z) * g⁻¹)
    simpa only [mul_smul, inv_smul_smul, maxIm] using h

def logMaxIm (z : ℍ) := Real.log (maxIm z)
lemma logMaxIm_smul (g : SL(2, ℤ)) (z : ℍ) : logMaxIm (g • z) = logMaxIm z := by
  unfold logMaxIm
  rw [maxIm_smul]

lemma logMaxIm_sub_le_dist (z w : ℍ) : logMaxIm z - logMaxIm w ≤ dist z w := by
  let g := Classical.choose (exists_max_im z)
  have h : Real.log (g • w).im ≤ logMaxIm w :=
    Real.log_le_log (UpperHalfPlane.im_pos _) (im_smul_le_maxIm w g)
  have hd := UpperHalfPlane.dist_log_im_le (g • z) (g • w)
  rw [(integer_action_isometry g).dist_eq, Real.dist_eq] at hd
  have hab := (le_abs_self (Real.log (g • z).im - Real.log (g • w).im)).trans hd
  change Real.log (g • z).im - logMaxIm w ≤ _
  linarith

lemma logMaxIm_lipschitz : LipschitzWith 1 logMaxIm := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro z w
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, abs_le]
  exact ⟨by have h := logMaxIm_sub_le_dist w z; rw [dist_comm] at h; linarith,
    logMaxIm_sub_le_dist z w⟩

def height (x : Surface) : ℝ := logMaxIm (sectionMap x)

lemma height_projection (z : ℍ) : height (projection z) = logMaxIm z := by
  obtain ⟨g,hg,he⟩ := (projection_eq_iff (sectionMap (projection z)) z).mp
    (sectionMap_rightInverse (projection z))
  dsimp [height]
  rw [← he,logMaxIm_smul]

lemma height_continuous : Continuous height := by
  apply projection_cover.toIsQuotientMap.continuous_iff.mpr
  have he : height ∘ projection = logMaxIm := funext height_projection
  rw [he]
  exact logMaxIm_lipschitz.continuous

lemma maxIm_eq_im_of_high {z : ℍ} (hz : 1 < z.im) : maxIm z = z.im := by
  apply le_antisymm ?_ (im_le_maxIm z)
  let g := Classical.choose (exists_max_im z)
  by_cases hg : 1 < (g • z).im
  · have hc := bottomLeft_eq_zero_of_high g z hz hg
    obtain ⟨n,hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hc
    change (g • z).im ≤ z.im
    rw [hn z, im_T_zpow_smul]
  · change (g • z).im ≤ z.im
    linarith

lemma height_projection_high {z : ℍ} (hz : 1 < z.im) :
    height (projection z) = Real.log z.im := by
  rw [height_projection,logMaxIm,maxIm_eq_im_of_high hz]

lemma mem_cusp_iff_height {a : ℝ} (ha : 1 < a) (x : Surface) :
    x ∈ cusp a ↔ Real.log a < height x := by
  constructor
  · rintro ⟨z,hz,rfl⟩
    rw [height_projection_high (ha.trans hz)]
    exact Real.log_lt_log (by linarith) hz
  · intro hx
    obtain ⟨z,rfl⟩ := projection_cover.surjective x
    rw [height_projection,logMaxIm] at hx
    have hi : a < maxIm z := (Real.log_lt_log_iff (by linarith) (maxIm_pos z)).mp hx
    let g := Classical.choose (exists_max_im z)
    obtain ⟨n,h,hh,he⟩ := coset_representative g
    refine ⟨h • z, ?_, projection_smul h hh z⟩
    change a < (g • z).im at hi
    rw [← he,mul_smul] at hi
    have him := im_T_zpow_smul (h • z) (n.val : ℤ)
    rw [zpow_natCast] at him
    rwa [him] at hi

lemma height_sublevel_compact {a : ℝ} (ha : 1 < a) :
    IsCompact {x : Surface | height x ≤ Real.log a} := by
  have he : {x : Surface | height x ≤ Real.log a} = (cusp a)ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_cusp_iff_height ha, not_lt]
  rw [he]
  exact cusp_complement_compact a

def OpenCore (a : ℝ) := {x : Surface // height x < Real.log a}
instance (a : ℝ) : TopologicalSpace (OpenCore a) := inferInstanceAs
  (TopologicalSpace {x : Surface // height x < Real.log a})

lemma openCore_open (a : ℝ) : IsOpen {x : Surface | height x < Real.log a} :=
  isOpen_lt height_continuous continuous_const

lemma compact_core_slice {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    IsCompact {x : OpenCore b | height x.val ≤ Real.log a} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  convert height_sublevel_compact ha using 1
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩; exact hx
  · intro hy
    exact ⟨⟨y, hy.trans_lt (Real.log_lt_log (by linarith) hab)⟩,hy,rfl⟩

end

lemma height_cuspCoordinates (a : ℝ) (ha : 1 < a) (x : cusp a) :
    height x.1 = Real.log ((cuspCoordinates a ha x).1 : ℝ) := by
  obtain ⟨z,hz⟩ := (highProjection_openQuotient a).surjective x
  rw [← hz]
  change height (projection z.1) = _
  unfold highProjection
  rw [cuspCoordinates_apply a ha z.1 z.2, height_projection_high (ha.trans z.2)]

def clipCusp (a c : ℝ) (ha : 1 < a) (hac : a < c) (x : Surface) : Surface := by
  classical
  exact if hx : x ∈ cusp a then
    ((cuspCoordinates a ha).symm
      (⟨min ((cuspCoordinates a ha ⟨x,hx⟩).1 : ℝ) c,
        lt_min ((cuspCoordinates a ha ⟨x,hx⟩).1.2) hac⟩,
        (cuspCoordinates a ha ⟨x,hx⟩).2)).1
  else x

lemma clipCusp_of_mem (a c : ℝ) (ha : 1 < a) (hac : a < c)
    (x : cusp a) :
    clipCusp a c ha hac x.1 =
      ((cuspCoordinates a ha).symm
        (⟨min ((cuspCoordinates a ha x).1 : ℝ) c,
          lt_min ((cuspCoordinates a ha x).1.2) hac⟩,
          (cuspCoordinates a ha x).2)).1 := by
  simp only [clipCusp, dite_eq_left x.2]

lemma clipCusp_eq_self (a c : ℝ) (ha : 1 < a) (hac : a < c)
    {x : Surface} (hx : height x ≤ Real.log c) : clipCusp a c ha hac x = x := by
  by_cases hm : x ∈ cusp a
  · rw [clipCusp_of_mem a c ha hac ⟨x,hm⟩]
    have hy : ((cuspCoordinates a ha ⟨x,hm⟩).1 : ℝ) ≤ c := by
      rw [height_cuspCoordinates a ha ⟨x,hm⟩] at hx
      exact (Real.log_le_log_iff ((by linarith : 0 < a).trans (cuspCoordinates a ha ⟨x,hm⟩).1.2)
        (by linarith)).mp hx
    simp only [min_eq_left hy]
    exact congrArg Subtype.val ((cuspCoordinates a ha).symm_apply_apply ⟨x,hm⟩)
  · simp [clipCusp, hm]

lemma clipCusp_height_le (a c : ℝ) (ha : 1 < a) (hac : a < c) (x : Surface) :
    height (clipCusp a c ha hac x) ≤ Real.log c := by
  by_cases hm : x ∈ cusp a
  · rw [clipCusp_of_mem a c ha hac ⟨x,hm⟩]
    rw [height_cuspCoordinates a ha, Homeomorph.apply_symm_apply]
    exact Real.log_le_log (lt_min ((by linarith : 0 < a).trans (cuspCoordinates a ha ⟨x,hm⟩).1.2) (by linarith))
      (min_le_right _ _)
  · rw [clipCusp, dite_eq_right hm]
    have hx : height x ≤ Real.log a := le_of_not_gt ((mem_cusp_iff_height ha x).not.mp hm)
    exact hx.trans (Real.log_le_log (by linarith) hac.le)

lemma clipCusp_continuous_on_cusp (a c : ℝ) (ha : 1 < a) (hac : a < c) :
    Continuous (fun x : cusp a => clipCusp a c ha hac x.1) := by
  simp_rw [clipCusp_of_mem]
  apply continuous_subtype_val.comp
  apply (cuspCoordinates a ha).symm.continuous.comp
  refine Continuous.prodMk ?_ ((cuspCoordinates a ha).continuous.snd)
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.comp (cuspCoordinates a ha).continuous.fst).min continuous_const)

lemma clipCusp_continuous (a c : ℝ) (ha : 1 < a) (hac : a < c) :
    Continuous (clipCusp a c ha hac) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : height x < Real.log c
  · have he : clipCusp a c ha hac =ᶠ[𝓝 x] id := by
      filter_upwards [(isOpen_lt height_continuous continuous_const).mem_nhds hx] with y hy
      exact clipCusp_eq_self a c ha hac hy.le
    exact continuousAt_id.congr_of_eventuallyEq he
  · have hm : x ∈ cusp a := (mem_cusp_iff_height ha x).mpr
      ((Real.log_lt_log (by linarith) hac).trans_le (le_of_not_gt hx))
    have hc : ContinuousOn (clipCusp a c ha hac) (cusp a) :=
      continuousOn_iff_continuous_domRestrict.mpr (clipCusp_continuous_on_cusp a c ha hac)
    exact (hc x hm).continuousAt ((cusp_open a).mem_nhds hm)

lemma range_clipCusp (a c : ℝ) (ha : 1 < a) (hac : a < c) :
    range (clipCusp a c ha hac) = {x : Surface | height x ≤ Real.log c} := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩; exact clipCusp_height_le a c ha hac y
  · intro hx; exact ⟨x,clipCusp_eq_self a c ha hac hx⟩

lemma height_sublevel_connected {c : ℝ} (hc : 1 < c) :
    IsConnected {x : Surface | height x ≤ Real.log c} := by
  obtain ⟨a,ha,hac⟩ := exists_between hc
  rw [← range_clipCusp a c ha hac, ← image_univ]
  exact isConnected_univ.image _ (clipCusp_continuous a c ha hac).continuousOn

lemma openCore_preconnected {b : ℝ} (hb : 1 < b) :
    IsPreconnected {x : Surface | height x < Real.log b} := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  obtain ⟨r,hr,hrb⟩ := exists_between (max_lt (max_lt hx hy) (Real.log_pos hb))
  have hrpos : 0 < r := (le_max_right _ _).trans_lt hr
  let c := Real.exp r
  have hc : 1 < c := Real.one_lt_exp_iff.mpr hrpos
  have he : Real.log c = r := Real.log_exp r
  refine ⟨{z : Surface | height z ≤ Real.log c}, ?_, ?_, ?_, (height_sublevel_connected hc).2⟩
  · intro z hz; exact hz.trans_lt (he ▸ hrb)
  · change height x ≤ Real.log c
    rw [he]
    exact ((le_max_left _ _).trans (le_max_left _ _)).trans hr.le
  · change height y ≤ Real.log c
    rw [he]
    exact ((le_max_right _ _).trans (le_max_left _ _)).trans hr.le

lemma openCore_nonempty {b : ℝ} (hb : 1 < b) : Nonempty (OpenCore b) := by
  obtain ⟨c,hc,hcb⟩ := exists_between hb
  let z : ℍ := ⟨⟨0,c⟩, by linarith⟩
  refine ⟨⟨projection z, ?_⟩⟩
  rw [height_projection_high (show 1 < z.im from hc)]
  exact Real.log_lt_log (show 0 < z.im from by dsimp [z]; linarith) hcb

lemma openCore_connected {b : ℝ} (hb : 1 < b) : ConnectedSpace (OpenCore b) := by
  let : Nonempty (OpenCore b) := openCore_nonempty hb
  have : PreconnectedSpace (OpenCore b) := Subtype.preconnectedSpace (openCore_preconnected hb)
  exact ⟨inferInstance⟩

end ThreeManifold.HyperbolicCore

end

end OAI


