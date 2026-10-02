-- Prove2me | Definitions.Def_AnosovPlugs_Section5
-- name    : AnosovPlugs_Section5
-- status  : Definition
-- author  : @ebayuser
-- created : 2026-10-02T09:53:14.229233+00:00
-- url     : https://prove2.me/theorems/119c42ce-9bd5-48ad-9d61-ce82c5dffb3c
-- title:
--   Anosov plugs VIII: crossing and return maps, invariant foliations, normal form, cone fields (Section 5 objects)
-- statement:
--   Objects used in Section 5 of Béguin–Bonatti–Yu (arXiv:1408.3951v1; Section 6 of the published version), on top of the mission's definition layers I to V.
--
--   Let $(U,X)$ be a plug. The **crossing map** $\Gamma$ (Definition 2.13) sends a point $x$ of the entrance boundary $\partial^{in}U$ that is not in the entrance lamination $L^s$ to the first point where its forward orbit reaches the exit boundary $\partial^{out}U$; the **crossing time** is the corresponding first positive time. For a gluing map $\psi:\partial^{out}U\to\partial^{in}U$ the **return map** is
--   $$\Theta_\psi:=\psi\circ\Gamma:\ \partial^{in}U\setminus L^s\longrightarrow\partial^{in}U .$$
--
--   A **two-dimensional foliation** of the 3-manifold $U$ is given by a foliated atlas: smooth charts covering $U$, with convex images, whose changes of coordinates locally preserve the third coordinate; plaques are the level sets of that coordinate, leaves are plaque chains, and the **tangent plane** at a point is the kernel of the differential of the third coordinate. A foliation **induces** on $\partial^{in}U$ (resp. $\partial^{out}U$) the one-dimensional foliation whose leaf through $p$ is the path component of $p$ in (leaf of $p$) $\cap\,\partial^{in}U$, with tangent line the intersection of the tangent plane with the tangent plane of the boundary. A foliation is **$X$-invariant** when every orbit segment stays in the leaf of its starting point.
--
--   The **normal form** of Proposition 4.2, `IsNormalForm X φ₁ As Au`, packages: two invariant foliations $\mathcal G^s,\mathcal G^u$ transverse to each other; $W^s(\Lambda)$ is a union of leaves of $\mathcal G^s$ and $W^u(\Lambda)$ a union of leaves of $\mathcal G^u$ (sublaminations); every compact leaf of $\mathcal G^s_{in}$ and of $\mathcal G^u_{out}$ has holonomy conjugate to a homothety of ratio $\mu$, $\mu\neq0$, $|\mu|\neq1$, along a $C^1$ transverse arc (`HasHomotheticHolonomy`; a negative ratio covers one-sided compact leaves on non-orientable boundary components); and $(\varphi_1)_*\mathcal G^u_{out}$ is transverse to $\mathcal G^s_{in}$.
--
--   A **cone field** on a set $S\subset\partial^{in}U$ is given by symmetric matrices $Q(x)$: the cone at $x$ is $\{v\in T_x\partial^{in}U : v^{\mathsf T}Q(x)v\ge 0\}$, and continuity is continuity of the quadratic form on the tangent bundle over $S$ (`IsConeField`, `cone`). `ConeFieldHypotheses X ψ As Au Qs Qu` is the hypothesis block of Lemma 5.1 for $\Theta_\psi$: for some continuous Riemannian metric and some $\mu>1$, $d\Theta_\psi$ maps $C^u$ into $C^u$ and expands its vectors by $\mu$, the preimage of $C^s$ lies in $C^s$ and $d\Theta_\psi^{-1}$ expands it by $\mu$ (stated without inverses); $C^u$ contains the directions of $\mathcal G^u_{in}$ and $\psi_*\mathcal G^u_{out}$ and meets the directions of $\mathcal G^s_{in}$ and $\psi_*\mathcal G^s_{out}$ only in $0$, and $C^s$ contains the directions of $\mathcal G^s_{in}$ and $\psi_*\mathcal G^s_{out}$ and meets the direction of $\psi_*\mathcal G^u_{out}$ only in $0$. Lemma 5.1 also lists two further exclusions ($\psi_*\mathcal G^s_{out}$ from $C^u$ and $\mathcal G^u_{in}$ from $C^s$); its proof does not use them and they are not part of this block.
--
--   `Prop52Data X g As Au λ ε ψin ψout` is the conclusion block of Proposition 5.2 for a Riemannian metric $g$: $\psi^{in}$ (resp. $\psi^{out}$) is a diffeomorphism of $\partial^{in}U$ (resp. $\partial^{out}U$), equal to the identity near $L^s$ (resp. $L^u$), preserving each leaf of $\mathcal G^u_{in}$ (resp. $\mathcal G^s_{out}$), with $(\psi^{in})^{-1}_*\mathcal G^s_{in}$ (resp. $(\psi^{out})_*\mathcal G^u_{out}$) $\varepsilon$-close to $\mathcal G^s_{in}$ (resp. $\mathcal G^u_{out}$) in the sense that their tangent lines contain $g$-unit vectors at $g$-distance $<\varepsilon$ (`LinesClose`), and $\Gamma\circ\psi^{in}$ expands nonzero vectors tangent to $\mathcal G^u_{in}$ by more than $\lambda$ while the inverse of $\psi^{out}\circ\Gamma$ expands nonzero vectors tangent to $\mathcal G^s_{out}$ by more than $\lambda$.
--
--   **Formalization Note** Tangent vectors are written in the half-space chart at their base point, as in the mission's `normalCoord`; the boundary tangent plane is $\{v_0=0\}$ (`boundaryTangent`). Derivatives along a boundary surface are `mfderivWithin`, which is determined on vectors tangent to the surface; every statement applies them only to such vectors. The crossing map is a junk value on $L^s$ and is only used on $\partial^{in}U\setminus L^s$. "$\varepsilon$-$C^1$-close foliations" is encoded as $\varepsilon$-closeness of tangent lines at each point.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837 (arXiv:1408.3951v1): Definition 2.13 (crossing map, p. 10), Section 5 intro and Lemma 5.1 (pp. 21–22), Proposition 4.2 (p. 18), Proposition 5.2 (p. 23). Item numbers follow arXiv v1; the published version shifts section numbers by one.

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

/-!
Béguin–Bonatti–Yu, *Building Anosov flows on 3-manifolds*, arXiv:1408.3951v1 (Geom. Topol. 21
(2017)). Objects used in Section 5 of arXiv v1: the crossing map (Definition 2.13) and the return
map, two-dimensional foliations of a 3-manifold with boundary and the foliations that they induce
on the boundary, the normal form of Proposition 4.2, cone fields and the hypotheses of Lemma 5.1,
and the conclusion of Proposition 5.2.

Tangent vectors are written in the chart at their base point, as in `normalCoord`. The model is
the half-space `{x₀ ≥ 0}`, so at a boundary point the tangent plane of the boundary is the plane
`{v₀ = 0}`. Norms of tangent vectors are the norms of `EuclideanSpace ℝ (Fin 3)` in these charts.
-/

open scoped Manifold ContDiff Topology
open Set Filter Function

namespace AnosovPlugs

variable {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
  [IsManifold I3 ∞ U]

section CrossingMap

/-- The crossing time of `x` (Definition 2.13 of arXiv:1408.3951v1): the first positive time at
which the forward orbit of `x` is in the exit boundary. For `x ∈ ∂^{in} U ∖ L^s` this time is
finite and positive. -/
noncomputable def crossingTime (X : (x : U) → TangentSpace I3 x) (x : U) : ℝ :=
  sInf {t | 0 < t ∧ FlowDefined X x t ∧ flowMap X t x ∈ outBoundary X}

/-- The crossing map `Γ` (Definition 2.13 of arXiv:1408.3951v1): the point `Γ(x)` where the
forward orbit of `x ∈ ∂^{in} U ∖ L^s` reaches the exit boundary `∂^{out} U ∖ L^u`. -/
noncomputable def crossingMap (X : (x : U) → TangentSpace I3 x) (x : U) : U :=
  flowMap X (crossingTime X x) x

/-- The return map `Θ_ψ = ψ ∘ Γ` on `∂^{in} U ∖ L^s` for a gluing map
`ψ : ∂^{out} U → ∂^{in} U` (Section 5 and Lemma 5.1 of arXiv:1408.3951v1). -/
noncomputable def returnMap (X : (x : U) → TangentSpace I3 x) (ψ : U → U) (x : U) : U :=
  ψ (crossingMap X x)

end CrossingMap

/-- The tangent plane of the boundary in the chart at a boundary point: the vectors `v` with
`v₀ = 0`. This uses the same convention as `normalCoord`. -/
noncomputable def boundaryTangent : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (0 : Fin 3))

section Foliation

/-- `A` is an atlas of a smooth two-dimensional foliation of the 3-manifold `U` (possibly with
boundary), used for the foliations `G^s`, `G^u` of Proposition 4.2 of arXiv:1408.3951v1. The
charts are in the smooth maximal atlas of `U`, they cover `U`, each chart has a convex image in
`ℝ³`, and the changes of coordinates locally preserve the third coordinate `x₂`. The plaques are
the level sets of `x₂` in a chart. They are transverse to the boundary `{x₀ = 0}`. -/
def IsFoliatedAtlas3 (A : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3))) : Prop :=
  A ⊆ IsManifold.maximalAtlas I3 ∞ U ∧ (∀ x : U, ∃ e ∈ A, x ∈ e.source) ∧
    (∀ e ∈ A, Convex ℝ ((fun z : EuclideanHalfSpace 3 => z.1) '' e.target)) ∧
    ∀ e ∈ A, ∀ e' ∈ A, ∀ z ∈ (e.symm.trans e').source, ∀ᶠ w in 𝓝 z,
      w ∈ (e.symm.trans e').source →
        w.1 2 = z.1 2 → (e.symm.trans e' w).1 2 = (e.symm.trans e' z).1 2

/-- Two points lie on a common plaque of the foliated atlas `A`: some chart of `A` contains both
points and gives them the same third coordinate. -/
def SamePlaque3 (A : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3))) (a b : U) : Prop :=
  ∃ e ∈ A, a ∈ e.source ∧ b ∈ e.source ∧
    (e a).1 2 = (e b).1 2

/-- The leaf through `p` of the two-dimensional foliation given by `A`: the points that a finite
chain of plaques connects to `p`. -/
def foliationLeaf3 (A : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3))) (p : U) : Set U :=
  {q | Relation.ReflTransGen (SamePlaque3 A) p q}

/-- The tangent plane at `x` of the foliation given by `A`: the vectors that the differential of
the third coordinate of every chart of `A` at `x` sends to `0`. -/
noncomputable def tangentPlane (A : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3)))
    (x : U) : Submodule ℝ (TangentSpace I3 x) :=
  ⨅ e ∈ A, ⨅ (_ : x ∈ e.source), LinearMap.ker
    (mfderiv I3 𝓘(ℝ, ℝ)
      (fun y => (e y).1 2) x).toLinearMap

/-- The leaf through `p` of the one-dimensional foliation induced by `A` on the entrance boundary
(for example `G^s_in` and `G^u_in` in Section 5 of arXiv:1408.3951v1): the path component of `p`
in the intersection of the leaf of `A` through `p` with `∂^{in} U`. -/
def inducedLeaf (X : (x : U) → TangentSpace I3 x)
    (A : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3))) (p : U) : Set U :=
  pathComponentIn (foliationLeaf3 A p ∩ inBoundary X) p

/-- The leaf through `p` of the one-dimensional foliation induced by `A` on the exit boundary
(for example `G^s_out` and `G^u_out` in Section 5 of arXiv:1408.3951v1). -/
def exitInducedLeaf (X : (x : U) → TangentSpace I3 x)
    (A : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3))) (p : U) : Set U :=
  pathComponentIn (foliationLeaf3 A p ∩ outBoundary X) p

/-- The tangent line at a boundary point `x` of the one-dimensional foliation induced by `A` on
the boundary: the intersection of the tangent plane of `A` with the tangent plane of the
boundary. -/
noncomputable def inducedLine (A : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3)))
    (x : U) : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  tangentPlane A x ⊓ boundaryTangent

/-- The foliation given by `A` is invariant under the flow of `X`: every orbit segment stays in
one leaf. -/
def IsInvariantFoliation (X : (x : U) → TangentSpace I3 x)
    (A : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3))) : Prop :=
  ∀ (x : U) (t : ℝ), FlowDefined X x t → flowMap X t x ∈ foliationLeaf3 A x

end Foliation

section Holonomy

variable {T : Type} [TopologicalSpace T]

/-- The holonomy along the loop `c` (for the leaves `leaf`), on the transverse arc `τ` through
`c 0 = τ 0`, is conjugate to a homothety (Proposition 4.2, third item, of arXiv:1408.3951v1).
The data `ε`, `h`, `H` are as in `HasContractingHolonomy`. In addition there are a C¹
diffeomorphism `θ` of the transverse parameter with `θ 0 = 0` and `θ' > 0` on `[-ε, ε]`, and a
real `μ` with `μ ≠ 0` and `|μ| ≠ 1`, such that `θ (h s) = μ θ(s)` for `s ∈ [-ε, ε]`. A negative
`μ` is allowed: the holonomy of a one-sided compact leaf reverses the orientation of the arc. -/
def HasHomotheticHolonomy (leaf : T → Set T) (c τ : ℝ → T) : Prop :=
  c 0 = τ 0 ∧ ∃ ε > (0 : ℝ), ∃ h : ℝ → ℝ, ∃ H : ℝ × ℝ → T,
    ContinuousOn H (Icc 0 1 ×ˢ Icc (-ε) ε) ∧ (∀ u ∈ Icc (0 : ℝ) 1, H (u, 0) = c u) ∧
    (∀ s ∈ Icc (-ε) ε, H (0, s) = τ s ∧ H (1, s) = τ (h s) ∧
      ∀ u ∈ Icc (0 : ℝ) 1, H (u, s) ∈ leaf (τ s)) ∧
    ∃ θ : ℝ → ℝ, ContDiff ℝ 1 θ ∧ StrictMono θ ∧ θ 0 = 0 ∧
      (∀ s ∈ Icc (-ε) ε, 0 < deriv θ s) ∧
      ∃ μ : ℝ, μ ≠ 0 ∧ |μ| ≠ 1 ∧ ∀ s ∈ Icc (-ε) ε, θ (h s) = μ * θ s

end Holonomy

section NormalForm

/-- The normal form of Proposition 4.2 of arXiv:1408.3951v1 for the plug `(U, X)` with gluing
map `φ₁`, with foliations `G^s`, `G^u` given by the atlases `As`, `Au`:
* `G^s` and `G^u` are smooth two-dimensional foliations, invariant under `X`, and transverse to
  each other;
* `W^s(Λ)` is a sublamination of `G^s`, and `W^u(Λ)` is a sublamination of `G^u`;
* the holonomy of each compact leaf of `G^s_in` and of `G^u_out` is conjugate to a homothety.
  The compact leaf has a loop parametrisation `c` (as in `IsLoopParam`), and the transverse arc
  `τ` is C¹ and transverse to the leaf at `c 0`, as in `IsContractingOrientation`;
* the image of `G^u_out` by `φ₁` is transverse to `G^s_in`. -/
def IsNormalForm (X : (x : U) → TangentSpace I3 x) (φ₁ : U → U)
    (As Au : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3))) : Prop :=
  IsFoliatedAtlas3 As ∧ IsFoliatedAtlas3 Au ∧
    IsInvariantFoliation X As ∧ IsInvariantFoliation X Au ∧
    (∀ x : U, tangentPlane As x ⊔ tangentPlane Au x = ⊤) ∧
    (∀ p ∈ maxInvSet X, ∀ q ∈ weakStableSet X p, foliationLeaf3 As q ⊆ weakStableSet X p) ∧
    (∀ p ∈ maxInvSet X, ∀ q ∈ weakStableSet (fun x => -X x) p,
      foliationLeaf3 Au q ⊆ weakStableSet (fun x => -X x) p) ∧
    (∀ p ∈ inBoundary X, IsCompact (inducedLeaf X As p) → ∃ c τ : ℝ → U,
      Continuous c ∧ Periodic c 1 ∧ InjOn c (Ico 0 1) ∧ range c = inducedLeaf X As p ∧ range τ ⊆ inBoundary X ∧
      ContMDiff 𝓘(ℝ, ℝ) I3 1 c ∧ ContMDiff 𝓘(ℝ, ℝ) I3 1 τ ∧
      LinearIndependent ℝ ![(mfderiv 𝓘(ℝ, ℝ) I3 c 0 1 : EuclideanSpace ℝ (Fin 3)),
        (mfderiv 𝓘(ℝ, ℝ) I3 τ 0 1 : EuclideanSpace ℝ (Fin 3))] ∧
      HasHomotheticHolonomy (inducedLeaf X As) c τ) ∧
    (∀ p ∈ outBoundary X, IsCompact (exitInducedLeaf X Au p) → ∃ c τ : ℝ → U,
      Continuous c ∧ Periodic c 1 ∧ InjOn c (Ico 0 1) ∧ range c = exitInducedLeaf X Au p ∧ range τ ⊆ outBoundary X ∧
      ContMDiff 𝓘(ℝ, ℝ) I3 1 c ∧ ContMDiff 𝓘(ℝ, ℝ) I3 1 τ ∧
      LinearIndependent ℝ ![(mfderiv 𝓘(ℝ, ℝ) I3 c 0 1 : EuclideanSpace ℝ (Fin 3)),
        (mfderiv 𝓘(ℝ, ℝ) I3 τ 0 1 : EuclideanSpace ℝ (Fin 3))] ∧
      HasHomotheticHolonomy (exitInducedLeaf X Au) c τ) ∧
    ∀ p ∈ inBoundary X,
      CurvesTransverseAt (pushLeaf φ₁ (outBoundary X) (exitInducedLeaf X Au) p)
        (inducedLeaf X As p) p

end NormalForm

section ConeFields

/-- `Q` is a continuous field of symmetric matrices on `S`: each `Q x` is symmetric, and the
quadratic form `v ↦ vᵀ (Q x) v` is continuous on the tangent bundle over `S`. Continuity is
stated on the tangent bundle, so it does not depend on the charts. The quadratic forms `Q x`
define the cones `cone Q x` of a continuous cone field (Lemma 5.1 of arXiv:1408.3951v1). -/
def IsConeField (Q : U → Matrix (Fin 3) (Fin 3) ℝ) (S : Set U) : Prop :=
  (∀ x ∈ S, (Q x).IsSymm) ∧
    ContinuousOn (fun p : TangentBundle I3 U =>
        WithLp.ofLp p.2 ⬝ᵥ (Q p.proj).mulVec (WithLp.ofLp p.2))
      {p : TangentBundle I3 U | p.proj ∈ S}

/-- The cone at `x` of the cone field given by `Q`: the vectors `v` tangent to the boundary with
`vᵀ (Q x) v ≥ 0`. -/
def cone (Q : U → Matrix (Fin 3) (Fin 3) ℝ) (x : U) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {v | v ∈ boundaryTangent ∧ 0 ≤ WithLp.ofLp v ⬝ᵥ (Q x).mulVec (WithLp.ofLp v)}

/-- The hypotheses of Lemma 5.1 of arXiv:1408.3951v1 for the return map `Θ_ψ = ψ ∘ Γ`, the
foliations given by `As`, `Au`, and the cone fields `C^s_in`, `C^u_in` given by `Qs`, `Qu`.
Here `D x` is the derivative of `Θ_ψ` at `x` along `∂^{in} U ∖ L^s`.
* For some continuous Riemannian metric `g` and some `μ > 1`: `D` maps `C^u_in` into `C^u_in`
  and expands its vectors by `μ`; the preimage under `D` of `C^s_in` is in `C^s_in`, and `D⁻¹`
  expands the vectors of `C^s_in` by `μ`. The statements about `D⁻¹` use no inverse.
* `C^u_in` contains the directions of `G^u_in` and of `ψ_*(G^u_out)`, and it contains no
  nonzero vector tangent to `G^s_in`.
* `C^s_in` contains the directions of `G^s_in` and of `ψ_*(G^s_out)`, and it contains no
  nonzero vector tangent to `ψ_*(G^u_out)`.
Lemma 5.1 also lists the exclusions of `ψ_*(G^s_out)` from `C^u_in` and of `G^u_in` from
`C^s_in`. Its proof does not use them, and they are not stated here. -/
def ConeFieldHypotheses (X : (x : U) → TangentSpace I3 x) (ψ : U → U)
    (As Au : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3)))
    (Qs Qu : U → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  let D := fun x : U =>
    mfderivWithin I3 I3 (returnMap X ψ) (inBoundary X \ entranceLamination X) x
  (∃ g : RiemannianMetric3 U, ∃ μ > (1 : ℝ), ∀ x ∈ inBoundary X \ entranceLamination X,
      (∀ v ∈ cone Qu x, (D x v : EuclideanSpace ℝ (Fin 3)) ∈ cone Qu (returnMap X ψ x)) ∧
      (∀ v ∈ cone Qu x, μ * g.norm x v ≤ g.norm (returnMap X ψ x) (D x v)) ∧
      (∀ v ∈ boundaryTangent,
        (D x v : EuclideanSpace ℝ (Fin 3)) ∈ cone Qs (returnMap X ψ x) → v ∈ cone Qs x) ∧
      (∀ v ∈ boundaryTangent, (D x v : EuclideanSpace ℝ (Fin 3)) ∈ cone Qs (returnMap X ψ x) →
        μ * g.norm (returnMap X ψ x) (D x v) ≤ g.norm x v)) ∧
    ∀ x ∈ inBoundary X,
      (∀ v ∈ inducedLine Au x, v ∈ cone Qu x) ∧
      (∀ y ∈ outBoundary X, ψ y = x →
        ∀ v ∈ (inducedLine Au y).map (mfderivWithin I3 I3 ψ (outBoundary X) y).toLinearMap,
          v ∈ cone Qu x) ∧
      (∀ v ∈ inducedLine As x, v ∈ cone Qu x → v = 0) ∧
      (∀ v ∈ inducedLine As x, v ∈ cone Qs x) ∧
      (∀ y ∈ outBoundary X, ψ y = x →
        ∀ v ∈ (inducedLine As y).map (mfderivWithin I3 I3 ψ (outBoundary X) y).toLinearMap,
          v ∈ cone Qs x) ∧
      (∀ y ∈ outBoundary X, ψ y = x →
        ∀ v ∈ (inducedLine Au y).map (mfderivWithin I3 I3 ψ (outBoundary X) y).toLinearMap,
          v ∈ cone Qs x → v = 0)

end ConeFields

section Prop52

/-- The lines `L₁`, `L₂` in the tangent space at `x` are `eps`-close for the Riemannian metric
`g`: they contain `g`-unit vectors at `g`-distance less than `eps`. -/
def LinesClose (g : RiemannianMetric3 U) (x : U)
    (L₁ L₂ : Submodule ℝ (TangentSpace I3 x)) (eps : ℝ) : Prop :=
  ∃ u ∈ L₁, ∃ w ∈ L₂, g.norm x u = 1 ∧ g.norm x w = 1 ∧ g.norm x (u - w) < eps

/-- The conclusion of Proposition 5.2 of arXiv:1408.3951v1 for the Riemannian metric `g`, the
constants `lam > 1`, `eps > 0`, the foliations `G^s`, `G^u` given by `As`, `Au`, and the maps
`ψin`, `ψout`.
* `ψin` is a diffeomorphism of `∂^{in} U`. It is the identity on a neighbourhood of `L^s`, it
  preserves each leaf of `G^u_in`, the foliation `(ψin)⁻¹_*(G^s_in)` is `eps`-close to
  `G^s_in`, and `Γ ∘ ψin` expands the nonzero vectors tangent to `G^u_in` by more than `lam`.
* `ψout` is a diffeomorphism of `∂^{out} U`. It is the identity on a neighbourhood of `L^u`,
  it preserves each leaf of `G^s_out`, the foliation `(ψout)_*(G^u_out)` is `eps`-close to
  `G^u_out`, and the inverse of the exit-side composition `ψout ∘ Γ` expands the nonzero vectors
  tangent to `G^s_out` by more than `lam`.
The closeness of two foliations is the `eps`-closeness of their tangent lines at each point.
Norms are taken for `g`. -/
def Prop52Data (X : (x : U) → TangentSpace I3 x) (g : RiemannianMetric3 U)
    (As Au : Set (OpenPartialHomeomorph U (EuclideanHalfSpace 3))) (lam eps : ℝ)
    (ψin ψout : U → U) : Prop :=
  (IsBoundaryDiffeo ψin (inBoundary X) (inBoundary X) ∧
    (∃ O ∈ 𝓝ˢ (entranceLamination X), ∀ x ∈ O ∩ inBoundary X, ψin x = x) ∧
    (∀ x ∈ inBoundary X, ψin x ∈ inducedLeaf X Au x) ∧
    (∀ x ∈ inBoundary X,
      LinesClose g x ((inducedLine As (ψin x)).comap
          (mfderivWithin I3 I3 ψin (inBoundary X) x).toLinearMap ⊓ boundaryTangent)
        (inducedLine As x) eps) ∧
    ∀ x ∈ inBoundary X \ entranceLamination X, ∀ v ∈ inducedLine Au x, v ≠ 0 →
      lam * g.norm x v <
        g.norm (crossingMap X (ψin x))
          (mfderivWithin I3 I3 (crossingMap X ∘ ψin) (inBoundary X) x v)) ∧
  (IsBoundaryDiffeo ψout (outBoundary X) (outBoundary X) ∧
    (∃ O ∈ 𝓝ˢ (exitLamination X), ∀ x ∈ O ∩ outBoundary X, ψout x = x) ∧
    (∀ x ∈ outBoundary X, ψout x ∈ exitInducedLeaf X As x) ∧
    (∀ x ∈ outBoundary X,
      LinesClose g (ψout x) ((inducedLine Au x).map
          (mfderivWithin I3 I3 ψout (outBoundary X) x).toLinearMap)
        (inducedLine Au (ψout x)) eps) ∧
    ∀ x ∈ inBoundary X \ entranceLamination X, ∀ v ∈ inducedLine As (ψout (crossingMap X x)),
      v ≠ 0 → ∀ w ∈ boundaryTangent,
        mfderivWithin I3 I3 (ψout ∘ crossingMap X) (inBoundary X) x w = v →
          lam * g.norm (ψout (crossingMap X x)) v < g.norm x w)

end Prop52

end AnosovPlugs


