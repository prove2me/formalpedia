-- Prove2me | Definitions.Def_AnosovPlugs_Surfaces
-- name    : AnosovPlugs_Surfaces
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-01T02:20:19.888373+00:00
-- url     : https://prove2.me/theorems/0185ce0c-78c4-4f2d-80c4-44792650b2d0
-- title:
--   Anosov plugs VI: MS foliations of surfaces, contracting holonomy, incoherent attractors
-- statement:
--   1. **Orientable surface**: a smooth surface with an atlas whose transition maps have positive Jacobian.
--   2. **Foliated atlas**: charts onto $(-1,1)^2$ covering $S$ whose coordinate changes locally preserve horizontal lines (plaques). The **leaf** through $p$ is the set of points reachable from $p$ by a finite chain of plaques.
--   3. **Contracting holonomy.** For a compact leaf $K$ parametrised as a loop $c$ and a transverse arc $\tau$ through $c(0)$, the holonomy is a contraction if there is a continuous family of paths $u\mapsto H(u,s)$ inside the leaf through $\tau(s)$, from $\tau(s)$ to $\tau(h(s))$, deforming $c$, with $|h(s)|<|s|$ for small $s\neq0$.
--   4. **MS foliation** (Definition 3.9): finitely many compact leaves; every half leaf is asymptotic to a compact leaf; each compact leaf can be oriented so that its holonomy is a contraction.
--   5. **Incoherent attractor** (§1.4.2): an attracting plug whose entrance foliation has two compact leaves in the same component of $\partial^{in}U$ which, with their contracting orientations, are not freely homotopic.
--
--   **Formalization Note** Foliations of abstract surfaces are topological (C⁰); for the entrance lamination of a plug, transverse arcs are taken C¹ with velocity independent of the leaf's velocity. Free homotopy is taken inside the entrance boundary $\partial^{in}U$.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, Definition 3.9 (p. 1855), §1.4.2 (Theorem 1.10, Corollary 1.11 and the definition of incoherent attractors, p. 1845)

import Mathlib
import Definitions.Def_AnosovPlugs_Plugs

/-!
Béguin–Bonatti–Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017).
One-dimensional foliations of closed surfaces, MS foliations (Definition 3.9), contracting
holonomy of compact leaves, and incoherent attractors (§1.4.2).
-/

open scoped Manifold ContDiff Topology
open Set Filter Function

namespace AnosovPlugs

section Surface

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]

/-- The surface `S` is orientable: it admits an atlas of charts from its smooth maximal atlas,
covering `S`, all of whose transition maps have positive Jacobian determinant. -/
def IsOrientableSurface (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] : Prop :=
  ∃ A : Set (OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2))),
    A ⊆ IsManifold.maximalAtlas (𝓡 2) ∞ S ∧ (∀ x : S, ∃ e ∈ A, x ∈ e.source) ∧
    ∀ e ∈ A, ∀ e' ∈ A, ∀ x ∈ e.source ∩ e'.source,
      0 < LinearMap.det
        (fderiv ℝ (e' ∘ e.symm) (e x) :
          EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))

/-- `A` is an atlas of a (topological) one-dimensional foliation of `S`: charts onto the open
square `(-1,1)²` covering `S`, whose changes of coordinates locally preserve the horizontal
lines (the plaques). -/
def IsFoliatedAtlas (A : Set (OpenPartialHomeomorph S (ℝ × ℝ))) : Prop :=
  (∀ x : S, ∃ e ∈ A, x ∈ e.source) ∧ (∀ e ∈ A, e.target = Ioo (-1) 1 ×ˢ Ioo (-1) 1) ∧
    ∀ e ∈ A, ∀ e' ∈ A, ∀ z ∈ (e.symm.trans e').source, ∀ᶠ w in 𝓝 z,
      w ∈ (e.symm.trans e').source → w.2 = z.2 → (e.symm.trans e' w).2 = (e.symm.trans e' z).2

/-- Two points lie on a common plaque of the foliated atlas `A`. -/
def SamePlaque (A : Set (OpenPartialHomeomorph S (ℝ × ℝ))) (a b : S) : Prop :=
  ∃ e ∈ A, a ∈ e.source ∧ b ∈ e.source ∧ (e a).2 = (e b).2

/-- The leaf through `p` of the foliation defined by `A`: the points reachable from `p` by a
finite chain of plaques. -/
def foliationLeaf (A : Set (OpenPartialHomeomorph S (ℝ × ℝ))) (p : S) : Set S :=
  {q | Relation.ReflTransGen (SamePlaque A) p q}

/-- `τ` is a transverse arc at `τ 0`: `τ([-1,1])` lies in a foliated chart `e ∈ A` in which `τ`
is a vertical segment traversed monotonically. -/
def IsTransverseArc (A : Set (OpenPartialHomeomorph S (ℝ × ℝ))) (τ : ℝ → S) : Prop :=
  ∃ e ∈ A, τ '' Icc (-1) 1 ⊆ e.source ∧ StrictMonoOn (fun s => (e (τ s)).2) (Icc (-1) 1) ∧
    ∀ s ∈ Icc (-1 : ℝ) 1, (e (τ s)).1 = (e (τ 0)).1

end Surface

section Holonomy

variable {X : Type} [TopologicalSpace X]

/-- `c : ℝ → X` is a loop parametrising `K` once: continuous, `1`-periodic, injective on
`[0,1)`, with image `K`. -/
def IsLoopParam (c : ℝ → X) (K : Set X) : Prop :=
  Continuous c ∧ Periodic c 1 ∧ InjOn c (Ico 0 1) ∧ range c = K

/-- The holonomy along the loop `c` (with respect to the leaves `leaf`), computed on the
transverse arc `τ` through `c 0 = τ 0`, is a contraction: there are `ε > 0`, a map `h` and a
continuous `H : [0,1] × [-ε, ε] → X` with `H(u, 0) = c(u)`, `H(0, s) = τ(s)`,
`H(1, s) = τ(h s)`, each path `u ↦ H(u, s)` contained in the leaf through `τ(s)`, and
`|h(s)| < |s|` for `0 < |s| ≤ ε`. -/
def HasContractingHolonomy (leaf : X → Set X) (c τ : ℝ → X) : Prop :=
  c 0 = τ 0 ∧ ∃ ε > (0 : ℝ), ∃ h : ℝ → ℝ, ∃ H : ℝ × ℝ → X,
    ContinuousOn H (Icc 0 1 ×ˢ Icc (-ε) ε) ∧ (∀ u ∈ Icc (0 : ℝ) 1, H (u, 0) = c u) ∧
    (∀ s ∈ Icc (-ε) ε, H (0, s) = τ s ∧ H (1, s) = τ (h s) ∧
      ∀ u ∈ Icc (0 : ℝ) 1, H (u, s) ∈ leaf (τ s)) ∧
    ∀ s ∈ Icc (-ε) ε, s ≠ 0 → |h s| < |s|

/-- Two loops `c₁, c₂` (`1`-periodic maps) are freely homotopic inside the set `T`. -/
def FreelyHomotopicIn (T : Set X) (c₁ c₂ : ℝ → X) : Prop :=
  ∃ H : ℝ × ℝ → X, ContinuousOn H (Icc 0 1 ×ˢ univ) ∧ (∀ s, H (0, s) = c₁ s) ∧
    (∀ s, H (1, s) = c₂ s) ∧ (∀ u ∈ Icc (0 : ℝ) 1, ∀ s, H (u, s + 1) = H (u, s)) ∧
    ∀ u ∈ Icc (0 : ℝ) 1, ∀ s, H (u, s) ∈ T

end Holonomy

section MSFoliation

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]

/-- Definition 3.9: the foliation given by `A` is an MS foliation:
1. it has finitely many compact leaves;
2. every half leaf is asymptotic to a compact leaf: for every non-compact leaf, parametrised
   continuously and injectively by `c : ℝ → S`, each of its two ends accumulates exactly on a
   compact leaf (`⋂_T closure c([T, ∞)) ` and `⋂_T closure c((-∞, T])` are compact leaves);
3. each compact leaf may be oriented (parametrised as a loop `c`) so that its holonomy (on some
   transverse arc) is a contraction. -/
def IsMSFoliation (A : Set (OpenPartialHomeomorph S (ℝ × ℝ))) : Prop :=
  IsFoliatedAtlas A ∧
    {L : Set S | ∃ p, L = foliationLeaf A p ∧ IsCompact L}.Finite ∧
    (∀ p, ¬ IsCompact (foliationLeaf A p) → ∀ c : ℝ → S, Continuous c → Injective c →
      range c = foliationLeaf A p →
        (∃ q, IsCompact (foliationLeaf A q) ∧
          ⋂ T : ℝ, closure (c '' Ici T) = foliationLeaf A q) ∧
        (∃ q, IsCompact (foliationLeaf A q) ∧
          ⋂ T : ℝ, closure (c '' Iic T) = foliationLeaf A q)) ∧
    ∀ p, IsCompact (foliationLeaf A p) → ∃ c τ : ℝ → S,
      IsLoopParam c (foliationLeaf A p) ∧ IsTransverseArc A τ ∧
        HasContractingHolonomy (foliationLeaf A) c τ

end MSFoliation

section Incoherent

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold I3 ∞ M]

/-- A contracting orientation of a compact leaf `K` of the entrance lamination of `X`: a C¹
regular loop `c` parametrising `K`, and a C¹ arc `τ` in the entrance boundary through `c 0`,
transverse to `K` there, along which the holonomy of the entrance lamination is a
contraction. -/
def IsContractingOrientation (X : (x : M) → TangentSpace I3 x) (K : Set M) (c : ℝ → M) :
    Prop :=
  IsLoopParam c K ∧ ContMDiff 𝓘(ℝ, ℝ) I3 1 c ∧ ∃ τ : ℝ → M, range τ ⊆ inBoundary X ∧
    ContMDiff 𝓘(ℝ, ℝ) I3 1 τ ∧
    LinearIndependent ℝ ![(mfderiv 𝓘(ℝ, ℝ) I3 c 0 1 : EuclideanSpace ℝ (Fin 3)),
      (mfderiv 𝓘(ℝ, ℝ) I3 τ 0 1 : EuclideanSpace ℝ (Fin 3))] ∧
    HasContractingHolonomy (entranceLeaf X) c τ

/-- The maximal invariant set (attractor) of the attracting plug `(M, X)` is incoherent (§1.4.2):
there are two compact leaves `K₁, K₂` of the entrance lamination in the same connected component
of `∂^{in} M` which, endowed with contracting orientations, are not freely homotopic in
`∂^{in} M`. -/
def IsIncoherent (X : (x : M) → TangentSpace I3 x) : Prop :=
  ∃ p₁ ∈ entranceLamination X, ∃ p₂ ∈ entranceLamination X,
    IsCompact (entranceLeaf X p₁) ∧ IsCompact (entranceLeaf X p₂) ∧
    p₂ ∈ connectedComponentIn (inBoundary X) p₁ ∧
    ∃ c₁ c₂ : ℝ → M, IsContractingOrientation X (entranceLeaf X p₁) c₁ ∧
      IsContractingOrientation X (entranceLeaf X p₂) c₂ ∧
      ¬ FreelyHomotopicIn (inBoundary X) c₁ c₂

end Incoherent

end AnosovPlugs


