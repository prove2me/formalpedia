-- Prove2me | Definitions.Def_AlgebraicGeometry_PolarisationPicZero
-- name    : AlgebraicGeometry_PolarisationPicZero
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/2804f3b4-c3d5-5847-a855-01f8855814f8
-- title:
--   Degree-zero Picard condition and stabiliser points
-- statement:
--   Throughout, $k$ is a commutative ring, $f : A \to \operatorname{Spec} k$ a morphism of schemes, and $L$ a `RelativeGroupLaw` on $f$, i.e. a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of sections of $f$ over a variable base morphism $t : T \to \operatorname{Spec} k$, with multiplication, unit and inverse compatible with composition in $T$. A point of $A$ over the base is a pair $x = (x_1, \,x_1 \circ f = \mathrm{id})$, an element of $\mathrm{SchemeHomOver}\,(\mathbf 1_{\operatorname{Spec} k})\,f$, and $L$ produces from such an $x$ the translation endomorphism `L.translate x` of $A$ over $\operatorname{Spec} k$.
--
--   Two notions are introduced. First, `InPicZero M`, for a sheaf of modules $M$ on $A$, is the conjunction of two conditions: $M$ satisfies the project's invertibility predicate `Scheme.Modules.IsInvertible` (each point of $A$ has an open neighbourhood $U$ on which the restriction of $M$ is isomorphic to the unit sheaf of modules of $U$), and for every point $x$ of $A$ over $\operatorname{Spec} k$ the pullback of $M$ along `L.translate x` admits an isomorphism to $M$. The latter is stated as `Nonempty` of the type of isomorphisms, so it asserts existence and carries no chosen isomorphism. This is the translation-invariance definition of $\operatorname{Pic}^0$, tested only on points of $A$ over the base.
--
--   Second, `kernelPts 𝓛` is the set of points $x$ of $A$ over $\operatorname{Spec} k$ satisfying `L.IsInStabilizer 𝓛 (𝟙 (Spec k)) x`: writing $t = \mathbf 1_{\operatorname{Spec} k}$, the pullbacks of $\mathcal L$ along the relative translation $\mathrm{mulRight}\,t\,x$ and along the first projection of $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$ are required to be isomorphic locally over the base, in the sense of `LocallyIsoOver`: every point of the base has an open neighbourhood $U$ over which the two pullbacks, restricted to the preimage of $U$, become isomorphic. Thus `kernelPts` records the points of the stabiliser subgroup $K(\mathcal L)$ as a subset, not as a scheme.
--
--   **Relation to Mathlib.** Mathlib has no notion of a relative group law on a scheme morphism, nor of $\operatorname{Pic}^0$ or of the stabiliser of a line bundle under translation; these are the project's own predicates, built on Mathlib's sheaves of modules on a scheme and their pullback functors together with the project's local-triviality predicate `Scheme.Modules.IsInvertible` and the local-isomorphism-over-the-base relation `Scheme.Modules.LocallyIsoOver`.
--
--   **Where it is used.** These predicates provide the vocabulary for line bundles on abelian schemes and Jacobians over a base: degree-zero classes in the translation-invariant sense, and the set of base points stabilising a given bundle, whose finiteness is the hypothesis in the classical criterion for a polarisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_PolarisationPicZero.lean

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

variable {k : Type u} [CommRing k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)

def InPicZero (M : A.Modules) : Prop :=
  Scheme.Modules.IsInvertible M ∧
    ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      Nonempty ((Scheme.Modules.pullback (L.translate x)).obj M ≅ M)

def kernelPts (𝓛 : A.Modules) : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :=
  {x | L.IsInStabilizer 𝓛 (𝟙 (Spec (CommRingCat.of k))) x}

end AlgebraicGeometry.Polarisation

end


