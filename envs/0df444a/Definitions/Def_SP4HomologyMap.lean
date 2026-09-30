-- Prove2me | Definitions.Def_SP4HomologyMap
-- name    : SP4HomologyMap
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-09T02:56:00.031106+00:00
-- url     : https://prove2.me/theorems/10aa0543-c4d3-4e8d-8a04-91fbb98f0bea
-- title:
--   Induced map $f_*\colon H_k(X;\mathbb Z)\to H_k(Y;\mathbb Z)$ on integral singular homology
-- statement:
--   For a continuous map $f\colon X\to Y$ between topological spaces (in universe zero) and $k\ge0$, `SP4Homology.map k f` is the induced homomorphism
--
--   $$
--   f_*\colon H_k(X;\mathbb Z)\longrightarrow H_k(Y;\mathbb Z)
--   $$
--
--   on integral singular homology, i.e. the action of Mathlib's singular homology functor (with coefficients in the $\mathbb Z$-module $\mathbb Z$) on the morphism $f$ of the category of topological spaces. It is functorial: the identity induces the identity and $(g\circ f)_*=g_*\circ f_*$; these two structural facts are recorded as `SP4Homology.map_id` and `SP4Homology.map_comp`. The definition complements `SP4Homology.H` and allows statements such as "the inclusion $M\setminus\{p\}\hookrightarrow M$ induces an isomorphism on $H_k$" or "a homotopy equivalence induces isomorphisms on homology" to be expressed with the standard induced maps rather than with abstract isomorphisms.
--
--   **Formalization Note** `SP4Homology.map k f : SP4Homology.H k X ⟶ SP4Homology.H k Y` is `((singularHomologyFunctor (ModuleCat ℤ) k).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)`, a morphism in `ModuleCat ℤ`. "Isomorphism on homology" is expressed as Mathlib's `IsIso (SP4Homology.map k f)`.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1, p. 111 (induced homomorphisms f_* : Hₙ(X) → Hₙ(Y) and their functoriality (fg)_* = f_* g_*, 1_* = 1). Mathlib: `AlgebraicTopology.singularHomologyFunctor` (Mathlib/AlgebraicTopology/SingularHomology/Basic.lean).

import Definitions.Def_SP4Homology

set_option autoImplicit false

open CategoryTheory AlgebraicTopology

namespace SP4Homology

/-- **Induced map on integral singular homology.** A continuous map `f : X → Y` induces the
`ℤ`-linear map `f_* : H_k(X; ℤ) → H_k(Y; ℤ)` (Hatcher, *Algebraic Topology*, §2.1, p. 111); this is
the action of Mathlib's singular homology functor on the morphism `f` of `TopCat`. -/
noncomputable def map (k : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : H k X ⟶ H k Y :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[simp]
theorem map_id (k : ℕ) : map k (ContinuousMap.id X) = 𝟙 (H k X) :=
  CategoryTheory.Functor.map_id _ _

theorem map_comp (k : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    map k (g.comp f) = map k f ≫ map k g :=
  CategoryTheory.Functor.map_comp _ _ _

end SP4Homology


