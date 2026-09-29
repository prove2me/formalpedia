-- Prove2me | Definitions.Def_AlgebraicGeometry_SymmRootAdm
-- name    : AlgebraicGeometry_SymmRootAdm
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/dd3de6b8-281d-53be-8e95-384a6c36f207
-- title:
--   Admissibility predicate: symmetric, tensor-square trivial relative bundles
-- statement:
--   Throughout, $S$ is a commutative ring, $f\colon A\to\operatorname{Spec}S$ a morphism of schemes carrying a relative group law $L$ (a functorial group structure on the sets of sections $\mathrm{SchemeHomOver}\,t\,f$), and $R_0$ an $S$-algebra. Test objects are objects $B$ of `Under (CommRingCat.of R₀)`, i.e. rings equipped with a map from $R_0$, viewed as $S$-algebras, with structure morphism $\iota_B\colon\operatorname{Spec}B\to\operatorname{Spec}S$, and one works on the base change $A_B=A\times_{\operatorname{Spec}S}\operatorname{Spec}B$ with its projection `pullback.snd` to $\operatorname{Spec}B$.
--
--   `admPred L R₀ B N`, for $N$ a sheaf of modules on $A_B$, is the conjunction of two conditions, each expressed through `LocIsoOnBase`: a relation $M\simeq M'$ holding when every point $s$ of the base $\operatorname{Spec}B$ has an open neighbourhood $U$ such that the restrictions of $M$ and $M'$ to the preimage of $U$ in $A_B$ are isomorphic. The first condition is that the pullback of $N$ along the inversion morphism `negMor` of the base-changed group law $L.\mathrm{baseChange}\,\iota_B$ is locally-on-the-base isomorphic to $N$ — this is precisely the predicate `IsSymmetric` for that law, as `admPred_iff'` records; the second is that $N\otimes N$ is locally-on-the-base isomorphic to the monoidal unit, i.e. to the structure sheaf of $A_B$. Thus admissibility asks for symmetry and $2$-torsion of $N$, both only up to isomorphism locally over the base, and both stated for the chosen module $N$ rather than for an isomorphism class. `admPred_iff` restates the definition verbatim.
--
--   `admStablePred L R₀ h` takes as input a proof $h$ that admissibility of the underlying module of a rigidified line bundle on $A_B$ (rigidified along the unit section $L.\mathrm{one}$ over the base) is preserved by pullback along $\psi_\varphi$ for every morphism $\varphi\colon B\to B'$, and assembles the pair into a `StablePred`, the structure whose fields are such a predicate together with its pullback-stability. This is exactly the input required by `classFunctor`, which then yields the covariant functor on $R_0$-algebras sending $B$ to the set of isomorphism classes of rigidified line bundles on $A_B$ that are symmetric and of order dividing two, locally over the base.
--
--   **Relation to Mathlib.** The sheaves of modules on a scheme, their pullback functors and the monoidal structure are Mathlib's; the relative group law, local isomorphism over the base, symmetry, rigidified line bundles and stable predicates feeding the class functor are the project's own notions.
--
--   **Where it is used.** Admissibility is the predicate cut out on the relative Picard-type functor of rigidified line bundles whose classes form the structure group of the functor of symmetric square roots; it is used in the corepresentability statements for that functor and in the associated $2$-torsion character arguments in the treatment of polarisations and good reduction of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SymmRootAdm.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmRootFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

namespace AlgebraicGeometry.SymmRoot

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (R₀ : Type u) [CommRing R₀] [Algebra S R₀]

def admPred (B : Under (CommRingCat.of R₀)) (N : (pullback f (ι S R₀ B)).Modules) : Prop :=
  LocIsoOnBase (pullback.snd f (ι S R₀ B))
      ((Scheme.Modules.pullback (negMor (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)))).obj N) N ∧
    LocIsoOnBase (pullback.snd f (ι S R₀ B)) (N ⊗ N) (𝟙_ ((pullback f (ι S R₀ B)).Modules))

theorem admPred_iff (B : Under (CommRingCat.of R₀)) (N : (pullback f (ι S R₀ B)).Modules) :
    admPred L R₀ B N ↔
      LocIsoOnBase (pullback.snd f (ι S R₀ B))
          ((Scheme.Modules.pullback (negMor (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)))).obj N) N ∧
        LocIsoOnBase (pullback.snd f (ι S R₀ B)) (N ⊗ N) (𝟙_ ((pullback f (ι S R₀ B)).Modules)) :=
  Iff.rfl

theorem admPred_iff' (B : Under (CommRingCat.of R₀)) (N : (pullback f (ι S R₀ B)).Modules) :
    admPred L R₀ B N ↔
      IsSymmetric (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)) N ∧
        LocIsoOnBase (pullback.snd f (ι S R₀ B)) (N ⊗ N) (𝟙_ ((pullback f (ι S R₀ B)).Modules)) :=
  Iff.rfl

abbrev admStablePred
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (N : RigidifiedLineBundle f (L.one (𝟙 _)) (ι S R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (ψ S R₀ φ)).L) :
    StablePred f (L.one (𝟙 _)) R₀ :=
  ⟨admPred L R₀, h⟩

example
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (N : RigidifiedLineBundle f (L.one (𝟙 _)) (ι S R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (ψ S R₀ φ)).L)
    (B : Under (CommRingCat.of R₀)) :
    (admStablePred L R₀ h).P B = admPred L R₀ B := rfl

end AlgebraicGeometry.SymmRoot

end


