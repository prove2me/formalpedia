-- Prove2me | Definitions.Def_CerednikDrinfeld_AlgFunctorConst
-- name    : CerednikDrinfeld_AlgFunctorConst
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/326a7b54-28a9-5ba3-830c-eb84d2ea0488
-- title:
--   The constant functor on commutative algebras
-- statement:
--   The ambient notion is the project's record `AlgFunctor 𝒪`, for a commutative ring $\mathcal O$: such a datum consists of a type $F(B)$ for every commutative $\mathcal O$-algebra $B$, a map $F(\varphi) : F(B) \to F(B')$ for every $\mathcal O$-algebra homomorphism $\varphi : B \to B'$, and two fields recording the functor laws, namely that $F(\mathrm{id}_B)$ is the identity on $F(B)$ pointwise and that $F(g \circ f)$ agrees pointwise with $F(g) \circ F(f)$. Thus an `AlgFunctor` is a covariant functor from commutative $\mathcal O$-algebras to types, presented as a structure rather than through a category instance.
--
--   This module defines, for a type $X$, the constant such functor `const X`: its value on every commutative $\mathcal O$-algebra $B$ is the type $X$ itself, and the map attached to every $\mathcal O$-algebra homomorphism $B \to B'$ is the identity of $X$. Both functor laws hold on the nose. The accompanying lemma `const_map` records the computation rule: for a type $X$, commutative $\mathcal O$-algebras $B$ and $B'$, an $\mathcal O$-algebra homomorphism $\varphi : B \to B'$ and $x : X$, one has $(\mathrm{const}\,X).\mathrm{map}\ \varphi\ x = x$. No finiteness, flatness or connectedness condition on the test algebras is imposed; in particular `const X` is a presheaf-style functor of points, which on a disconnected test algebra differs from the functor of points of the disjoint union of copies of $\operatorname{Spec}\mathcal O$ indexed by $X$, the two agreeing on connected test algebras such as fields.
--
--   **Relation to Mathlib.** Mathlib has constant functors for its `CategoryTheory.Functor`, but `AlgFunctor` is the project's own hand-rolled notion of a functor on commutative $\mathcal O$-algebras valued in types; `const` is the corresponding constant functor for that structure.
--
--   **Where it is used.** The `AlgFunctor` formalism carries the chart functors used to describe the formal model of Drinfeld's $p$-adic upper half-plane along the Bruhat–Tits tree, together with products, corepresentable functors, natural transformations and group actions on them. The constant functors provide the discrete members of that formalism, available as factors in products and as sources or targets of natural transformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_AlgFunctorConst.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CerednikDrinfeld.FormalOmega.AlgFunctor

variable {𝒪 : Type} [CommRing 𝒪]

def const (X : Type) : AlgFunctor 𝒪 where
  obj _ := X
  map _ x := x
  map_id _ := rfl
  map_comp _ _ _ := rfl

@[simp] theorem const_map (X : Type) {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') (x : X) : (const (𝒪 := 𝒪) X).map φ x = x := rfl

end CerednikDrinfeld.FormalOmega.AlgFunctor


