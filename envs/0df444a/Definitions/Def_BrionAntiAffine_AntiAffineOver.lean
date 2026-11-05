-- Prove2me | Definitions.Def_BrionAntiAffine_AntiAffineOver
-- name    : BrionAntiAffine_AntiAffineOver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:46.633241+00:00
-- url     : https://prove2.me/theorems/d4172e6d-821c-4be3-a306-d8b676c4db38
-- title:
--   Anti-affine groups over an abelian variety
-- statement:
--   Let $k$ be a field. Schemes over $k$ form a category with products $X\times_k Y$, and a group scheme is a group object in it. A group scheme $G$ of finite type over $k$ is **anti-affine** if $\mathcal O(G)=k$, that is, the structure map $k\to\Gamma(G,\mathcal O_G)$ is bijective. An **algebraic group** is a smooth group scheme of finite type, and an **abelian variety** is a connected, smooth, proper group scheme.
--
--   Given a homomorphism $\alpha:G\to A$ onto an abelian variety, $\alpha$ is the **Chevalley quotient** of $G$ if
--
--   $$\alpha:\ G\longrightarrow G/G_{\mathrm{aff}}\simeq A,$$
--
--   where $G_{\mathrm{aff}}$ is the smallest normal connected affine subgroup scheme of $G$ with abelian variety quotient. Concretely: $\alpha$ is faithfully flat and quasi-compact, its kernel is affine and connected, and every other such homomorphism $\beta:G\to B$ to an abelian variety factors as $\beta=f\circ\alpha$ for a homomorphism $f:A\to B$.
--
--   An **anti-affine group over $A$** is a pair $(G,\alpha)$ with $G$ anti-affine and $\alpha$ a Chevalley quotient. An **isomorphism over $A$** of two such pairs is an isomorphism of group schemes $e:G\to G'$ with $\alpha'\circ e=\alpha$. These are the objects classified by Theorem 2.7.
--
--   **Formalization Note** The category is `Over (Spec k)` with its cartesian monoidal structure. The predicate `IsAntiAffine` takes only the underlying scheme, since the group law does not enter the formula. Smoothness, connectedness and commutativity of an anti-affine group are not assumed: they are consequences. The minimality clause cannot be dropped, as a Frobenius isogeny $A\to A^{(p)}$ also has connected affine kernel.
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, §0, p.1 (anti-affine); p.3 (conventions, (0.1)); §2.1, p.6 (group schemes over A)

import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

/-- Schemes over a field `k`: the ambient category of every statement of Brion, arXiv:0710.5211v3.
It carries its cartesian monoidal structure, so that `X ⊗ Y` is the fibre product over `Spec k` and
a group scheme is a `GrpObj`. -/
abbrev Sch (k : Type u) [Field k] : Type (u + 1) := Over (Spec (CommRingCat.of k))

variable {k : Type u} [Field k]

/-- A `k`-scheme of finite type. Brion, arXiv:0710.5211v3, Notation and conventions, p.3: "By a
scheme, we mean a scheme of finite type over k". -/
structure IsFiniteTypeOver (X : Sch k) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType X.hom
  quasiCompact : QuasiCompact X.hom

/-- The structure map `k → Γ(X, ⊤)` of a `k`-scheme. -/
def constants (X : Sch k) : k →+* Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop).hom

/-- `G` is anti-affine: of finite type over `k` with `O(G) = k`. Brion, arXiv:0710.5211v3, §0, p.1:
"a group scheme G of finite type over a field k is anti-affine if O(G) = k".

**Formalization Note.** The map `k → Γ(G, ⊤)` is asked to be bijective. It is always injective, so
surjectivity is the content. Smoothness, connectedness and commutativity are not assumed: the paper
states them as consequences. The group law does not enter the formula, so the predicate takes only
the underlying `k`-scheme; it is applied to group objects, and to their base changes in Lemma 1.1. -/
structure IsAntiAffine (G : Sch k) : Prop where
  finiteType : IsFiniteTypeOver G
  bijective_constants : Function.Bijective (constants G)

/-- An algebraic group in the sense of Brion, arXiv:0710.5211v3, p.3: a smooth group scheme, which
by the conventions of that page is of finite type over `k`; possibly non-connected. -/
structure IsAlgebraicGroup (G : Sch k) [GrpObj G] : Prop where
  finiteType : IsFiniteTypeOver G
  smooth : Smooth G.hom

/-- An abelian variety: "a connected and complete algebraic group". Brion, arXiv:0710.5211v3, p.3.
"Complete" is `IsProper` of the structure morphism. -/
structure IsAbelianVariety (A : Sch k) [GrpObj A] : Prop where
  smooth : Smooth A.hom
  isProper : IsProper A.hom
  connected : ConnectedSpace A.left

/-- `α : G ⟶ A` is a quotient homomorphism with connected affine kernel: faithfully flat and
quasi-compact, with kernel `pullback α η[A]` affine and connected. -/
structure IsConnectedAffineQuotient {G A : Sch k} [GrpObj G] [GrpObj A] (α : G ⟶ A) : Prop where
  flat : Flat α.left
  surjective : Surjective α.left
  quasiCompact : QuasiCompact α.left
  isAffine_ker : IsAffine (pullback α η[A]).left
  connected_ker : ConnectedSpace (pullback α η[A]).left

/-- `α : G ⟶ A` is the quotient `αG : G → G/Gaff ≃ A`. Brion, arXiv:0710.5211v3, (0.1), p.3, and
§2.1, p.6: `Gaff` is the smallest normal connected affine subgroup scheme of `G` such that `G/Gaff`
is an abelian variety.

**Formalization Note.** Stated without forming `Gaff`: `A` is an abelian variety, `α` is a
homomorphism and a quotient with connected affine kernel, and it is *minimal*: every other such
homomorphism `β : G ⟶ B` to an abelian variety factors through `α` by a homomorphism. A subgroup
scheme is contained in `ker β` exactly when `β` factors through the quotient by it, so this says
`ker α` is the smallest such subgroup scheme. Minimality cannot be dropped: a Frobenius isogeny
`A → A^(p)` has connected affine kernel. -/
structure IsChevalleyQuotient {G A : Sch k} [GrpObj G] [GrpObj A] (α : G ⟶ A) : Prop where
  abelianVariety : IsAbelianVariety A
  isMonHom : IsMonHom α
  quotient : IsConnectedAffineQuotient α
  minimal : ∀ (B : Sch k) [GrpObj B] (β : G ⟶ B), IsAbelianVariety B → IsMonHom β →
    IsConnectedAffineQuotient β → ∃ f : A ⟶ B, IsMonHom f ∧ α ≫ f = β

/-- An anti-affine group over the abelian variety `A`: an anti-affine `G` with the isomorphism
`G/Gaff ≃ A`, given as the quotient homomorphism `α : G ⟶ A`. Brion, arXiv:0710.5211v3, §2.1, p.6. -/
structure AntiAffineOver (A : Sch k) [GrpObj A] where
  /-- The group scheme. -/
  G : Sch k
  /-- Its group law. -/
  [grp : GrpObj G]
  /-- The quotient homomorphism onto `A`. -/
  α : G ⟶ A
  antiAffine : IsAntiAffine G
  chevalley : IsChevalleyQuotient α

attribute [instance] AntiAffineOver.grp

/-- An isomorphism of group schemes over `A`, "in an obvious sense" (Brion, arXiv:0710.5211v3, §2.1,
p.6): an isomorphism that is a homomorphism and commutes with the maps to `A`. -/
structure IsoOver {A : Sch k} [GrpObj A] (G G' : AntiAffineOver A) where
  /-- The underlying isomorphism of `k`-schemes. -/
  e : G.G ≅ G'.G
  isMonHom : IsMonHom e.hom
  comm : e.hom ≫ G'.α = G.α

end BrionAntiAffine


