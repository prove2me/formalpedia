-- Prove2me | Definitions.Def_AlgebraicGeometry_AffineLimit
-- name    : AlgebraicGeometry_AffineLimit
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/d91266b7-1c5b-5ac9-9d51-3be933719977
-- title:
--   Finite-presentation limit conditions for presheaves over SpecR
-- statement:
--   Fix a commutative ring $R$. The helper abbreviations package the directed system of finitely generated subalgebras of an $R$-algebra on the geometric side: `specOver R A` is $\operatorname{Spec} A$ viewed as an object of the category of schemes over $\operatorname{Spec} R$, via the morphism induced by the structure map $R \to A$; `specOverOfSubalgebra R A₀` is the morphism $\operatorname{Spec} A \to \operatorname{Spec} A_0$ over $\operatorname{Spec} R$ induced by the inclusion of a subalgebra $A_0 \subseteq A$; and `specOverOfLE R A₀ A₁ h` is the morphism $\operatorname{Spec} A_1 \to \operatorname{Spec} A_0$ induced by an inclusion $A_0 \le A_1$ of subalgebras of $A$.
--
--   Two predicates are then defined on a presheaf of sets $G$ on the category of schemes over $\operatorname{Spec} R$ (with values in an arbitrary universe). `IsLFPSurj G` asserts that for every $R$-algebra $A$ and every section $x \in G(\operatorname{Spec} A)$ there are a finitely generated subalgebra $A_0 \subseteq A$ and a section $x_0 \in G(\operatorname{Spec} A_0)$ whose restriction along $\operatorname{Spec} A \to \operatorname{Spec} A_0$ is $x$. `IsLFPInj G` asserts that for every $R$-algebra $A$, every finitely generated subalgebra $A_0 \subseteq A$ and every pair of sections $x_0, x_0' \in G(\operatorname{Spec} A_0)$ having equal restrictions to $\operatorname{Spec} A$, there is a finitely generated subalgebra $A_1$ with $A_0 \le A_1 \subseteq A$ over which the two restrictions already agree. Together these say that $G$ turns the presentation of $\operatorname{Spec} A$ as the limit of the $\operatorname{Spec} A_0$ into a colimit, stated elementwise rather than as an isomorphism of sets.
--
--   `HomIsLFP ξ`, for a morphism $\xi \colon X \to \operatorname{Spec} R$ of schemes, is the conjunction of the same two conditions for the functor of $R$-morphisms into $X$: every $\varphi \colon \operatorname{Spec} A \to X$ over $\operatorname{Spec} R$ (the compatibility being expressed by $\varphi$ followed by $\xi$ equalling the morphism induced by $R \to A$) factors as $\operatorname{Spec} A \to \operatorname{Spec} A_0 \to X$ through some $R$-morphism $\varphi_0$ defined on a finitely generated $A_0 \subseteq A$; and two such $R$-morphisms on $\operatorname{Spec} A_0$ that become equal after composition with $\operatorname{Spec} A \to \operatorname{Spec} A_0$ become equal already after composition with $\operatorname{Spec} A_1 \to \operatorname{Spec} A_0$ for some finitely generated $A_1 \supseteq A_0$ inside $A$.
--
--   **Relation to Mathlib.** Mathlib has predicates for morphisms of schemes locally of finite type or finite presentation, but no notion of a presheaf commuting with the limits presenting $\operatorname{Spec} A$ as a limit of spectra of finitely generated subalgebras; these predicates are the project's own, built from Mathlib's `Over`, `Spec` and `Subalgebra.FG`.
--
--   **Where it is used.** This vocabulary is the concrete form of "locally of finite presentation" used to reduce assertions about arbitrary affine test schemes over $R$ to test schemes of finite type, as in spreading-out arguments over a Noetherian base. It is invoked for morphisms into a scheme locally of finite type over a Noetherian ring and for the rigidified relative Picard presheaf of a smooth proper curve, and hence in the representability arguments for the moduli problems appearing in the modularity route.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_AffineLimit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe w u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AffineLimit

variable (R : Type u) [CommRing R]

noncomputable abbrev specOver (A : Type u) [CommRing A] [Algebra R A] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

noncomputable abbrev specOverOfSubalgebra {A : Type u} [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) :
    specOver R A ⟶ specOver R A₀ :=
  Over.homMk (Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl)

noncomputable abbrev specOverOfLE {A : Type u} [CommRing A] [Algebra R A] (A₀ A₁ : Subalgebra R A) (h : A₀ ≤ A₁) :
    specOver R A₁ ⟶ specOver R A₀ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl)

variable {R}

def IsLFPSurj (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A] (x : G.obj (op (specOver R A))),
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (x₀ : G.obj (op (specOver R A₀))),
      G.map (specOverOfSubalgebra R A₀).op x₀ = x

def IsLFPInj (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) (_ : A₀.FG)
    (x₀ x₀' : G.obj (op (specOver R A₀))),
    G.map (specOverOfSubalgebra R A₀).op x₀ = G.map (specOverOfSubalgebra R A₀).op x₀' →
    ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (h : A₀ ≤ A₁),
      G.map (specOverOfLE R A₀ A₁ h).op x₀ = G.map (specOverOfLE R A₀ A₁ h).op x₀'

def HomIsLFP {X : Scheme.{u}} (ξ : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  (∀ (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X),
      φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
      ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of A₀) ⟶ X),
        φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) ∧
        Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ) ∧
  (∀ (A : Type u) [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) (_ : A₀.FG)
      (φ₀ φ₀' : Spec (CommRingCat.of A₀) ⟶ X),
      φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) →
      φ₀' ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) →
      Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀' →
      ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (h : A₀ ≤ A₁),
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) ≫ φ₀ =
          Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) ≫ φ₀')

end AlgebraicGeometry.AffineLimit


