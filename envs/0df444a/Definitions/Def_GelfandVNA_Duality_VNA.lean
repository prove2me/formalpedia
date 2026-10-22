-- Prove2me | Definitions.Def_GelfandVNA_Duality_VNA
-- name    : GelfandVNA_Duality_VNA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:10.476692+00:00
-- url     : https://prove2.me/theorems/48faf855-58b4-458b-9803-ab4379f4b92d
-- title:
--   Defs 3.3, 3.10, Prop 3.8, pp. 23–25 — normal functionals, the category CVNA, the Boolean algebra ProjAlg(A)
-- statement:
--   All C\*-algebras are unital and all \*-homomorphisms preserve the unit (§3.1, Definition 3.2).
--
--   1. **Von Neumann algebras** (Definition 3.3). A von Neumann algebra is a C\*-algebra $A$ that admits a predual: a complex Banach space $A_*$ with an isometric isomorphism $\int\colon A\to(A_*)^*$. A **normal functional** on $A$ is a functional of the form $a\mapsto\big(\int a\big)(x)$ for a predual $A_*$ and a vector $x\in A_*$.
--   2. **Normal \*-homomorphisms.** A unital \*-homomorphism $f\colon A\to B$ of von Neumann algebras is *normal* if for every normal functional $\varphi$ on $B$ the functional $\varphi\circ f$ on $A$ is normal. The category **CVNA** has the commutative von Neumann algebras as objects and the normal unital \*-homomorphisms as morphisms.
--   3. **Projections** (Proposition 3.8). For a commutative C\*-algebra $A$,
--   $$\mathsf{ProjAlg}(A)=\{x\in A\mid x^*=x,\ x^2=x\}$$
--   is a Boolean algebra with meet $pq$, join $p+q-pq$, complement $1-p$, bottom $0$ and top $1$ (equivalently, Boolean ring with multiplication and $p\oplus q=(p-q)^2$); its order is $p\le q\iff pq=p$.
--   4. **Restriction to projections** (Definition 3.10). A unital \*-homomorphism $f\colon A\to B$ sends projections to projections; its restriction is $\mathsf{ProjAlg}(f)\colon\mathsf{ProjAlg}(A)\to\mathsf{ProjAlg}(B)$.
--
--   These are the objects of the von Neumann algebra end of Theorem 1.1, $\mathsf{MLoc}\simeq\mathsf{CVNA}^{\mathrm{op}}$, whose inverse equivalence sends $A$ to $\mathsf{ProjAlg}(A)$.
--
--   **Formalization Note** Von Neumann algebras are Mathlib's `CommCStarAlgebra` with `WStarAlgebra` (a predual $X$ in the same universe and an isometric isomorphism $X^*\cong A$). Mathlib's isomorphism is conjugate-linear, so the normal functional is written as the complex conjugate of $a\mapsto(e^{-1}a)(x)$, which is $\mathbb C$-linear. Definition 3.3 defines a morphism as a \*-homomorphism admitting a predual map $f_*$ with $(f_*)^*\circ\int=\int'\circ f$; the encoding uses the equivalent condition "pulls normal functionals back to normal functionals" (equivalent by Sakai's uniqueness of the predual, Remark 3.4, and Remark 3.7). This form makes composition of morphisms immediate. `ProjAlg` is a Boolean subalgebra of Mathlib's Boolean algebra of idempotents of a commutative ring. The zero algebra is not excluded.
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, pp. 23–25, Definitions 3.2, 3.3, 3.10, Remarks 3.4, 3.7, Proposition 3.8

import Mathlib

namespace GelfandVNA.Duality

open CategoryTheory

universe u

/-- A normal functional on a C*-algebra `A` (Definition 3.3 and Remark 3.4, p. 23): a functional
`a ↦ ∫(a)(x)` obtained from some predual `X` of `A` and some vector `x ∈ X`. Mathlib's predual
isomorphism `e : X* ≃ A` is conjugate-linear, so `a ↦ (e⁻¹ a)(x)` is conjugate-linear and its
complex conjugate is the ℂ-linear functional. -/
def IsNormalFunctional {A : Type u} [CStarAlgebra A] (φ : A → ℂ) : Prop :=
  ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X) (_ : CompleteSpace X)
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (x : X), ∀ a, φ a = star ((e.symm a) x)

/-- Definition 3.3, p. 23, in the equivalent form "pulls back normal functionals to normal
functionals": a unital *-homomorphism `f : A → B` is normal if `φ ∘ f` is a normal functional on
`A` for every normal functional `φ` on `B`. -/
def IsNormalStarHom {A B : Type u} [CStarAlgebra A] [CStarAlgebra B] (f : A →⋆ₐ[ℂ] B) : Prop :=
  ∀ φ : B → ℂ, IsNormalFunctional φ → IsNormalFunctional (φ ∘ f)

/-- An object of `CVNA` (Definitions 3.2, 3.3, p. 23): a commutative unital C*-algebra that admits
a predual (`WStarAlgebra`). -/
structure CVNA : Type (u + 1) where
  /-- The underlying algebra. -/
  carrier : Type u
  [comm : CommCStarAlgebra carrier]
  [wstar : WStarAlgebra carrier]

attribute [instance] CVNA.comm CVNA.wstar

/-- Definition 3.3, p. 23: morphisms of `CVNA` are the normal unital *-homomorphisms. -/
instance : Category.{u} CVNA.{u} where
  Hom A B := {f : A.carrier →⋆ₐ[ℂ] B.carrier // IsNormalStarHom f}
  id A := ⟨StarAlgHom.id ℂ A.carrier, fun _ h => h⟩
  comp f g := ⟨g.1.comp f.1, fun φ h => f.2 _ (g.2 φ h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The projections of a commutative C*-algebra, as a Boolean subalgebra of the Boolean algebra of
idempotents (meet `pq`, join `p + q - pq`, complement `1 - p`, `⊥ = 0`, `⊤ = 1`). -/
def projSubalgebra (A : Type u) [CommCStarAlgebra A] :
    BooleanSubalgebra {a : A // IsIdempotentElem a} where
  carrier := {p | IsSelfAdjoint p.1}
  supClosed' p hp q hq := by
    change IsSelfAdjoint (p.1 + q.1 - p.1 * q.1)
    exact (hp.add hq).sub (hp.mul hq)
  infClosed' p hp q hq := by
    change IsSelfAdjoint (p.1 * q.1)
    exact hp.mul hq
  compl_mem' {p} hp := by
    change IsSelfAdjoint (1 - p.1)
    exact (IsSelfAdjoint.one A).sub hp
  bot_mem' := by
    change IsSelfAdjoint (0 : A)
    exact IsSelfAdjoint.zero A

/-- Proposition 3.8, p. 24: the Boolean algebra `ProjAlg(A) = {x ∈ A | x* = x, x² = x}` of
projections of a commutative von Neumann algebra (or C*-algebra) `A`. -/
abbrev ProjAlg (A : Type u) [CommCStarAlgebra A] : Type u := projSubalgebra A

/-- The underlying element of `A` of a projection. -/
def ProjAlg.val {A : Type u} [CommCStarAlgebra A] (p : ProjAlg A) : A := p.1.1

lemma ProjAlg.isStarProjection {A : Type u} [CommCStarAlgebra A] (p : ProjAlg A) :
    IsStarProjection p.val :=
  ⟨p.1.2, p.2⟩

/-- Definition 3.10, p. 25: the restriction `ProjAlg(f) : ProjAlg(A) → ProjAlg(B)` of a
*-homomorphism to projections. -/
def projMap {A B : Type u} [CommCStarAlgebra A] [CommCStarAlgebra B] (f : A →⋆ₐ[ℂ] B)
    (p : ProjAlg A) : ProjAlg B :=
  ⟨⟨f p.val, (p.isStarProjection.map f).isIdempotentElem⟩,
    (p.isStarProjection.map f).isSelfAdjoint⟩

end GelfandVNA.Duality


