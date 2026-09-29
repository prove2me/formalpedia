-- Prove2me | Definitions.Def_Deformations_ConjQuotSubfunctor
-- name    : Deformations_ConjQuotSubfunctor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/562973cd-a64c-56f3-a84a-9e56aea22ba7
-- title:
--   Conjugation quotient of a lifting condition, and two stability axioms
-- statement:
--   Throughout, $n$ is a finite index set, $G$ a topological group, and $\mathcal{O}$ a local commutative ring; the base category is `ProartinianCat 𝓞` of pro-artinian local topological $\mathcal{O}$-algebras whose structure map is local and induces an isomorphism on residue fields. On it sit the functor `repnFunctor n G 𝓞`, $A \mapsto \{\,\rho : G \to \mathrm{GL}_n(A)$ continuous homomorphisms$\,\}$, and its quotient `repnQuotFunctor n G 𝓞`, whose value at $A$ is the set of orbits of the conjugation action of `conjKer A`, the subgroup of $\mathrm{ConjAct}(\mathrm{GL}_n(A))$ given by those $\gamma$ whose image in $\mathrm{GL}_n$ of the residue field of $A$ is the identity; `toRepnQuot` is the objectwise orbit map. Given a subfunctor $F$ of `repnFunctor n G 𝓞`, `conjQuotSubfunctor n F` is the subfunctor of `repnQuotFunctor n G 𝓞` whose value at $A$ is the image $\bigl(\mathrm{toRepnQuot}\bigr)_A\bigl(F(A)\bigr)$, that is, the set of orbits admitting at least one representative in $F(A)$; stability under the transition maps is part of the datum. Accompanying lemmas record the membership criterion (an orbit lies in $(\mathrm{conjQuot}\,F)(A)$ exactly when it is the class of some $\rho' \in F(A)$), that the class of a member of $F(A)$ lies in it, and monotonicity in $F$. The natural transformation `condLiftToDeformation n F` from $F$, viewed as a functor, to `conjQuotSubfunctor n F`, viewed as a functor, sends $\rho'$ to its orbit, and `condLiftToDeformation_surjective` states that each of its components is surjective.
--
--   Two predicates on such a subfunctor $F$ are defined. `ConjStable n F` asserts that for every $A$, every $\rho' \in F(A)$ and every $\gamma \in$ `conjKer A`, the conjugate $\gamma \cdot \rho'$ again lies in $F(A)$. `ReflectedByInjective n F` asserts that for every morphism $\iota : T \to A$ whose underlying map is injective and every continuous $\sigma : G \to \mathrm{GL}_n(T)$, membership of the pushforward $\iota_{*}\sigma$ in $F(A)$ forces $\sigma \in F(T)$.
--
--   **Relation to Mathlib.** Built on Mathlib's `CategoryTheory.Subfunctor` and its orbit-quotient machinery; the representation and quotient functors on pro-artinian local algebras, and the two axioms on a lifting condition, are the project's own notions.
--
--   **Where it is used.** These are the hypotheses under which a subfunctor of framed lifts gives rise to a pro-representable deformation functor: applying the conjugation quotient to the functor of lifts of a fixed residual representation, with or without extra local conditions, produces the deformation functors whose universal rings enter the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_ConjQuotSubfunctor.lean

import Mathlib
import Definitions.Def_Deformations_TraceAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Function IsLocalRing

namespace Deformation

section ConjQuot

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

open ProartinianCat

variable (n) in

noncomputable def conjQuotSubfunctor (F : Subfunctor (repnFunctor n G 𝓞)) :
    Subfunctor (repnQuotFunctor n G 𝓞) where
  obj R := (toRepnQuot n G 𝓞).app R '' F.obj R
  map {R S} f := by
    rintro _ ⟨ρ', hρ', rfl⟩
    exact ⟨(repnFunctor n G 𝓞).map f ρ', F.map f hρ', rfl⟩

variable (n) in

lemma mem_conjQuotSubfunctor_obj_iff {F : Subfunctor (repnFunctor n G 𝓞)}
    {R : ProartinianCat 𝓞} (q : (repnQuotFunctor n G 𝓞).obj R) :
    q ∈ (conjQuotSubfunctor n F).obj R ↔
      ∃ ρ' ∈ F.obj R, (Quotient.mk'' ρ' : (repnQuotFunctor n G 𝓞).obj R) = q := by
  constructor
  · rintro ⟨ρ', hρ', rfl⟩
    exact ⟨ρ', hρ', rfl⟩
  · rintro ⟨ρ', hρ', rfl⟩
    exact ⟨ρ', hρ', rfl⟩

variable (n) in

lemma mk_mem_conjQuotSubfunctor_obj {F : Subfunctor (repnFunctor n G 𝓞)}
    {R : ProartinianCat 𝓞} {ρ' : G →ₜ* GL n R} (hρ' : ρ' ∈ F.obj R) :
    (Quotient.mk'' ρ' : (repnQuotFunctor n G 𝓞).obj R) ∈ (conjQuotSubfunctor n F).obj R :=
  ⟨ρ', hρ', rfl⟩

variable (n) in

lemma conjQuotSubfunctor_mono {F F' : Subfunctor (repnFunctor n G 𝓞)} (h : F ≤ F') :
    conjQuotSubfunctor n F ≤ conjQuotSubfunctor n F' := by
  rintro R _ ⟨ρ', hρ', rfl⟩
  exact ⟨ρ', h _ hρ', rfl⟩

variable (n) in

noncomputable def condLiftToDeformation (F : Subfunctor (repnFunctor n G 𝓞)) :
    F.toFunctor ⟶ (conjQuotSubfunctor n F).toFunctor where
  app R := TypeCat.ofHom
    fun ρ' => ⟨Quotient.mk'' ρ'.1, mk_mem_conjQuotSubfunctor_obj n ρ'.2⟩
  naturality R S f := by
    ext ρ'
    rfl

variable (n) in

lemma condLiftToDeformation_surjective (F : Subfunctor (repnFunctor n G 𝓞))
    (R : ProartinianCat 𝓞) :
    Function.Surjective ((condLiftToDeformation n F).app R) := by
  rintro ⟨q, hq⟩
  obtain ⟨ρ', hρ', hq'⟩ := (mem_conjQuotSubfunctor_obj_iff n q).mp hq
  exact ⟨⟨ρ', hρ'⟩, Subtype.ext hq'⟩

end ConjQuot

section Assembly

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

open ProartinianCat

variable (n) in

def ConjStable (F : Subfunctor (repnFunctor n G 𝓞)) : Prop :=
  ∀ {A : ProartinianCat 𝓞} {ρ' : G →ₜ* GL n A}, ρ' ∈ F.obj A →
    ∀ {γ : ConjAct (GL n A)}, γ ∈ conjKer (n := n) A → γ • ρ' ∈ F.obj A

variable (n) in

def ReflectedByInjective (F : Subfunctor (repnFunctor n G 𝓞)) : Prop :=
  ∀ {T A : ProartinianCat 𝓞} (ι : T ⟶ A), Function.Injective ι.hom →
    ∀ {σ : G →ₜ* GL n T}, (repnFunctor n G 𝓞).map ι σ ∈ F.obj A → σ ∈ F.obj T

end Assembly

end Deformation


