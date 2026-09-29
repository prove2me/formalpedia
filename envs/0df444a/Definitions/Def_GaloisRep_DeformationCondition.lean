-- Prove2me | Definitions.Def_GaloisRep_DeformationCondition
-- name    : GaloisRep_DeformationCondition
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/dca1eaa8-29f2-54cf-8454-535617ff3728
-- title:
--   Artinian test algebras, deformation conditions, tangent finiteness
-- statement:
--   Fix a commutative local ring $\mathcal{O}$. [`GaloisRep.IsArtinianTestAlgebra`](../def/GaloisRep_DeformationCondition.html#L14) is a Prop-valued structure on a local $\mathcal{O}$-algebra $A$ with three fields: the structure map $\mathcal{O}\to A$ is a local homomorphism, the composite $\mathcal{O}\to A\to A/\mathfrak{m}_A$ is surjective (so $A$ has the residue field of $\mathcal{O}$, expressed by surjectivity rather than by a chosen isomorphism), and $A$ is an Artinian ring.
--
--   [`GaloisRep.IsDeformationCondition`](../def/GaloisRep_DeformationCondition.html#L19) is a Prop-valued structure taking a predicate $\mathcal{D}$ on [`GaloisRepAdic A`](../def/GaloisRep_Adic.html#L16), uniformly in local $\mathcal{O}$-algebras $A$ — here a [`GaloisRepAdic A`](../def/GaloisRep_Adic.html#L16) is a free rank-two $A$-module $V$ together with a monoid homomorphism from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $\mathrm{End}_A V$ that is $\mathfrak{m}_A$-adically continuous in the sense that for each $n$ some finite subextension $L/\mathbb{Q}$ has its pointwise stabiliser acting trivially on $V/\mathfrak{m}_A^nV$. Its five fields are: (1) on Artinian test algebras, $\mathcal{D}$ is invariant under the existence of an $A$-linear Galois-equivariant isomorphism; (2) $\mathcal{D}$ is preserved by base change $B\otimes_A V$ along any local $\mathcal{O}$-algebra map $\varphi:A\to B$ between Artinian test algebras; (3) it is reflected along such a $\varphi$ when $\varphi$ is injective; (4) if $P$ presents the fibre product of $f:A\to C$ and $g:B\to C$ (all four Artinian test algebras, $f\circ p_A=g\circ p_B$, $x\mapsto(p_Ax,p_Bx)$ injective, and every pair with $fa=gb$ is of this form, with $p_A,p_B$ local), then $\mathcal{D}$ of both base changes implies $\mathcal{D}(\rho)$; (5) for $A$ Noetherian local, $\mathfrak{m}_A$-adically complete, with local structure map and surjective composite to the residue field, $\mathcal{D}(\rho)$ holds exactly when $\mathcal{D}$ holds of the base change along every surjective local $\mathcal{O}$-algebra map onto an Artinian test algebra.
--
--   [`GaloisRep.TangentFinite`](../def/GaloisRep_DeformationCondition.html#L59) asserts, for $\bar\rho$ a residual representation over $k=\mathcal{O}/\mathfrak{m}$ and a predicate $\mathcal{D}$, that the type of those $\rho$ over the dual numbers $k[\varepsilon]$ satisfying $\mathcal{D}$ whose residual representation is isomorphic to the base change of $\bar\rho$, taken modulo the equivalence relation of isomorphism of representations (the setoid being supplied explicitly from reflexivity, symmetry and transitivity), is finite.
--
--   **Relation to Mathlib.** Mathlib has no notion of a deformation condition or of deformations of Galois representations; these are the project's own, built from Mathlib's `IsLocalRing`, `IsLocalHom`, `IsArtinianRing`, `IsAdicComplete`, `IsLocalRing.residue` and `DualNumber`.
--
--   **Where it is used.** These are the axioms under which the deformation functor of a residual representation is shown to be representable by a complete local $\mathcal{O}$-algebra, uniformly in the condition $\mathcal{D}$; tangent finiteness is what makes the representing ring Noetherian. Concrete conditions (minimality, behaviour at $p$, prescribed level structure at auxiliary primes) are then checked against this interface in the Taylor–Wiles comparison of deformation rings with Hecke algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_DeformationCondition.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace GaloisRep

open IsLocalRing

variable (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]

structure IsArtinianTestAlgebra (A : Type) [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] : Prop where
  isLocalHom : IsLocalHom (algebraMap 𝒪 A)
  residue_surjective : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A)
  isArtinian : IsArtinianRing A

structure IsDeformationCondition
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop) :
    Prop where

  of_isEquiv : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
    IsArtinianTestAlgebra 𝒪 A → ∀ ⦃ρ ρ' : GaloisRepAdic A⦄, ρ.IsEquiv ρ' → 𝒟 ρ → 𝒟 ρ'

  baseChangeAlong : ∀ ⦃A B : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [CommRing B] [IsLocalRing B] [Algebra 𝒪 B],
    IsArtinianTestAlgebra 𝒪 A → IsArtinianTestAlgebra 𝒪 B →
    ∀ (φ : A →ₐ[𝒪] B) (hφ : IsLocalHom (φ : A →+* B)) ⦃ρ : GaloisRepAdic A⦄,
      𝒟 ρ → 𝒟 (ρ.baseChangeAlong (φ : A →+* B) hφ)

  of_baseChangeAlong_injective : ∀ ⦃A B : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [CommRing B] [IsLocalRing B] [Algebra 𝒪 B],
    IsArtinianTestAlgebra 𝒪 A → IsArtinianTestAlgebra 𝒪 B →
    ∀ (φ : A →ₐ[𝒪] B) (hφ : IsLocalHom (φ : A →+* B)), Function.Injective φ →
      ∀ ⦃ρ : GaloisRepAdic A⦄, 𝒟 (ρ.baseChangeAlong (φ : A →+* B) hφ) → 𝒟 ρ

  of_fibreProduct : ∀ ⦃A B C P : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] [CommRing C] [IsLocalRing C] [Algebra 𝒪 C]
    [CommRing P] [IsLocalRing P] [Algebra 𝒪 P],
    IsArtinianTestAlgebra 𝒪 A → IsArtinianTestAlgebra 𝒪 B → IsArtinianTestAlgebra 𝒪 C →
    IsArtinianTestAlgebra 𝒪 P →
    ∀ (f : A →ₐ[𝒪] C) (g : B →ₐ[𝒪] C) (pA : P →ₐ[𝒪] A) (pB : P →ₐ[𝒪] B)
      (hpA : IsLocalHom (pA : P →+* A)) (hpB : IsLocalHom (pB : P →+* B)),
      f.comp pA = g.comp pB →
      Function.Injective (fun x => (pA x, pB x)) →
      (∀ a b, f a = g b → ∃ x, pA x = a ∧ pB x = b) →
      ∀ ⦃ρ : GaloisRepAdic P⦄,
        𝒟 (ρ.baseChangeAlong (pA : P →+* A) hpA) → 𝒟 (ρ.baseChangeAlong (pB : P →+* B) hpB) → 𝒟 ρ

  iff_forall_surjective : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra 𝒪 A],
    IsLocalHom (algebraMap 𝒪 A) → Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A) →
    ∀ (ρ : GaloisRepAdic A),
      𝒟 ρ ↔ ∀ ⦃B : Type⦄ [CommRing B] [IsLocalRing B] [Algebra 𝒪 B], IsArtinianTestAlgebra 𝒪 B →
        ∀ (q : A →ₐ[𝒪] B) (hq : IsLocalHom (q : A →+* B)), Function.Surjective q →
          𝒟 (ρ.baseChangeAlong (q : A →+* B) hq)

def TangentFinite (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop) : Prop :=
  letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
    ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
      (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
  letI : Algebra (ResidueField 𝒪) (ResidueField (DualNumber (ResidueField 𝒪))) :=
    ((IsLocalRing.residue (DualNumber (ResidueField 𝒪))).comp
      (algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪)))).toAlgebra
  Finite (Quotient (⟨fun ρ ρ' : {ρ : GaloisRepAdic (DualNumber (ResidueField 𝒪)) //
      𝒟 ρ ∧ ρ.residual.IsEquiv (ρbar.baseChange (ResidueField (DualNumber (ResidueField 𝒪)))) } =>
      ρ.1.IsEquiv ρ'.1, ⟨fun ρ => ⟨GaloisRepAdic.Equiv.refl ρ.1⟩,
        fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩⟩ : Setoid _))

end GaloisRep

end


