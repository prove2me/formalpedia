-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
-- name    : OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:47:34.450711+00:00
-- url     : https://prove2.me/theorems/c4cdd7a5-f85c-4472-8432-a3db169f7c39
-- title:
--   Relative canonical isomorphism $\Omega^{n+r}_{B/R}\cong\Omega^{r}_{B/A}$ for a formally smooth algebra, given a basis of $\Omega_{A/R}$
-- statement:
--   For a homomorphism of commutative rings $R\to A$ write $\Omega_{A/R}$ for the module of Kähler differentials, $d\colon A\to\Omega_{A/R}$ for the universal derivation, $\Omega^n_{A/R}:=\bigwedge^n_A\Omega_{A/R}$ for its $n$-th exterior power and $(\Omega^n_{A/R})^{\otimes m}$ for the $m$-fold tensor product of $\Omega^n_{A/R}$ over $A$. Let $R\to A\to B$ be homomorphisms of commutative rings, the composite being the structure map $R\to B$, and assume that $A\to B$ is formally smooth. Let $\iota\colon B\otimes_A\Omega_{A/R}\to\Omega_{B/R}$, $\lambda\otimes da\mapsto\lambda\,d\bar a$, and $\pi\colon\Omega_{B/R}\to\Omega_{B/A}$, $z\mapsto\bar z$, be the canonical maps.
--
--   1. **Injectivity.** The map $\iota$ is injective. Together with the standard exactness of $B\otimes_A\Omega_{A/R}\to\Omega_{B/R}\to\Omega_{B/A}\to0$, this gives a short exact sequence
--   $$0\to B\otimes_A\Omega_{A/R}\xrightarrow{\ \iota\ }\Omega_{B/R}\xrightarrow{\ \pi\ }\Omega_{B/A}\to0 .$$
--   2. **Based adjunction isomorphism.** Let $b=(\beta_1,\dots,\beta_n)$ be an $A$-basis of $\Omega_{A/R}$ and $c=(c_1,\dots,c_r)$ a $B$-basis of $\Omega_{B/A}$. Applying the determinant isomorphism of short exact sequences to the sequence of item 1, with the bases $1\otimes b$ of $B\otimes_A\Omega_{A/R}$ and $c$ of $\Omega_{B/A}$, gives a $B$-linear isomorphism
--   $$\alpha_{b,c}\colon\textstyle\bigwedge^n_B\big(B\otimes_A\Omega_{A/R}\big)\otimes_B\Omega^r_{B/A}\xrightarrow{\ \sim\ }\Omega^{n+r}_{B/R}$$
--   with $\alpha_{b,c}\big((v_1\wedge\cdots\wedge v_n)\otimes(\bar z_1\wedge\cdots\wedge\bar z_r)\big)=\iota(v_1)\wedge\cdots\wedge\iota(v_n)\wedge z_1\wedge\cdots\wedge z_r$ for all $v_i\in B\otimes_A\Omega_{A/R}$ and $z_k\in\Omega_{B/R}$.
--   3. **Relative canonical isomorphism.** The $B$-linear isomorphism
--   $$\theta_{b,c}\colon\Omega^{n+r}_{B/R}\xrightarrow{\ \sim\ }\Omega^r_{B/A}$$
--   obtained from $\alpha_{b,c}^{-1}$ by trivialising $\bigwedge^n_B(B\otimes_A\Omega_{A/R})\cong B$ with the determinant coordinate of the basis $1\otimes b$ and then identifying $B\otimes_B\Omega^r_{B/A}=\Omega^r_{B/A}$. Writing $\tilde\beta_i:=\iota(1\otimes\beta_i)$ for the image of $\beta_i$ in $\Omega_{B/R}$, it removes the base directions: $\theta_{b,c}\big(\tilde\beta_1\wedge\cdots\wedge\tilde\beta_n\wedge z_1\wedge\cdots\wedge z_r\big)=\bar z_1\wedge\cdots\wedge\bar z_r$ for all $z_1,\dots,z_r\in\Omega_{B/R}$.
--
--   Geometrically, if $\operatorname{Spec}B\to\operatorname{Spec}A$ is a smooth morphism of relative dimension $r$ and $\Omega_{A/R}$ is free of rank $n$, then $\theta_{b,c}$ is the isomorphism $\omega_{B/R}\cong\omega_{A/R}|_B\otimes\omega_{B/A}\cong\omega_{B/A}$ in which the base factor is trivialised by $\beta_1\wedge\cdots\wedge\beta_n$. It is the first step in restricting a top-degree form on the total space of a fibration to a fibre.
--
--   **Formalization Note** Item 1 is `formallySmooth_mapBaseChange_injective`, a statement about `KaehlerDifferential.mapBaseChange R A B`. Item 2 is `basedAdjunction`, defined by choice from the existence theorem `exact_canonical_adjunction`, so the displayed formula is its defining property; the basis $1\otimes b$ is `b.baseChange B`. Item 3 is `basedRelativeCanonicalEquiv R A B n r b c`. Bases are indexed by `Fin n` and `Fin r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/RelativeCanonical.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/RelativeCanonical.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LogKodairaFiberNegative mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.RelativeCanonical
open scoped TensorProduct
open CanonicalAdjunction DifferentialBaseChange

 

 

 

end ReverseLogKodaira.RelativeCanonical

namespace ReverseLogKodaira.BasedRelativeCanonical
-- [generator] trimmed: open CanonicalAdjunction DifferentialBaseChange RelativeCanonical
open CanonicalAdjunction DifferentialBaseChange

lemma formallySmooth_mapBaseChange_injective
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] :
    Function.Injective (KaehlerDifferential.mapBaseChange R A B) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [hy0, map_zero] at hy
  exact hy.symm

 

def basedAdjunction
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] (n r : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    (⋀[B]^n (BaseDifferentials R A B)) ⊗[B] Canonical A B r ≃ₗ[B]
      Canonical R B (n + r) :=
  (exact_canonical_adjunction (KaehlerDifferential.mapBaseChange R A B)
    (KaehlerDifferential.map R A B B) (formallySmooth_mapBaseChange_injective R A B)
    (KaehlerDifferential.exact_mapBaseChange_map R A B)
    (KaehlerDifferential.map_surjective R A B) (b.baseChange B) c).choose

 
def basedRelativeCanonicalEquiv
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] (n r : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    Canonical R B (n + r) ≃ₗ[B] Canonical A B r :=
  (basedAdjunction R A B n r b c).symm.trans
    ((TensorProduct.congr (determinantCoordinate (b.baseChange B))
      (LinearEquiv.refl B (Canonical A B r))).trans
        (TensorProduct.lid B (Canonical A B r)))

end ReverseLogKodaira.BasedRelativeCanonical

namespace ReverseLogKodaira.BasedRelativeCanonical
-- [generator] trimmed: open CanonicalAdjunction DifferentialBaseChange RelativeCanonical
open CanonicalAdjunction DifferentialBaseChange

 

end ReverseLogKodaira.BasedRelativeCanonical

end

end OAI


