-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
-- name    : OAI_AlgebraicGeometry_LogKodaira_Specialization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:48:44.547381+00:00
-- url     : https://prove2.me/theorems/44885e48-5f94-4303-90e8-98e895d0f0af
-- title:
--   Specialization of top-degree and pluricanonical forms to a fibre, and division by the $m$-th power of a local equation
-- statement:
--   For a homomorphism of commutative rings $R\to A$ write $\Omega_{A/R}$ for the module of Kähler differentials, $d\colon A\to\Omega_{A/R}$ for the universal derivation, $\Omega^n_{A/R}:=\bigwedge^n_A\Omega_{A/R}$ for its $n$-th exterior power and $(\Omega^n_{A/R})^{\otimes m}$ for the $m$-fold tensor product of $\Omega^n_{A/R}$ over $A$. For ring homomorphisms $R\to A\to B$ with $A\to B$ formally smooth, an $A$-basis $b=(\beta_1,\dots,\beta_n)$ of $\Omega_{A/R}$ and a $B$-basis $c$ of $\Omega_{B/A}$ with $r$ elements, $\theta_{b,c}\colon\Omega^{n+r}_{B/R}\xrightarrow{\ \sim\ }\Omega^r_{B/A}$ denotes the relative canonical isomorphism; it satisfies $\theta_{b,c}\big(\tilde\beta_1\wedge\cdots\wedge\tilde\beta_n\wedge z_1\wedge\cdots\wedge z_r\big)=\bar z_1\wedge\cdots\wedge\bar z_r$ for all $z_k\in\Omega_{B/R}$, where $\tilde\beta_i$ is the image of $\beta_i$ in $\Omega_{B/R}$ and $\bar z$ the image of $z$ in $\Omega_{B/A}$.
--
--   **Setting.** Let $R\to A\to B$ be ring homomorphisms with $A\to B$ formally smooth, let $b$ be an $A$-basis of $\Omega_{A/R}$ with $n$ elements and $c$ a $B$-basis of $\Omega_{B/A}$ with $r$ elements. Let moreover $A\to S$, $B\to C$ and $S\to C$ be ring homomorphisms such that the square formed by $A\to B\to C$ and $A\to S\to C$ commutes, and let $\rho\colon\Omega_{B/A}\to\Omega_{C/S}$, $dg\mapsto d\bar g$, be the induced map of differentials. In the application, $A$ and $B$ are coordinate rings of affine charts of the base and of the total space of a fibration, $S=\mathbb{C}$ is the residue field at a point of the base, and $C$ is the function field of the fibre over that point.
--
--   1. **Specialization of canonical forms.** The $B$-linear map
--   $$\operatorname{sp}_{b,c}:=\textstyle\bigwedge^r\rho\circ\theta_{b,c}\colon\ \Omega^{n+r}_{B/R}\longrightarrow\Omega^r_{C/S}.$$
--   2. **Specialization of pluricanonical forms.** Its $m$-th tensor power $\operatorname{sp}^{\otimes m}_{b,c}\colon(\Omega^{n+r}_{B/R})^{\otimes m}\to(\Omega^r_{C/S})^{\otimes m}$, a $B$-linear map.
--   3. **Logarithmic pullback.** For ring homomorphisms $R\to B\to K$ (compatible with $R\to K$) with $K$ a field, $n,m\in\mathbb{N}$ and $t\in B$, the $B$-linear map
--   $$(\Omega^n_{B/R})^{\otimes m}\to(\Omega^n_{K/R})^{\otimes m},\qquad q\mapsto(\bar t^{\,m})^{-1}\,\pi(q),$$
--   where $\pi$ is the map induced on $m$-th tensor powers of $n$-th exterior powers by $\Omega_{B/R}\to\Omega_{K/R}$, and $\bar t$ is the image of $t$ in $K$.
--   4. **Logarithmic specialization.** In the setting above, with $C$ a field and $t\in B$, the $B$-linear map
--   $$(\Omega^{n+r}_{B/R})^{\otimes m}\to(\Omega^r_{C/S})^{\otimes m},\qquad q\mapsto(\bar t^{\,m})^{-1}\operatorname{sp}^{\otimes m}_{b,c}(q),$$
--   with $\bar t$ the image of $t$ in $C$.
--
--   When $B$ is the coordinate ring of an affine chart of a variety, $K$ its function field and $t$ a local equation of a boundary divisor, item 3 writes a rational pluricanonical form with logarithmic poles along $t=0$ as a regular numerator $q$ divided by $t^m$. Item 4 applies the same division after specializing the numerator to a fibre; together they define the restriction of log pluricanonical forms from the total space of a fibration to its fibres.
--
--   **Formalization Note** The items are `specializeCanonical`, `specializePluricanonical`, `logarithmicPullback` and `logarithmicSpecialize`; $\theta_{b,c}$ is `basedRelativeCanonicalEquiv` and $\bigwedge^r\rho$ is `exteriorDifferentialMap A S B C r`. The inverse $(\bar t^{\,m})^{-1}$ is the field inverse, with Lean's convention that the inverse of $0$ is $0$; so both logarithmic maps are the zero map when $\bar t=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/Specialization.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/Specialization.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LogKodairaFiberNegative mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange BasedRelativeCanonical

def specializeCanonical
    (R A B S C : Type*) [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [Algebra.FormallySmooth A B] (n r : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    Canonical R B (n + r) →ₗ[B] Canonical S C r :=
  (exteriorDifferentialMap A S B C r).comp
    (basedRelativeCanonicalEquiv R A B n r b c).toLinearMap

 
def specializePluricanonical
    (R A B S C : Type*) [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [Algebra.FormallySmooth A B] (n r m : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    Pluricanonical R B (n + r) m →ₗ[B] Pluricanonical S C r m :=
  tensorScalarMap B C _ _ (specializeCanonical R A B S C n r b c) m

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange BasedRelativeCanonical

 

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FractionalCanonical
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

 

end ReverseLogKodaira.FractionalCanonical

namespace ReverseLogKodaira.LogarithmicSpecialization
-- [generator] trimmed: open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization

 

def logarithmicPullback
    (R B K : Type*) [CommRing R] [CommRing B] [Field K]
    [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    (n m : ℕ) (t : B) : Pluricanonical R B n m →ₗ[B] Pluricanonical R K n m :=
  ((algebraMap B K t)^m)⁻¹ • pluricanonicalMap R R B K n m

 

def logarithmicSpecialize
    (R A B S C : Type*) [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [Field C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [Algebra.FormallySmooth A B] (n r m : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) (t : B) :
    Pluricanonical R B (n + r) m →ₗ[B] Pluricanonical S C r m :=
  ((algebraMap B C t)^m)⁻¹ • specializePluricanonical R A B S C n r m b c

end ReverseLogKodaira.LogarithmicSpecialization

namespace ReverseLogKodaira.LogarithmicSpecialization
-- [generator] trimmed: open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization

 

end ReverseLogKodaira.LogarithmicSpecialization

namespace ReverseLogKodaira.LogarithmicSpecialization
-- [generator] trimmed: open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization

 

end ReverseLogKodaira.LogarithmicSpecialization

end

end OAI


