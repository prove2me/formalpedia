-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_NonzeroFiber
-- name    : OAI_AlgebraicGeometry_LogKodaira_NonzeroFiber
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:53:48.316868+00:00
-- url     : https://prove2.me/theorems/ebf2a75b-9f8f-4053-bd51-2be4cec7e80a
-- title:
--   The coordinate of a pluricanonical form of a formally smooth algebra with respect to base and relative bases
-- statement:
--   For a homomorphism of commutative rings $R\to A$ write $\Omega_{A/R}$ for the module of Kähler differentials, $d\colon A\to\Omega_{A/R}$ for the universal derivation, $\Omega^n_{A/R}:=\bigwedge^n_A\Omega_{A/R}$ for its $n$-th exterior power and $(\Omega^n_{A/R})^{\otimes m}$ for the $m$-fold tensor product of $\Omega^n_{A/R}$ over $A$. For ring homomorphisms $R\to A\to B$ with $A\to B$ formally smooth, an $A$-basis $b=(\beta_1,\dots,\beta_n)$ of $\Omega_{A/R}$ and a $B$-basis $c$ of $\Omega_{B/A}$ with $r$ elements, $\theta_{b,c}\colon\Omega^{n+r}_{B/R}\xrightarrow{\ \sim\ }\Omega^r_{B/A}$ denotes the relative canonical isomorphism; it satisfies $\theta_{b,c}\big(\tilde\beta_1\wedge\cdots\wedge\tilde\beta_n\wedge z_1\wedge\cdots\wedge z_r\big)=\bar z_1\wedge\cdots\wedge\bar z_r$ for all $z_k\in\Omega_{B/R}$, where $\tilde\beta_i$ is the image of $\beta_i$ in $\Omega_{B/R}$ and $\bar z$ the image of $z$ in $\Omega_{B/A}$. For a basis $c$ with $r$ elements, $\delta_c\colon\Omega^r_{B/A}\to B$ is the determinant coordinate, $\delta_c(w_1\wedge\cdots\wedge w_r)=\det_c(w)$, the determinant of the coordinate matrix of $w_1,\dots,w_r$ in the basis $c$.
--
--   1. **Pluricanonical coordinate.** Let $R\to A\to B$ be ring homomorphisms with $A\to B$ formally smooth, $b$ an $A$-basis of $\Omega_{A/R}$ with $n$ elements, $c$ a $B$-basis of $\Omega_{B/A}$ with $r$ elements, and $m\in\mathbb{N}$. The $B$-linear isomorphism
--   $$\kappa_{b,c}\colon(\Omega^{n+r}_{B/R})^{\otimes m}\xrightarrow{\ \sim\ }B$$
--   applies $\delta_c\circ\theta_{b,c}\colon\Omega^{n+r}_{B/R}\cong B$ to every tensor factor and then multiplies the $m$ resulting elements (the isomorphism $B^{\otimes_B m}\cong B$). Thus, for $z_{j,k}\in\Omega_{B/R}$,
--   $$\kappa_{b,c}\Big(\textstyle\bigotimes_{j=1}^m\big(\tilde\beta_1\wedge\cdots\wedge\tilde\beta_n\wedge z_{j,1}\wedge\cdots\wedge z_{j,r}\big)\Big)=\prod_{j=1}^m\det\nolimits_c\big(\bar z_{j,1},\dots,\bar z_{j,r}\big).$$
--   Equivalently, $\kappa_{b,c}(q)$ is the coefficient of $q$ with respect to the generator $\big(\tilde\beta_1\wedge\cdots\wedge\tilde\beta_n\wedge\tilde c_1\wedge\cdots\wedge\tilde c_r\big)^{\otimes m}$, where $\tilde c_k\in\Omega_{B/R}$ are any lifts of the basis vectors $c_k$.
--   2. **Reindexing a basis.** For an equality $r=r'$, a basis indexed by $\{1,\dots,r\}$ is regarded as a basis indexed by $\{1,\dots,r'\}$.
--
--   Since $\kappa_{b,c}$ is an isomorphism, a pluricanonical numerator $q$ on a chart of the total space of a fibration is nonzero exactly when the function $\kappa_{b,c}(q)$ is nonzero. The locus where this function does not vanish is used to locate fibres to which a nonzero log pluricanonical form restricts nontrivially.
--
--   **Formalization Note** Item 1 is `pluricanonicalCoordinate R A B n r m b c`, built from `basedRelativeCanonicalEquiv`, `determinantCoordinate` and `PiTensorProduct.constantBaseRingEquiv`; item 2 is the transport `basisDegreeTransport`, needed because bases are indexed by `Fin r` and the relative dimension is only known to equal $\dim F$ propositionally.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/NonzeroFiber.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/NonzeroFiber.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LogKodairaFiberNegative mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LatticeBaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_GlobalSpecialization

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.CanonicalSpecialization
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

 

def pluricanonicalCoordinate
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] (n r m : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    Pluricanonical R B (n + r) m ≃ₗ[B] B :=
  (PiTensorProduct.congr fun _ : Fin m =>
    (basedRelativeCanonicalEquiv R A B n r b c).trans (determinantCoordinate c)).trans
      (PiTensorProduct.constantBaseRingEquiv (Fin m) B).toLinearEquiv

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

 

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization

 

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.RelativeCharts

 

end ReverseLogKodaira.RelativeCharts

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.DifferentialBaseChange

def basisDegreeTransport {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M]
    {r r' : ℕ} (h : r = r') (c : Module.Basis (Fin r) B M) :
    Module.Basis (Fin r') B M := h ▸ c

end ReverseLogKodaira.DifferentialBaseChange

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.SmoothProjectiveVariety

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety
open DifferentialBaseChange CanonicalSpecialization FiberChartSpecialization

 

end ReverseLogKodaira.SmoothProjectiveVariety

end

end OAI


