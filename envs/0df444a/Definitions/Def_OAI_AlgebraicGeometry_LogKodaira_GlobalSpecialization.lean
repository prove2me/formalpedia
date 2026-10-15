-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_GlobalSpecialization
-- name    : OAI_AlgebraicGeometry_LogKodaira_GlobalSpecialization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:52:57.266945+00:00
-- url     : https://prove2.me/theorems/55da5eb3-74b7-403d-ad66-12358c308843
-- title:
--   Numerator charts of a rational pluricanonical form near a fibre, and the value of a chart on the fibre
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; every ring of sections $\mathcal{O}_Z(W)$ is a $\mathbb{C}$-algebra through the structure morphism, and $K(Z)$ denotes the function field. For a smooth projective variety $X$, write $\omega^m_{K(X)}=\big(\textstyle\bigwedge^{\dim X}_{K(X)}\Omega_{K(X)/\mathbb{C}}\big)^{\otimes m}$ for the $K(X)$-vector space of rational $m$-pluricanonical forms.
--
--   A *reduced simple normal crossing (SNC) boundary* $E$ on a smooth projective variety $X$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim X-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_X(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$.
--
--   For smooth projective varieties $X$ and $Y$ with reduced SNC boundaries $E$ and $D$, a *boundary fibration* $f\colon(X,E)\to(Y,D)$ is a surjective morphism $f\colon X\to Y$ over $\mathbb{C}$ whose fibres over all complex points are connected and with $f^{-1}(\operatorname{Supp}D)\subseteq\operatorname{Supp}E$ (no smoothness is assumed). A *complex point* $y$ of $Y$ is a section $\operatorname{Spec}\mathbb{C}\to Y$ of the structure morphism; we write $y\in U$ when its image point lies in $U$, and $a(y)\in\mathbb{C}$ for the value at $y$ of a section $a\in\mathcal{O}_Y(U)$. A *fibre model* of $f$ over $y$ is a triple $(F,i,E_F)$ consisting of a smooth projective variety $F$, a morphism $i\colon F\to X$ such that $F$, together with $i$ and its structure morphism, is a fibre product $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$, and a reduced SNC boundary $E_F$ on $F$ whose ideal sheaf is the pullback $i^{-1}\mathcal{I}_E\cdot\mathcal{O}_F$. For opens $U\subseteq Y$ and $V\subseteq f^{-1}(U)$, $f^{*}\colon\mathcal{O}_Y(U)\to\mathcal{O}_X(V)$ is the pullback of sections, and when $i^{-1}(V)\neq\emptyset$ we write $g|_F\in K(F)$ for the image of $i^{*}g\in\mathcal{O}_F(i^{-1}V)$ in the function field of $F$ ($g\in\mathcal{O}_X(V)$).
--
--   For a homomorphism of commutative rings $R\to A$ write $\Omega_{A/R}$ for the module of Kähler differentials, $d\colon A\to\Omega_{A/R}$ for the universal derivation, $\Omega^n_{A/R}:=\bigwedge^n_A\Omega_{A/R}$ for its $n$-th exterior power and $(\Omega^n_{A/R})^{\otimes m}$ for the $m$-fold tensor product of $\Omega^n_{A/R}$ over $A$. For ring homomorphisms $R\to A\to B$ with $A\to B$ formally smooth, an $A$-basis $b=(\beta_1,\dots,\beta_n)$ of $\Omega_{A/R}$ and a $B$-basis $c$ of $\Omega_{B/A}$ with $r$ elements, $\theta_{b,c}\colon\Omega^{n+r}_{B/R}\xrightarrow{\ \sim\ }\Omega^r_{B/A}$ denotes the relative canonical isomorphism; it satisfies $\theta_{b,c}\big(\tilde\beta_1\wedge\cdots\wedge\tilde\beta_n\wedge z_1\wedge\cdots\wedge z_r\big)=\bar z_1\wedge\cdots\wedge\bar z_r$ for all $z_k\in\Omega_{B/R}$, where $\tilde\beta_i$ is the image of $\beta_i$ in $\Omega_{B/R}$ and $\bar z$ the image of $z$ in $\Omega_{B/A}$.
--
--   1. **Degree transport.** For a ring homomorphism $R\to B$ and an equality $n=n'$ of natural numbers, the identification $(\Omega^n_{B/R})^{\otimes m}\cong(\Omega^{n'}_{B/R})^{\otimes m}$ given by the identity.
--   2. **Numerator chart.** Fix a boundary fibration $f\colon(X,E)\to(Y,D)$, a complex point $y$ of $Y$, a fibre model $(F,i,E_F)$ of $f$ over $y$, an affine open $U\subseteq Y$ with $A:=\mathcal{O}_Y(U)$, the hypothesis $\dim X=\dim Y+\dim F$, an integer $m\in\mathbb{N}$ and an arbitrary rational form $s\in\omega^m_{K(X)}$. A *numerator chart* $P=(V,c,t,q)$ for $s$ consists of (a) an affine open $V\subseteq X$ with $V\subseteq f^{-1}(U)$, $V\neq\emptyset$ and $i^{-1}(V)\neq\emptyset$, where $B:=\mathcal{O}_X(V)$ is an $A$-algebra via $f^{*}$; (b) the property that $A\to B$ is formally smooth, together with a $B$-basis $c=(c_1,\dots,c_{\dim F})$ of $\Omega_{B/A}$; (c) an element $t\in B$ with $t\neq0$ and $\mathcal{I}_E(V)=(t)$; and (d) a *numerator* $q\in(\Omega^{\dim Y+\dim F}_{B/\mathbb{C}})^{\otimes m}$ such that
--   $$(\bar t^{\,m})^{-1}\,\iota_V(q)=s\qquad\text{in }\big(\textstyle\bigwedge^{\dim Y+\dim F}_{K(X)}\Omega_{K(X)/\mathbb{C}}\big)^{\otimes m},$$
--   where $\iota_V$ is the map induced by $B\to K(X)$ on $m$-th tensor powers of exterior powers of differentials, $\bar t$ is the image of $t$ in $K(X)$, and $s\in\omega^m_{K(X)}$ is transported to degree $\dim Y+\dim F$ along $\dim X=\dim Y+\dim F$ by item 1.
--   3. **Value of a chart.** For a numerator chart $P=(V,c,t,q)$, the hypothesis $y\in U$ and an $A$-basis $b$ of $\Omega_{A/\mathbb{C}}$ with $\dim Y$ elements, the *value* of $P$ is the logarithmic specialization of the numerator to the fibre,
--   $$\sigma_P(b):=\big((t|_F)^m\big)^{-1}\big(\textstyle\bigwedge^{\dim F}\rho\circ\theta_{b,c}\big)^{\otimes m}(q)\in\omega^m_{K(F)},$$
--   where $\rho\colon\Omega_{B/A}\to\Omega_{K(F)/\mathbb{C}}$, $dg\mapsto d(g|_F)$.
--
--   Heuristically, $\sigma_P(b)$ is obtained from $s$ by dividing by $(\beta_1\wedge\cdots\wedge\beta_{\dim Y})^{\otimes m}$ pulled back from the base and restricting to the fibre $F$. When in addition $f$ is stratum-smooth (smooth over $Y\setminus\operatorname{Supp}D$, also on every stratum of $E$), $U\subseteq Y\setminus\operatorname{Supp}D$, $y\in U$ and $s$ is a log $m$-pluriform, these values are shown to be independent of the chart and to form a log $m$-pluriform on $(F,E_F)$; this is the restriction of log pluricanonical forms to fibres.
--
--   **Formalization Note** Item 1 is `degreeTransport` (defined by substituting the equality), item 2 is the structure `NumeratorChart f y F U hdim m s` with fields `V`, `overOpen`, `nonempty`, `fiberNonempty`, `formallySmooth`, `relativeBasis`, `equation`, `equation_ne_zero`, `ideal_eq`, `numerator`, `source_eq`, and item 3 is `NumeratorChart.value P hy b`, defined through `logarithmicNumerator`. The structure does not require $y\in U$, $U$ to avoid $\operatorname{Supp}D$, or $s$ to be a log pluriform. The inverses are field inverses with the convention that the inverse of $0$ is $0$ (in $K(X)$ the element $\bar t$ is nonzero because $t\neq0$ and $X$ is integral).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/GlobalSpecialization.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/GlobalSpecialization.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.DifferentialBaseChange

 
def degreeTransport (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    {n n' : ℕ} (h : n = n') (m : ℕ) :
    Pluricanonical R B n m ≃ₗ[B] Pluricanonical R B n' m := by
  subst n'
  exact LinearEquiv.refl B _

end ReverseLogKodaira.DifferentialBaseChange

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

 

structure NumeratorChart
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) where
  V : X.scheme.affineOpens
  overOpen : V.1 ≤ f.hom ⁻¹ᵁ U.1
  nonempty : Nonempty V.1
  fiberNonempty : Nonempty (F.inclusion ⁻¹ᵁ V.1)
  formallySmooth :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 overOpen).hom.toAlgebra
    Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1)
  relativeBasis :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 overOpen).hom.toAlgebra
    Module.Basis (Fin F.variety.dimension) Γ(X.scheme, V.1)
      (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
  equation : Γ(X.scheme, V.1)
  equation_ne_zero : equation ≠ 0
  ideal_eq : E.ideal.ideal V = Ideal.span {equation}
  numerator : Pluricanonical ℂ Γ(X.scheme, V.1) (Y.dimension + F.variety.dimension) m
  source_eq :
    letI := nonempty
    logarithmicPullback ℂ Γ(X.scheme, V.1) X.scheme.functionField
      (Y.dimension + F.variety.dimension) m equation numerator =
        degreeTransport ℂ X.scheme.functionField hdim m s

namespace NumeratorChart
variable {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
  {f : BoundaryFibration X Y E D} {y : Y.ComplexPoint} {F : FiberModel f y}
  {U : Y.scheme.affineOpens} {hdim : X.dimension = Y.dimension + F.variety.dimension}
  {m : ℕ} {s : X.RationalPluriform m}

def value (P : NumeratorChart f y F U hdim m s) (hy : y.point ∈ U.1)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1))) : F.variety.RationalPluriform m :=
  letI := P.fiberNonempty
  logarithmicNumerator f y F U hy P.V P.overOpen P.formallySmooth
    Y.dimension F.variety.dimension m b P.relativeBasis P.equation P.numerator

end NumeratorChart
end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

namespace NumeratorChart

end NumeratorChart
end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization.NumeratorChart
open SmoothProjectiveVariety DifferentialBaseChange

variable {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
  {f : BoundaryFibration X Y E D} {y : Y.ComplexPoint} {F : FiberModel f y}
  {U : Y.scheme.affineOpens} {hdim : X.dimension = Y.dimension + F.variety.dimension}
  {m : ℕ} {s : X.RationalPluriform m}

end ReverseLogKodaira.FiberChartSpecialization.NumeratorChart

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

 

end ReverseLogKodaira.FiberChartSpecialization

end

end OAI


