-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts
-- name    : OAI_AlgebraicGeometry_LogKodaira_FiberCharts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:51:38.656432+00:00
-- url     : https://prove2.me/theorems/9a81ae29-3fed-490a-906e-660a3f7edde9
-- title:
--   Logarithmic specialization on a chart of a fibration, and affine charts of a fibre as $\mathcal{O}_X(V)\otimes_{\mathcal{O}_Y(U)}\mathbb{C}$
-- statement:
--   Throughout, a *smooth projective variety* is an integral scheme $Z$ whose structure morphism $Z\to\operatorname{Spec}\mathbb{C}$ is smooth of relative dimension $\dim Z$ and factors through a closed immersion into some projective space $\mathbb{P}^N_{\mathbb{C}}$; every ring of sections $\mathcal{O}_Z(W)$ is a $\mathbb{C}$-algebra through the structure morphism, and $K(Z)$ denotes the function field. For a smooth projective variety $X$, write $\omega^m_{K(X)}=\big(\textstyle\bigwedge^{\dim X}_{K(X)}\Omega_{K(X)/\mathbb{C}}\big)^{\otimes m}$ for the $K(X)$-vector space of rational $m$-pluricanonical forms.
--
--   A *reduced simple normal crossing (SNC) boundary* $E$ on a smooth projective variety $X$ is given by finitely many Cartier ideal sheaves $\mathcal{I}_{E_1},\dots,\mathcal{I}_{E_k}$ with transverse intersections (every intersection of $p\ge1$ components is empty or smooth of relative dimension $\dim X-p$ over $\mathbb{C}$) whose product $\mathcal{I}_E=\prod_i\mathcal{I}_{E_i}$ is again Cartier: every point has an affine open neighbourhood $W$ on which $\mathcal{I}_E(W)=(t)$ for a nonzero $t\in\mathcal{O}_X(W)$. Its support $\operatorname{Supp}E$ is the zero locus of $\mathcal{I}_E$.
--
--   For smooth projective varieties $X$ and $Y$ with reduced SNC boundaries $E$ and $D$, a *boundary fibration* $f\colon(X,E)\to(Y,D)$ is a surjective morphism $f\colon X\to Y$ over $\mathbb{C}$ whose fibres over all complex points are connected and with $f^{-1}(\operatorname{Supp}D)\subseteq\operatorname{Supp}E$ (no smoothness is assumed). A *complex point* $y$ of $Y$ is a section $\operatorname{Spec}\mathbb{C}\to Y$ of the structure morphism; we write $y\in U$ when its image point lies in $U$, and $a(y)\in\mathbb{C}$ for the value at $y$ of a section $a\in\mathcal{O}_Y(U)$. A *fibre model* of $f$ over $y$ is a triple $(F,i,E_F)$ consisting of a smooth projective variety $F$, a morphism $i\colon F\to X$ such that $F$, together with $i$ and its structure morphism, is a fibre product $X\times_{Y,y}\operatorname{Spec}\mathbb{C}$, and a reduced SNC boundary $E_F$ on $F$ whose ideal sheaf is the pullback $i^{-1}\mathcal{I}_E\cdot\mathcal{O}_F$. For opens $U\subseteq Y$ and $V\subseteq f^{-1}(U)$, $f^{*}\colon\mathcal{O}_Y(U)\to\mathcal{O}_X(V)$ is the pullback of sections, and when $i^{-1}(V)\neq\emptyset$ we write $g|_F\in K(F)$ for the image of $i^{*}g\in\mathcal{O}_F(i^{-1}V)$ in the function field of $F$ ($g\in\mathcal{O}_X(V)$).
--
--   For a homomorphism of commutative rings $R\to A$ write $\Omega_{A/R}$ for the module of Kähler differentials, $d\colon A\to\Omega_{A/R}$ for the universal derivation, $\Omega^n_{A/R}:=\bigwedge^n_A\Omega_{A/R}$ for its $n$-th exterior power and $(\Omega^n_{A/R})^{\otimes m}$ for the $m$-fold tensor product of $\Omega^n_{A/R}$ over $A$. For ring homomorphisms $R\to A\to B$ with $A\to B$ formally smooth, an $A$-basis $b=(\beta_1,\dots,\beta_n)$ of $\Omega_{A/R}$ and a $B$-basis $c$ of $\Omega_{B/A}$ with $r$ elements, $\theta_{b,c}\colon\Omega^{n+r}_{B/R}\xrightarrow{\ \sim\ }\Omega^r_{B/A}$ denotes the relative canonical isomorphism; it satisfies $\theta_{b,c}\big(\tilde\beta_1\wedge\cdots\wedge\tilde\beta_n\wedge z_1\wedge\cdots\wedge z_r\big)=\bar z_1\wedge\cdots\wedge\bar z_r$ for all $z_k\in\Omega_{B/R}$, where $\tilde\beta_i$ is the image of $\beta_i$ in $\Omega_{B/R}$ and $\bar z$ the image of $z$ in $\Omega_{B/A}$.
--
--   Fix a boundary fibration $f\colon(X,E)\to(Y,D)$, a complex point $y$ of $Y$, a fibre model $(F,i,E_F)$ of $f$ over $y$, an affine open $U\subseteq Y$ with $y\in U$ and $A:=\mathcal{O}_Y(U)$, and an affine open $V\subseteq X$ with $V\subseteq f^{-1}(U)$ and $B:=\mathcal{O}_X(V)$, an $A$-algebra via $f^{*}$.
--
--   1. **Logarithmic numerator map.** Assume $i^{-1}(V)\neq\emptyset$. Then $A\to B$ (via $f^*$), $A\to\mathbb{C}$ (evaluation $a\mapsto a(y)$), $B\to K(F)$ ($g\mapsto g|_F$) and $\mathbb{C}\to K(F)$ (constants) form a commutative square of ring homomorphisms, compatible with the $\mathbb{C}$-algebra structures of $A$ and $B$. Given a proof that $A\to B$ is formally smooth, numbers $n,r,m\in\mathbb{N}$, an $A$-basis $b$ of $\Omega_{A/\mathbb{C}}$ with $n$ elements, a $B$-basis $c$ of $\Omega_{B/A}$ with $r$ elements and $t\in B$, the construction returns the logarithmic specialization for this square, i.e. the $B$-linear map
--   $$(\Omega^{n+r}_{B/\mathbb{C}})^{\otimes m}\longrightarrow(\Omega^r_{K(F)/\mathbb{C}})^{\otimes m},\qquad q\longmapsto\big((t|_F)^m\big)^{-1}\big(\textstyle\bigwedge^r\rho\circ\theta_{b,c}\big)^{\otimes m}(q),$$
--   where $\rho\colon\Omega_{B/A}\to\Omega_{K(F)/\mathbb{C}}$, $dg\mapsto d(g|_F)$. For $r=\dim F$ the target is the space $\omega^m_{K(F)}$ of rational $m$-pluricanonical forms on $F$.
--   2. **Affine charts of the fibre.** (No nonemptiness assumption.) The preimage $i^{-1}(V)$ is an affine open of $F$, and the square of rings formed by $f^{*}\colon\mathcal{O}_Y(U)\to\mathcal{O}_X(V)$, the evaluation $\mathcal{O}_Y(U)\to\mathbb{C}$ at $y$, the pullback $i^{*}\colon\mathcal{O}_X(V)\to\mathcal{O}_F(i^{-1}V)$ and the constants $\mathbb{C}\to\mathcal{O}_F(i^{-1}V)$ is a pushout of commutative rings; that is,
--   $$\mathcal{O}_F\big(i^{-1}V\big)\cong\mathcal{O}_X(V)\otimes_{\mathcal{O}_Y(U)}\mathbb{C}.$$
--
--   Item 1 is how the restriction of a log pluricanonical form of $(X,E)$ to the fibre $F$ is computed on a chart: the form is written as a numerator $q$ over a power of a local equation $t$ of $E$, and $q$ is specialized to $F$. Item 2 identifies the coordinate rings of the induced affine charts of the fibre with the base change of the charts of $X$, which is what is needed to check that the specialized form is regular, respectively has logarithmic poles, on $F$.
--
--   **Formalization Note** `logarithmicNumerator f y F U hy V e` is a function of the formal-smoothness proof and of `n r m b c t`; it installs the algebra structures above locally (using `appLE`, `complexPointEvaluation` and `chartToFunctionField`), proves the required scalar-tower compatibilities with `appLE_constants` and `fiber_chart_base_scalar`, and returns `logarithmicSpecialize` with $R=S=\mathbb{C}$ and $C=K(F)$. The inverse is the field inverse in $K(F)$, with the convention that the inverse of $0$ is $0$. Item 2 is the theorem `fiber_affine_chart_pushout`, stated with `IsPushout` in `CommRingCat`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/LogKodaira/FiberCharts.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/FiberCharts.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization

 

def logarithmicNumerator
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D)
    (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1)
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] :=
  letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    (f.hom.appLE U.1 V.1 e).hom.toAlgebra
  letI : Algebra Γ(Y.scheme, U.1) ℂ := (complexPointEvaluation y U.1 hy).toAlgebra
  letI : Algebra Γ(Y.scheme, U.1) F.variety.scheme.functionField :=
    ((algebraMap ℂ F.variety.scheme.functionField).comp
      (complexPointEvaluation y U.1 hy)).toAlgebra
  letI : Algebra Γ(X.scheme, V.1) F.variety.scheme.functionField :=
    (chartToFunctionField F.inclusion V.1).toAlgebra
  letI : IsScalarTower ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (appLE_constants f.hom f.over_base U.1 V.1 e c).symm
  letI : IsScalarTower Γ(Y.scheme, U.1) ℂ F.variety.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower Γ(Y.scheme, U.1) Γ(X.scheme, V.1) F.variety.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (fiber_chart_base_scalar f y F U.1 hy V.1 e a).symm
  fun (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
    (n r m : ℕ)
    (b : Module.Basis (Fin n) Γ(Y.scheme, U.1) (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
    (c : Module.Basis (Fin r) Γ(X.scheme, V.1)
      (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
    (t : Γ(X.scheme, V.1)) =>
    letI := hsm
    LogarithmicSpecialization.logarithmicSpecialize ℂ Γ(Y.scheme, U.1)
      Γ(X.scheme, V.1) ℂ F.variety.scheme.functionField n r m b c t
end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

theorem fiber_affine_chart_pushout
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1) (V : X.scheme.affineOpens)
    (e : V.1 ≤ f.hom ⁻¹ᵁ U.1) :
    IsAffineOpen (F.inclusion ⁻¹ᵁ V.1) ∧
      IsPushout (f.hom.appLE U.1 V.1 e)
        (CommRingCat.ofHom (complexPointEvaluation y U.1 hy))
        (F.inclusion.app V.1)
        (CommRingCat.ofHom (F.variety.constants (F.inclusion ⁻¹ᵁ V.1))) := by
  let W := F.inclusion ⁻¹ᵁ V.1
  let C : complexBase.Opens := ⊤
  let : IsAffine U.1 := U.2
  let : IsAffine V.1 := V.2
  let : IsAffine C.toScheme := isAffineOpen_top complexBase
  have hW : W = F.inclusion ⁻¹ᵁ V.1 ⊓ F.variety.structural ⁻¹ᵁ C := by simp [W, C]
  have hp := Scheme.Hom.isPullback_resLE F.square
    (complexPoint_preimage_top y U.1 hy) e hW
  let : IsAffine W.toScheme := IsAffine.of_isPullback hp
  refine ⟨‹IsAffine W.toScheme›, ?_⟩
  have hr := isPushout_appTop_of_isPullback hp
  refine hr.of_iso U.1.topIso V.1.topIso
    (C.topIso ≪≫ Scheme.ΓSpecIso (CommRingCat.of ℂ)) W.topIso ?_ ?_ ?_ ?_
  · simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.trans_hom,
      Category.assoc]
    rfl
  · simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Scheme.Hom.appLE_eq_app]
  · simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.trans_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change C.topIso.hom ≫ F.variety.structural.appLE C W _ =
      C.topIso.hom ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ F.variety.structural.appLE C W _
    simp

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange BasedRelativeCanonical

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

 

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.SmoothProjectiveVariety

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

 

end ReverseLogKodaira.FiberChartSpecialization

end

end OAI


