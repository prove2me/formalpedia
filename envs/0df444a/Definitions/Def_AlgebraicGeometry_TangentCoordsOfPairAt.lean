-- Prove2me | Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
-- name    : AlgebraicGeometry_TangentCoordsOfPairAt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/8b204ec9-0ea8-5dd3-bcb4-82c9bd50ed89
-- title:
--   Tangent coordinates of a pair in a chart at the unit
-- statement:
--   Throughout, $T'$ is a commutative local ring with residue field $k$, $I \subseteq T'$ an ideal, $V$ a $k$-module (with compatible right module and central-scalar structures) which is also a $T'$-module over the tower $T' \to k$, $\iota \colon V \to T'$ a $T'$-linear map, and $C$ a commutative $T'$-algebra; `thickening T' V C` denotes $(k \otimes_{T'} C) \otimes_k \mathrm{TrivSqZeroExt}\,k\,V$, whose spectrum is the fibre product of $\operatorname{Spec}(k \otimes_{T'} C)$ with the square-zero disc $\operatorname{Spec}(k \oplus V)$ over $\operatorname{Spec} k$.
--
--   `chartRingHom` is pullback of functions along a morphism $w_1 \colon \operatorname{Spec}(\mathrm{thickening}\,T'\,V\,C) \to U_e$ into an open subscheme $U_e$ of a scheme $A_k$: the ring map $\Gamma(A_k, U_e) \to \mathrm{thickening}\,T'\,V\,C$ obtained from the identification of $\Gamma(A_k,U_e)$ with the global sections of $U_e$, the map on global sections induced by $w_1$, and the identification of the global sections of an affine spectrum with its ring.
--
--   `IsTangentCoordsOfPairAt` is a predicate on the data: a scheme $Y$ with two morphisms $u, v \colon \operatorname{Spec} C \to Y$; a scheme $A_k$ with a structure morphism $x_k \colon A_k \to \operatorname{Spec} k$, a relative group law $L_k$ on $x_k$ (a functorial group structure on the $k$-points of $x_k$ over arbitrary bases, with naturality in the base), a morphism $a_k \colon A_k \to Y$, an open $U_e \subseteq A_k$, and a function $c$ from $\Gamma(A_k, U_e)$ to $\operatorname{Hom}_k(V^\vee, k \otimes_{T'} C)$. It asserts the existence of $w_0 \colon \operatorname{Spec}(\mathrm{thickening}\,T'\,V\,C) \to A_k$ lying over the structure map of the thickening, and of $w_1 \colon \operatorname{Spec}(\mathrm{thickening}\,T'\,V\,C) \to U_e$, such that three conditions hold. First, $w_0$ followed by $a_k$ is a tangent morphism of the pair $(u,v)$ in the sense of `IsTangentOfPair`: there are a ring map $\vartheta$ from the subring of pairs in $C \times C$ congruent modulo $I\cdot C$ to the thickening, satisfying the two Schlessinger normalisations (diagonal pairs $(a,a)$ go to $a \otimes 1$, and pairs $(0, \iota(v)c)$ go to $c \otimes \mathrm{inr}\,v$), and a morphism $\varphi$ from the spectrum of that subring to $Y$ restricting along the two projections to $u$ and $v$, with $w_0 \circ a_k = \varphi \circ \operatorname{Spec}\vartheta$. Second, $w_1$ followed by the open immersion $U_e \to A_k$ is the left translate of $w_0$ by the inverse of its restriction along the zero section, formed in $L_k$, which is a relative tangent point based at the unit section. Third, $c$ is the tangent-coordinate function of the ring map `chartRingHom` of $w_1$: the $V$-component of the image of a section, taken in $(k \otimes_{T'} C) \otimes_k V$, read as a $k$-linear map $V^\vee \to k \otimes_{T'} C$ via $m \otimes w \mapsto (\xi \mapsto \xi(w)\,m)$. Thus the predicate fixes a chart at the unit and records the coordinates in that chart, rather than quantifying over an abstract dictionary of tangent identifications.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used (trivial square-zero extension `TrivSqZeroExt`, residue fields of local rings, `Module.Dual`, schemes and pullbacks); the relative group law on a scheme over an affine base, relative tangent points, the ring of pairs congruent modulo an ideal together with the Schlessinger normalisation, and the tangent-coordinate maps are the project's own definitions.
--
--   **Where it is used.** These definitions belong to the infinitesimal-lifting infrastructure for smooth group schemes over a local base: a pair of morphisms out of $\operatorname{Spec} C$ agreeing modulo a small ideal determines, after translation to the unit of the special fibre, a tangent vector whose coordinates in a fixed affine chart are recorded by the predicate. They are used in the Néron model and good-reduction analysis of Jacobians that feeds the Galois-representation part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TangentCoordsOfPairAt.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T')
  (C : Type u) [CommRing C] [Algebra T' C]

def chartRingHom {Ak : Scheme.{u}} (Ue : Ak.Opens)
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) :
    Γ(Ak, Ue) →+* thickening T' V C :=
  (Ue.topIso.inv ≫ w₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (thickening T' V C))).hom).hom

def IsTangentCoordsOfPairAt {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))) : Prop :=
  ∃ (w₀ : Spec (CommRingCat.of (thickening T' V C)) ⟶ Ak)
    (hw₀ : w₀ ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})),
    IsTangentOfPair I V ι C u v (w₀ ≫ ak) ∧
    w₁ ≫ Ue.ι = (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
                  (thickening_isPullback V C) w₀ hw₀).1 ∧
    c = tangentCoords T' V C (chartRingHom V C Ue w₁)

end AlgebraicGeometry.SmallExtension

end


