-- Prove2me | Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
-- name    : AlgebraicGeometry_TangentCoordsOfPairAtVia
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/15c6a0c1-5094-52d4-9de3-10981c8aa656
-- title:
--   Tangent coordinates of a pair via an open comparison map
-- statement:
--   Throughout, $T'$ is a commutative local ring with residue field $k =$ `ResidueField T'`, $I \subseteq T'$ an ideal, $V$ a $k$-module (with the central bimodule data and a compatible $T'$-module structure), $\iota \colon V \to T'$ a $T'$-linear map, and $C$ a commutative $T'$-algebra. Write $E = (k \otimes_{T'} C) \otimes_k \mathrm{TrivSqZeroExt}(k,V)$ for the thickening, with its two structure maps `thickeningFst`, `thickeningSnd` exhibiting $\operatorname{Spec} E$ as the fibre product of $\operatorname{Spec}(k \otimes_{T'} C)$ and the square-zero scheme $\operatorname{Spec}(k \oplus V)$ over $\operatorname{Spec} k$.
--
--   The predicate `IsTangentCoordsOfPairAtVia` takes two morphisms $u, v \colon \operatorname{Spec} C \to Y$, a $k$-scheme $x_k \colon A_k \to \operatorname{Spec} k$ carrying a relative group law $L_k$ (a functorial group structure on $T$-points over $\operatorname{Spec} k$, natural in $T$), an open $W \subseteq A_k$ together with a comparison morphism $a_W \colon W \to Y$, a further open $U_e \subseteq A_k$, and a bare function $c \colon \Gamma(A_k,U_e) \to \mathrm{Hom}_k(V^\vee, k \otimes_{T'} C)$. It asserts the existence of $w_0 \colon \operatorname{Spec} E \to W$ whose composite with the open immersion $W \hookrightarrow A_k$ and with $x_k$ is the structure map `thickeningSnd` followed by `SquareZero.toBase`, and of $w_1 \colon \operatorname{Spec} E \to U_e$, such that: (i) $w_0$ followed by $a_W$ is a tangent morphism of the pair $(u,v)$ in the sense of `IsTangentOfPair`, i.e. it factors as $\operatorname{Spec}$ of a Schlessinger map $\vartheta$ on the ring of pairs congruent modulo $I\,C$ followed by a morphism $\varphi$ restricting to $u$ and $v$ along the two projections; (ii) $w_1$ followed by $U_e \hookrightarrow A_k$ is the underlying morphism of the $L_k$-translate of $w_0 \gg (W \hookrightarrow A_k)$ to the unit section, a relative tangent point in the sense of `RelTangentPoints`; and (iii) $c$ coincides with `tangentCoords` of the ring map $\Gamma(A_k,U_e) \to E$ induced by $w_1$ on sections, that is, $c(f)(\xi)$ is obtained from the $V$-component of the image of $f$ in $E$ by contracting with $\xi \in V^\vee$.
--
--   This is the variant of `IsTangentCoordsOfPairAt` in which the comparison with $Y$ is given only on an open $W$ of $A_k$; the group law, the translation to the unit and the chart $U_e$ still live on all of $A_k$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient material used here (`TrivSqZeroExt`, `Module.Dual`, residue fields of local rings, tensor products and the pushout/pullback comparison for affine schemes); the relative group law structure, the square-zero relative tangent points, the pair-tangent and tangent-coordinate predicates are the project's own.
--
--   **Where it is used.** The predicate is used in the good-reduction and Néron model infrastructure, where square-zero deformations of an abelian scheme and of its group law are compared through local lifts $Y$ that only receive an open piece $W$ of the special fibre; the tangent coordinates of a pair provide the cochain data for the corresponding lifting obstructions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TangentCoordsOfPairAtVia.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt

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

def IsTangentCoordsOfPairAtVia {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Y) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))) : Prop :=
  ∃ (w₀ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (W : Scheme.{u}))
    (hw₀ : (w₀ ≫ W.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})),
    IsTangentOfPair I V ι C u v (w₀ ≫ aW) ∧
    w₁ ≫ Ue.ι = (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
                  (thickening_isPullback V C) (w₀ ≫ W.ι) hw₀).1 ∧
    c = tangentCoords T' V C (chartRingHom V C Ue w₁)

end AlgebraicGeometry.SmallExtension

end


