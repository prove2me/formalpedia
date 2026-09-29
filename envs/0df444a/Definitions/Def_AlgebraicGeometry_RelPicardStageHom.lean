-- Prove2me | Definitions.Def_AlgebraicGeometry_RelPicardStageHom
-- name    : AlgebraicGeometry_RelPicardStageHom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/1805d2b2-f525-5624-936e-74d446e099d2
-- title:
--   Stage morphisms on Spec and base change of two-chart covers
-- statement:
--   Fix a commutative ring $R$. For $R$-algebras $A_0$, $A'$ and an $R$-algebra homomorphism $f : A_0 \to A'$, `stageHom R f` is the induced morphism $\operatorname{Spec} A' \to \operatorname{Spec} A_0$, regarded as a morphism of schemes over $\operatorname{Spec} R$: here `SchemeHomOver g h` denotes the subtype of morphisms $\varphi$ with $\varphi \circ h = g$ (composition written diagrammatically), and `specMap R A` is the morphism $\operatorname{Spec} A \to \operatorname{Spec} R$ induced by the structure map $R \to A$, so that the second component of `stageHom R f` is the commutativity of the triangle, obtained from $f$ being $R$-linear. The companion lemma `stageHom_val` records that the underlying scheme morphism is $\operatorname{Spec}$ applied to the ring homomorphism underlying $f$.
--
--   The remaining three statements concern how such a morphism interacts with a two-chart affine cover after base change. Let $C$ be a scheme, $c : C \to \operatorname{Spec} R$, and let $\mathcal V$ consist of two affine opens $U_0, U_1$ of $C$ whose union is all of $C$ and whose intersection is again affine. For $R$-algebras $A_0, A'$ and any $\psi \in$ `SchemeHomOver (specMap R A') (specMap R A₀)`, `RelPicard.baseChangeSnd c ψ` is the induced morphism $C \times_{\operatorname{Spec} R} \operatorname{Spec} A' \to C \times_{\operatorname{Spec} R} \operatorname{Spec} A_0$ (identity on $C$, $\psi$ on the second factor). `baseChangeSnd_fst` states that this morphism followed by the first projection is the first projection, i.e. it is a morphism over $C$. Since the charts of the base-changed cover $\mathcal V$ over $A$ are by definition the preimages of $U_0$, $U_1$ under the first projection, it follows that the preimage under `baseChangeSnd c ψ` of the $A_0$-chart $U_0$ (respectively $U_1$, respectively $U_0 \cap U_1$) equals the corresponding $A'$-chart. These are equalities of open subsets, proved rather than holding by definition.
--
--   **Relation to Mathlib.** `SchemeHomOver` and the two-chart affine cover structure are the project's own packaging; the underlying ingredients ($\operatorname{Spec}$ as a functor, fibre products of schemes, preimages of opens along a morphism) are Mathlib's.
--
--   **Where it is used.** This is vocabulary for the relative Picard presheaf of rigidified line bundles: `baseChangeSnd` is the transition morphism along which line bundles are pulled back, and the compatibility with a two-chart affine cover lets Čech computations on the two charts be carried along a system of $R$-algebras, for instance when passing to a limit over finitely generated subalgebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardStageHom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.RelPicard.LFP

open Scheme.TwoAffineOpenCover

variable (R : Type u) [CommRing R]

noncomputable def stageHom {A₀ A' : Type u} [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A']
    (f : A₀ →ₐ[R] A') : SchemeHomOver (specMap R A') (specMap R A₀) :=
  ⟨Spec.map (CommRingCat.ofHom f.toRingHom), by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    change f.toRingHom (algebraMap R A₀ x) = algebraMap R A' x
    exact f.commutes x⟩

@[simp] theorem stageHom_val {A₀ A' : Type u} [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A']
    (f : A₀ →ₐ[R] A') : (stageHom R f).1 = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

end AlgebraicGeometry.RelPicard.LFP

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    {A₀ A' : Type u} [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A']
    (ψ : SchemeHomOver (specMap R A') (specMap R A₀))

theorem baseChangeSnd_fst :
    RelPicard.baseChangeSnd c ψ ≫ Limits.pullback.fst c (specMap R A₀) =
      Limits.pullback.fst c (specMap R A') :=
  (Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem baseChangeSnd_preimage_U0 :
    RelPicard.baseChangeSnd c ψ ⁻¹ᵁ (𝒱.pullback c A₀).U0 = (𝒱.pullback c A').U0 := by
  rw [pullback_U0, pullback_U0, ← Scheme.Hom.comp_preimage, baseChangeSnd_fst]

theorem baseChangeSnd_preimage_U1 :
    RelPicard.baseChangeSnd c ψ ⁻¹ᵁ (𝒱.pullback c A₀).U1 = (𝒱.pullback c A').U1 := by
  rw [pullback_U1, pullback_U1, ← Scheme.Hom.comp_preimage, baseChangeSnd_fst]

theorem baseChangeSnd_preimage_inf :
    RelPicard.baseChangeSnd c ψ ⁻¹ᵁ ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1) =
      (𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1 := by
  rw [Scheme.Hom.preimage_inf, baseChangeSnd_preimage_U0, baseChangeSnd_preimage_U1]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover


