-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverPreimage
-- name    : AlgebraicGeometry_TwoAffineOpenCoverPreimage
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/0715a20a-16cf-51dc-bd5f-1ff71f38847f
-- title:
--   Preimage of a two-chart affine cover along an affine morphism
-- statement:
--   Throughout, a `TwoAffineOpenCover` of a scheme $X$ is the project's structure consisting of two opens $U_0,U_1$ of $X$, proofs that $U_0$, $U_1$ and $U_0\cap U_1$ are affine opens, and a proof that $U_0\sqcup U_1=\top$. For such a cover $\mathcal V$ of $X$ and an affine morphism $g\colon Y\to X$, `preimage` is the cover of $Y$ with charts $g^{-1}U_0$ and $g^{-1}U_1$; the three affineness fields come from affineness of preimages of affine opens under an affine morphism together with $g^{-1}U_0\cap g^{-1}U_1=g^{-1}(U_0\cap U_1)$, and the covering condition from $g^{-1}(U_0\sqcup U_1)=\top$. Two lemmas record the charts, and `pullback_eq_preimage` states that the base-changed cover $\mathcal V_A$ of $X\times_{\operatorname{Spec}R}\operatorname{Spec}A$, for $c\colon X\to\operatorname{Spec}R$ and an $R$-algebra $A$, is this preimage cover along the first projection.
--
--   The remaining declarations produce morphisms in the project's structure `HomOver τ 𝒱 c 𝒲 c'`, whose fields are a morphism $h\colon Y\to X$, the identity $h$ followed by $c$ equals $c'$ followed by $\operatorname{Spec}\tau$, and the two inclusions $\mathcal W_i\le h^{-1}\mathcal V_i$. `HomOver.ofPreimage` turns an affine $g$ satisfying that commutation over $\tau\colon R\to S$ into such a morphism from $(Y,g^{-1}\mathcal V,c')$ to $(X,\mathcal V,c)$, the chart inclusions being equalities; a lemma identifies its underlying morphism with $g$. `HomOver.pullback` base changes a morphism $f$ over $\mathrm{id}_R$ between covered $R$-schemes to one over $\mathrm{id}_A$ between the pullback covers, its underlying morphism being the induced map of fibre products with components $f$ and the identity of $\operatorname{Spec}A$. Finally `HomOver.pullback_hom` states that this morphism followed by the projection to $X$ equals the projection $Y_A\to Y$ followed by $f$, and `HomOver.pullback_hom_comp_stage_hom` that, for an $R$-algebra map $g\colon A\to B$, the square formed by the base changes of $f$ to $B$ and to $A$ and the two stage morphisms induced by $\operatorname{Spec}g$ commutes.
--
--   **Relation to Mathlib.** The two-chart cover structure and the `HomOver` morphisms are the project's own; Mathlib's affine open covers are indexed families without the two-chart and affine-intersection conditions. Affineness of the preimage charts is Mathlib's `IsAffineOpen.preimage` for a morphism with `IsAffineHom`.
--
--   **Where it is used.** These constructions give functoriality of the two-chart Čech description of $H^1$ of the structure sheaf in the scheme variable: a morphism compatible with the covers induces maps on Čech cochains and on $H^1$, and for an affine morphism the preimage cover is the canonical compatible cover of the source. They feed the base-change and stage maps used in the relative Picard/deformation part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCoverPreimage.lean

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {X Y : Scheme.{u}}

def preimage (𝒱 : X.TwoAffineOpenCover) (g : Y ⟶ X) [IsAffineHom g] : Y.TwoAffineOpenCover where
  U0 := g ⁻¹ᵁ 𝒱.U0
  U1 := g ⁻¹ᵁ 𝒱.U1
  isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage g
  isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage g
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage g

@[simp] theorem preimage_U0 (𝒱 : X.TwoAffineOpenCover) (g : Y ⟶ X) [IsAffineHom g] :
    (𝒱.preimage g).U0 = g ⁻¹ᵁ 𝒱.U0 := rfl

@[simp] theorem preimage_U1 (𝒱 : X.TwoAffineOpenCover) (g : Y ⟶ X) [IsAffineHom g] :
    (𝒱.preimage g).U1 = g ⁻¹ᵁ 𝒱.U1 := rfl

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S]

theorem pullback_eq_preimage (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] :
    𝒱.pullback c A =
      @preimage _ _ 𝒱 (Limits.pullback.fst c (specMap R A)) (isAffineHom_fst c A) := rfl

def HomOver.ofPreimage {τ : R →+* S} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (c' : Y ⟶ Spec (.of S)) (g : Y ⟶ X) [IsAffineHom g]
    (hg : g ≫ c = c' ≫ Spec.map (CommRingCat.ofHom τ)) :
    HomOver τ 𝒱 c (𝒱.preimage g) c' where
  hom := g
  comm := hg
  U0_le := le_rfl
  U1_le := le_rfl

@[simp] theorem HomOver.ofPreimage_hom {τ : R →+* S} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (c' : Y ⟶ Spec (.of S)) (g : Y ⟶ X) [IsAffineHom g]
    (hg : g ≫ c = c' ≫ Spec.map (CommRingCat.ofHom τ)) :
    (HomOver.ofPreimage 𝒱 c c' g hg).hom = g := rfl

def HomOver.pullback {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)} {𝒲 : Y.TwoAffineOpenCover}
    {c' : Y ⟶ Spec (.of R)} (f : HomOver (RingHom.id R) 𝒱 c 𝒲 c')
    (A : Type u) [CommRing A] [Algebra R A] :
    HomOver (RingHom.id A) (𝒱.pullback c A) (Limits.pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (Limits.pullback.snd c' (specMap R A)) where
  hom := Limits.pullback.map c' (specMap R A) c (specMap R A) f.hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, f.comm, CommRingCat.ofHom_id]; erw [Spec.map_id]; try rw [Category.comp_id]) (by simp)
  comm := by
    rw [Limits.pullback.lift_snd, CommRingCat.ofHom_id]
    erw [Spec.map_id]
    try rw [Category.comp_id, Category.comp_id]
  U0_le := by
    change Limits.pullback.fst c' (specMap R A) ⁻¹ᵁ 𝒲.U0 ≤
      Limits.pullback.map c' (specMap R A) c (specMap R A) f.hom (𝟙 _) (𝟙 _) _ _ ⁻¹ᵁ
        (Limits.pullback.fst c (specMap R A) ⁻¹ᵁ 𝒱.U0)
    rw [← Scheme.Hom.comp_preimage, Limits.pullback.lift_fst, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ f.U0_le
  U1_le := by
    change Limits.pullback.fst c' (specMap R A) ⁻¹ᵁ 𝒲.U1 ≤
      Limits.pullback.map c' (specMap R A) c (specMap R A) f.hom (𝟙 _) (𝟙 _) _ _ ⁻¹ᵁ
        (Limits.pullback.fst c (specMap R A) ⁻¹ᵁ 𝒱.U1)
    rw [← Scheme.Hom.comp_preimage, Limits.pullback.lift_fst, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ f.U1_le

theorem HomOver.pullback_hom {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)} {𝒲 : Y.TwoAffineOpenCover}
    {c' : Y ⟶ Spec (.of R)} (f : HomOver (RingHom.id R) 𝒱 c 𝒲 c') (A : Type u) [CommRing A] [Algebra R A] :
    (f.pullback A).hom ≫ Limits.pullback.fst c (specMap R A) = Limits.pullback.fst c' (specMap R A) ≫ f.hom :=
  Limits.pullback.lift_fst _ _ _

theorem HomOver.pullback_hom_comp_stage_hom {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
    {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of R)} (f : HomOver (RingHom.id R) 𝒱 c 𝒲 c')
    {A : Type u} [CommRing A] [Algebra R A] {B : Type u} [CommRing B] [Algebra R B] (g : A →ₐ[R] B) :
    (f.pullback B).hom ≫ (HomOver.stage 𝒱 c g).hom = (HomOver.stage 𝒲 c' g).hom ≫ (f.pullback A).hom := by
  apply Limits.pullback.hom_ext <;>
    simp only [HomOver.pullback, HomOver.stage, RelPicard.baseChangeSnd, Category.assoc, Limits.pullback.lift_fst,
      Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc, Category.comp_id,
      Category.id_comp]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end


