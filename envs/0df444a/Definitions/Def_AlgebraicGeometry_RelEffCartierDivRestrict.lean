-- Prove2me | Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
-- name    : AlgebraicGeometry_RelEffCartierDivRestrict
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/865ceb54-a6e0-5dd3-8e90-4b4b86bd52c6
-- title:
--   Restricting and extending relative divisors along open charts
-- statement:
--   Throughout, $f \colon \mathcal{C} \to S$ is a morphism of schemes, $r$ a natural number, $V \subseteq S$ and $U \subseteq f^{-1}(V)$ open subschemes, and $f|_U \colon U \to V$ (written `f.resLE V U hUV`) the induced morphism; a test object is a scheme $T$ with morphisms $g_V \colon T \to V$ and $g \colon T \to S$ tied by $g_V$ followed by the inclusion $V \hookrightarrow S$ equal to $g$. Recall that an element of `RelEffCartierDiv f r g` is an ideal sheaf datum $I$ on $\mathcal{C} \times_S T$ whose closed subscheme, mapped to $T$ by the second projection, is finite, flat and locally of finite presentation with flat rank identically $r$, and that $I$ is `SupportedIn U` when the support of $I$ lies in the preimage of $U$ under the first projection. First, `resProdMap` is the canonical morphism $U \times_V T \to \mathcal{C} \times_S T$ induced by $U \hookrightarrow \mathcal{C}$, $\mathrm{id}_T$ and $V \hookrightarrow S$; it is an open immersion, compatible with both projections, exhibits $U \times_V T$ as the fibre product of $\mathcal{C} \times_S T \to \mathcal{C}$ with $U \hookrightarrow \mathcal{C}$, and has image exactly the preimage of $U$ under the first projection. Then `restrictAlong` sends a divisor $D$ for $f$ and $g$ with support in $U$ to the divisor for $f|_U$ and $g_V$ whose ideal sheaf is the comap of $D.I$ along `resProdMap`, the finiteness, flatness, finite presentation and rank $r$ conditions being inherited because the comparison of the two subschemes is an isomorphism. Conversely, for $f$ separated, `extendAlong` sends a divisor $D'$ for $f|_U$ and $g_V$ to the divisor whose ideal sheaf is the kernel ideal of the composite of the closed immersion of $D'.I$ with `resProdMap`, equivalently the image $D'.I.\mathrm{map}$ of $D'.I$; this composite is a closed immersion because the subscheme is finite over $T$ and $\mathcal{C} \times_S T \to T$ is separated. The extension is supported in $U$, the two constructions are mutually inverse, and extension commutes with pullback along a $V$-morphism $\varphi \colon T_1 \to T_2$, the relevant square of `resProdMap`s and `mapOnProdOver`s being a pullback. Finally, if $r > 0$ and some divisor for $g$ is supported in $U$, then $g$ factors set-theoretically through $V$: its image lies in the image of $V \hookrightarrow S$.
--
--   **Relation to Mathlib.** Built on Mathlib's `Scheme.Hom.resLE`, ideal sheaf data with their comap, image and kernel ideals, and the flat-rank (`finrank`) theory; the notion of relative effective Cartier divisor of degree $r$ and the restriction/extension correspondence along an open chart are the project's own.
--
--   **Where it is used.** The bijection between divisors of $\mathcal{C}/S$ supported in an open $U$ and divisors of the chart $U \to V$ is the dictionary by which representability of the functor of relative effective Cartier divisors is reduced to the case of a chart over an affine base, the representing objects being glued afterwards.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelEffCartierDivRestrict.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (V : S.Opens) (U : 𝒞.Opens) (hUV : U ≤ f ⁻¹ᵁ V)

section ResProd

variable {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S) (hg : gV ≫ V.ι = g)

noncomputable def resProdMap : pullback (f.resLE V U hUV) gV ⟶ pullback f g :=
  pullback.map _ _ _ _ U.ι (𝟙 T) V.ι (Scheme.Hom.resLE_comp_ι f hUV) (by rw [Category.id_comp, hg])

instance isOpenImmersion_resProdMap : IsOpenImmersion (resProdMap f V U hUV gV g hg) := by
  delta resProdMap; infer_instance

@[reassoc (attr := simp)]
lemma resProdMap_fst : resProdMap f V U hUV gV g hg ≫ pullback.fst f g = pullback.fst _ _ ≫ U.ι := by
  delta resProdMap; exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma resProdMap_snd : resProdMap f V U hUV gV g hg ≫ pullback.snd f g = pullback.snd _ _ := by
  delta resProdMap; exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma isPullback_of_comp_mono {A B W Z : Scheme.{u}} (a : A ⟶ W) (b : B ⟶ W) (i : W ⟶ Z) [Mono i]
    {a' : A ⟶ Z} {b' : B ⟶ Z} (ha : a ≫ i = a') (hb : b ≫ i = b') :
    IsPullback (pullback.fst a b) (pullback.snd a b) a' b' := by
  subst ha hb
  exact IsPullback.of_isLimit (pullbackIsPullbackOfCompMono a b i)

lemma isPullback_resProdMap :
    IsPullback (resProdMap f V U hUV gV g hg) (pullback.fst (f.resLE V U hUV) gV)
      (pullback.fst f g) U.ι := by

  have outer : IsPullback (pullback.snd (f.resLE V U hUV) gV) (pullback.fst (f.resLE V U hUV) gV)
      g (U.ι ≫ f) := by
    exact (isPullback_of_comp_mono (f.resLE V U hUV) gV V.ι (Scheme.Hom.resLE_comp_ι f hUV) hg).flip
  rw [← resProdMap_snd f V U hUV gV g hg] at outer
  exact IsPullback.of_right outer (resProdMap_fst f V U hUV gV g hg) (IsPullback.of_hasPullback f g).flip

end ResProd

end AlgebraicGeometry.RelEffCartierDiv

namespace AlgebraicGeometry.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (V : S.Opens) (U : 𝒞.Opens) (hUV : U ≤ f ⁻¹ᵁ V)

section ResProd2

variable {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S) (hg : gV ≫ V.ι = g)

lemma range_resProdMap :
    Set.range (resProdMap f V U hUV gV g hg) = (pullback.fst f g) ⁻¹' (U : Set 𝒞) := by
  have sq := isPullback_resProdMap f V U hUV gV g hg
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr sq.isoPullback.hom.surjective, Set.image_univ, Scheme.Pullback.range_fst,
    Scheme.Opens.range_ι]

lemma range_resProdMap' :
    Set.range (resProdMap f V U hUV gV g hg) = ((pullback.fst f g) ⁻¹ᵁ U : (pullback f g).Opens) :=
  range_resProdMap f V U hUV gV g hg

end ResProd2

variable {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S)

section Restrict

variable (hg : gV ≫ V.ι = g) (D : RelEffCartierDiv f r g) (hD : D.SupportedIn U)

include hD in

lemma isIso_pullback_snd_resProdMap :
    IsIso (pullback.snd (resProdMap f V U hUV gV g hg) D.I.subschemeι) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  ext1
  rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Scheme.Pullback.range_snd,
    range_resProdMap, Set.eq_univ_iff_forall]
  intro z
  change pullback.fst f g (D.I.subschemeι z) ∈ (U : Set 𝒞)
  have hz : D.I.subschemeι z ∈ (D.I.support : Set ↥(pullback f g)) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact Set.mem_range_self z
  exact hD hz

noncomputable def restrictAlong : RelEffCartierDiv (f.resLE V U hUV) r gV :=
  haveI := isIso_pullback_snd_resProdMap f r V U hUV gV g hg D hD
  have key : (D.I.comap (resProdMap f V U hUV gV g hg)).subschemeι ≫
      pullback.snd (f.resLE V U hUV) gV =
      ((D.I.comapIso (resProdMap f V U hUV gV g hg)).hom ≫
        pullback.snd (resProdMap f V U hUV gV g hg) D.I.subschemeι) ≫
        (D.I.subschemeι ≫ pullback.snd f g) := by
    rw [← resProdMap_snd f V U hUV gV g hg, ← Scheme.IdealSheafData.comapIso_hom_fst]
    simp only [Category.assoc, pullback.condition_assoc]
  { I := D.I.comap (resProdMap f V U hUV gV g hg)
    isFinite := by have := D.isFinite; rw [key]; infer_instance
    flat := by have := D.flat; rw [key]; infer_instance
    locallyOfFinitePresentation := by have := D.locallyOfFinitePresentation; rw [key]; infer_instance
    finrank_eq := fun t => by
      have := D.isFinite; have := D.flat
      rw [key, Scheme.Hom.finrank_comp_left_of_isIso]; exact D.finrank_eq t }

@[simp] lemma restrictAlong_I :
    (restrictAlong f r V U hUV gV g hg D hD).I = D.I.comap (resProdMap f V U hUV gV g hg) := rfl

end Restrict

section Extend

variable (hg : gV ≫ V.ι = g) (D' : RelEffCartierDiv (f.resLE V U hUV) r gV)

instance isClosedImmersion_subschemeι_resProdMap [IsSeparated f] :
    IsClosedImmersion (D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg) := by
  rw [IsClosedImmersion.iff_isFinite_and_mono]
  refine ⟨?_, inferInstance⟩
  have : IsFinite ((D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg) ≫ pullback.snd f g) := by
    rw [Category.assoc, resProdMap_snd]; exact D'.isFinite
  exact MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) _ (pullback.snd f g)
    inferInstance this

variable [IsSeparated f]

noncomputable def extendAlong : RelEffCartierDiv f r g :=
  let h := D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg
  have key : h.ker.subschemeι ≫ pullback.snd f g =
      inv h.toImage ≫ (D'.I.subschemeι ≫ pullback.snd (f.resLE V U hUV) gV) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, Scheme.Hom.toImage_imageι, Category.assoc,
      resProdMap_snd]
  { I := h.ker
    isFinite := by have := D'.isFinite; rw [key]; infer_instance
    flat := by have := D'.flat; rw [key]; infer_instance
    locallyOfFinitePresentation := by have := D'.locallyOfFinitePresentation; rw [key]; infer_instance
    finrank_eq := fun t => by
      have := D'.isFinite; have := D'.flat
      rw [key, Scheme.Hom.finrank_comp_left_of_isIso]; exact D'.finrank_eq t }

@[simp] lemma extendAlong_I :
    (extendAlong f r V U hUV gV g hg D').I = (D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg).ker := rfl

lemma extendAlong_I_eq_map :
    (extendAlong f r V U hUV gV g hg D').I = D'.I.map (resProdMap f V U hUV gV g hg) := rfl

lemma extendAlong_supportedIn : (extendAlong f r V U hUV gV g hg D').SupportedIn U := by
  intro z hz
  rw [extendAlong_I, Scheme.Hom.support_ker, IsClosed.closure_eq
    (D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg).isClosedEmbedding.isClosed_range] at hz
  obtain ⟨w, rfl⟩ := hz
  show pullback.fst f g ((D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg) w) ∈ U
  have : resProdMap f V U hUV gV g hg (D'.I.subschemeι w) ∈ Set.range (resProdMap f V U hUV gV g hg) :=
    Set.mem_range_self _
  rw [range_resProdMap] at this
  exact this

end Extend

end AlgebraicGeometry.RelEffCartierDiv

namespace AlgebraicGeometry.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (V : S.Opens) (U : 𝒞.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
  {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S)

section RoundTrip

variable [IsSeparated f] (hg : gV ≫ V.ι = g)

@[simp] lemma extendAlong_restrictAlong (D : RelEffCartierDiv f r g) (hD : D.SupportedIn U) :
    extendAlong f r V U hUV gV g hg (restrictAlong f r V U hUV gV g hg D hD) = D := by
  haveI := isIso_pullback_snd_resProdMap f r V U hUV gV g hg D hD
  refine RelEffCartierDiv.ext ?_
  rw [extendAlong_I, restrictAlong_I, ← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc,
    pullback.condition, ← Category.assoc, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_subschemeι]

@[simp] lemma restrictAlong_extendAlong (D' : RelEffCartierDiv (f.resLE V U hUV) r gV) :
    restrictAlong f r V U hUV gV g hg (extendAlong f r V U hUV gV g hg D')
      (extendAlong_supportedIn f r V U hUV gV g hg D') = D' := by
  refine RelEffCartierDiv.ext ?_
  set j := resProdMap f V U hUV gV g hg with hj
  set h := D'.I.subschemeι ≫ j with hh
  rw [restrictAlong_I, extendAlong_I, ← hj, ← hh, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion h j]

  have hfst : pullback.fst j h = pullback.snd j h ≫ D'.I.subschemeι :=
    (cancel_mono j).mp (by rw [Category.assoc, pullback.condition])
  haveI : IsIso (pullback.snd j h) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext1
    rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Scheme.Pullback.range_snd,
      Set.eq_univ_iff_forall]
    intro z
    exact ⟨D'.I.subschemeι z, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [hfst, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

end RoundTrip

section Naturality

lemma isPullback_mapOnProdOver_resProdMap {T₁ T₂ : Scheme.{u}} {gV₁ : T₁ ⟶ V} {gV₂ : T₂ ⟶ V}
    {g₁ : T₁ ⟶ S} {g₂ : T₂ ⟶ S} (hg₁ : gV₁ ≫ V.ι = g₁) (hg₂ : gV₂ ≫ V.ι = g₂)
    (φ : T₁ ⟶ T₂) (hφV : φ ≫ gV₂ = gV₁) (hφ : φ ≫ g₂ = g₁) :
    IsPullback (mapOnProdOver (f.resLE V U hUV) φ hφV) (resProdMap f V U hUV gV₁ g₁ hg₁)
      (resProdMap f V U hUV gV₂ g₂ hg₂) (mapOnProdOver f φ hφ) := by
  have s := (isPullback_resProdMap f V U hUV gV₁ g₁ hg₁).flip

  rw [← mapOnProdOver_fst (f.resLE V U hUV) φ hφV, ← mapOnProdOver_fst f φ hφ] at s
  refine IsPullback.of_right s ?_ (isPullback_resProdMap f V U hUV gV₂ g₂ hg₂).flip
  apply pullback.hom_ext
  · simp only [Category.assoc, resProdMap_fst, mapOnProdOver_fst, mapOnProdOver_fst_assoc]
  · simp only [Category.assoc, resProdMap_snd, mapOnProdOver_snd, resProdMap_snd_assoc]

variable [IsSeparated f] in

lemma extendAlong_pullbackAlong {T₁ T₂ : Scheme.{u}} {gV₁ : T₁ ⟶ V} {gV₂ : T₂ ⟶ V}
    {g₁ : T₁ ⟶ S} {g₂ : T₂ ⟶ S} (hg₁ : gV₁ ≫ V.ι = g₁) (hg₂ : gV₂ ≫ V.ι = g₂)
    (D' : RelEffCartierDiv (f.resLE V U hUV) r gV₂) (φ : T₁ ⟶ T₂) (hφV : φ ≫ gV₂ = gV₁)
    (hφ : φ ≫ g₂ = g₁) :
    extendAlong f r V U hUV gV₁ g₁ hg₁ (D'.pullbackAlong φ hφV) =
      (extendAlong f r V U hUV gV₂ g₂ hg₂ D').pullbackAlong φ hφ := by
  refine RelEffCartierDiv.ext ?_
  set j₁ := resProdMap f V U hUV gV₁ g₁ hg₁ with hj₁
  set j₂ := resProdMap f V U hUV gV₂ g₂ hg₂ with hj₂
  set m := mapOnProdOver (f.resLE V U hUV) φ hφV with hm
  set M := mapOnProdOver f φ hφ with hM
  set h₂ := D'.I.subschemeι ≫ j₂ with hh₂
  change ((D'.I.comap m).subschemeι ≫ j₁).ker = (h₂.ker).comap M
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion h₂ M,
    ← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Scheme.Hom.ker_comp_of_isIso]

  have big : IsPullback (pullback.fst m D'.I.subschemeι ≫ j₁) (pullback.snd m D'.I.subschemeι) M h₂ :=
    ((IsPullback.of_hasPullback m D'.I.subschemeι).flip.paste_vert
      (isPullback_mapOnProdOver_resProdMap f V U hUV hg₁ hg₂ φ hφV hφ)).flip
  rw [← big.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end Naturality

section Range

include hUV in

lemma range_subset_of_supportedIn {g : T ⟶ S} (D : RelEffCartierDiv f r g)
    (hD : D.SupportedIn U) (hr : 0 < r) : Set.range g ⊆ Set.range V.ι := by
  rintro _ ⟨t, rfl⟩
  have := D.isFinite; have := D.flat; have := D.locallyOfFinitePresentation
  have hsurj : Surjective (D.I.subschemeι ≫ pullback.snd f g) := by
    rw [← Scheme.Hom.one_le_finrank_iff_surjective]
    intro t; rw [D.finrank_eq]; exact hr
  obtain ⟨z, hz⟩ := hsurj.surj t
  have hzU : pullback.fst f g (D.I.subschemeι z) ∈ U := by
    have hz' : D.I.subschemeι z ∈ (D.I.support : Set ↥(pullback f g)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact Set.mem_range_self z
    exact hD hz'
  rw [Scheme.Opens.range_ι]
  change g t ∈ V
  rw [← hz, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ g, ← pullback.condition,
    Scheme.Hom.comp_apply]
  exact hUV hzU

end Range

end AlgebraicGeometry.RelEffCartierDiv


