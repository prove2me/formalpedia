-- Prove2me | Definitions.Def_ProEtale_Algebra_LocalizationColimit
-- name    : ProEtale_Algebra_LocalizationColimit
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:39:58.123419+00:00
-- url     : https://prove2.me/theorems/2fa5efdf-5022-4b50-b88d-d3a1c9b4edf6
-- title:
--   Localizations at a prime of a filtered colimit of algebras, and stability of bijectivity on stalks under filtered colimits
-- statement:
--   Let $R$ be a commutative ring and let $S$ be an $R$-algebra presented as the colimit of a diagram $i \mapsto A_i$ of commutative $R$-algebras indexed by a small category $\iota$, with colimit maps $\iota_i \colon A_i \to S$. For a prime $\mathfrak p \subset S$ put $\mathfrak p_i = \iota_i^{-1}(\mathfrak p)$, a prime of $A_i$.
--
--   Definitions:
--   - the **localization diagram** $i \mapsto (A_i)_{\mathfrak p_i}$, with transition maps induced by those of the diagram;
--   - the **localization cocone** over it with apex $S_{\mathfrak p}$, with legs $(A_i)_{\mathfrak p_i} \to S_{\mathfrak p}$ induced by $\iota_i$;
--   - the comparison maps $R_{\mathfrak p \cap R} \to (A_i)_{\mathfrak p_i}$.
--
--   Principal results:
--   1. Routine compatibilities: $\mathfrak p_i \cap R = \mathfrak p \cap R$; $\mathfrak p_i$ is the preimage of $\mathfrak p_j$ along each transition map $A_i \to A_j$; the comparison maps from $R_{\mathfrak p\cap R}$ commute with the transition maps and with the cocone legs (whose composite is the stalk map $R_{\mathfrak p \cap R} \to S_{\mathfrak p}$).
--   2. Assume $\iota$ is filtered. Every element of $S_{\mathfrak p}$ is the image of an element of some $(A_i)_{\mathfrak p_i}$; and two elements of $(A_i)_{\mathfrak p_i}$ with the same image in $S_{\mathfrak p}$ already become equal in $(A_k)_{\mathfrak p_k}$ for some morphism $i \to k$. (Together: $S_{\mathfrak p} = \operatorname{colim}_i (A_i)_{\mathfrak p_i}$ elementwise.)
--   3. Assume $\iota$ is filtered. If every $R \to A_i$ is bijective on stalks (i.e. $R_{\mathfrak q\cap R} \to (A_i)_{\mathfrak q}$ is bijective for all primes $\mathfrak q$ of $A_i$), then so is $R \to S$.
--
--   The last statement is used to show that being bijective on stalks is preserved by ind-constructions, e.g. for ind-Zariski and ind-étale algebras.
--
--   **Formalization Note** All rings and the index category live in one universe `u`; the presentation is a `ColimitPresentation ι (CommAlgCat.of R S)`. The main declarations are `Localization.AtPrime.contractionIdeal`, `Localization.AtPrime.localizationDiag` (a functor `ι ⥤ CommRingCat`), `Localization.AtPrime.localizationCocone`, `Localization.AtPrime.toLocalizationDiag`, `Localization.AtPrime.exists_localizationCocone_ι_app_eq`, `Localization.AtPrime.exists_localizationDiag_map_eq` and `Algebra.BijectiveOnStalks.of_colimitPresentation`. The module docstring mentions an `IsColimit` statement for the cocone; this file contains the elementwise lifting and equalizing lemmas, not that statement.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/LocalizationColimit.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.Inseparable
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Localization of a filtered colimit of algebras at a prime

Let `S = colim_i Aᵢ` be a filtered colimit of `R`-algebras and let `p` be a prime of `S`. Writing
`pᵢ` for the contraction of `p` to `Aᵢ`, the localizations `(Aᵢ)_{pᵢ}` form a filtered diagram
with colimit `S_p`. This is `Localization.AtPrime.isColimitLocalizationCocone`.

As an application we show in `Algebra.BijectiveOnStalks.of_colimitPresentation` that being
bijective on stalks is stable under filtered colimits.
-/

universe u

open CategoryTheory Limits

namespace Localization
namespace AtPrime

section ColimitPresentation

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type u} [SmallCategory ι] (P : ColimitPresentation ι (CommAlgCat.of R S))

/-- The contraction of an ideal `p` of the colimit `S` to a constituent `P.diag.obj i`. -/
noncomputable def contractionIdeal (p : Ideal S) (i : ι) : Ideal (P.diag.obj i) :=
  p.comap (P.ι.app i).hom.toRingHom

instance contractionIdeal.isPrime (p : Ideal S) [p.IsPrime] (i : ι) :
    (contractionIdeal P p i).IsPrime :=
  Ideal.IsPrime.comap _

@[simp]
lemma contractionIdeal_comap_algebraMap (p : Ideal S) (i : ι) :
    (contractionIdeal P p i).comap (algebraMap R (P.diag.obj i)) = p.comap (algebraMap R S) := by
  symm
  ext r
  simp only [Ideal.mem_comap, contractionIdeal,
    ← ColimitPresentation.ι_app_algebraMap_apply P i r]
  rfl

@[simp]
lemma contractionIdeal_comap_diag (p : Ideal S) {i j : ι} (f : i ⟶ j) :
    (contractionIdeal P p j).comap (P.diag.map f).hom.toRingHom = contractionIdeal P p i := by
  symm
  ext r
  change (P.ι.app i).hom r ∈ p ↔ (P.ι.app j).hom ((P.diag.map f).hom r) ∈ p
  rw [ColimitPresentation.ι_app_diag_map_apply P f r]

variable (p : Ideal S) [p.IsPrime]

/-- The diagram of localizations `Localization.AtPrime (contractionIdeal P p i)` for `i : ι`, with
transition maps given by `Localization.localRingHom`. -/
noncomputable def localizationDiag : ι ⥤ CommRingCat.{u} where
  obj i := .of (Localization.AtPrime (contractionIdeal P p i))
  map {i j} f := CommRingCat.ofHom <| Localization.localRingHom _ _
    (P.diag.map f).hom.toRingHom (contractionIdeal_comap_diag P p f).symm
  map_id i := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
      (contractionIdeal P p i).primeCompl x
    rw [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply,
      Localization.localRingHom_mk']
    exact congrArg₂ (IsLocalization.mk' _) (P.diag_map_id_apply i r)
      (Subtype.ext (P.diag_map_id_apply i s))
  map_comp {i j k} f g := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
      (contractionIdeal P p i).primeCompl x
    rw [CommRingCat.hom_ofHom, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      CommRingCat.hom_ofHom, Localization.localRingHom_mk', RingHom.comp_apply,
      Localization.localRingHom_mk', Localization.localRingHom_mk']
    exact congrArg₂ (IsLocalization.mk' _) (P.diag_map_comp_apply f g r)
      (Subtype.ext (P.diag_map_comp_apply f g s))

lemma localizationDiag_map_apply {i j : ι} (f : i ⟶ j)
    (x : Localization.AtPrime (contractionIdeal P p i)) :
    ((localizationDiag P p).map f).hom x =
      Localization.localRingHom _ _ (P.diag.map f).hom.toRingHom
        (contractionIdeal_comap_diag P p f).symm x :=
  rfl

/-- The cocone over `localizationDiag P p` with apex `Localization.AtPrime p`. -/
noncomputable def localizationCocone : Cocone (localizationDiag P p) where
  pt := .of (Localization.AtPrime p)
  ι :=
    { app i := CommRingCat.ofHom <|
        Localization.localRingHom (contractionIdeal P p i) p (P.ι.app i).hom.toRingHom rfl
      naturality {i j} f := by
        apply CommRingCat.hom_ext
        refine RingHom.ext fun (x : Localization.AtPrime (contractionIdeal P p i)) ↦ ?_
        obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
          (contractionIdeal P p i).primeCompl x
        change (Localization.localRingHom (contractionIdeal P p j) p (P.ι.app j).hom.toRingHom rfl)
            ((Localization.localRingHom (contractionIdeal P p i) (contractionIdeal P p j)
              (P.diag.map f).hom.toRingHom (contractionIdeal_comap_diag P p f).symm)
                (IsLocalization.mk' _ r ⟨s, hs⟩)) =
          (Localization.localRingHom (contractionIdeal P p i) p (P.ι.app i).hom.toRingHom rfl)
            (IsLocalization.mk' _ r ⟨s, hs⟩)
        rw [Localization.localRingHom_mk', Localization.localRingHom_mk',
          Localization.localRingHom_mk']
        exact congrArg₂ (IsLocalization.mk' _)
          (ColimitPresentation.ι_app_diag_map_apply P f r)
          (Subtype.ext (ColimitPresentation.ι_app_diag_map_apply P f s)) }

lemma localizationCocone_ι_app_apply (i : ι) (x : Localization.AtPrime (contractionIdeal P p i)) :
    ((localizationCocone P p).ι.app i).hom x =
      Localization.localRingHom (contractionIdeal P p i) p (P.ι.app i).hom.toRingHom rfl x :=
  rfl

/-- The comparison map from the localization of `R` at the contraction of `p` to the localization
of `P.diag.obj i` at the contraction of `p` to `P.diag.obj i`. -/
noncomputable def toLocalizationDiag (i : ι) :
    Localization.AtPrime (p.comap (algebraMap R S)) →+*
      Localization.AtPrime (contractionIdeal P p i) :=
  Localization.localRingHom _ _ (algebraMap R (P.diag.obj i))
    (contractionIdeal_comap_algebraMap P p i).symm

@[simp]
lemma localizationDiag_map_toLocalizationDiag {i j : ι} (f : i ⟶ j)
    (x : Localization.AtPrime (p.comap (algebraMap R S))) :
    ((localizationDiag P p).map f).hom (toLocalizationDiag P p i x) =
      toLocalizationDiag P p j x := by
  have h : (Localization.localRingHom (contractionIdeal P p i) (contractionIdeal P p j)
      (P.diag.map f).hom.toRingHom (contractionIdeal_comap_diag P p f).symm).comp
        (toLocalizationDiag P p i) = toLocalizationDiag P p j :=
    (Localization.localRingHom_unique _ (contractionIdeal P p j) (algebraMap R (P.diag.obj j))
      (contractionIdeal_comap_algebraMap P p j).symm fun r ↦ by
        rw [RingHom.comp_apply, toLocalizationDiag, Localization.localRingHom_to_map,
          Localization.localRingHom_to_map]
        exact congrArg _ ((P.diag.map f).hom.commutes r)).symm
  exact congr($h x)

@[simp]
lemma localizationCocone_ι_app_toLocalizationDiag (i : ι)
    (x : Localization.AtPrime (p.comap (algebraMap R S))) :
    ((localizationCocone P p).ι.app i).hom (toLocalizationDiag P p i x) =
      Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl x := by
  have h : (Localization.localRingHom (contractionIdeal P p i) p
      (P.ι.app i).hom.toRingHom rfl).comp (toLocalizationDiag P p i) =
        Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl :=
    (Localization.localRingHom_unique _ p (algebraMap R S) rfl fun r ↦ by
      rw [RingHom.comp_apply, toLocalizationDiag, Localization.localRingHom_to_map,
        Localization.localRingHom_to_map]
      exact congrArg _ ((P.ι.app i).hom.commutes r)).symm
  exact congr($h x)

variable [IsFiltered ι]

/-- Every element of `Localization.AtPrime p` lifts to an element of
`Localization.AtPrime (contractionIdeal P p i)` for some `i : ι`. -/
lemma exists_localizationCocone_ι_app_eq (z : Localization.AtPrime p) :
    ∃ (i : ι) (zᵢ : Localization.AtPrime (contractionIdeal P p i)),
      ((localizationCocone P p).ι.app i).hom zᵢ = z := by
  obtain ⟨⟨s, u, hu⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  obtain ⟨i₁, s₀, hs₀⟩ := Concrete.isColimit_exists_rep _ P.isColimit s
  obtain ⟨i₂, u₀, hu₀⟩ := Concrete.isColimit_exists_rep _ P.isColimit u
  let i : ι := IsFiltered.max i₁ i₂
  let s' : P.diag.obj i := (P.diag.map (IsFiltered.leftToMax i₁ i₂)).hom s₀
  let u' : P.diag.obj i := (P.diag.map (IsFiltered.rightToMax i₁ i₂)).hom u₀
  have hs' : (P.ι.app i).hom s' = s :=
    (ColimitPresentation.ι_app_diag_map_apply P (IsFiltered.leftToMax i₁ i₂) s₀).trans hs₀
  have hu' : (P.ι.app i).hom u' = u :=
    (ColimitPresentation.ι_app_diag_map_apply P (IsFiltered.rightToMax i₁ i₂) u₀).trans hu₀
  have hu'_mem : u' ∈ (contractionIdeal P p i).primeCompl := fun hmem ↦ hu (hu' ▸ hmem)
  refine ⟨i, IsLocalization.mk' _ s' ⟨u', hu'_mem⟩, ?_⟩
  change Localization.localRingHom (contractionIdeal P p i) p (P.ι.app i).hom.toRingHom rfl
    (IsLocalization.mk' _ s' ⟨u', hu'_mem⟩) = _
  rw [Localization.localRingHom_mk']
  exact congrArg₂ (IsLocalization.mk' _) hs' (Subtype.ext hu')

/-- If two elements of `Localization.AtPrime (contractionIdeal P p i)` have equal images in
`Localization.AtPrime p`, they become equal in `Localization.AtPrime (contractionIdeal P p k)` for
some morphism `i ⟶ k`. -/
lemma exists_localizationDiag_map_eq (i : ι)
    (x y : Localization.AtPrime (contractionIdeal P p i))
    (hxy : ((localizationCocone P p).ι.app i).hom x = ((localizationCocone P p).ι.app i).hom y) :
    ∃ (k : ι) (f : i ⟶ k),
      ((localizationDiag P p).map f).hom x = ((localizationDiag P p).map f).hom y := by
  simp only [localizationCocone_ι_app_apply] at hxy
  obtain ⟨⟨r₁, s₁, hs₁⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (contractionIdeal P p i).primeCompl x
  obtain ⟨⟨r₂, s₂, hs₂⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (contractionIdeal P p i).primeCompl y
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk'] at hxy
  obtain ⟨⟨c, hcp⟩, hc⟩ := (IsLocalization.eq (S := Localization.AtPrime p)).mp hxy
  obtain ⟨k₀, c₀, hc₀⟩ := Concrete.isColimit_exists_rep _ P.isColimit c
  let l : i ⟶ IsFiltered.max i k₀ := IsFiltered.leftToMax i k₀
  let c' : P.diag.obj (IsFiltered.max i k₀) := (P.diag.map (IsFiltered.rightToMax i k₀)).hom c₀
  have hkey :
      (P.ι.app _).hom (c' * ((P.diag.map l).hom s₂ * (P.diag.map l).hom r₁)) =
        (P.ι.app _).hom (c' * ((P.diag.map l).hom s₁ * (P.diag.map l).hom r₂)) := by
    simp only [map_mul, ColimitPresentation.ι_app_diag_map_apply, c', hc₀]
    exact hc
  obtain ⟨k, g, hkeq⟩ := (IsColimit.eq_iff' P.isColimit _ _).mp hkey
  have hck : (P.ι.app k).hom ((P.diag.map g).hom c') = c := by
    rw [ColimitPresentation.ι_app_diag_map_apply, ColimitPresentation.ι_app_diag_map_apply, hc₀]
  have hck_mem : (P.diag.map g).hom c' ∈ (contractionIdeal P p k).primeCompl :=
    fun hmem ↦ hcp (hck ▸ hmem)
  refine ⟨k, l ≫ g, ?_⟩
  change Localization.localRingHom (contractionIdeal P p i) (contractionIdeal P p k)
      (P.diag.map (l ≫ g)).hom.toRingHom (contractionIdeal_comap_diag P p (l ≫ g)).symm
      (IsLocalization.mk' _ r₁ ⟨s₁, hs₁⟩) =
    Localization.localRingHom (contractionIdeal P p i) (contractionIdeal P p k)
      (P.diag.map (l ≫ g)).hom.toRingHom (contractionIdeal_comap_diag P p (l ≫ g)).symm
      (IsLocalization.mk' _ r₂ ⟨s₂, hs₂⟩)
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk', IsLocalization.eq]
  refine ⟨⟨(P.diag.map g).hom c', hck_mem⟩, ?_⟩
  have hkeq' : (P.diag.map g).hom (c' * ((P.diag.map l).hom s₂ * (P.diag.map l).hom r₁)) =
      (P.diag.map g).hom (c' * ((P.diag.map l).hom s₁ * (P.diag.map l).hom r₂)) := hkeq
  simp only [map_mul, ← P.diag_map_comp_apply] at hkeq'
  exact hkeq'


end ColimitPresentation

end AtPrime
end Localization

namespace Algebra
namespace BijectiveOnStalks

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type u} [SmallCategory ι] [IsFiltered ι]
  (P : ColimitPresentation ι (CommAlgCat.of R S))

open Localization.AtPrime

/-- If `S` is a filtered colimit of `R`-algebras `Aᵢ` and each `R → Aᵢ` is bijective on stalks,
then so is `R → S`. -/
lemma of_colimitPresentation (h : ∀ i, Algebra.BijectiveOnStalks R (P.diag.obj i)) :
    Algebra.BijectiveOnStalks R S := by
  refine ⟨fun p hp ↦ ?_⟩
  -- The comparison maps `R_{p ∩ R} → (Aᵢ)_{pᵢ}` are bijective by assumption.
  have hφ (i : ι) : Function.Bijective (toLocalizationDiag P p i) :=
    (RingHom.bijectiveOnStalks_algebraMap.mpr (h i)).localRingHom_of_eq
      (contractionIdeal_comap_algebraMap P p i).symm
  obtain ⟨i₀⟩ : Nonempty ι := IsFiltered.nonempty
  refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
  · -- Injectivity: `x` and `y` already agree in `(Aᵢ)_{pᵢ}` for some `i`.
    obtain ⟨k, f, hk⟩ := exists_localizationDiag_map_eq P p i₀
      (toLocalizationDiag P p i₀ x) (toLocalizationDiag P p i₀ y)
      ((localizationCocone_ι_app_toLocalizationDiag P p i₀ x).trans
        (hxy.trans (localizationCocone_ι_app_toLocalizationDiag P p i₀ y).symm))
    exact (hφ k).1 (by simpa using hk)
  · -- Surjectivity: lift `z` to some `(Aᵢ)_{pᵢ}` and use that the comparison map is onto.
    obtain ⟨i, zᵢ, rfl⟩ := exists_localizationCocone_ι_app_eq P p z
    obtain ⟨w, rfl⟩ := (hφ i).2 zᵢ
    exact ⟨w, (localizationCocone_ι_app_toLocalizationDiag P p i w).symm⟩

end BijectiveOnStalks
end Algebra


