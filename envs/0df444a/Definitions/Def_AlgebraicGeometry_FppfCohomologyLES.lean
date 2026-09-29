-- Prove2me | Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
-- name    : AlgebraicGeometry_FppfCohomologyLES
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/eacca162-e5dd-5dff-9f5e-906066258d33
-- title:
--   Long exact sheaf-cohomology sequence, with fppf-site instantiation
-- statement:
--   The module works on a site $(\mathcal C, J)$ with sheafification for abelian-group-valued sheaves and an `HasExt` structure on $\mathrm{Sh}(J,\mathrm{AddCommGrpCat})$. Here $\mathbb{Z}_J :=$ `constIntSheaf J` is the constant sheaf on the additive group $\mathrm{ULift}\,\mathbb{Z}$, and `sheafH_eq_ext` records that Mathlib's sheaf cohomology $F.H\,n$ is, by definition, $\mathrm{Ext}^n(\mathbb{Z}_J, F)$. On this identification two maps are defined: `cohomologyMap φ n : F.H n →+ G.H n`, postcomposition with the degree-zero Ext class of a morphism $φ : F \to G$, and, for a short exact sequence $S = (F_1 \to F_2 \to F_3)$ of sheaves, `cohomologyδ hS n₀ n₁ h : F_3.H n₀ →+ F_1.H n₁` (for $n_0+1=n_1$), postcomposition with the $\mathrm{Ext}^1$-class of the extension. Functoriality (`cohomologyMap_id`, `cohomologyMap_comp`), the three exactness statements at the $H^n(F_1)$, $H^n(F_2)$ and $H^n(F_3)$ spots, phrased as `Function.Exact`, injectivity of $H^0(F_1) \to H^0(F_2)$, the assembled six-term sequence `sixTermLES`, the six-term diagram as an exact `ComposableArrows`, and the identification $F.H\,0 \simeq_+ (\mathbb{Z}_J \to F)$ follow from Mathlib's covariant Ext long exact sequence. Further lemmas give naturality of `cohomologyMap` and of $\delta$ along a morphism or isomorphism of short exact sequences (ladder form and conjugation form), bijectivity of `cohomologyMap` for an isomorphism, surjectivity when $φ$ admits a section, and, for the split sequence `biprodSES F G` given by $F \to F \oplus G \to G$ together with its swap variant and a map in the third argument, the vanishing of $\delta$.
--
--   The fppf section installs $\mathrm{Sh}(\mathrm{fppf}, \mathrm{Ab}_{u+1})$ as a Grothendieck abelian category (via essential smallness of $\mathrm{Scheme}_u$) and restates the above for the big fppf site, with `FppfH F n` as notation for $F.H\,n$. A final group of elementary computations: the class group of $\mathbb{Z}$ has one element and $\mathrm{Pic}(\mathbb{Z})$ is a subsingleton; the $p$-th power map on $\mathbb{Z}^\times$ has kernel and range $\bot$ resp. $\top$ for odd $p$ and $\top$ resp. $\bot$ for $p = 2$, so both the $p$-torsion of $\mathbb{Z}^\times$ and $\mathbb{Z}^\times/(\mathbb{Z}^\times)^p$ have order $2$ if $p=2$ and $1$ otherwise, together with the exactness data of the Kummer sequence for $\mathbb{Z}^\times$.
--
--   **Relation to Mathlib.** Sheaf cohomology, the Ext groups, and the covariant Ext long exact sequence are Mathlib's; `cohomologyMap` and `cohomologyδ` repackage `Ext.mk₀`/`Ext.postcomp` as additive monoid homomorphisms and restate Mathlib's exactness in `Function.Exact` form. The arithmetic lemmas on $\mathrm{ClassGroup}\,\mathbb{Z}$, $\mathrm{CommRing.Pic}\,\mathbb{Z}$ and $\mathbb{Z}^\times$ are consequences of Mathlib results.
--
--   **Where it is used.** These statements supply the fppf-cohomology long exact sequence used in the Kummer-theoretic arguments on modular curves over $\operatorname{Spec}\mathbb{Z}$, where a short exact sequence of fppf abelian sheaves is converted into exact sequences of global sections and $H^1$; the arithmetic computations provide the unit and class-group inputs at the base $\mathbb{Z}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_FppfCohomologyLES.lean

import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.PicardGroup
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.Fintype.Units
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe w' w v u

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section GenericSite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

noncomputable abbrev constIntSheaf : Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))

theorem sheafH_eq_ext (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    F.H n = Ext (constIntSheaf J) F n := rfl

variable {J}

noncomputable def cohomologyMap {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (n : ℕ) :
    F.H n →+ G.H n :=
  (Ext.mk₀ φ).postcomp (constIntSheaf J) (add_zero n)

@[simp]
lemma cohomologyMap_apply {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (n : ℕ)
    (x : Ext (constIntSheaf J) F n) :
    cohomologyMap φ n x = x.comp (Ext.mk₀ φ) (add_zero n) := rfl

noncomputable def cohomologyδ {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.X₃.H n₀ →+ S.X₁.H n₁ :=
  hS.extClass.postcomp (constIntSheaf J) h

@[simp]
lemma cohomologyδ_apply {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) S.X₃ n₀) :
    cohomologyδ hS n₀ n₁ h x = x.comp hS.extClass h := rfl

theorem cohomologyMap_id (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ)
    (x : Ext (constIntSheaf J) F n) :
    cohomologyMap (𝟙 F) n x = x := by
  rw [cohomologyMap_apply]; simp

theorem cohomologyMap_comp {F G H : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (ψ : G ⟶ H)
    (n : ℕ) (x : Ext (constIntSheaf J) F n) :
    cohomologyMap (φ ≫ ψ) n x = cohomologyMap ψ n (cohomologyMap φ n x) := by
  rw [cohomologyMap_apply, cohomologyMap_apply, cohomologyMap_apply, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero]

theorem cohomology_exact_two {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (cohomologyMap S.f n) (cohomologyMap S.g n) := by
  have h2 := Ext.covariant_sequence_exact₂' (constIntSheaf J) hS n
  rw [ShortComplex.ab_exact_iff_function_exact] at h2
  exact h2

theorem cohomology_exact_three {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyMap S.g n₀) (cohomologyδ hS n₀ n₁ h) := by
  have h3 := Ext.covariant_sequence_exact₃' (constIntSheaf J) hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at h3
  exact h3

theorem cohomology_exact_one {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyδ hS n₀ n₁ h) (cohomologyMap S.f n₁) := by
  have h1 := Ext.covariant_sequence_exact₁' (constIntSheaf J) hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at h1
  exact h1

theorem cohomologyMap_zero_injective_of_mono {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    [Mono φ] :
    Function.Injective (cohomologyMap φ 0) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective (constIntSheaf J) F).surjective x
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective (constIntSheaf J) F).surjective y
  rw [cohomologyMap_apply, cohomologyMap_apply] at hxy
  have hxy' : Ext.mk₀ (a ≫ φ) = Ext.mk₀ (b ≫ φ) := by
    simpa only [Ext.mk₀_comp_mk₀] using hxy
  have hab : a ≫ φ = b ≫ φ := (Ext.mk₀_bijective _ _).injective hxy'
  rw [cancel_mono] at hab
  rw [hab]

theorem cohomologyMap_surjective_of_section {F G : Sheaf J AddCommGrpCat.{w}}
    (φ : F ⟶ G) (s : G ⟶ F) (hs : s ≫ φ = 𝟙 G) (n : ℕ) :
    Function.Surjective (cohomologyMap φ n) := by
  intro y
  refine ⟨cohomologyMap s n y, ?_⟩
  rw [← cohomologyMap_comp, hs, cohomologyMap_id]

theorem sixTermLES {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) :
    Function.Injective (cohomologyMap S.f 0) ∧
    Function.Exact (cohomologyMap S.f 0) (cohomologyMap S.g 0) ∧
    Function.Exact (cohomologyMap S.g 0) (cohomologyδ hS 0 1 rfl) ∧
    Function.Exact (cohomologyδ hS 0 1 rfl) (cohomologyMap S.f 1) ∧
    Function.Exact (cohomologyMap S.f 1) (cohomologyMap S.g 1) := by
  have : Mono S.f := hS.mono_f
  exact ⟨cohomologyMap_zero_injective_of_mono S.f, cohomology_exact_two hS 0,
    cohomology_exact_three hS 0 1 rfl, cohomology_exact_one hS 0 1 rfl,
    cohomology_exact_two hS 1⟩

noncomputable def cohomologyComposableArrows {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{w'} 5 :=
  Ext.covariantSequence (constIntSheaf J) hS n₀ n₁ h

theorem cohomologyComposableArrows_exact {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (cohomologyComposableArrows hS n₀ n₁ h).Exact :=
  Ext.covariantSequence_exact (constIntSheaf J) hS n₀ n₁ h

noncomputable def cohomologyZeroAddEquivHom (F : Sheaf J AddCommGrpCat.{w}) :
    F.H 0 ≃+ (constIntSheaf J ⟶ F) :=
  Ext.addEquiv₀

noncomputable def biprodSES (F G : Sheaf J AddCommGrpCat.{w}) :
    ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk (biprod.inl : F ⟶ F ⊞ G) (biprod.snd : F ⊞ G ⟶ G) (by simp)

theorem biprodSES_shortExact (F G : Sheaf J AddCommGrpCat.{w}) :
    (biprodSES F G).ShortExact :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact

theorem biprodSES_delta_apply_eq_zero (F G : Sheaf J AddCommGrpCat.{w}) (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁) (x : Ext (constIntSheaf J) (biprodSES F G).X₃ n₀) :
    cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x = 0 := by
  have hsurj : Function.Surjective (cohomologyMap (biprodSES F G).g n₀) :=
    cohomologyMap_surjective_of_section (biprodSES F G).g biprod.inr (by simp [biprodSES]) n₀
  obtain ⟨z, rfl⟩ := hsurj x
  exact (cohomology_exact_three (biprodSES_shortExact F G) n₀ n₁ h).apply_apply_eq_zero z

end GenericSite

section FppfSite

open AlgebraicGeometry

instance fppfSheavesIsGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} Scheme.{u} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall Scheme.fppfTopology Ab.{u + 1}

example : HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) := inferInstance

example : HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1} := inferInstance

example : Scheme.fppfTopology.{u}.Subcanonical := inferInstance

noncomputable example : IsTerminal (Spec (CommRingCat.of ℤ)) := specZIsTerminal

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

noncomputable abbrev FppfH (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Type (u + 1) :=
  F.H n

theorem fppfH_eq_sheafH (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (n : ℕ) :
    FppfH F n = F.H n := rfl

theorem fppf_les_exact_two {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (cohomologyMap S.f n) (cohomologyMap S.g n) :=
  cohomology_exact_two hS n

theorem fppf_les_exact_three {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyMap S.g n₀) (cohomologyδ hS n₀ n₁ h) :=
  cohomology_exact_three hS n₀ n₁ h

theorem fppf_les_exact_one {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (cohomologyδ hS n₀ n₁ h) (cohomologyMap S.f n₁) :=
  cohomology_exact_one hS n₀ n₁ h

theorem fppf_sixTermLES {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) :
    Function.Injective (cohomologyMap S.f 0) ∧
    Function.Exact (cohomologyMap S.f 0) (cohomologyMap S.g 0) ∧
    Function.Exact (cohomologyMap S.g 0) (cohomologyδ hS 0 1 rfl) ∧
    Function.Exact (cohomologyδ hS 0 1 rfl) (cohomologyMap S.f 1) ∧
    Function.Exact (cohomologyMap S.f 1) (cohomologyMap S.g 1) :=
  sixTermLES hS

theorem fppf_composableArrowsLES_exact
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (cohomologyComposableArrows hS n₀ n₁ h).Exact :=
  cohomologyComposableArrows_exact hS n₀ n₁ h

noncomputable def fppfCohomologyZeroAddEquivHom (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    FppfH F 0 ≃+ (constIntSheaf Scheme.fppfTopology.{u} ⟶ F) :=
  cohomologyZeroAddEquivHom F

theorem fppf_satGate_biprodSES_shortExact (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    (biprodSES F G).ShortExact :=
  biprodSES_shortExact F G

theorem fppf_satGate_les_applies (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Function.Exact (cohomologyMap (biprodSES F G).f n) (cohomologyMap (biprodSES F G).g n) :=
  fppf_les_exact_two (biprodSES_shortExact F G) n

theorem fppf_satGate_delta_eq_zero (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) (biprodSES F G).X₃ n₀) :
    cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x = 0 :=
  biprodSES_delta_apply_eq_zero F G n₀ n₁ h x

end WithLocalInstances

end FppfSite

section ElementaryComputations

theorem classGroup_int_card_eq_one : Fintype.card (ClassGroup ℤ) = 1 :=
  card_classGroup_eq_one

theorem classGroup_int_subsingleton : Subsingleton (ClassGroup ℤ) :=
  Fintype.card_le_one_iff_subsingleton.mp (le_of_eq card_classGroup_eq_one)

theorem natCard_classGroup_int : Nat.card (ClassGroup ℤ) = 1 := by
  rw [Nat.card_eq_fintype_card, classGroup_int_card_eq_one]

theorem pic_int_subsingleton : Subsingleton (CommRing.Pic ℤ) :=
  inferInstance

theorem intUnits_powMonoidHom_ker_of_odd (p : ℕ) (hp : Odd p) :
    (powMonoidHom p : ℤˣ →* ℤˣ).ker = ⊥ := by
  ext u
  simp only [MonoidHom.mem_ker, powMonoidHom_apply, Subgroup.mem_bot]
  rw [Int.units_pow_eq_pow_mod_two u p, Nat.odd_iff.mp hp, pow_one]

theorem intUnits_powMonoidHom_ker_two :
    (powMonoidHom 2 : ℤˣ →* ℤˣ).ker = ⊤ := by
  ext u
  simp only [MonoidHom.mem_ker, powMonoidHom_apply, Subgroup.mem_top, iff_true]
  exact Int.units_sq u

theorem intUnits_powMonoidHom_range_of_odd (p : ℕ) (hp : Odd p) :
    (powMonoidHom p : ℤˣ →* ℤˣ).range = ⊤ := by
  rw [MonoidHom.range_eq_top]
  intro u
  refine ⟨u, ?_⟩
  rw [powMonoidHom_apply, Int.units_pow_eq_pow_mod_two u p, Nat.odd_iff.mp hp, pow_one]

theorem intUnits_powMonoidHom_range_two :
    (powMonoidHom 2 : ℤˣ →* ℤˣ).range = ⊥ := by
  ext u
  simp only [MonoidHom.mem_range, powMonoidHom_apply, Subgroup.mem_bot]
  constructor
  · rintro ⟨v, rfl⟩
    exact Int.units_sq v
  · rintro rfl
    exact ⟨1, one_pow 2⟩

theorem natCard_intUnits : Nat.card ℤˣ = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

theorem natCard_intUnits_pthTorsion (p : ℕ) (hp : p.Prime) :
    Nat.card (powMonoidHom p : ℤˣ →* ℤˣ).ker = if p = 2 then 2 else 1 := by
  split_ifs with h
  · subst h
    rw [intUnits_powMonoidHom_ker_two, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  · rw [intUnits_powMonoidHom_ker_of_odd p (hp.odd_of_ne_two h), Subgroup.card_bot]

theorem natCard_intUnits_modPthPowers (p : ℕ) (hp : p.Prime) :
    Nat.card (ℤˣ ⧸ (powMonoidHom p : ℤˣ →* ℤˣ).range) = if p = 2 then 2 else 1 := by
  split_ifs with h
  · subst h
    rw [intUnits_powMonoidHom_range_two]
    rw [Nat.card_congr (QuotientGroup.quotientBot (G := ℤˣ)).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  · rw [intUnits_powMonoidHom_range_of_odd p (hp.odd_of_ne_two h)]
    have : Subsingleton (ℤˣ ⧸ (⊤ : Subgroup ℤˣ)) := QuotientGroup.subsingleton_quotient_top
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨this, ⟨1⟩⟩

theorem intUnits_kummer_exact_left (p : ℕ) :
    ((powMonoidHom p : ℤˣ →* ℤˣ).ker.subtype).range = (powMonoidHom p : ℤˣ →* ℤˣ).ker :=
  Subgroup.range_subtype _

theorem intUnits_kummer_exact_middle (p : ℕ) :
    (powMonoidHom p : ℤˣ →* ℤˣ).range =
      (QuotientGroup.mk' (powMonoidHom p : ℤˣ →* ℤˣ).range).ker :=
  (QuotientGroup.ker_mk' _).symm

theorem intUnits_kummer_mk'_surjective (p : ℕ) :
    Function.Surjective (QuotientGroup.mk' (powMonoidHom p : ℤˣ →* ℤˣ).range) :=
  QuotientGroup.mk'_surjective _

end ElementaryComputations

end FppfCohomologyLES

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section GenericSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

theorem cohomology_naturality_f {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (φ : S₁ ⟶ S₂) (n : ℕ) (x : Ext (constIntSheaf J) S₁.X₁ n) :
    cohomologyMap φ.τ₂ n (cohomologyMap S₁.f n x) =
      cohomologyMap S₂.f n (cohomologyMap φ.τ₁ n x) := by
  rw [← cohomologyMap_comp, ← cohomologyMap_comp, ShortComplex.Hom.comm₁₂]

theorem cohomology_naturality_g {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (φ : S₁ ⟶ S₂) (n : ℕ) (x : Ext (constIntSheaf J) S₁.X₂ n) :
    cohomologyMap φ.τ₃ n (cohomologyMap S₁.g n x) =
      cohomologyMap S₂.g n (cohomologyMap φ.τ₂ n x) := by
  rw [← cohomologyMap_comp, ← cohomologyMap_comp, ShortComplex.Hom.comm₂₃]

theorem cohomology_naturality_f_hom {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (φ : S₁ ⟶ S₂) (n : ℕ) :
    (cohomologyMap φ.τ₂ n).comp (cohomologyMap S₁.f n) =
      (cohomologyMap S₂.f n).comp (cohomologyMap φ.τ₁ n) :=
  AddMonoidHom.ext fun x => by
    simp only [AddMonoidHom.comp_apply]
    exact cohomology_naturality_f φ n x

theorem cohomology_naturality_g_hom {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (φ : S₁ ⟶ S₂) (n : ℕ) :
    (cohomologyMap φ.τ₃ n).comp (cohomologyMap S₁.g n) =
      (cohomologyMap S₂.g n).comp (cohomologyMap φ.τ₂ n) :=
  AddMonoidHom.ext fun x => by
    simp only [AddMonoidHom.comp_apply]
    exact cohomology_naturality_g φ n x

theorem cohomologyδ_naturality {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) S₁.X₃ n₀) :
    cohomologyδ hS₂ n₀ n₁ h (cohomologyMap φ.τ₃ n₀ x) =
      cohomologyMap φ.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x) := by
  simp only [cohomologyMap_apply, cohomologyδ_apply, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]
  rw [ShortComplex.ShortExact.extClass_naturality hS₁ hS₂ φ]

theorem cohomologyδ_naturality_hom {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (cohomologyδ hS₂ n₀ n₁ h).comp (cohomologyMap φ.τ₃ n₀) =
      (cohomologyMap φ.τ₁ n₁).comp (cohomologyδ hS₁ n₀ n₁ h) :=
  AddMonoidHom.ext fun x => by
    simp only [AddMonoidHom.comp_apply]
    exact cohomologyδ_naturality hS₁ hS₂ φ n₀ n₁ h x

theorem cohomologyδ_naturality_elem {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    {z : Ext (constIntSheaf J) S₁.X₃ n₀} {c : Ext (constIntSheaf J) S₁.X₁ n₁}
    (hzc : cohomologyδ hS₁ n₀ n₁ h z = c) :
    cohomologyδ hS₂ n₀ n₁ h (cohomologyMap φ.τ₃ n₀ z) = cohomologyMap φ.τ₁ n₁ c := by
  rw [cohomologyδ_naturality hS₁ hS₂ φ n₀ n₁ h z, hzc]

theorem cohomologyLES_ladder {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (∀ x, cohomologyMap φ.τ₂ n₀ (cohomologyMap S₁.f n₀ x) =
        cohomologyMap S₂.f n₀ (cohomologyMap φ.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap φ.τ₃ n₀ (cohomologyMap S₁.g n₀ x) =
        cohomologyMap S₂.g n₀ (cohomologyMap φ.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ hS₂ n₀ n₁ h (cohomologyMap φ.τ₃ n₀ x) =
        cohomologyMap φ.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x)) :=
  ⟨fun x => cohomology_naturality_f φ n₀ x, fun x => cohomology_naturality_g φ n₀ x,
    fun x => cohomologyδ_naturality hS₁ hS₂ φ n₀ n₁ h x⟩

noncomputable def cohomologyMapAddEquiv {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) (n : ℕ) :
    F.H n ≃+ G.H n where
  toFun := cohomologyMap e.hom n
  invFun := cohomologyMap e.inv n
  left_inv x := by rw [← cohomologyMap_comp, Iso.hom_inv_id, cohomologyMap_id]
  right_inv x := by rw [← cohomologyMap_comp, Iso.inv_hom_id, cohomologyMap_id]
  map_add' x y := map_add (cohomologyMap e.hom n) x y

@[simp]
lemma cohomologyMapAddEquiv_apply {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) (n : ℕ)
    (x : Ext (constIntSheaf J) F n) :
    cohomologyMapAddEquiv e n x = cohomologyMap e.hom n x := rfl

@[simp]
lemma cohomologyMapAddEquiv_symm_apply {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) (n : ℕ)
    (y : Ext (constIntSheaf J) G n) :
    (cohomologyMapAddEquiv e n).symm y = cohomologyMap e.inv n y := rfl

theorem cohomologyMap_bijective_of_isIso {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    [IsIso φ] (n : ℕ) :
    Function.Bijective (cohomologyMap φ n) := by
  constructor
  · intro x y hxy
    have h2 := congrArg (cohomologyMap (inv φ) n) hxy
    rwa [← cohomologyMap_comp, ← cohomologyMap_comp, IsIso.hom_inv_id, cohomologyMap_id,
      cohomologyMap_id] at h2
  · intro y
    refine ⟨cohomologyMap (inv φ) n y, ?_⟩
    rw [← cohomologyMap_comp, IsIso.inv_hom_id, cohomologyMap_id]

theorem cohomologyLES_iso_compatible {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e : S₁ ≅ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Bijective (cohomologyMap e.hom.τ₁ n₀) ∧
    Function.Bijective (cohomologyMap e.hom.τ₂ n₀) ∧
    Function.Bijective (cohomologyMap e.hom.τ₃ n₀) ∧
    (∀ x, cohomologyMap e.hom.τ₂ n₀ (cohomologyMap S₁.f n₀ x) =
        cohomologyMap S₂.f n₀ (cohomologyMap e.hom.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap e.hom.τ₃ n₀ (cohomologyMap S₁.g n₀ x) =
        cohomologyMap S₂.g n₀ (cohomologyMap e.hom.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ hS₂ n₀ n₁ h (cohomologyMap e.hom.τ₃ n₀ x) =
        cohomologyMap e.hom.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x)) :=
  ⟨cohomologyMap_bijective_of_isIso e.hom.τ₁ n₀,
    cohomologyMap_bijective_of_isIso e.hom.τ₂ n₀,
    cohomologyMap_bijective_of_isIso e.hom.τ₃ n₀,
    fun x => cohomology_naturality_f e.hom n₀ x,
    fun x => cohomology_naturality_g e.hom n₀ x,
    fun x => cohomologyδ_naturality hS₁ hS₂ e.hom n₀ n₁ h x⟩

theorem cohomologyδ_conj_of_iso {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e : S₁ ≅ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) S₁.X₃ n₀) :
    cohomologyδ hS₁ n₀ n₁ h x =
      cohomologyMap e.inv.τ₁ n₁ (cohomologyδ hS₂ n₀ n₁ h (cohomologyMap e.hom.τ₃ n₀ x)) := by
  rw [cohomologyδ_naturality hS₁ hS₂ e.hom n₀ n₁ h x, ← cohomologyMap_comp,
    ← ShortComplex.comp_τ₁, Iso.hom_inv_id, ShortComplex.id_τ₁, cohomologyMap_id]

theorem satGate_id_delta_naturality {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) S.X₃ n₀) :
    cohomologyδ hS n₀ n₁ h (cohomologyMap (𝟙 S : S ⟶ S).τ₃ n₀ x) =
        cohomologyMap (𝟙 S : S ⟶ S).τ₁ n₁ (cohomologyδ hS n₀ n₁ h x) ∧
    cohomologyδ hS n₀ n₁ h (cohomologyMap (𝟙 S : S ⟶ S).τ₃ n₀ x) =
        cohomologyδ hS n₀ n₁ h x ∧
    cohomologyMap (𝟙 S : S ⟶ S).τ₁ n₁ (cohomologyδ hS n₀ n₁ h x) =
        cohomologyδ hS n₀ n₁ h x :=
  ⟨cohomologyδ_naturality hS hS (𝟙 S) n₀ n₁ h x,
    by rw [ShortComplex.id_τ₃, cohomologyMap_id],
    by rw [ShortComplex.id_τ₁, cohomologyMap_id]⟩

noncomputable def biprodSESHom (F : Sheaf J AddCommGrpCat.{w})
    {G G' : Sheaf J AddCommGrpCat.{w}} (ψ : G ⟶ G') :
    biprodSES F G ⟶ biprodSES F G' where
  τ₁ := 𝟙 F
  τ₂ := biprod.map (𝟙 F) ψ
  τ₃ := ψ
  comm₁₂ := by simp [biprodSES]
  comm₂₃ := by simp [biprodSES]

@[simp]
lemma biprodSESHom_τ₁ (F : Sheaf J AddCommGrpCat.{w}) {G G' : Sheaf J AddCommGrpCat.{w}}
    (ψ : G ⟶ G') : (biprodSESHom F ψ).τ₁ = 𝟙 F := rfl

@[simp]
lemma biprodSESHom_τ₃ (F : Sheaf J AddCommGrpCat.{w}) {G G' : Sheaf J AddCommGrpCat.{w}}
    (ψ : G ⟶ G') : (biprodSESHom F ψ).τ₃ = ψ := rfl

theorem satGate_biprodSESHom_delta_naturality (F : Sheaf J AddCommGrpCat.{w})
    {G G' : Sheaf J AddCommGrpCat.{w}} (ψ : G ⟶ G') (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) (biprodSES F G).X₃ n₀) :
    cohomologyδ (biprodSES_shortExact F G') n₀ n₁ h
        (cohomologyMap (biprodSESHom F ψ).τ₃ n₀ x) =
      cohomologyMap (biprodSESHom F ψ).τ₁ n₁
        (cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x) :=
  cohomologyδ_naturality (biprodSES_shortExact F G) (biprodSES_shortExact F G')
    (biprodSESHom F ψ) n₀ n₁ h x

theorem satGate_biprodSESHom_delta_zero_consistency (F : Sheaf J AddCommGrpCat.{w})
    {G G' : Sheaf J AddCommGrpCat.{w}} (ψ : G ⟶ G') (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf J) (biprodSES F G).X₃ n₀) :
    cohomologyδ (biprodSES_shortExact F G') n₀ n₁ h
        (cohomologyMap (biprodSESHom F ψ).τ₃ n₀ x) = 0 ∧
    cohomologyMap (biprodSESHom F ψ).τ₁ n₁
        (cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x) = 0 :=
  ⟨biprodSES_delta_apply_eq_zero F G' n₀ n₁ h _,
    by rw [biprodSES_delta_apply_eq_zero F G n₀ n₁ h x, map_zero]⟩

noncomputable def biprodSESSwap (F G : Sheaf J AddCommGrpCat.{w}) :
    ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk (biprod.inr : F ⟶ G ⊞ F) (biprod.fst : G ⊞ F ⟶ G) (by simp)

noncomputable def biprodSESSwapIso (F G : Sheaf J AddCommGrpCat.{w}) :
    biprodSES F G ≅ biprodSESSwap F G :=
  ShortComplex.isoMk (Iso.refl F) (biprod.braiding F G) (Iso.refl G)
    (by
      dsimp [biprodSES, biprodSESSwap]
      apply biprod.hom_ext <;> simp)
    (by
      dsimp [biprodSES, biprodSESSwap]
      simp)

theorem biprodSESSwap_shortExact (F G : Sheaf J AddCommGrpCat.{w}) :
    (biprodSESSwap F G).ShortExact :=
  ShortComplex.shortExact_of_iso (biprodSESSwapIso F G) (biprodSES_shortExact F G)

theorem satGate_swapIso_les_compatible (F G : Sheaf J AddCommGrpCat.{w}) (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁) :
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₀) ∧
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀) ∧
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀) ∧
    (∀ x, cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀
            (cohomologyMap (biprodSES F G).f n₀ x) =
        cohomologyMap (biprodSESSwap F G).f n₀
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀
            (cohomologyMap (biprodSES F G).g n₀ x) =
        cohomologyMap (biprodSESSwap F G).g n₀
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ (biprodSESSwap_shortExact F G) n₀ n₁ h
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀ x) =
        cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₁
            (cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x)) :=
  cohomologyLES_iso_compatible (biprodSES_shortExact F G) (biprodSESSwap_shortExact F G)
    (biprodSESSwapIso F G) n₀ n₁ h

end GenericSite

section FppfSite

open AlgebraicGeometry

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

theorem fppf_naturality_f {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (φ : S₁ ⟶ S₂) (n : ℕ) (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) S₁.X₁ n) :
    cohomologyMap φ.τ₂ n (cohomologyMap S₁.f n x) =
      cohomologyMap S₂.f n (cohomologyMap φ.τ₁ n x) :=
  cohomology_naturality_f φ n x

theorem fppf_naturality_g {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (φ : S₁ ⟶ S₂) (n : ℕ) (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) S₁.X₂ n) :
    cohomologyMap φ.τ₃ n (cohomologyMap S₁.g n x) =
      cohomologyMap S₂.g n (cohomologyMap φ.τ₂ n x) :=
  cohomology_naturality_g φ n x

theorem fppf_delta_naturality {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) S₁.X₃ n₀) :
    cohomologyδ hS₂ n₀ n₁ h (cohomologyMap φ.τ₃ n₀ x) =
      cohomologyMap φ.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x) :=
  cohomologyδ_naturality hS₁ hS₂ φ n₀ n₁ h x

theorem fppf_delta_naturality_hom
    {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (cohomologyδ hS₂ n₀ n₁ h).comp (cohomologyMap φ.τ₃ n₀) =
      (cohomologyMap φ.τ₁ n₁).comp (cohomologyδ hS₁ n₀ n₁ h) :=
  cohomologyδ_naturality_hom hS₁ hS₂ φ n₀ n₁ h

theorem fppf_les_ladder {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (∀ x, cohomologyMap φ.τ₂ n₀ (cohomologyMap S₁.f n₀ x) =
        cohomologyMap S₂.f n₀ (cohomologyMap φ.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap φ.τ₃ n₀ (cohomologyMap S₁.g n₀ x) =
        cohomologyMap S₂.g n₀ (cohomologyMap φ.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ hS₂ n₀ n₁ h (cohomologyMap φ.τ₃ n₀ x) =
        cohomologyMap φ.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x)) :=
  cohomologyLES_ladder hS₁ hS₂ φ n₀ n₁ h

theorem fppf_les_iso_compatible
    {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e : S₁ ≅ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Bijective (cohomologyMap e.hom.τ₁ n₀) ∧
    Function.Bijective (cohomologyMap e.hom.τ₂ n₀) ∧
    Function.Bijective (cohomologyMap e.hom.τ₃ n₀) ∧
    (∀ x, cohomologyMap e.hom.τ₂ n₀ (cohomologyMap S₁.f n₀ x) =
        cohomologyMap S₂.f n₀ (cohomologyMap e.hom.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap e.hom.τ₃ n₀ (cohomologyMap S₁.g n₀ x) =
        cohomologyMap S₂.g n₀ (cohomologyMap e.hom.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ hS₂ n₀ n₁ h (cohomologyMap e.hom.τ₃ n₀ x) =
        cohomologyMap e.hom.τ₁ n₁ (cohomologyδ hS₁ n₀ n₁ h x)) :=
  cohomologyLES_iso_compatible hS₁ hS₂ e n₀ n₁ h

theorem fppf_delta_conj_of_iso
    {S₁ S₂ : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e : S₁ ≅ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) S₁.X₃ n₀) :
    cohomologyδ hS₁ n₀ n₁ h x =
      cohomologyMap e.inv.τ₁ n₁ (cohomologyδ hS₂ n₀ n₁ h (cohomologyMap e.hom.τ₃ n₀ x)) :=
  cohomologyδ_conj_of_iso hS₁ hS₂ e n₀ n₁ h x

theorem fppf_satGate_biprodSESHom_delta_naturality
    (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    {G G' : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}} (ψ : G ⟶ G') (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) (biprodSES F G).X₃ n₀) :
    cohomologyδ (biprodSES_shortExact F G') n₀ n₁ h
        (cohomologyMap (biprodSESHom F ψ).τ₃ n₀ x) =
      cohomologyMap (biprodSESHom F ψ).τ₁ n₁
        (cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x) :=
  satGate_biprodSESHom_delta_naturality F ψ n₀ n₁ h x

theorem fppf_satGate_id_delta_naturality
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Ext (constIntSheaf Scheme.fppfTopology.{u}) S.X₃ n₀) :
    cohomologyδ hS n₀ n₁ h (cohomologyMap (𝟙 S : S ⟶ S).τ₃ n₀ x) =
        cohomologyMap (𝟙 S : S ⟶ S).τ₁ n₁ (cohomologyδ hS n₀ n₁ h x) ∧
    cohomologyδ hS n₀ n₁ h (cohomologyMap (𝟙 S : S ⟶ S).τ₃ n₀ x) =
        cohomologyδ hS n₀ n₁ h x ∧
    cohomologyMap (𝟙 S : S ⟶ S).τ₁ n₁ (cohomologyδ hS n₀ n₁ h x) =
        cohomologyδ hS n₀ n₁ h x :=
  satGate_id_delta_naturality hS n₀ n₁ h x

theorem fppf_satGate_swapIso_les_compatible (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₀) ∧
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀) ∧
    Function.Bijective (cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀) ∧
    (∀ x, cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀
            (cohomologyMap (biprodSES F G).f n₀ x) =
        cohomologyMap (biprodSESSwap F G).f n₀
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₀ x)) ∧
    (∀ x, cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀
            (cohomologyMap (biprodSES F G).g n₀ x) =
        cohomologyMap (biprodSESSwap F G).g n₀
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₂ n₀ x)) ∧
    (∀ x, cohomologyδ (biprodSESSwap_shortExact F G) n₀ n₁ h
            (cohomologyMap (biprodSESSwapIso F G).hom.τ₃ n₀ x) =
        cohomologyMap (biprodSESSwapIso F G).hom.τ₁ n₁
            (cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h x)) :=
  satGate_swapIso_les_compatible F G n₀ n₁ h

end WithLocalInstances

end FppfSite

end FppfCohomologyLES


