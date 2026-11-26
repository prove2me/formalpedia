-- Prove2me | Definitions.Def_ProEtale_Algebra_IndWeaklyEtale_Lib
-- name    : ProEtale_Algebra_IndWeaklyEtale_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:52:54.346112+00:00
-- url     : https://prove2.me/theorems/09d56ee6-d85a-5f69-b8e7-c443e317daae
-- title:
--   Weak étaleness over localizations of the base, and bijectivity on stalks of weakly étale algebras at strictly henselian points
-- statement:
--   This file continues the published file of the same name. Recall that an $A$-algebra $B$ is *weakly étale* if both $A \to B$ and the multiplication map $B \otimes_A B \to B$ are flat, and that $A \to B$ is *bijective on stalks* if for every prime $\mathfrak q \subset B$ the induced map $A_{\mathfrak q \cap A} \to B_{\mathfrak q}$ is bijective.
--
--   Principal results:
--   1. **Base localization.** Let $A'$ be the localization of $A$ at a submonoid $M$ and let $B$ be an $A'$-algebra (compatibly with $A \to A' \to B$). If $B$ is weakly étale over $A$, then $B$ is weakly étale over $A'$.
--   2. **Localization of a localization.** For a submonoid $M \subseteq B$, a prime $\mathfrak q_1$ of $M^{-1}B$ and $\mathfrak q = \mathfrak q_1 \cap B$, the canonical map $B_{\mathfrak q} \to (M^{-1}B)_{\mathfrak q_1}$ is bijective.
--   3. Let $B$ be weakly étale over $A$ and $\mathfrak n \subset B$ a prime such that $A_{\mathfrak n \cap A}$ is strictly henselian. Then the stalk map
--   $$ A_{\mathfrak n \cap A} \longrightarrow B_{\mathfrak n} $$
--   is bijective.
--   4. Let $B$ be weakly étale over $A$, and suppose every prime $\mathfrak q \subset B$ is contained in some prime $\mathfrak n$ such that $A_{\mathfrak n \cap A}$ is strictly henselian. Then $A \to B$ is bijective on stalks.
--
--   Item 4 is the key step in showing that an ind-étale algebra over a w-contractible ring which acquires sections has a retraction: stalk maps at the primes $\mathfrak n$ are bijective by item 3, and the stalk maps at smaller primes are further localizations of these.
--
--   **Formalization Note** All rings are in a single universe `u`. Weak étaleness is Mathlib's `Algebra.WeaklyEtale` and bijectivity on stalks is the class `Algebra.BijectiveOnStalks`. The declarations are `Algebra.WeaklyEtale.localization_base`, `Localization.bijective_localRingHom_algebraMap_of_comap_eq`, `Algebra.WeaklyEtale.bijective_localRingHom_of_isStrictlyHenselianLocalRing` (stalk map phrased via `Localization.localRingHom`) and `Algebra.WeaklyEtale.bijectiveOnStalks`, whose hypothesis is `∀ q prime, ∃ n prime, q ≤ n ∧ IsStrictlyHenselianLocalRing (Localization.AtPrime (n.comap (algebraMap A B)))`. Item 3 reduces to the local statement `Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing` from the published file.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/IndWeaklyEtale.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Algebra_IndWeaklyEtale of the same module.

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Ring.Fin
import Mathlib.Algebra.Ring.Pi
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.WithTerminal.Lemmas
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Logic.Function.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.Inseparable
import Definitions.Def_ProEtale_Algebra_Bijective
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_Etale_Lib
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat_Lib
import Definitions.Def_ProEtale_Algebra_HenselianLocalRing
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndEtale_Lib
import Definitions.Def_ProEtale_Algebra_IndZariski
import Definitions.Def_ProEtale_Algebra_IntegralLocal
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Algebra_LocalizationColimit
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_Algebra_WeakDimension
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Algebra_WeaklyEtale_Lib
import Definitions.Def_ProEtale_Algebra_WeaklyEtaleField
import Definitions.Def_ProEtale_FiniteFields_Etale_AlgebraicHenselization
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtale
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtaleStructural
import Definitions.Def_ProEtale_Mathlib_Algebra_Algebra_Pi
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
import Definitions.Def_ProEtale_Mathlib_Algebra_GroupWithZero_NonZeroDivisors
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_IndSpreads
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_ObjectProperty_FiniteProducts
import Definitions.Def_ProEtale_Mathlib_FieldTheory_IsSepClosed
import Definitions.Def_ProEtale_Mathlib_Logic_Function_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Field
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Flat_FaithfullyFlat_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian_Lib
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents
import Definitions.Def_ProEtale_Mathlib_RingTheory_IntegralClosure_IntegrallyClosed
import Definitions.Def_ProEtale_Mathlib_RingTheory_Localization_Pi
import Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
import Definitions.Def_ProEtale_Mathlib_RingTheory_TensorProduct_Maps
import Definitions.Def_ProEtale_Mathlib_RingTheory_WeaklyEtale_Localization
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe u

open TensorProduct CategoryTheory Limits


section LocalizationBase

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]

/-- Weak étaleness descends along a localization of the base: if `B` is weakly étale over `A`
and `B` is an algebra over a localization `A'` of `A`, then `B` is weakly étale over `A'`. -/
theorem Algebra.WeaklyEtale.localization_base (M : Submonoid A) [Algebra A A']
    [IsLocalization M A'] [Algebra A B] [Algebra A' B] [IsScalarTower A A' B]
    [Algebra.WeaklyEtale A B] : Algebra.WeaklyEtale A' B where
  flat := (Module.flat_iff_of_isLocalization (S := A') (p := M) (M := B)).mpr inferInstance
  flat_lmul' := by
    have hcompat : TensorProduct.CompatibleSMul A A' B B :=
      IsLocalization.tensorProduct_compatibleSMul M A' B B
    let e : B ⊗[A'] B ≃ₐ[A'] B ⊗[A] B :=
      Algebra.TensorProduct.equivOfCompatibleSMul A A' A' B B
    have key : (Algebra.TensorProduct.lmul' A' (S := B)).toRingHom =
        (Algebra.TensorProduct.lmul' A (S := B)).toRingHom.comp (e : B ⊗[A'] B →+* B ⊗[A] B) := by
      refine RingHom.ext fun x ↦ ?_
      induction x with
      | zero => simp
      | tmul a b =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, Algebra.TensorProduct.lmul'_apply_tmul]
        rw [show (e (a ⊗ₜ[A'] b) : B ⊗[A] B) = a ⊗ₜ[A] b from rfl,
          Algebra.TensorProduct.lmul'_apply_tmul]
      | add x y hx hy => simp_all [map_add]
    change (Algebra.TensorProduct.lmul' A' (S := B)).toRingHom.Flat
    rw [key]
    exact RingHom.Flat.comp (.of_bijective e.bijective) (Algebra.WeaklyEtale.flat_lmul' A B)

end LocalizationBase

section LocalizationLocalization

variable {B : Type u} [CommRing B]

/-- Localizing a localization of `B` at a prime lying over the prime `q` of `B` gives the
localization of `B` at `q`: the canonical map is bijective. -/
theorem Localization.bijective_localRingHom_algebraMap_of_comap_eq (M : Submonoid B)
    (q₁ : Ideal (Localization M)) [q₁.IsPrime] (q : Ideal B) [q.IsPrime]
    (hq : q = q₁.comap (algebraMap B (Localization M))) :
    Function.Bijective
      (Localization.localRingHom q q₁ (algebraMap B (Localization M)) hq) := by
  subst hq
  -- `Localization.AtPrime q₁` is an `AtPrime` localization of `B` itself.
  haveI : IsLocalization.AtPrime (Localization.AtPrime q₁)
      (q₁.comap (algebraMap B (Localization M))) :=
    IsLocalization.isLocalization_atPrime_localization_atPrime M q₁
  set q := q₁.comap (algebraMap B (Localization M))
  -- The canonical comparison `AlgEquiv` between the two `AtPrime q` localizations.
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
    (Localization.AtPrime q₁)
  have he : Localization.localRingHom q q₁ (algebraMap B (Localization M)) rfl =
      (e : Localization.AtPrime q →+* Localization.AtPrime q₁) := by
    apply IsLocalization.ringHom_ext q.primeCompl
    refine RingHom.ext fun b ↦ ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, Localization.localRingHom_to_map,
      RingHom.coe_coe, IsLocalization.algEquiv_apply, IsLocalization.map_eq,
      ← IsScalarTower.algebraMap_apply]
    rfl
  rw [he]
  exact e.bijective

end LocalizationLocalization

section StrictlyHenselian

open IsLocalRing

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]


/-- The stalkwise version of
`Algebra.WeaklyEtale.bijective_algebraMap_localization_atPrime`: for a weakly étale
algebra `B` over `A` and a prime `n` of `B` such that the localization of `A` at `n ∩ A` is
strictly henselian, the stalk map `A_{n ∩ A} → B_n` is bijective. -/
theorem Algebra.WeaklyEtale.bijective_localRingHom_of_isStrictlyHenselianLocalRing
    [Algebra.WeaklyEtale A B] (n : Ideal B) [n.IsPrime]
    [IsStrictlyHenselianLocalRing (Localization.AtPrime (n.comap (algebraMap A B)))] :
    Function.Bijective
      (Localization.localRingHom (n.comap (algebraMap A B)) n (algebraMap A B) rfl) := by
  haveI : (n.comap (algebraMap A B)).IsPrime := ‹n.IsPrime›.comap (algebraMap A B)
  set m := n.comap (algebraMap A B) with hm
  set A' := Localization.AtPrime m with hA'
  set L := Localization.AtPrime n with hLdef
  letI : Algebra A' L := (Localization.localRingHom m n (algebraMap A B) rfl).toAlgebra
  haveI : IsScalarTower A A' L := .of_algebraMap_eq fun a ↦ by
    change algebraMap A L a = Localization.localRingHom m n (algebraMap A B) rfl
      (algebraMap A A' a)
    rw [Localization.localRingHom_to_map, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.WeaklyEtale B L := .of_isLocalization B n.primeCompl _
  haveI : Algebra.WeaklyEtale A L := .trans A B _
  haveI : Algebra.WeaklyEtale A' L := .localization_base m.primeCompl
  haveI : IsLocalHom (algebraMap A' L) :=
    Localization.isLocalHom_localRingHom m n (algebraMap A B) rfl
  exact Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing

/-- A weakly étale algebra `B` over `A` is bijective on stalks as soon as every prime of `B` is
contained in a prime `n` for which the localization of `A` at `n ∩ A` is strictly henselian.

This is the key step of the blueprint lemma
`thm:ind-etale-plus-c-has-retraction-if-w-contractible`: the stalk maps at such primes `n` are
bijective, and stalk maps at smaller primes are further localizations of these. -/
theorem Algebra.WeaklyEtale.bijectiveOnStalks [Algebra.WeaklyEtale A B]
    (hmax : ∀ (q : Ideal B) [q.IsPrime], ∃ (n : Ideal B) (hn : n.IsPrime), q ≤ n ∧
      (letI := hn
       letI : (n.comap (algebraMap A B)).IsPrime := hn.comap (algebraMap A B)
       IsStrictlyHenselianLocalRing (Localization.AtPrime (n.comap (algebraMap A B))))) :
    Algebra.BijectiveOnStalks A B := by
  constructor
  intro q hq
  obtain ⟨n, hn, hqn, hsh⟩ := hmax q
  haveI := hn
  haveI : (n.comap (algebraMap A B)).IsPrime := hn.comap (algebraMap A B)
  haveI : IsStrictlyHenselianLocalRing (Localization.AtPrime (n.comap (algebraMap A B))) := hsh
  set f := algebraMap A B
  set p := q.comap f
  set m := n.comap f
  set A' := Localization.AtPrime m with hA'
  set L := Localization.AtPrime n with hL
  set ψ := Localization.localRingHom m n f rfl with hψ
  have hψbij : Function.Bijective ψ :=
    Algebra.WeaklyEtale.bijective_localRingHom_of_isStrictlyHenselianLocalRing n
  -- The prime of `L` lying over `q`.
  have hdisj : Disjoint (n.primeCompl : Set B) (q : Set B) := by
    rw [Set.disjoint_iff]
    rintro x ⟨hx1, hx2⟩
    exact hx1 (hqn hx2)
  set q₁ : Ideal L := q.map (algebraMap B L) with hq₁def
  haveI hq₁prime : q₁.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint n.primeCompl L q hq hdisj
  have hq₁comap : q₁.comap (algebraMap B L) = q :=
    IsLocalization.under_map_of_isPrime_disjoint n.primeCompl L hq hdisj
  -- The prime of `A'` lying over `p`.
  set p₁ : Ideal A' := q₁.comap ψ with hp₁def
  haveI hp₁prime : p₁.IsPrime := hq₁prime.comap ψ
  -- The two composites `A → L` agree.
  have hcomm : ψ.comp (algebraMap A A') = (algebraMap B L).comp f := by
    refine RingHom.ext fun a ↦ ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact Localization.localRingHom_to_map m n f rfl a
  have hp₁comap : p₁.comap (algebraMap A A') = p := by
    rw [hp₁def, Ideal.comap_comap, hcomm, ← Ideal.comap_comap, hq₁comap]
  -- Decompose the localization of the composite in two ways.
  have hcomp₁ : Localization.localRingHom p q₁ ((algebraMap B L).comp f)
        (by rw [← Ideal.comap_comap, hq₁comap]) =
      (Localization.localRingHom q q₁ (algebraMap B L) hq₁comap.symm).comp
        (Localization.localRingHom p q f rfl) :=
    Localization.localRingHom_comp p q q₁ f rfl (algebraMap B L) hq₁comap.symm
  have hcomp₂ : Localization.localRingHom p q₁ (ψ.comp (algebraMap A A'))
        (by rw [← Ideal.comap_comap, ← hp₁def, hp₁comap]) =
      (Localization.localRingHom p₁ q₁ ψ rfl).comp
        (Localization.localRingHom p p₁ (algebraMap A A') hp₁comap.symm) :=
    Localization.localRingHom_comp p p₁ q₁ (algebraMap A A') hp₁comap.symm ψ rfl
  -- The left-hand sides agree.
  have hlhs : Localization.localRingHom p q₁ ((algebraMap B L).comp f)
        (by rw [← Ideal.comap_comap, hq₁comap]) =
      Localization.localRingHom p q₁ (ψ.comp (algebraMap A A'))
        (by rw [← Ideal.comap_comap, ← hp₁def, hp₁comap]) := by
    apply Localization.localRingHom_unique
    intro x
    rw [Localization.localRingHom_to_map, hcomm]
  -- All the outer maps are bijective.
  have hb : Function.Bijective (Localization.localRingHom q q₁ (algebraMap B L) hq₁comap.symm) :=
    Localization.bijective_localRingHom_algebraMap_of_comap_eq n.primeCompl q₁ q hq₁comap.symm
  have hc : Function.Bijective
      (Localization.localRingHom p p₁ (algebraMap A A') hp₁comap.symm) :=
    Localization.bijective_localRingHom_algebraMap_of_comap_eq m.primeCompl p₁ p hp₁comap.symm
  have hd : Function.Bijective (Localization.localRingHom p₁ q₁ ψ rfl) := by
    have := (RingEquiv.ofBijective ψ hψbij).bijectiveOnStalks q₁
    exact this
  -- Two-out-of-three.
  have hcomposite : Function.Bijective
      ((Localization.localRingHom q q₁ (algebraMap B L) hq₁comap.symm).comp
        (Localization.localRingHom p q f rfl)) := by
    rw [← hcomp₁, hlhs, hcomp₂]
    exact hd.comp hc
  constructor
  · intro x y hxy
    refine hcomposite.injective ?_
    simp only [RingHom.comp_apply]
    exact congrArg _ hxy
  · intro y
    obtain ⟨x, hx⟩ := hcomposite.surjective
      (Localization.localRingHom q q₁ (algebraMap B L) hq₁comap.symm y)
    exact ⟨x, hb.injective hx⟩

end StrictlyHenselian


/- `Algebra.WeaklyEtale.exists_indEtale` and `RingHom.WeaklyEtale.exists_indEtale_comp`
(blueprint `thm:weakly-etale-ind-etale`) are proved in
`Proetale.Algebra.WeaklyEtaleIndEtale`, which builds on this file. -/


