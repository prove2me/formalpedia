-- Prove2me | Definitions.Def_ProEtale_Algebra_WeaklyEtaleField
-- name    : ProEtale_Algebra_WeaklyEtaleField
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:47:56.435706+00:00
-- url     : https://prove2.me/theorems/660a2526-2011-441f-9a59-3fabedd40f9e
-- title:
--   Weakly étale algebras over a field are ind-étale, and weakly étale field extensions are separable
-- statement:
--   A commutative $R$-algebra $S$ is *weakly étale* if $R \to S$ is flat and the multiplication map $S \otimes_R S \to S$ is flat. A commutative ring is *absolutely flat* (von Neumann regular) if every module over it is flat. Let $k$ be a field.
--
--   Principal results:
--
--   1. If $L$ is a field and $k \to L$ is weakly étale, then $L/k$ is separable, i.e. every element of $L$ is algebraic over $k$ with separable minimal polynomial.
--   2. If $R$ is a weakly étale $k$-algebra, then every finitely generated $k$-subalgebra $A \subseteq R$ is étale over $k$, i.e. a finite product of finite separable field extensions of $k$.
--   3. Every weakly étale $k$-algebra $R$ is ind-étale over $k$: it is a filtered colimit of étale $k$-algebras.
--   4. If $K \to L$ is weakly étale and $L$ is absolutely flat (for instance a field), then $L \otimes_K L$ is absolutely flat.
--
--   The file also has two private lemmas used in the proofs. First, von Neumann regularity of $L \otimes_k L$ passes to $E \otimes_k E$ for every intermediate field $E$ of $L/k$. Second, a minimal prime $\mathfrak q$ of a subalgebra $A$ of a weakly étale $k$-algebra is maximal, and $A/\mathfrak q$ is separable and integral over $k$.
--
--   The result that weakly étale algebras over a field are ind-étale is the base case of the comparison between weakly étale and ind-étale maps.
--
--   **Formalization Note** Main declarations: `Algebra.WeaklyEtale.isAlgebraic` (whose conclusion is `Algebra.IsSeparable k L`, despite its name), `Algebra.WeaklyEtale.etale_of_fg`, `Algebra.WeaklyEtale.indEtale_field`, and the instance `Algebra.WeaklyEtale.absolutelyFlat_tensor_self`. In items 2 and 3, $k$ and $R$ lie in the same universe `u`. In item 1, $L$ may lie in any universe. In item 4, $K$ and $L$ are arbitrary commutative rings in universe `u`. Ind-étale means the existence of a filtered colimit presentation in `CommAlgCat` with étale stages (`Algebra.IndEtale`).
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 092P; Stacks Project, Tag 092I. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/WeaklyEtaleField.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
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
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
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
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
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
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.Inseparable
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_Etale_Lib
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat_Lib
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndEtale_Lib
import Definitions.Def_ProEtale_Algebra_IndZariski
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Algebra_LocalizationColimit
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_Algebra_WeakDimension
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Algebra_WeaklyEtale_Lib
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
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Field
import Definitions.Def_ProEtale_Mathlib_RingTheory_Flat_FaithfullyFlat_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents
import Definitions.Def_ProEtale_Mathlib_RingTheory_IntegralClosure_IntegrallyClosed
import Definitions.Def_ProEtale_Mathlib_RingTheory_Localization_Pi
import Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
import Definitions.Def_ProEtale_Mathlib_RingTheory_TensorProduct_Maps
import Definitions.Def_ProEtale_Mathlib_RingTheory_WeaklyEtale_Localization
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Weakly étale algebras over a field

Let `K → L` be a weakly étale extension of fields. This file collects basic
properties of the tensor product `L ⊗[K] L` and the multiplication map
`μ : L ⊗[K] L → L`, in preparation for the proof of
[Stacks 092P](https://stacks.math.columbia.edu/tag/092P) (a weakly étale extension
of fields is separable algebraic).

## Main results

* `Algebra.WeaklyEtale.absolutelyFlat_tensor_self` —
  if `K → L` is weakly étale and `L` is absolutely flat (in particular,
  a field), then `L ⊗[K] L` is absolutely flat. Reducedness follows
  automatically from the general `Ring.AbsolutelyFlat ⇒ IsReduced` instance.

We also introduce the `L`-algebra evaluation map
`tensorEvalRight : L[X] →ₐ[L] L ⊗[K] L`, `X ↦ 1 ⊗ a`, and check its basic
properties (`X`, `C`, and `X - C a` evaluations, plus that composing with
multiplication recovers `Polynomial.aeval a`).
-/

universe u

open scoped TensorProduct

open IntermediateField

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R]

namespace Algebra
namespace WeaklyEtale

/-- If every element `a` of `L ⊗[k] L` can be written as `a = a * a * u`, then the same holds
in `E ⊗[k] E` for any intermediate field `E` of `L/k`. Indeed, any `E`-linear retraction
`L → E` of the inclusion induces a retraction `L ⊗[k] L → E ⊗[k] E` which is semilinear over
`E ⊗[k] E`. -/
private lemma exists_eq_mul_self_mul_tensor_of_intermediateField {L : Type*} [Field L]
    [Algebra k L] (E : IntermediateField k L)
    (h : ∀ a : L ⊗[k] L, ∃ u, a = a * a * u) (b : E ⊗[k] E) :
    ∃ v, b = b * b * v := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E L)
    (LinearMap.ker_eq_bot.mpr (algebraMap E L).injective)
  have hπ' : ∀ c : E, π c = c := fun c ↦ by
    simpa using LinearMap.congr_fun hπ c
  let ι : E ⊗[k] E →ₐ[k] L ⊗[k] L := Algebra.TensorProduct.map E.val E.val
  let r : L ⊗[k] L →ₗ[k] E ⊗[k] E :=
    _root_.TensorProduct.map (π.restrictScalars k) (π.restrictScalars k)
  have hπmul : ∀ (c : E) (z : L), π (c * z) = c * π z := fun c z ↦ by
    rw [show (c : L) * z = c • z by rw [Algebra.smul_def, IntermediateField.algebraMap_apply],
      map_smul, smul_eq_mul]
  have hr : ∀ (c : E ⊗[k] E) (z : L ⊗[k] L), r (ι c * z) = c * r z := by
    intro c z
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c c' hc hc' => simp only [map_add, add_mul, hc, hc']
    | tmul c₁ c₂ =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, mul_add, hz, hz']
      | tmul z₁ z₂ =>
        simp only [ι, r, Algebra.TensorProduct.map_tmul, IntermediateField.coe_val,
          Algebra.TensorProduct.tmul_mul_tmul, _root_.TensorProduct.map_tmul,
          LinearMap.coe_restrictScalars, hπmul]
  have h1 : r 1 = 1 := by
    simp only [r, Algebra.TensorProduct.one_def, _root_.TensorProduct.map_tmul,
      LinearMap.coe_restrictScalars]
    rw [show (1 : L) = ((1 : E) : L) by simp, hπ' 1]
  have hrι : ∀ b : E ⊗[k] E, r (ι b) = b := fun b ↦ by
    have := hr b 1
    rwa [mul_one, h1, mul_one] at this
  obtain ⟨u, hu⟩ := h (ι b)
  refine ⟨r u, ?_⟩
  calc b = r (ι b) := (hrι b).symm
    _ = r (ι (b * b) * u) := by rw [map_mul ι b b, ← hu]
    _ = b * b * r u := hr _ _

/-- Any weakly étale extension of fields is algebraic separable -/
lemma isAlgebraic {L : Type*} [Field L] [Algebra k L] [WeaklyEtale k L] :
    Algebra.IsSeparable k L := by
  have habs : Ring.AbsolutelyFlat (L ⊗[k] L) :=
    .of_flat_lmul' L (L ⊗[k] L) (flat_lmul' L (L ⊗[k] L))
  refine ⟨fun x ↦ ?_⟩
  -- The von Neumann regularity of `L ⊗[k] L` descends to `k⟮x⟯ ⊗[k] k⟮x⟯`, hence `k⟮x⟯` is
  -- weakly étale over `k`.
  have : Ring.AbsolutelyFlat (k⟮x⟯ ⊗[k] k⟮x⟯) :=
    .of_forall_exists_eq_mul_self_mul <|
      exists_eq_mul_self_mul_tensor_of_intermediateField k⟮x⟯
        fun a ↦ Ring.AbsolutelyFlat.exists_eq_mul_self_mul a
  have : WeaklyEtale k k⟮x⟯ :=
    ⟨inferInstance, RingHom.Flat.of_pure_ker_of_surjective
      (fun y ↦ ⟨1 ⊗ₜ y, by simp⟩) (Ring.AbsolutelyFlat.flat _)⟩
  -- `k⟮x⟯` is essentially of finite type and formally unramified over `k`, hence separable.
  have : Algebra.EssFiniteType k k⟮x⟯ :=
    IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite (Set.toFinite _))
  have : Algebra.IsSeparable k k⟮x⟯ := Algebra.FormallyUnramified.isSeparable k k⟮x⟯
  exact IntermediateField.isSeparable_of_mem_isSeparable k L
    (IntermediateField.mem_adjoin_simple_self k x)

/-- If the localization of `R` at a prime `p` is a field, the kernel of the localization map
is `p` itself. -/
private lemma ker_algebraMap_localization_eq_of_isField {R : Type u} [CommRing R]
    {p : Ideal R} [p.IsPrime] (hf : IsField (Localization.AtPrime p)) :
    RingHom.ker (algebraMap R (Localization.AtPrime p)) = p := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ x).mp hx
    have hmem : ↑s * x ∈ p := by rw [hs]; exact p.zero_mem
    exact (‹p.IsPrime›.mem_or_mem hmem).resolve_left s.2
  · have h0 : Ideal.map (algebraMap R (Localization.AtPrime p)) p = ⊥ := by
      rw [Localization.AtPrime.map_eq_maximalIdeal]
      exact IsLocalRing.isField_iff_maximalIdeal_eq.mp hf
    rw [RingHom.mem_ker, ← Ideal.mem_bot, ← h0]
    exact Ideal.mem_map_of_mem _ hx

/-- A minimal prime `q` of a subalgebra `A` of a weakly étale `k`-algebra `R` is maximal,
with residue field separable and integral over `k`. Indeed, `q` is the contraction of a
prime `p` of `R`, and `A ⧸ q` embeds into the localization `R_p`, which is a field that is
separable algebraic over `k`. -/
private lemma isMaximal_isSeparable_of_mem_minimalPrimes [WeaklyEtale k R]
    (A : Subalgebra k R) {q : Ideal A} (hq : q ∈ minimalPrimes A) :
    q.IsMaximal ∧ Algebra.IsSeparable k (A ⧸ q) ∧ Algebra.IsIntegral k (A ⧸ q) := by
  haveI : Ring.AbsolutelyFlat R := .of_flat_lmul' k R (flat_lmul' k R)
  obtain ⟨p, hp, hcomap⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective
    (f := algebraMap A R) Subtype.val_injective q hq
  haveI := hp
  have hfield : IsField (Localization.AtPrime p) :=
    Ring.AbsolutelyFlat.isField_of_isLocalization_prime R p _
  letI : Field (Localization.AtPrime p) := hfield.toField
  haveI : WeaklyEtale R (Localization.AtPrime p) := .of_isLocalization R p.primeCompl _
  haveI : WeaklyEtale k (Localization.AtPrime p) := .trans k R (Localization.AtPrime p)
  haveI : Algebra.IsSeparable k (Localization.AtPrime p) := isAlgebraic
  haveI : Algebra.IsAlgebraic k (Localization.AtPrime p) :=
    ⟨fun x ↦ (Algebra.IsSeparable.isSeparable k x).isIntegral.isAlgebraic⟩
  -- The induced embedding `A ⧸ q → R_p`.
  let f : A →ₐ[k] Localization.AtPrime p :=
    (IsScalarTower.toAlgHom k R (Localization.AtPrime p)).comp A.val
  have hf : ∀ a : A, f a = 0 ↔ a ∈ q := fun a ↦ by
    have h1 : f a = 0 ↔ algebraMap A R a ∈ RingHom.ker (algebraMap R (Localization.AtPrime p)) :=
      RingHom.mem_ker.symm
    rw [h1, ker_algebraMap_localization_eq_of_isField hfield, ← hcomap, Ideal.mem_comap]
  let ψ : (A ⧸ q) →ₐ[k] Localization.AtPrime p :=
    Ideal.Quotient.liftₐ q f fun a ha ↦ (hf a).mpr ha
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    intro ha
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (hf a).mp (by simpa [ψ] using ha)
  have hmax : q.IsMaximal := by
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact (AlgEquiv.ofInjective ψ hψ).toMulEquiv.isField
      (Subalgebra.isField_of_algebraic ψ.range)
  have hsep : Algebra.IsSeparable k (A ⧸ q) := ⟨fun x ↦ by
    change (minpoly k x).Separable
    rw [← minpoly.algHom_eq ψ hψ x]
    exact Algebra.IsSeparable.isSeparable k (ψ x)⟩
  exact ⟨hmax, hsep, ⟨fun x ↦ (hsep.isSeparable' x).isIntegral⟩⟩

/-- Any finitely-generated subalgebra of a weakly étale algebra is étale. -/
lemma etale_of_fg [WeaklyEtale k R] (A : Subalgebra k R) (hA : A.FG) : Etale k A := by
  haveI : Ring.AbsolutelyFlat R := .of_flat_lmul' k R (flat_lmul' k R)
  haveI : Algebra.FiniteType k A := hA.finiteType
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsReduced A := isReduced_of_injective A.val Subtype.val_injective
  -- Every prime of `A` contains a minimal prime, which is maximal by the key lemma.
  have hmax : ∀ q : Ideal A, q.IsPrime → q.IsMaximal := fun q hq ↦ by
    haveI := hq
    obtain ⟨q₀, hq₀, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := q) bot_le
    have h := (isMaximal_isSeparable_of_mem_minimalPrimes A hq₀).1
    exact h.eq_of_le hq.ne_top hle ▸ h
  haveI : Ring.KrullDimLE 0 A := Ring.krullDimLE_zero_iff.mpr hmax
  haveI : IsArtinianRing A := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have hmin : ∀ I : MaximalSpectrum A, I.asIdeal ∈ minimalPrimes A := fun I ↦ by
    obtain ⟨q₀, hq₀, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A))
      (J := I.asIdeal) bot_le
    have h := (isMaximal_isSeparable_of_mem_minimalPrimes A hq₀).1
    rwa [h.eq_of_le I.isMaximal.ne_top hle] at hq₀
  -- Hence `A` is a finite product of finite separable field extensions of `k`.
  rw [Algebra.Etale.iff_exists_algEquiv_prod]
  refine ⟨MaximalSpectrum A, inferInstance, fun I ↦ A ⧸ I.asIdeal,
    fun I ↦ Ideal.Quotient.field I.asIdeal, fun I ↦ inferInstance,
    (IsArtinianRing.equivPi A).restrictScalars k, fun I ↦ ⟨?_, ?_⟩⟩
  · haveI := (isMaximal_isSeparable_of_mem_minimalPrimes A (hmin I)).2.2
    haveI : Algebra.FiniteType k (A ⧸ I.asIdeal) :=
      .of_surjective (Ideal.Quotient.mkₐ k I.asIdeal) (Ideal.Quotient.mkₐ_surjective k _)
    exact Algebra.IsIntegral.finite
  · exact (isMaximal_isSeparable_of_mem_minimalPrimes A (hmin I)).2.1

variable (k R) in
/-- Any weakly étale algebra over a field is ind-étale. -/
theorem indEtale_field [WeaklyEtale k R] : IndEtale k R :=
  .of_forall_fg_etale fun A hA ↦ etale_of_fg A hA

/-- If `K → L` is weakly étale and `L` is absolutely flat (e.g. a field), then `L ⊗[K] L`
is absolutely flat.

Special case of Stacks [092I] (weakly étale algebras over absolutely flat rings are absolutely
flat) applied to the base change `L → L ⊗[K] L`. -/
instance absolutelyFlat_tensor_self (K L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    [Ring.AbsolutelyFlat L] [Algebra.WeaklyEtale K L] :
    Ring.AbsolutelyFlat (L ⊗[K] L) :=
  Ring.AbsolutelyFlat.of_flat_lmul' L (L ⊗[K] L)
    (Algebra.WeaklyEtale.flat_lmul' L (L ⊗[K] L))

variable (K L : Type u) [CommRing K] [CommRing L] [Algebra K L]


end WeaklyEtale
end Algebra


