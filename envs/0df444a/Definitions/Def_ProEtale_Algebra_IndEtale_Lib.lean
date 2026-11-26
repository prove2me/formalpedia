-- Prove2me | Definitions.Def_ProEtale_Algebra_IndEtale_Lib
-- name    : ProEtale_Algebra_IndEtale_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:45:22.035357+00:00
-- url     : https://prove2.me/theorems/7c865176-a22a-4421-a25d-57836fe304cd
-- title:
--   Ind-étale algebras: products, composition, base change, separability of residue fields, idempotents, and finitely generated subalgebras
-- statement:
--   This file continues the published file *Ind-étale algebras* (same module). Recall that an $R$-algebra $S$ is *ind-étale* if it is a filtered colimit, in the category of commutative $R$-algebras, of étale $R$-algebras; a ring homomorphism $f : R \to S$ is ind-étale if the induced algebra is. The file proves the following.
--
--   1. **Closure properties.** Ind-étale morphisms of commutative rings are stable under composition; étale $R$-algebras are closed under isomorphisms and under finite products; a finite product $\prod_{i\in I} A_i$ of ind-étale $R$-algebras is ind-étale; every ind-Zariski algebra is ind-étale (local isomorphisms are étale). For ring maps: $f$ ind-étale iff the algebra is ind-étale; $g\circ f$ is ind-étale if $f,g$ are; *cancellation*: if $f$ and $g \circ f$ are ind-étale then so is $g$; ind-étale maps are stable under base change; a map is ind-étale iff it is an ind-object of ind-étale maps, and a map written as a filtered colimit of ind-étale maps is ind-étale; for algebras, $R \to S \to T$ ind-étale implies $R \to T$ ind-étale.
--   2. **Separability.** Let $A \to B$ be ind-étale, $k$ a field and $L$ a local ring, with compatible $A$-algebra structures $A \to k \to L$. Then for every $A$-algebra homomorphism $\varphi : B \to L$ and every $b\in B$, the element $\varphi(b)$ is separable over $k$ (integral with separable minimal polynomial). Consequences: an ind-étale local algebra over a field $k$ is separable over $k$; if $R \to S$ is ind-étale and the prime $\mathfrak q \subset S$ lies over $\mathfrak p \subset R$, then $\kappa(\mathfrak q)$ is a separable extension of $\kappa(\mathfrak p)$; for $B$ ind-étale over a field $K$, every residue field $\kappa(\mathfrak q)$ of $B$ is separable over $K$.
--   3. **Idempotents over a field.** If $B$ is ind-étale over a field $K$ and has two distinct prime ideals, then $B$ has an idempotent $e$ with $e \neq 0, 1$. If $\mathfrak q \subset B$ is a prime with $K \to \kappa(\mathfrak q)$ not bijective, then $\kappa(\mathfrak q) \otimes_K B$ has an idempotent $e \ne 0,1$.
--   4. **Finitely generated subalgebras.** Every $R$-algebra $S$ is the filtered colimit of its finitely generated $R$-subalgebras (an explicit colimit presentation); hence if every finitely generated $R$-subalgebra of $S$ is étale over $R$, then $S$ is ind-étale over $R$.
--
--   These results feed into the study of weakly étale algebras over strictly henselian local rings and into the theory of w-strictly local rings.
--
--   **Formalization Note** All rings live in a single universe `u`, and ind-objects are taken with index categories in `Type u`. Main declarations: `Algebra.IndEtale.pi`, `Algebra.IndEtale.of_indZariski`, `Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing`, `Algebra.IndEtale.isSeparable`, `Algebra.IndEtale.isSeparable_residueField`, `Algebra.IndEtale.isSeparable_residueField_of_field`, `Algebra.IndEtale.exists_isIdempotentElem_of_two_primes`, `Algebra.IndEtale.exists_isIdempotentElem_tensorProduct_of_residueField_ne`, `Algebra.IndEtale.trans`, `RingHom.IndEtale.comp`, `RingHom.IndEtale.of_comp`, `RingHom.IndEtale.isStableUnderBaseChange`, `RingHom.IndEtale.iff_ind_indEtale`, `RingHom.IndEtale.of_isColimit`, `Subalgebra.fgColimitPresentation`, `Algebra.IndEtale.of_forall_fg_etale`. The residue-field separability instance is stated with an explicit algebra structure between the localizations $R_{\mathfrak p} \to S_{\mathfrak q}$ compatible with $\mathfrak q$ lying over $\mathfrak p$. "Separable" is Mathlib's `IsSeparable`/`Algebra.IsSeparable`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/IndEtale.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Algebra_IndEtale of the same module.

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
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
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Ring.Fin
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
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Ideal
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
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.Inseparable
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_Etale_Lib
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat_Lib
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndZariski
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Algebra_LocalizationColimit
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_Mathlib_Algebra_Algebra_Pi
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
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
import Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents
import Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Algebra_IndEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Ind-étale algebras

In this file we define ind-étale algebras and ring homomorphisms.
-/

universe u

open CategoryTheory Limits TensorProduct

variable (R : Type u) {S : Type u} [CommRing R] [CommRing S] [Algebra R S]


instance inst_AlgebraIndEtale_L34 : (MorphismProperty.ind.{u} CommRingCat.etale.{u}).IsStableUnderComposition :=
  .ind_of_le_isFinitelyPresentable CommRingCat.etale_le_isFinitelyPresentable.{u}


namespace Algebra
namespace IndEtale

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]


instance inst_AlgebraIndEtale_L68 : (CommAlgCat.etale.{u} R).IsClosedUnderIsomorphisms := by
  rw [CommAlgCat.etale_eq]
  exact RingHom.Etale.respectsIso.isClosedUnderIsomorphisms_toObjectProperty R

/-- Étale algebras are closed under finite products. -/
instance inst_AlgebraIndEtale_L72 (I : Type u) [Finite I] :
    (CommAlgCat.etale.{u} R).IsClosedUnderLimitsOfShape (Discrete I) where
  limitsOfShape_le := by
    rintro X ⟨h⟩
    have (i : I) : Algebra.Etale R (h.diag.obj ⟨i⟩) := h.prop_diag_obj _
    have hpi : (CommAlgCat.etale.{u} R) (CommAlgCat.of R (∀ i, h.diag.obj ⟨i⟩)) :=
      inferInstanceAs (Algebra.Etale R _)
    exact (CommAlgCat.etale.{u} R).prop_of_iso
      (h.isLimit.conePointsIsoOfNatIso
        (CommAlgCat.isLimitPiFan fun i ↦ h.diag.obj ⟨i⟩) Discrete.natIsoFunctor).symm hpi

/-- Finite products of ind-étale algebras are ind-étale. -/
instance pi {I : Type u} [Finite I] (A : I → Type u) [∀ i, CommRing (A i)]
    [∀ i, Algebra R (A i)] [∀ i, IndEtale R (A i)] :
    IndEtale R (∀ i, A i) := by
  rw [iff_ind_etale]
  have hprop (i : I) : ObjectProperty.ind.{u} (CommAlgCat.etale.{u} R) (.of R (A i)) :=
    (iff_ind_etale R (A i)).mp inferInstance
  exact ObjectProperty.prop_of_isLimit
    (P := ObjectProperty.ind.{u} (CommAlgCat.etale.{u} R))
    (CommAlgCat.isLimitPiFan fun i ↦ CommAlgCat.of R (A i)) (fun ⟨i⟩ ↦ hprop i)

lemma isLocalIso_le_etale (R : Type u) [CommRing R] :
    CommAlgCat.isLocalIso R ≤ CommAlgCat.etale R := fun X hX ↦
  have : Algebra.IsLocalIso R X := hX
  Algebra.IsLocalIso.etale R X

/-- An ind-Zariski algebra is ind-étale, since localizations are étale. -/
instance (priority := 100) of_indZariski [IndZariski R S] : IndEtale R S := by
  rw [iff_ind_etale]
  refine ObjectProperty.ind_mono (isLocalIso_le_etale R) _ ?_
  rwa [← Algebra.IndZariski.iff_ind_isLocalIso]

/-- Let `A → B` be an ind-étale algebra and let `L` be a local ring that is also an algebra
over a field `k`, in a way compatible with the `A`-algebra structures. Then for every
`A`-algebra homomorphism `φ : B →ₐ[A] L` and every `b : B`, the image `φ b` is separable
over `k`. -/
lemma isSeparable_of_algHom_to_isLocalRing {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IndEtale A B] (k L : Type u) [Field k] [CommRing L] [IsLocalRing L]
    [Algebra A k] [Algebra A L] [Algebra k L] [IsScalarTower A k L]
    (φ : B →ₐ[A] L) (b : B) : IsSeparable k (φ b) := by
  obtain ⟨ι, hcat, hfilt, P, hP⟩ := IndEtale.exists_colimitPresentation (R := A) (S := B)
  letI : SmallCategory ι := hcat
  letI : IsFiltered ι := hfilt
  have hcolim : IsColimit ((forget (CommAlgCat.{u} A)).mapCocone P.cocone) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} A)) P.isColimit
  obtain ⟨i, bᵢ, hbᵢ⟩ := Types.jointly_surjective_of_isColimit hcolim b
  have : Algebra.Etale A (P.diag.obj i) := hP i
  let ψ : (k ⊗[A] P.diag.obj i) →ₐ[k] L :=
    Algebra.TensorProduct.lift (Algebra.ofId k L) (φ.comp (P.ι.app i).hom)
      (fun _ _ ↦ Commute.all _ _)
  have hψ : ψ ((1 : k) ⊗ₜ[A] bᵢ) = φ b := by
    simpa [ψ] using congrArg φ hbᵢ
  rw [← hψ]
  exact IsSeparable.of_algHom_etale_to_isLocalRing k _ L ψ _

instance isSeparable (k : Type u) [Field k] [Algebra k R] [IndEtale k R] [IsLocalRing R] :
    Algebra.IsSeparable k R :=
  ⟨fun x ↦ isSeparable_of_algHom_to_isLocalRing k R (AlgHom.id k R) x⟩

/-- If every element of `S` has separable image in `κ(q)` over a field `F`, then the residue
field `κ(q)` is separable over `F`. A general element of `κ(q)` is a ratio of images of two
elements of `S`, so the conclusion follows from `separableClosure` being closed under
division. -/
private lemma isSeparable_residueField_of_forall_isSeparable {F : Type u} [Field F]
    {T : Type u} [CommRing T] (q : Ideal T) [q.IsPrime] [Algebra F q.ResidueField]
    (key : ∀ s : T, IsSeparable F (algebraMap T q.ResidueField s)) :
    Algebra.IsSeparable F q.ResidueField := by
  refine ⟨fun y ↦ ?_⟩
  rw [← mem_separableClosure_iff (F := F) (E := q.ResidueField)]
  obtain ⟨x', m', -, hxm⟩ := IsFractionRing.div_surjective (A := T ⧸ q) y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x'
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m'
  rw [← hxm, Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk]
  exact div_mem (mem_separableClosure_iff.mpr (key x))
    (mem_separableClosure_iff.mpr (key m))

/-- An ind-étale ring extension `R → S` induces a separable extension `κ(p) → κ(q)` on
residue fields, for any pair of primes `q ∈ Spec S` lying over `p ∈ Spec R`. -/
instance isSeparable_residueField [IndEtale R S] (p : Ideal R) (q : Ideal S)
    [q.LiesOver p] [p.IsPrime] [q.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Algebra.IsSeparable p.ResidueField q.ResidueField :=
  -- Every image in `q.ResidueField` of an element of `S` factors through a finite étale
  -- `p.ResidueField`-subalgebra, hence is separable over `p.ResidueField`.
  isSeparable_residueField_of_forall_isSeparable q fun s ↦
    isSeparable_of_algHom_to_isLocalRing p.ResidueField q.ResidueField
      (IsScalarTower.toAlgHom R S q.ResidueField) s

/-- If `B` is an ind-étale algebra over a field `K`, then the residue field of any prime of
`B` is separable over `K`. -/
theorem isSeparable_residueField_of_field {K B : Type u} [Field K] [CommRing B]
    [Algebra K B] [IndEtale K B] (q : Ideal B) [q.IsPrime] :
    Algebra.IsSeparable K q.ResidueField :=
  isSeparable_residueField_of_forall_isSeparable q fun s ↦
    isSeparable_of_algHom_to_isLocalRing K q.ResidueField
      (IsScalarTower.toAlgHom K B q.ResidueField) s

/-- An étale algebra over a field with two distinct primes `p₁ ≠ p₂` contains an idempotent
separating `p₁` from `p₂`. -/
private lemma exists_isIdempotentElem_mem_of_ne {K C : Type u} [Field K] [CommRing C]
    [Algebra K C] [Algebra.Etale K C] {p₁ p₂ : Ideal C} [p₁.IsPrime] [p₂.IsPrime]
    (h : p₁ ≠ p₂) :
    ∃ e : C, IsIdempotentElem e ∧ e ∈ p₁ ∧ 1 - e ∈ p₂ := by
  classical
  obtain ⟨I, hfin, Ai, hfield, halg, eqv, -⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := C)).mp inferInstance
  have : Finite I := hfin
  let _ : ∀ i, Field (Ai i) := hfield
  let _ : ∀ i, Algebra K (Ai i) := halg
  let f : (∀ i, Ai i) →ₐ[K] C := eqv.symm.toAlgHom
  have hfx : ∀ x : C, f (eqv x) = x := fun x ↦ eqv.symm_apply_apply x
  obtain ⟨j₁, hj₁⟩ := Ideal.exists_eq_ker_evalRingHom (p₁.comap f)
  obtain ⟨j₂, hj₂⟩ := Ideal.exists_eq_ker_evalRingHom (p₂.comap f)
  have hj : j₁ ≠ j₂ := by
    rintro rfl
    refine h (SetLike.ext fun x ↦ ?_)
    have h₁ : x ∈ p₁ ↔ eqv x ∈ p₁.comap f := by rw [Ideal.mem_comap, hfx]
    have h₂ : x ∈ p₂ ↔ eqv x ∈ p₂.comap f := by rw [Ideal.mem_comap, hfx]
    rw [h₁, h₂, hj₁, hj₂]
  have hidem : IsIdempotentElem (Pi.single j₁ (1 : Ai j₁)) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  refine ⟨f ((1 : ∀ i, Ai i) - Pi.single j₁ 1), hidem.one_sub.map f, ?_, ?_⟩
  · have hz : ((1 : ∀ i, Ai i) - Pi.single j₁ 1) ∈ p₁.comap f := by
      rw [hj₁, RingHom.mem_ker]
      simp
    exact Ideal.mem_comap.mp hz
  · have h1f : (1 : C) - f ((1 : ∀ i, Ai i) - Pi.single j₁ 1) = f (Pi.single j₁ 1) := by
      rw [map_sub, map_one, sub_sub_cancel]
    rw [h1f]
    have hz : (Pi.single j₁ (1 : Ai j₁) : ∀ i, Ai i) ∈ p₂.comap f := by
      rw [hj₂, RingHom.mem_ker, Pi.evalRingHom_apply]
      exact Pi.single_eq_of_ne (Ne.symm hj) 1
    exact Ideal.mem_comap.mp hz

/-- If `B` is an ind-étale algebra over a field `K` and `B` has at least two distinct prime
ideals, then `B` has a nontrivial idempotent element. -/
theorem exists_isIdempotentElem_of_two_primes {K B : Type u} [Field K] [CommRing B]
    [Algebra K B] [Algebra.IndEtale K B] {q₁ q₂ : Ideal B} [q₁.IsPrime] [q₂.IsPrime]
    (h : q₁ ≠ q₂) :
    ∃ e : B, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  -- Pick an element distinguishing `q₁` from `q₂`.
  obtain ⟨x, hx⟩ : ∃ x : B, ¬ (x ∈ q₁ ↔ x ∈ q₂) :=
    not_forall.mp fun hc ↦ h (SetLike.ext hc)
  -- Lift `x` to a stage of a filtered colimit presentation by étale algebras.
  obtain ⟨ι, _, _, P, hP⟩ := exists_colimitPresentation (R := K) (S := B)
  have hc' := isColimitOfPreserves (forget (CommAlgCat K)) P.isColimit
  obtain ⟨i, x₀, hx'⟩ := Types.jointly_surjective_of_isColimit hc' x
  let φ : P.diag.obj i →ₐ[K] B := (P.ι.app i).hom
  replace hx' : φ x₀ = x := by simpa using hx'
  have : Algebra.Etale K (P.diag.obj i) := hP i
  -- The contractions of `q₁` and `q₂` to the étale stage are distinct primes.
  have hne : q₁.comap φ ≠ q₂.comap φ := fun he ↦
    hx (by rw [← hx', ← Ideal.mem_comap, ← Ideal.mem_comap, he])
  obtain ⟨e', he', hm₁, hm₂⟩ := exists_isIdempotentElem_mem_of_ne (K := K) hne
  refine ⟨φ e', he'.map φ, ?_, ?_⟩
  · intro h0
    have h1 : (1 : B) - φ e' ∈ q₂ := by
      have hm : φ (1 - e') ∈ q₂ := Ideal.mem_comap.mp hm₂
      rwa [map_sub, map_one] at hm
    rw [h0, sub_zero] at h1
    exact (Ideal.ne_top_iff_one q₂).mp ‹q₂.IsPrime›.ne_top h1
  · intro h1
    have h2 : φ e' ∈ q₁ := Ideal.mem_comap.mp hm₁
    rw [h1] at h2
    exact (Ideal.ne_top_iff_one q₁).mp ‹q₁.IsPrime›.ne_top h2

end IndEtale
end Algebra


namespace RingHom
namespace IndEtale

variable (S) in
lemma algebraMap_iff : (algebraMap R S).IndEtale ↔ Algebra.IndEtale R S :=
  toAlgebra_algebraMap (R := R) (S := S).symm ▸ Iff.rfl


variable {R S : Type u} [CommRing R] [CommRing S]

lemma comp {T : Type u} [CommRing T] {g : S →+* T} {f : R →+* S} (hg : g.IndEtale)
    (hf : f.IndEtale) : (g.comp f).IndEtale := by
  rw [iff_ind_etale] at hf hg ⊢
  rw [CommRingCat.ofHom_comp]
  exact (MorphismProperty.ind.{u} CommRingCat.etale).comp_mem _ _ hf hg

/-- Cancellation for ind-étale ring maps: if `f : R →+* S` and `g ∘ f : R →+* T` are
ind-étale, then so is `g : S →+* T`. -/
lemma of_comp {T : Type u} [CommRing T] {f : R →+* S} {g : S →+* T} (hf : f.IndEtale)
    (hgf : (g.comp f).IndEtale) : g.IndEtale := by
  haveI : (MorphismProperty.ind.{u} CommRingCat.etale.{u}).HasOfPrecompProperty
      (MorphismProperty.ind.{u} CommRingCat.etale.{u}) :=
    MorphismProperty.ind_hasOfPrecompProperty_ind CommRingCat.etale_le_isFinitelyPresentable.{u}
  rw [iff_ind_etale] at hf hgf ⊢
  rw [CommRingCat.ofHom_comp] at hgf
  exact MorphismProperty.of_precomp (W := MorphismProperty.ind.{u} CommRingCat.etale.{u})
    (W' := MorphismProperty.ind.{u} CommRingCat.etale.{u})
    (CommRingCat.ofHom f) (CommRingCat.ofHom g) hf hgf

/-- Ind-étale ring homomorphisms are stable under base change. -/
lemma isStableUnderBaseChange : IsStableUnderBaseChange IndEtale := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ hpush hRS
  rw [iff_ind_etale] at hRS ⊢
  rw [← CommRingCat.isPushout_iff_isPushout] at hpush
  exact (inferInstance : (MorphismProperty.ind CommRingCat.etale).IsStableUnderCobaseChange).1
    hpush.flip hRS

/-- Ind-étale is equivalent to ind-ind-étale. -/
lemma iff_ind_indEtale (f : R →+* S) :
    f.IndEtale ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IndEtale) (CommRingCat.ofHom f) := by
  rw [iff_ind_etale]
  have heq : RingHom.toMorphismProperty RingHom.IndEtale =
      MorphismProperty.ind.{u} CommRingCat.etale := by
    ext X Y g
    exact iff_ind_etale g.hom
  rw [heq, MorphismProperty.ind_ind CommRingCat.etale_le_isFinitelyPresentable.{u}]

/-- A ring hom is ind-étale if it can be written as a filtered colimit of ind-étale maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.IndEtale ∧ t.app i ≫ c.app i = f) : f.hom.IndEtale :=
  (iff_ind_indEtale _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc,
    fun i ↦ ⟨by exact (htc i).1, by rw [(htc i).2]; rfl⟩⟩


end IndEtale
end RingHom

namespace Algebra
namespace IndEtale

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

lemma trans (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.IndEtale R S] [Algebra.IndEtale S T] :
    Algebra.IndEtale R T := by
  rw [← RingHom.IndEtale.algebraMap_iff R T, IsScalarTower.algebraMap_eq R S T]
  exact RingHom.IndEtale.comp
    ((RingHom.IndEtale.algebraMap_iff S T).mpr ‹_›)
    ((RingHom.IndEtale.algebraMap_iff R S).mpr ‹_›)

/-- If `B` is an ind-étale algebra over a field `K` and `q` is a prime ideal of `B` whose
residue field is strictly larger than `K`, then the tensor product
`κ(q) ⊗[K] B` has a nontrivial idempotent element. -/
theorem exists_isIdempotentElem_tensorProduct_of_residueField_ne {K B : Type u}
    [Field K] [CommRing B] [Algebra K B] [Algebra.IndEtale K B]
    (q : Ideal B) [q.IsPrime]
    (h : ¬ Function.Bijective (algebraMap K q.ResidueField)) :
    ∃ e : q.ResidueField ⊗[K] B, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  have : Algebra.IsSeparable K q.ResidueField := isSeparable_residueField_of_field q
  -- `κ(q) ⊗[K] B` is ind-étale over `κ(q)` by base change.
  have : Algebra.IndEtale q.ResidueField (q.ResidueField ⊗[K] B) := by
    have hbc := RingHom.IsStableUnderBaseChange.tensorProduct
      RingHom.IndEtale.isStableUnderBaseChange (R := K) (S := B) q.ResidueField
      ((RingHom.IndEtale.algebraMap_iff (R := K) (S := B)).mpr inferInstance)
    exact (RingHom.IndEtale.algebraMap_iff (R := q.ResidueField)
      (S := q.ResidueField ⊗[K] B)).mp hbc
  -- By `exists_isIdempotentElem_of_two_primes` it suffices to exhibit two distinct primes.
  suffices hp : ∃ P₁ P₂ : Ideal (q.ResidueField ⊗[K] B),
      P₁.IsPrime ∧ P₂.IsPrime ∧ P₁ ≠ P₂ by
    obtain ⟨P₁, P₂, hP₁, hP₂, hPne⟩ := hp
    have := hP₁
    have := hP₂
    exact exists_isIdempotentElem_of_two_primes (K := q.ResidueField) hPne
  -- An element `y` of the residue field not in the image of `K`.
  obtain ⟨y, hy⟩ : ∃ y : q.ResidueField, y ∉ (algebraMap K q.ResidueField).range :=
    not_forall.mp fun hc ↦ h ⟨(algebraMap K q.ResidueField).injective,
      fun y ↦ RingHom.mem_range.mp (hc y)⟩
  have hyint : IsIntegral K y := (Algebra.IsSeparable.isSeparable K y).isIntegral
  -- The minimal polynomial of `y` has a second root `y'` in the algebraic closure.
  have hcard : 1 < Fintype.card
      ((minpoly K y).rootSet (AlgebraicClosure q.ResidueField)) := by
    rw [Polynomial.card_rootSet_eq_natDegree (Algebra.IsSeparable.isSeparable K y)
      (IsAlgClosed.splits _)]
    exact lt_of_lt_of_le one_lt_two ((minpoly.two_le_natDegree_iff hyint).mpr hy)
  have hy₀mem : algebraMap q.ResidueField (AlgebraicClosure q.ResidueField) y ∈
      (minpoly K y).rootSet (AlgebraicClosure q.ResidueField) := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hyint,
      by rw [Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]⟩
  obtain ⟨⟨y', hy'mem⟩, hne'⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨_, hy₀mem⟩
  have hyne : y' ≠ algebraMap q.ResidueField (AlgebraicClosure q.ResidueField) y :=
    fun hh ↦ hne' (Subtype.ext hh)
  -- A second embedding `σ : κ(q) →ₐ[K] Ω` with `σ y = y'`.
  obtain ⟨σ, hσ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
    (fun s : q.ResidueField ↦
      ⟨(Algebra.IsSeparable.isSeparable K s).isIntegral, IsAlgClosed.splits _⟩)
    ((Polynomial.mem_rootSet.mp hy'mem).2)
  -- Write `y` as a fraction of images of elements of `B`.
  obtain ⟨x', m', hm', hxm⟩ := IsFractionRing.div_surjective (A := B ⧸ q) y
  obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective x'
  obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective m'
  have hb₂ : algebraMap B q.ResidueField b₂ ≠ 0 := by
    have hb := map_ne_zero_of_mem_nonZeroDivisors (algebraMap (B ⧸ q) q.ResidueField)
      q.injective_algebraMap_quotient_residueField hm'
    rwa [Ideal.algebraMap_quotient_residueField_mk] at hb
  rw [Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk] at hxm
  have hyb : algebraMap B q.ResidueField b₁ = y * algebraMap B q.ResidueField b₂ :=
    (div_eq_iff hb₂).mp hxm
  -- The two maps to the algebraic closure, differing only on the left tensor factor.
  let ψ : B →ₐ[K] AlgebraicClosure q.ResidueField :=
    (IsScalarTower.toAlgHom K q.ResidueField (AlgebraicClosure q.ResidueField)).comp
      (IsScalarTower.toAlgHom K B q.ResidueField)
  let Φ₁ : q.ResidueField ⊗[K] B →ₐ[K] AlgebraicClosure q.ResidueField :=
    Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom K q.ResidueField (AlgebraicClosure q.ResidueField)) ψ
  let Φ₂ : q.ResidueField ⊗[K] B →ₐ[K] AlgebraicClosure q.ResidueField :=
    Algebra.TensorProduct.productMap σ ψ
  have hΦ₁tmul (l : q.ResidueField) (b : B) : Φ₁ (l ⊗ₜ[K] b) =
      algebraMap q.ResidueField (AlgebraicClosure q.ResidueField) l *
      algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)
        (algebraMap B q.ResidueField b) := by
    simp only [Φ₁, ψ, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
  have hΦ₂tmul (l : q.ResidueField) (b : B) : Φ₂ (l ⊗ₜ[K] b) =
      σ l * algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)
        (algebraMap B q.ResidueField b) := by
    simp only [Φ₂, ψ, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
  -- The element `y ⊗ b₂ - 1 ⊗ b₁` lies in `ker Φ₁` but not in `ker Φ₂`.
  have hw₁ : Φ₁ (y ⊗ₜ[K] b₂ - 1 ⊗ₜ[K] b₁) = 0 := by
    rw [map_sub, hΦ₁tmul y b₂, hΦ₁tmul 1 b₁, map_one, one_mul, ← map_mul, ← hyb,
      sub_self]
  have hβ₂Ω : algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)
      (algebraMap B q.ResidueField b₂) ≠ 0 := fun h0 ↦
    hb₂ (RingHom.injective (algebraMap q.ResidueField (AlgebraicClosure q.ResidueField))
      (by rw [h0, map_zero]))
  have hw₂ : Φ₂ (y ⊗ₜ[K] b₂ - 1 ⊗ₜ[K] b₁) ≠ 0 := by
    have hcalc : Φ₂ (y ⊗ₜ[K] b₂ - 1 ⊗ₜ[K] b₁) =
        (σ y - algebraMap q.ResidueField (AlgebraicClosure q.ResidueField) y) *
        algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)
          (algebraMap B q.ResidueField b₂) := by
      rw [map_sub, hΦ₂tmul y b₂, hΦ₂tmul 1 b₁, map_one, one_mul, hyb, map_mul, sub_mul]
    rw [hcalc]
    exact mul_ne_zero (sub_ne_zero_of_ne (by rwa [hσ])) hβ₂Ω
  refine ⟨RingHom.ker Φ₁, RingHom.ker Φ₂, RingHom.ker_isPrime _, RingHom.ker_isPrime _, ?_⟩
  intro hk
  apply hw₂
  have hmem : (y ⊗ₜ[K] b₂ - 1 ⊗ₜ[K] b₁ : q.ResidueField ⊗[K] B) ∈ RingHom.ker Φ₁ :=
    RingHom.mem_ker.mpr hw₁
  rw [hk] at hmem
  exact RingHom.mem_ker.mp hmem

end IndEtale
end Algebra

section FGColimitPresentation

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

namespace Subalgebra

instance inst_AlgebraIndEtale_L459 : Nonempty {A : Subalgebra R S // A.FG} :=
  ⟨⊥, Subalgebra.fg_bot⟩

instance inst_AlgebraIndEtale_L462 : IsDirected {A : Subalgebra R S // A.FG} (· ≤ ·) :=
  ⟨fun A B ↦ ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩,
    Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩⟩

variable (R S) in
/-- The filtered diagram of the finitely generated subalgebras of an `R`-algebra `S`. -/
@[simps]
def fgDiag : {A : Subalgebra R S // A.FG} ⥤ CommAlgCat.{u} R where
  obj A := .of R A.1
  map h := CommAlgCat.ofHom (Subalgebra.inclusion (Subtype.coe_le_coe.mpr h.le))
  map_id _ := CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl)
  map_comp _ _ := CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl)

private def descFun (c : Cocone (fgDiag R S)) (x : S) : c.pt :=
  (c.ι.app ⟨Algebra.adjoin R {x}, fg_def.mpr ⟨{x}, Set.finite_singleton x, rfl⟩⟩).hom
    ⟨x, Algebra.self_mem_adjoin_singleton R x⟩

private lemma descFun_eq {c : Cocone (fgDiag R S)} (A : {A : Subalgebra R S // A.FG})
    {x : S} (hx : x ∈ A.1) :
    descFun c x = (c.ι.app A).hom ⟨x, hx⟩ := by
  have h : (⟨Algebra.adjoin R {x}, fg_def.mpr ⟨{x}, Set.finite_singleton x, rfl⟩⟩ :
      {A : Subalgebra R S // A.FG}) ≤ A :=
    Subtype.coe_le_coe.mp (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx))
  have key := congrArg (fun f ↦ f.hom ⟨x, Algebra.self_mem_adjoin_singleton R x⟩)
    (c.w (homOfLE h))
  simpa [descFun] using key.symm

private def descAlgHom (c : Cocone (fgDiag R S)) : S →ₐ[R] c.pt where
  toFun := descFun c
  map_one' := by
    change descFun c 1 = 1
    rw [descFun_eq ⟨⊥, Subalgebra.fg_bot⟩ (one_mem _)]
    exact map_one _
  map_zero' := by
    change descFun c 0 = 0
    rw [descFun_eq ⟨⊥, Subalgebra.fg_bot⟩ (zero_mem _)]
    exact map_zero _
  map_mul' x y := by
    change descFun c (x * y) = descFun c x * descFun c y
    have hfg : (Algebra.adjoin R ({x, y} : Set S)).FG := fg_def.mpr ⟨_, Set.toFinite _, rfl⟩
    have hx : x ∈ Algebra.adjoin R ({x, y} : Set S) := Algebra.subset_adjoin (by simp)
    have hy : y ∈ Algebra.adjoin R ({x, y} : Set S) := Algebra.subset_adjoin (by simp)
    rw [descFun_eq ⟨_, hfg⟩ (mul_mem hx hy), descFun_eq ⟨_, hfg⟩ hx, descFun_eq ⟨_, hfg⟩ hy]
    exact map_mul (c.ι.app ⟨_, hfg⟩).hom ⟨x, hx⟩ ⟨y, hy⟩
  map_add' x y := by
    change descFun c (x + y) = descFun c x + descFun c y
    have hfg : (Algebra.adjoin R ({x, y} : Set S)).FG := fg_def.mpr ⟨_, Set.toFinite _, rfl⟩
    have hx : x ∈ Algebra.adjoin R ({x, y} : Set S) := Algebra.subset_adjoin (by simp)
    have hy : y ∈ Algebra.adjoin R ({x, y} : Set S) := Algebra.subset_adjoin (by simp)
    rw [descFun_eq ⟨_, hfg⟩ (add_mem hx hy), descFun_eq ⟨_, hfg⟩ hx, descFun_eq ⟨_, hfg⟩ hy]
    exact map_add (c.ι.app ⟨_, hfg⟩).hom ⟨x, hx⟩ ⟨y, hy⟩
  commutes' r := by
    change descFun c (algebraMap R S r) = algebraMap R c.pt r
    rw [descFun_eq ⟨⊥, Subalgebra.fg_bot⟩ (Subalgebra.algebraMap_mem _ r)]
    exact (c.ι.app _).hom.commutes r

variable (R S) in
/-- Every `R`-algebra `S` is the filtered colimit of its finitely generated subalgebras. -/
def fgColimitPresentation :
    ColimitPresentation {A : Subalgebra R S // A.FG} (CommAlgCat.of R S) where
  diag := fgDiag R S
  ι :=
    { app A := CommAlgCat.ofHom A.1.val
      naturality _ _ _ := CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl) }
  isColimit :=
    { desc c := CommAlgCat.ofHom (descAlgHom c)
      fac c A := CommAlgCat.hom_ext (AlgHom.ext fun x ↦ descFun_eq A x.2)
      uniq c m hm := by
        refine CommAlgCat.hom_ext (AlgHom.ext fun x ↦ ?_)
        have key := congrArg (fun f ↦ f.hom ⟨x, Algebra.self_mem_adjoin_singleton R x⟩)
          (hm ⟨Algebra.adjoin R {x}, fg_def.mpr ⟨{x}, Set.finite_singleton x, rfl⟩⟩)
        simpa [descAlgHom, descFun] using key }

end Subalgebra

/-- If every finitely generated `R`-subalgebra of `S` is étale, then `S` is an ind-étale
`R`-algebra. -/
theorem Algebra.IndEtale.of_forall_fg_etale
    (h : ∀ A : Subalgebra R S, A.FG → Algebra.Etale R A) :
    Algebra.IndEtale R S :=
  ⟨{A : Subalgebra R S // A.FG}, inferInstance, inferInstance,
    Subalgebra.fgColimitPresentation R S, fun A ↦ h A.1 A.2⟩

end FGColimitPresentation


