-- Prove2me | Definitions.Def_ProEtale_Algebra_HenselianLocalRing
-- name    : ProEtale_Algebra_HenselianLocalRing
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:49:59.601977+00:00
-- url     : https://prove2.me/theorems/966f67e6-ff5b-56bb-ad88-d8e6c8e37414
-- title:
--   A weakly étale local homomorphism out of a strictly henselian local ring is an isomorphism
-- statement:
--   Let $R \to S$ be a local homomorphism of local rings, with $R$ henselian with separably closed residue field (i.e. strictly henselian), and $S$ weakly étale over $R$. For a prime $\mathfrak p \subset R$ write $\kappa(\mathfrak p)$ for its residue field and $\kappa(\mathfrak p)\otimes_R S$ for the fibre ring. The file proves:
--
--   1. **No idempotents after algebraic field extensions.** For every prime $\mathfrak p$ of $R$ and every field $L$ that is an algebraic extension of $\kappa(\mathfrak p)$ (with compatible $R$-algebra structure), every idempotent $e \in L \otimes_R S$ satisfies $e = 0$ or $e = 1$.
--   2. **Fibres are points.** For every prime $\mathfrak p$ of $R$, the fibre ring $\kappa(\mathfrak p)\otimes_R S$ has at most one prime ideal.
--   3. **Trivial residue field extensions.** For every prime $\mathfrak q$ of $\kappa(\mathfrak p)\otimes_R S$, the map $\kappa(\mathfrak p) \to \kappa(\mathfrak q)$ is bijective.
--   4. **Main result.** The structure map is bijective:
--   $$R \xrightarrow{\ \sim\ } S.$$
--   This is stated both with hypotheses "henselian local and separably closed residue field" and with Mathlib's class of strictly henselian local rings.
--
--   The main result is used to show that strictly henselian local rings admit no nontrivial weakly étale local extensions, which underlies the description of stalks of the pro-étale site and of w-strictly local rings.
--
--   **Formalization Note** All rings are in one universe `u`; `S` is assumed `IsLocalRing` and `algebraMap R S` an `IsLocalHom`. Main declarations: `Algebra.WeaklyEtale.eq_of_isIdempotentElem`, `Algebra.WeaklyEtale.subsingleton_primeSpectrum_fiber`, `Algebra.WeaklyEtale.bijective_algebraMap_residueField_fiber`, `Algebra.WeaklyEtale.bijective_of_henselianLocalRing`, `Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing`. The fibre ring is Mathlib's `p.Fiber S`. In items 2–4 the generic algebra structure on residue fields is used instead of the one induced by local homomorphisms (an instance is locally disabled) so that it matches the one in the ind-étale idempotent lemma. A source comment cites Stacks 092W for integral closedness of $R'\otimes_R S$ in its base change, used in the proof of item 1.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 092W. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/HenselianLocalRing.lean (declarations needed by the transplanted proofs, unused ones removed).

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

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe u

variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing S]

open TensorProduct

/- In the declarations below that deal with residue fields of primes of the fibre ring
`κ(p) ⊗[R] S`, we locally disable the functorial algebra structure on residue fields of local
homomorphisms of local rings in favour of the generic one, so that the algebra structure of
`κ(p)` on these residue fields agrees with the one used in
`Algebra.IndEtale.exists_isIdempotentElem_tensorProduct_of_residueField_ne`. -/

namespace Algebra
namespace WeaklyEtale

variable [Algebra R S] [IsLocalHom (algebraMap R S)]

section

variable [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)] [WeaklyEtale R S]

set_option synthInstance.maxHeartbeats 400000 in
-- Instance searches on tensor products with the integral closure of `R` in `L` unfold long
-- chains of subalgebra and tensor product instances and exceed the default heartbeat limits.
set_option maxHeartbeats 1600000 in
-- Elaboration unfolds the same long instance chains as the instance searches.
/-- If `R → S` is a local homomorphism of local rings, `R` is strictly henselian and `S` is
weakly-étale over `R`, then for any algebraic field extension `L` of `κ(p)` the
tensorproduct `L ⊗[R] S` has no nontrivial idempotent elements. -/
lemma eq_of_isIdempotentElem (p : Ideal R) [p.IsPrime] (L : Type u) [Field L]
    [Algebra p.ResidueField L] [Algebra R L] [Algebra.IsAlgebraic p.ResidueField L]
    [IsScalarTower R p.ResidueField L] {e : L ⊗[R] S} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  -- Let `R'` be the integral closure of `R` (equivalently, of `R ⧸ p`) in `L`.
  let R' : Subalgebra R L := integralClosure R L
  haveI : Algebra.IsIntegral R R' := inferInstanceAs (Algebra.IsIntegral R (integralClosure R L))
  haveI : IsDomain R' := inferInstanceAs (IsDomain (integralClosure R L))
  haveI : IsIntegrallyClosedIn R' L :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure R L) L)
  -- `R'` is local with residue field algebraic, hence purely inseparable, over that of `R`.
  haveI hRloc : IsLocalRing R' :=
    IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain (R := R)
  haveI hlochom : IsLocalHom (algebraMap R R') :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R R')).out 0 4).mpr
      (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _))
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R') :=
    Algebra.IsAlgebraic.residueField_of_isIntegral
  -- Hence `R' ⊗[R] S` is a local ring.
  haveI hloc : IsLocalRing (R' ⊗[R] S) :=
    Algebra.isLocalRing_tensorProduct_of_isPurelyInseparable_residueField R R' S
      (Or.inl inferInstance)
  -- `L` is algebraic over `R'`, by clearing denominators via `κ(p) = Frac(R ⧸ p)`.
  letI : Algebra (R ⧸ p) L :=
    ((algebraMap p.ResidueField L).comp (algebraMap (R ⧸ p) p.ResidueField)).toAlgebra
  haveI : IsScalarTower (R ⧸ p) p.ResidueField L := .of_algebraMap_eq' rfl
  have hker : ∀ a ∈ p, algebraMap R R' a = 0 := fun a ha ↦ Subtype.ext <| by
    change algebraMap R L a = 0
    rw [IsScalarTower.algebraMap_apply R p.ResidueField L,
      Ideal.algebraMap_residueField_eq_zero.mpr ha, map_zero]
  letI : Algebra (R ⧸ p) R' := (Ideal.Quotient.lift p (algebraMap R R') hker).toAlgebra
  haveI : IsScalarTower (R ⧸ p) R' L := .of_algebraMap_eq fun a ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change algebraMap p.ResidueField L (algebraMap (R ⧸ p) p.ResidueField
      (Ideal.Quotient.mk p a)) =
      algebraMap R' L (Ideal.Quotient.lift p (algebraMap R R') hker (Ideal.Quotient.mk p a))
    rw [Ideal.Quotient.lift_mk, Ideal.algebraMap_quotient_residueField_mk,
      ← IsScalarTower.algebraMap_apply R p.ResidueField L,
      ← IsScalarTower.algebraMap_apply R R' L]
  have hinj : Function.Injective (algebraMap (R ⧸ p) R') := by
    have h2 : Function.Injective (algebraMap (R ⧸ p) L) := by
      change Function.Injective
        ⇑((algebraMap p.ResidueField L).comp (algebraMap (R ⧸ p) p.ResidueField))
      rw [RingHom.coe_comp]
      exact (RingHom.injective _).comp p.injective_algebraMap_quotient_residueField
    rw [IsScalarTower.algebraMap_eq (R ⧸ p) R' L, RingHom.coe_comp] at h2
    exact h2.of_comp
  haveI : Algebra.IsAlgebraic R' L :=
    ⟨fun x ↦ ((IsFractionRing.isAlgebraic_iff (R ⧸ p) p.ResidueField L).mpr
      (Algebra.IsAlgebraic.isAlgebraic x)).extendScalars hinj⟩
  haveI : FaithfulSMul R' L :=
    (faithfulSMul_iff_algebraMap_injective R' L).mpr Subtype.val_injective
  -- By Stacks 092W, `R' ⊗[R] S` is integrally closed in `(R' ⊗[R] S) ⊗[R'] L ≅ L ⊗[R] S`.
  haveI hic : IsIntegrallyClosedIn (R' ⊗[R] S) ((R' ⊗[R] S) ⊗[R'] L) :=
    Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct R' (R' ⊗[R] S) L
  let ψ : ((R' ⊗[R] S) ⊗[R'] L) ≃ₐ[R'] (L ⊗[R] S) :=
    (Algebra.TensorProduct.comm R' (R' ⊗[R] S) L).trans
      (Algebra.TensorProduct.cancelBaseChange R R' R' L S)
  -- The idempotent `e` is integral over `R' ⊗[R] S`, so it comes from this local ring.
  have he' : IsIdempotentElem (ψ.symm e) := he.map ψ.symm
  obtain ⟨b, hb⟩ : ∃ b, algebraMap (R' ⊗[R] S) ((R' ⊗[R] S) ⊗[R'] L) b = ψ.symm e := by
    rw [← IsIntegrallyClosedIn.isIntegral_iff]
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X]
      norm_num
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, pow_two, he',
        sub_self]
  have hbinj : Function.Injective (algebraMap (R' ⊗[R] S) ((R' ⊗[R] S) ⊗[R'] L)) :=
    hic.algebraMap_injective
  have hbidem : IsIdempotentElem b := by
    apply hbinj
    rw [map_mul, hb]
    exact he'
  -- A local ring has no nontrivial idempotents.
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self b with hu | hu
  · right
    have hb1 : b = 1 := hu.mul_left_cancel (by rw [mul_one]; exact hbidem)
    rw [← ψ.apply_symm_apply e, ← hb, hb1, map_one, map_one]
  · left
    have hb0 : b = 0 :=
      hu.mul_right_cancel (by rw [zero_mul, mul_sub, mul_one, hbidem, sub_self])
    rw [← ψ.apply_symm_apply e, ← hb, hb0, map_zero, map_zero]

attribute [-instance] IsLocalRing.ResidueField.instAlgebra in
/-- If `R → S` is a local homomorphism of local rings, `R` is henselian with separably
closed residue field and `S` is weakly étale over `R`, the fibre rings of `R → S` have a
single prime. -/
lemma subsingleton_primeSpectrum_fiber (p : Ideal R) [p.IsPrime] :
    Subsingleton (PrimeSpectrum (p.Fiber S)) := by
  have hind : IndEtale p.ResidueField (p.Fiber S) := indEtale_field p.ResidueField (p.Fiber S)
  refine ⟨fun q₁ q₂ ↦ ?_⟩
  by_contra hne
  obtain ⟨e, he, h0, h1⟩ := IndEtale.exists_isIdempotentElem_of_two_primes
    (K := p.ResidueField) (q₁ := q₁.asIdeal) (q₂ := q₂.asIdeal)
    fun h ↦ hne (PrimeSpectrum.ext h)
  rcases eq_of_isIdempotentElem p p.ResidueField he with h' | h'
  · exact h0 h'
  · exact h1 h'

set_option synthInstance.maxHeartbeats 400000 in
-- Instance searches on tensor products with residue fields of primes of the fibre ring
-- unfold long quotient/localization chains and exceed the default heartbeat limits.
set_option maxHeartbeats 1600000 in
-- Elaboration unfolds the same long quotient/localization chains as the instance searches.
attribute [-instance] IsLocalRing.ResidueField.instAlgebra in
/-- If `R → S` is a local homomorphism of local rings, `R` is henselian with separably
closed residue field and `S` is weakly étale over `R`, the residue field extensions of the
fibre rings of `R → S` are trivial. -/
lemma bijective_algebraMap_residueField_fiber (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) [q.IsPrime] :
    Function.Bijective (algebraMap p.ResidueField q.ResidueField) := by
  have hind : IndEtale p.ResidueField (p.Fiber S) := indEtale_field p.ResidueField (p.Fiber S)
  by_contra h
  obtain ⟨e, he, h0, h1⟩ := IndEtale.exists_isIdempotentElem_tensorProduct_of_residueField_ne q h
  have habs : Ring.AbsolutelyFlat (p.Fiber S) :=
    .of_flat_lmul' p.ResidueField (p.Fiber S) (flat_lmul' p.ResidueField (p.Fiber S))
  have htfae : Ring.AbsolutelyFlat (p.Fiber S) ↔
      IsReduced (p.Fiber S) ∧ ∀ P : Ideal (p.Fiber S), P.IsPrime → P.IsMaximal :=
    (Ring.AbsolutelyFlat.tfae (p.Fiber S)).out 0 1
  have hmax : q.IsMaximal := (htfae.mp habs).2 q inferInstance
  have hsurj : Function.Surjective (algebraMap (p.Fiber S) q.ResidueField) := by
    rw [IsScalarTower.algebraMap_eq (p.Fiber S) (p.Fiber S ⧸ q) q.ResidueField]
    exact (Ideal.bijective_algebraMap_quotient_residueField q).surjective.comp
      Ideal.Quotient.mk_surjective
  have hsep : Algebra.IsSeparable p.ResidueField q.ResidueField := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨b, rfl⟩ := hsurj y
    exact IndEtale.isSeparable_of_algHom_to_isLocalRing p.ResidueField q.ResidueField
      (IsScalarTower.toAlgHom p.ResidueField (p.Fiber S) q.ResidueField) b
  have halg : Algebra.IsAlgebraic p.ResidueField q.ResidueField :=
    Algebra.IsSeparable.isAlgebraic p.ResidueField q.ResidueField
  have htower : IsScalarTower R p.ResidueField q.ResidueField :=
    .of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R (p.Fiber S) q.ResidueField,
        IsScalarTower.algebraMap_apply R p.ResidueField (p.Fiber S),
        ← IsScalarTower.algebraMap_apply p.ResidueField (p.Fiber S) q.ResidueField]
  let φ := Algebra.TensorProduct.cancelBaseChange R p.ResidueField q.ResidueField
    q.ResidueField S
  rcases eq_of_isIdempotentElem p q.ResidueField (he.map φ) with h' | h'
  · exact h0 ((map_eq_zero_iff φ φ.injective).mp h')
  · exact h1 ((map_eq_one_iff φ φ.injective).mp h')

end

attribute [-instance] IsLocalRing.ResidueField.instAlgebra in
/-- If `R → S` is a local homomorphism of local rings, `R` is strictly henselian and `S` is
weakly-étale over `R`, then `R → S` is an isomorphism. -/
lemma bijective_of_henselianLocalRing [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [Algebra.WeaklyEtale R S] :
    Function.Bijective (algebraMap R S) := by
  have hff : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  refine bijective_algebraMap_of_bijective_residueFieldMap
    ⟨fun q₁ q₂ hq ↦ ?_, PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩ ?_
  · -- Injectivity of `Spec S → Spec R`: the fibres of `Spec S → Spec R` have a single point.
    have hsub : Subsingleton
        (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
          {PrimeSpectrum.comap (algebraMap R S) q₁} : Set (PrimeSpectrum S)) :=
      have := subsingleton_primeSpectrum_fiber (S := S)
        (PrimeSpectrum.comap (algebraMap R S) q₁).asIdeal
      (PrimeSpectrum.preimageEquivFiber R S _).subsingleton
    exact congrArg Subtype.val (Subsingleton.elim (h := hsub) ⟨q₁, rfl⟩ ⟨q₂, hq.symm⟩)
  · -- Triviality of the residue field extensions, via the corresponding prime of the fibre.
    intro p hp q hq hlies
    have hQ : PrimeSpectrum.comap (algebraMap R S) ⟨q, hq⟩ = (⟨p, hp⟩ : PrimeSpectrum R) :=
      PrimeSpectrum.ext hlies.over.symm
    set q' : PrimeSpectrum (p.Fiber S) :=
      PrimeSpectrum.preimageEquivFiber R S ⟨p, hp⟩ ⟨⟨q, hq⟩, hQ⟩ with hq'def
    have hcomap : q'.asIdeal.comap
        (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)
          (B := S)).toRingHom = q := by
      have h1 := (PrimeSpectrum.preimageEquivFiber R S ⟨p, hp⟩).symm_apply_apply ⟨⟨q, hq⟩, hQ⟩
      have h2 : PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q'
          = (⟨q, hq⟩ : PrimeSpectrum S) := congrArg Subtype.val h1
      exact congrArg PrimeSpectrum.asIdeal h2
    have hbij := bijective_algebraMap_residueField_fiber (S := S) p q'.asIdeal
    have htri : (Ideal.ResidueField.map q q'.asIdeal
          Algebra.TensorProduct.includeRight.toRingHom hcomap.symm).comp
        (Ideal.ResidueField.map p q (algebraMap R S) hlies.over) =
        algebraMap p.ResidueField q'.asIdeal.ResidueField := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (R ⧸ p))
      rw [← RingHom.cancel_right (Ideal.Quotient.mk_surjective (I := p))]
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply,
        Ideal.algebraMap_quotient_residueField_mk, Ideal.ResidueField.map_algebraMap,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      rw [← IsScalarTower.algebraMap_apply R (p.Fiber S) q'.asIdeal.ResidueField,
        ← IsScalarTower.algebraMap_apply R p.ResidueField q'.asIdeal.ResidueField]
    refine ⟨RingHom.injective _, fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := hbij.surjective (Ideal.ResidueField.map q q'.asIdeal
      Algebra.TensorProduct.includeRight.toRingHom hcomap.symm y)
    refine ⟨x, RingHom.injective (Ideal.ResidueField.map q q'.asIdeal
      Algebra.TensorProduct.includeRight.toRingHom hcomap.symm) ?_⟩
    rw [← hx, ← htri, RingHom.comp_apply]

/-- If `R → S` is a local homomorphism of local rings, `R` is strictly henselian and `S` is
weakly étale over `R`, then `R → S` is an isomorphism. -/
lemma bijective_of_isStrictlyHenselianLocalRing [IsStrictlyHenselianLocalRing R]
    [Algebra.WeaklyEtale R S] :
    Function.Bijective (algebraMap R S) :=
  bijective_of_henselianLocalRing

end WeaklyEtale
end Algebra


