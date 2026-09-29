-- Prove2me | Definitions.Def_AlgebraicCurve_CurveModelConstruction
-- name    : AlgebraicCurve_CurveModelConstruction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/27ce68ef-966f-5384-b645-ac2c6a052982
-- title:
--   Gluing integral-closure charts into a curve model
-- statement:
--   The standing data are a field $K$, an extension field $L$ of $K$ in the same universe and an element $t\in L$; the various sections add that $t\neq 0$, that $K$ has characteristic zero and that $L$ is finite over $K(t)$ and over $K(t^{-1})$. For $S\subseteq L$, `chartRing K S` denotes the integral closure of $K[S]$ in $L$. Two affine charts are formed, $X_0=\mathrm{Spec}$ of `chartRing K {t}` and $X_\infty$ for $\{t^{-1}\}$, together with the overlap chart for $\{t,t^{-1}\}$; the inclusions `incl₀`, `inclInf` present the overlap ring as the localisation of each chart ring away from the element $t$ (`tChart`) respectively $t^{-1}$ (`tInvChart`), so that `f₀` and `fInf` are open immersions. `glued` is the scheme-theoretic pushout of this span, with open immersions `ι₀`, `ιInf` and `ιU = f₀ ≫ ι₀`, and `gluedToBase` is the morphism to $\mathrm{Spec}\,K$ obtained from the two structure morphisms, which agree on the overlap. `gluedFunctionFieldEquiv` is a ring isomorphism from $L$ to the function field of `glued`, got from $L$ as fraction field of the overlap ring and the stalk at the generic point, and it carries $\mathrm{algebraMap}_{K,L}$ to `baseToFunctionField`. `gluedPlaceOfPoint` assigns to a closed point a place of $L/K$: according to which chart contains the point, the corresponding prime is of height one (non-zero primes of a chart ring are maximal, the chart ring not being a field), and `Place.ofHeightOneSpectrum` is applied; this map is proved bijective and the range of the stalk inside $L$ is shown to be the valuation subring of the place. For properness, `pullbackVS` is the valuation subring of elements of $L$ whose image under `gL` lies in the image of $S.R$; with the auxiliary `liftOfRange`, `thetaHom`, `stalkChartEquiv`, `φA` and `gA`, `ValuativeCriterion.Existence` for `gluedToBase` is established. Further instances record that `glued` is integral, compact, locally Noetherian and Jacobson, and that `gluedToBase` is locally of finite type, quasi-compact, quasi-separated and, for transcendental $t$, smooth of relative dimension one.
--
--   **Relation to Mathlib.** The construction is phrased with Mathlib's pushouts of open immersions of schemes, `ValuativeCriterion`, `IsDedekindDomain.HeightOneSpectrum`, `Scheme.functionField` and `Scheme.fromSpecStalk`; `chartRing` (the integral closure of `Algebra.adjoin K S` in `L`), `Place` and the `CurveModel` structure are the project's own notions.
--
--   **Where it is used.** The glued scheme, its function field identification, its place bijection and the valuative criterion supply exactly the components of the project's `CurveModel` structure for a one-variable function field over $K$, which is what the divisor-class-group and Jacobian material for modular curves is stated over.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CurveModelConstruction.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_AlgebraicCurve_CurveModelSmooth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IntermediateField IsDedekindDomain
open Topology TopCat

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)

section Charts

theorem singleton_subset_pair : ({t} : Set L) ⊆ {t, t⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

theorem singleton_inv_subset_pair : ({t⁻¹} : Set L) ⊆ {t, t⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))

abbrev incl₀ : chartRing K ({t} : Set L) →ₐ[K] chartRing K ({t, t⁻¹} : Set L) :=
  chartIncl K (singleton_subset_pair t)

abbrev inclInf : chartRing K ({t⁻¹} : Set L) →ₐ[K] chartRing K ({t, t⁻¹} : Set L) :=
  chartIncl K (singleton_inv_subset_pair t)

def tChart : chartRing K ({t} : Set L) := ⟨t, subset_chartRing K {t} (Set.mem_singleton t)⟩

def tInvChart : chartRing K ({t⁻¹} : Set L) :=
  ⟨t⁻¹, subset_chartRing K {t⁻¹} (Set.mem_singleton t⁻¹)⟩

@[simp] theorem coe_tChart : (tChart K t : L) = t := rfl

@[simp] theorem coe_tInvChart : (tInvChart K t : L) = t⁻¹ := rfl

theorem isUnit_incl₀_tChart (ht : t ≠ 0) : IsUnit (incl₀ K t (tChart K t)) := by
  refine IsUnit.of_mul_eq_one ⟨t⁻¹, subset_chartRing K {t, t⁻¹} (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_tChart]
  exact mul_inv_cancel₀ ht

theorem isUnit_inclInf_tInvChart (ht : t ≠ 0) : IsUnit (inclInf K t (tInvChart K t)) := by
  refine IsUnit.of_mul_eq_one ⟨t, subset_chartRing K {t, t⁻¹} (by simp)⟩ (Subtype.ext ?_)
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_tInvChart]
  exact inv_mul_cancel₀ ht

theorem isLocalization_away_incl₀ (ht : t ≠ 0) :
    letI := (incl₀ K t).toRingHom.toAlgebra
    IsLocalization.Away (tChart K t) (chartRing K ({t, t⁻¹} : Set L)) := by
  letI := (incl₀ K t).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_incl₀_tChart K t ht).pow n
  · intro z
    have hz : (z : L) ∈ chartRing K (insert t⁻¹ ({t} : Set L)) := by
      rw [show insert t⁻¹ ({t} : Set L) = {t, t⁻¹} from Set.pair_comm _ _]
      exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartRing (K := K) (Set.mem_singleton t) ht hz
    refine ⟨(⟨t ^ n * z, hn⟩, ⟨tChart K t ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_tChart]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective K _ h]

theorem isLocalization_away_inclInf (ht : t ≠ 0) :
    letI := (inclInf K t).toRingHom.toAlgebra
    IsLocalization.Away (tInvChart K t) (chartRing K ({t, t⁻¹} : Set L)) := by
  letI := (inclInf K t).toRingHom.toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [RingHom.algebraMap_toAlgebra, map_pow]
    exact (isUnit_inclInf_tInvChart K t ht).pow n
  · intro z
    have hz : (z : L) ∈ chartRing K (insert t⁻¹⁻¹ ({t⁻¹} : Set L)) := by
      rw [inv_inv]
      exact z.2
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartRing (K := K) (Set.mem_singleton t⁻¹)
      (inv_ne_zero ht) hz
    refine ⟨(⟨t⁻¹ ^ n * z, hn⟩, ⟨tInvChart K t ^ n, n, rfl⟩), Subtype.ext ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_chartIncl, coe_tInvChart]
    exact mul_comm _ _
  · intro x y h
    refine ⟨1, ?_⟩
    rw [RingHom.algebraMap_toAlgebra] at h
    rw [chartIncl_injective K _ h]

abbrev X₀ : Scheme.{u} := Spec (CommRingCat.of (chartRing K ({t} : Set L)))

abbrev XInf : Scheme.{u} := Spec (CommRingCat.of (chartRing K ({t⁻¹} : Set L)))

abbrev XOverlap : Scheme.{u} := Spec (CommRingCat.of (chartRing K ({t, t⁻¹} : Set L)))

abbrev f₀ : XOverlap K t ⟶ X₀ K t := Spec.map (CommRingCat.ofHom (incl₀ K t).toRingHom)

abbrev fInf : XOverlap K t ⟶ XInf K t := Spec.map (CommRingCat.ofHom (inclInf K t).toRingHom)

variable [Fact (t ≠ 0)]

instance isOpenImmersion_f₀ : IsOpenImmersion (f₀ K t) := by
  letI := (incl₀ K t).toRingHom.toAlgebra
  haveI := isLocalization_away_incl₀ K t (Fact.out)
  exact IsOpenImmersion.of_isLocalization (tChart K t)

instance isOpenImmersion_fInf : IsOpenImmersion (fInf K t) := by
  letI := (inclInf K t).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf K t (Fact.out)
  exact IsOpenImmersion.of_isLocalization (tInvChart K t)

end Charts

section Glue

variable [Fact (t ≠ 0)]

def glued : Scheme.{u} := pushout (f₀ K t) (fInf K t)

def ι₀ : X₀ K t ⟶ glued K t := pushout.inl (f₀ K t) (fInf K t)

def ιInf : XInf K t ⟶ glued K t := pushout.inr (f₀ K t) (fInf K t)

@[reassoc]
theorem glue_condition : f₀ K t ≫ ι₀ K t = fInf K t ≫ ιInf K t := pushout.condition

instance isOpenImmersion_ι₀ : IsOpenImmersion (ι₀ K t) :=
  (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).map_prop WalkingSpan.left

instance isOpenImmersion_ιInf : IsOpenImmersion (ιInf K t) :=
  (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).map_prop WalkingSpan.right

omit [Fact (t ≠ 0)] in

theorem f₀_toBase_eq_fInf_toBase :
    f₀ K t ≫ Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t} : Set L)))) =
      fInf K t ≫ Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t⁻¹} : Set L)))) := by

  have h : (incl₀ K t).toRingHom.comp (algebraMap K (chartRing K ({t} : Set L))) =
      (inclInf K t).toRingHom.comp (algebraMap K (chartRing K ({t⁻¹} : Set L))) :=
    RingHom.ext fun a => ((incl₀ K t).commutes a).trans ((inclInf K t).commutes a).symm
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

def gluedToBase : glued K t ⟶ Spec (CommRingCat.of K) :=
  pushout.desc (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t} : Set L)))))
    (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t⁻¹} : Set L)))))
    (f₀_toBase_eq_fInf_toBase K t)

@[reassoc (attr := simp)]
theorem ι₀_gluedToBase : ι₀ K t ≫ gluedToBase K t =
    Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t} : Set L)))) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem ιInf_gluedToBase : ιInf K t ≫ gluedToBase K t =
    Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t⁻¹} : Set L)))) :=
  pushout.inr_desc _ _ _

theorem smoothOfRelativeDimension_one_gluedToBase_of_charts
    (h₀ : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t} : Set L))))))
    (hInf : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t⁻¹} : Set L)))))) :
    SmoothOfRelativeDimension 1 (gluedToBase K t) := by
  have h₀' : SmoothOfRelativeDimension 1 (ι₀ K t ≫ gluedToBase K t) := by
    rwa [ι₀_gluedToBase]
  have hInf' : SmoothOfRelativeDimension 1 (ιInf K t ≫ gluedToBase K t) := by
    rwa [ιInf_gluedToBase]
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))) ?_
  rintro (_ | _ | _)
  ·

    have key : (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).f none ≫
        gluedToBase K t = f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t) := by
      show colimit.ι (span (f₀ K t) (fInf K t)) none ≫ gluedToBase K t = _
      rw [← colimit.w (span (f₀ K t) (fInf K t)) WalkingSpan.Hom.fst]
      erw [Category.assoc]
    erw [key]
    haveI := h₀'
    exact inferInstanceAs
      (SmoothOfRelativeDimension (0 + 1) (f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t)))
  · change SmoothOfRelativeDimension 1 (ι₀ K t ≫ gluedToBase K t)
    exact h₀'
  · change SmoothOfRelativeDimension 1 (ιInf K t ≫ gluedToBase K t)
    exact hInf'

theorem mem_range_ι₀_or_mem_range_ιInf (x : glued K t) :
    x ∈ Set.range (ι₀ K t).base ∨ x ∈ Set.range (ιInf K t).base := by
  obtain ⟨i, y, hy⟩ :=
    (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).exists_eq x
  rcases i with (_ | _ | _)
  · have hw : (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).f none =
        f₀ K t ≫ ι₀ K t :=
      (colimit.w (span (f₀ K t) (fInf K t)) WalkingSpan.Hom.fst).symm
    refine Or.inl ⟨(f₀ K t).base y, ?_⟩
    rw [← hy, hw]
    rfl
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

theorem range_ιInf_inter_range_ι₀_nonempty :
    (Set.range (ιInf K t).base ∩ Set.range (ι₀ K t).base).Nonempty := by
  obtain ⟨z⟩ := (inferInstance : Nonempty (XOverlap K t))
  refine ⟨(f₀ K t ≫ ι₀ K t).base z, ⟨(fInf K t).base z, ?_⟩, ⟨(f₀ K t).base z, rfl⟩⟩
  rw [glue_condition]
  rfl

end Glue

section Qualities

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

instance isIntegral_glued : IsIntegral (glued K t) := by
  let 𝒰 := Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))
  haveI : ∀ i, IsReduced (𝒰.X i) := by
    rintro (_ | _ | _)
    · change IsReduced (XOverlap K t); infer_instance
    · change IsReduced (X₀ K t); infer_instance
    · change IsReduced (XInf K t); infer_instance
  haveI : IsReduced (glued K t) := IsReduced.of_openCover _ 𝒰
  have hA : IsIrreducible (Set.range (ι₀ K t).base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (X₀ K t)).image _
      (ι₀ K t).base.hom.continuous.continuousOn
  have hB : IsIrreducible (Set.range (ιInf K t).base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (XInf K t)).image _
      (ιInf K t).base.hom.continuous.continuousOn
  have hBA : Set.range (ιInf K t).base ⊆ closure (Set.range (ι₀ K t).base) :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hB.isPreirreducible
      (ι₀ K t).isOpenEmbedding.isOpen_range (range_ιInf_inter_range_ι₀_nonempty K t)).trans
      (closure_mono Set.inter_subset_right)
  have huniv : closure (Set.range (ι₀ K t).base) = Set.univ :=
    Set.eq_univ_of_univ_subset fun x _ =>
      (mem_range_ι₀_or_mem_range_ιInf K t x).elim (fun h => subset_closure h) fun h => hBA h
  haveI : IrreducibleSpace (glued K t) := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← huniv]
    exact hA.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem smoothOfRelativeDimension_one_gluedToBase (ht : Transcendental K t) :
    SmoothOfRelativeDimension 1 (gluedToBase K t) :=
  smoothOfRelativeDimension_one_gluedToBase_of_charts K t
    (smoothOfRelativeDimension_one_Spec_chartRing K t ht)
    (smoothOfRelativeDimension_one_Spec_chartRing K t⁻¹ fun h => ht (IsAlgebraic.inv_iff.mp h))

instance isFractionRing_overlap : IsFractionRing (chartRing K ({t, t⁻¹} : Set L)) L :=
  IsFractionRing.of_field (chartRing K ({t, t⁻¹} : Set L)) L fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := chartRing K ({t} : Set L)) z
    exact ⟨⟨a, chartRing_mono K (singleton_subset_pair t) a.2⟩,
      ⟨b, chartRing_mono K (singleton_subset_pair t) b.2⟩, rfl⟩

instance algebra_overlap_functionField :
    Algebra (chartRing K ({t, t⁻¹} : Set L)) (XOverlap K t).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
    (CommRingCat.of (chartRing K ({t, t⁻¹} : Set L)))

instance isFractionRing_overlap_functionField :
    IsFractionRing (chartRing K ({t, t⁻¹} : Set L)) (XOverlap K t).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of (chartRing K ({t, t⁻¹} : Set L)))

def overlapFunctionFieldAlgEquiv :
    L ≃ₐ[chartRing K ({t, t⁻¹} : Set L)] (XOverlap K t).functionField :=
  IsLocalization.algEquiv (nonZeroDivisors (chartRing K ({t, t⁻¹} : Set L))) L _

def ιU : XOverlap K t ⟶ glued K t := f₀ K t ≫ ι₀ K t

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in
theorem ιU_eq : ιU K t = f₀ K t ≫ ι₀ K t := rfl

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in
theorem ιU_eq' : ιU K t = fInf K t ≫ ιInf K t := glue_condition K t

instance isOpenImmersion_ιU : IsOpenImmersion (ιU K t) :=
  inferInstanceAs (IsOpenImmersion (f₀ K t ≫ ι₀ K t))

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem ιU_gluedToBase : ιU K t ≫ gluedToBase K t =
    Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t, t⁻¹} : Set L)))) := by
  have h : (incl₀ K t).toRingHom.comp (algebraMap K (chartRing K ({t} : Set L))) =
      algebraMap K (chartRing K ({t, t⁻¹} : Set L)) :=
    RingHom.ext fun a => (incl₀ K t).commutes a
  rw [ιU_eq, Category.assoc, ι₀_gluedToBase]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem ιU_genericPoint :
    (ιU K t).base (genericPoint (XOverlap K t)) = genericPoint (glued K t) :=
  genericPoint_eq_of_isOpenImmersion (ιU K t)

def gluedFunctionFieldIsoOverlap :
    (glued K t).functionField ≅ (XOverlap K t).functionField :=
  (glued K t).presheaf.stalkCongr (.of_eq (ιU_genericPoint K t).symm) ≪≫
    asIso ((ιU K t).stalkMap (genericPoint (XOverlap K t)))

def gluedFunctionFieldEquiv : L ≃+* (glued K t).functionField :=
  (overlapFunctionFieldAlgEquiv K t).toRingEquiv.trans
    (gluedFunctionFieldIsoOverlap K t).commRingCatIsoToRingEquiv.symm

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem gluedFunctionFieldIsoOverlap_baseToFunctionField (a : K) :
    (gluedFunctionFieldIsoOverlap K t).hom (baseToFunctionField (gluedToBase K t) a) =
      algebraMap (chartRing K ({t, t⁻¹} : Set L)) (XOverlap K t).functionField
        (algebraMap K (chartRing K ({t, t⁻¹} : Set L)) a) := by
  change (ιU K t).stalkMap (genericPoint (XOverlap K t))
      ((glued K t).presheaf.stalkSpecializes
        (Inseparable.of_eq (ιU_genericPoint K t).symm).ge
        ((glued K t).presheaf.germ ⊤ (genericPoint (glued K t)) trivial
          ((gluedToBase K t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)))) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]
  change (XOverlap K t).presheaf.germ ⊤ (genericPoint (XOverlap K t)) trivial
      ((ιU K t ≫ gluedToBase K t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) = _
  rw [ιU_gluedToBase]

  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t, t⁻¹} : Set L))))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of (chartRing K ({t, t⁻¹} : Set L)))).inv
        (algebraMap K (chartRing K ({t, t⁻¹} : Set L)) a) := by
    have := congrArg (fun f : CommRingCat.of K ⟶ Γ(XOverlap K t, ⊤) => f a)
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap K (chartRing K ({t, t⁻¹} : Set L)))))
    exact this.symm
  rw [h1]
  rfl

omit [CharZero K] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem gluedFunctionFieldEquiv_algebraMap (a : K) :
    gluedFunctionFieldEquiv K t (algebraMap K L a) =
      baseToFunctionField (gluedToBase K t) a := by
  change (gluedFunctionFieldIsoOverlap K t).commRingCatIsoToRingEquiv.symm
      (overlapFunctionFieldAlgEquiv K t (algebraMap K L a)) = _
  rw [RingEquiv.symm_apply_eq]
  change _ = (gluedFunctionFieldIsoOverlap K t).hom (baseToFunctionField (gluedToBase K t) a)
  rw [gluedFunctionFieldIsoOverlap_baseToFunctionField,
    IsScalarTower.algebraMap_apply K (chartRing K ({t, t⁻¹} : Set L)) L a, AlgEquiv.commutes]

end Qualities

instance isIntegral_adjoin_chartRing (S : Set L) :
    Algebra.IsIntegral (Algebra.adjoin K S) (chartRing K S) :=
  IsIntegralClosure.isIntegral_algebra (Algebra.adjoin K S) (A := chartRing K S) L

theorem not_isField_chartRing (ht : Transcendental K t) :
    ¬ IsField (chartRing K ({t} : Set L)) := fun hF =>
  Polynomial.not_isField (R := K)
    (MulEquiv.isField
      (isField_of_isIntegral_of_isField
        (R := Algebra.adjoin K ({t} : Set L)) (S := chartRing K ({t} : Set L))
        (fun _ _ h => Subtype.ext (congrArg Subtype.val h :)) hF)
      (Polynomial.algEquivOfTranscendental K t ht).toMulEquiv)

theorem isMaximal_iff_ne_bot (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ L] [CharZero K]
    (𝔭 : Ideal (chartRing K ({t} : Set L))) [𝔭.IsPrime] : 𝔭.IsMaximal ↔ 𝔭 ≠ ⊥ :=
  ⟨fun h => Ring.ne_bot_of_isMaximal_of_not_isField h (not_isField_chartRing K t ht),
   fun h => Ideal.IsPrime.isMaximal inferInstance h⟩

section FiniteType

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

instance locallyOfFiniteType_gluedToBase : LocallyOfFiniteType (gluedToBase K t) := by
  have h₀' : LocallyOfFiniteType (ι₀ K t ≫ gluedToBase K t) := by
    rw [ι₀_gluedToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hInf' : LocallyOfFiniteType (ιInf K t ≫ gluedToBase K t) := by
    rw [ιInf_gluedToBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))) ?_
  rintro (_ | _ | _)
  · have key : (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t))).f none ≫
        gluedToBase K t = f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t) := by
      show colimit.ι (span (f₀ K t) (fInf K t)) none ≫ gluedToBase K t = _
      rw [← colimit.w (span (f₀ K t) (fInf K t)) WalkingSpan.Hom.fst]
      erw [Category.assoc]
    erw [key]
    haveI := h₀'
    exact inferInstanceAs (LocallyOfFiniteType (f₀ K t ≫ (ι₀ K t ≫ gluedToBase K t)))
  · change LocallyOfFiniteType (ι₀ K t ≫ gluedToBase K t)
    exact h₀'
  · change LocallyOfFiniteType (ιInf K t ≫ gluedToBase K t)
    exact hInf'

instance jacobsonSpace_glued : JacobsonSpace (glued K t) :=
  LocallyOfFiniteType.jacobsonSpace (gluedToBase K t)

theorem ι₀_mem_closedPoints_iff (x : X₀ K t) :
    (ι₀ K t).base x ∈ closedPoints (glued K t) ↔ x ∈ closedPoints (X₀ K t) := by
  rw [← Set.mem_preimage, (ι₀ K t).isOpenEmbedding.preimage_closedPoints]

theorem ιInf_mem_closedPoints_iff (x : XInf K t) :
    (ιInf K t).base x ∈ closedPoints (glued K t) ↔ x ∈ closedPoints (XInf K t) := by
  rw [← Set.mem_preimage, (ιInf K t).isOpenEmbedding.preimage_closedPoints]

end FiniteType

section Overlap

variable [Fact (t ≠ 0)]

theorem ι₀_eq_ιInf_iff (x₀ : X₀ K t) (xi : XInf K t) :
    (ι₀ K t).base x₀ = (ιInf K t).base xi ↔
      ∃ u : XOverlap K t, (f₀ K t).base u = x₀ ∧ (fInf K t).base u = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, u, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (f₀ K t) (fInf K t))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · cases fi
      cases fj
      exact ⟨u, h₁, h₂⟩
    · cases fj
    · cases fi
  · rintro ⟨u, rfl, rfl⟩
    change (f₀ K t ≫ ι₀ K t).base u = (fInf K t ≫ ιInf K t).base u
    rw [glue_condition]

theorem range_fInf : Set.range (fInf K t).base =
    ((PrimeSpectrum.basicOpen (tInvChart K t) :
        TopologicalSpace.Opens (PrimeSpectrum (chartRing K ({t⁻¹} : Set L)))) :
      Set (PrimeSpectrum (chartRing K ({t⁻¹} : Set L)))) := by
  letI := (inclInf K t).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf K t (Fact.out : t ≠ 0)
  exact PrimeSpectrum.localization_away_comap_range (chartRing K ({t, t⁻¹} : Set L))
    (tInvChart K t)

theorem range_f₀ : Set.range (f₀ K t).base =
    ((PrimeSpectrum.basicOpen (tChart K t) :
        TopologicalSpace.Opens (PrimeSpectrum (chartRing K ({t} : Set L)))) :
      Set (PrimeSpectrum (chartRing K ({t} : Set L)))) := by
  letI := (incl₀ K t).toRingHom.toAlgebra
  haveI := isLocalization_away_incl₀ K t (Fact.out : t ≠ 0)
  exact PrimeSpectrum.localization_away_comap_range (chartRing K ({t, t⁻¹} : Set L))
    (tChart K t)

theorem ιInf_mem_range_ι₀_iff (xi : XInf K t) :
    (ιInf K t).base xi ∈ Set.range (ι₀ K t).base ↔ tInvChart K t ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨u, -, hu⟩ := (ι₀_eq_ιInf_iff K t x₀ xi).mp h
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(f₀ K t).base u, (ι₀_eq_ιInf_iff K t _ _).mpr ⟨u, rfl, rfl⟩⟩

theorem ι₀_mem_range_ιInf_iff (x₀ : X₀ K t) :
    (ι₀ K t).base x₀ ∈ Set.range (ιInf K t).base ↔ tChart K t ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_f₀, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨u, hu, -⟩ := (ι₀_eq_ιInf_iff K t x₀ xi).mp h.symm
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(fInf K t).base u, ((ι₀_eq_ιInf_iff K t _ _).mpr ⟨u, rfl, rfl⟩).symm⟩

end Overlap

section StalkRange

variable [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]

variable (A : Subalgebra K L) (i : A →ₐ[K] chartRing K ({t, t⁻¹} : Set L))
  (hi : ∀ a : A, (i a : L) = a)
  (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom i.toRingHom))]
  (comm : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ιA = ιU K t)

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in

scoped instance stalkAlgebra_spec (p : Spec (CommRingCat.of A)) :
    Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
  StructureSheaf.stalkAlgebra (↥A) p

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in

scoped instance isLocalization_stalk_spec (p : Spec (CommRingCat.of A)) :
    IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk p) p.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk (↥A) p

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in

theorem specMap_genericPoint :
    (Spec.map (CommRingCat.ofHom i.toRingHom)).base (genericPoint (XOverlap K t)) =
      genericPoint (Spec (CommRingCat.of A)) :=
  genericPoint_eq_of_isOpenImmersion _

def thetaHom (p : Spec (CommRingCat.of A)) : (Spec (CommRingCat.of A)).presheaf.stalk p →+* L :=
  ((overlapFunctionFieldAlgEquiv K t).symm : (XOverlap K t).functionField →+* L).comp
    (((Spec.map (CommRingCat.ofHom i.toRingHom)).stalkMap (genericPoint (XOverlap K t))).hom.comp
      ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes
        (by rw [specMap_genericPoint]; exact genericPoint_specializes p)).hom)

include hi in
omit [Fact (t ≠ 0)] in

theorem thetaHom_toStalk (p : Spec (CommRingCat.of A)) (a : A) :
    thetaHom K t A i p (StructureSheaf.toStalk A p a) = a := by
  change (overlapFunctionFieldAlgEquiv K t).symm
      (((Spec.map (CommRingCat.ofHom i.toRingHom)).stalkMap (genericPoint (XOverlap K t)))
        (((Spec (CommRingCat.of A)).presheaf.stalkSpecializes _)
          (StructureSheaf.toStalk A p a))) = _
  erw [StructureSheaf.toStalk_stalkSpecializes_apply]
  erw [AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom i.toRingHom)
    (genericPoint (XOverlap K t)) a]
  change (overlapFunctionFieldAlgEquiv K t).symm
      (algebraMap (chartRing K ({t, t⁻¹} : Set L)) (XOverlap K t).functionField (i a)) = _
  rw [AlgEquiv.commutes]
  exact hi a

include hi in
omit [Fact (t ≠ 0)] in

theorem thetaHom_mk' (p : Spec (CommRingCat.of A)) (a : A) (b : p.asIdeal.primeCompl) :
    thetaHom K t A i p (IsLocalization.mk' _ a b) = (a : L) * ((b : A) : L)⁻¹ := by
  have hb : ((b : A) : L) ≠ 0 := by
    intro h
    have : (b : A) = 0 := Subtype.ext h
    exact b.2 (this ▸ p.asIdeal.zero_mem)
  rw [eq_mul_inv_iff_mul_eq₀ hb]
  have := congrArg (thetaHom K t A i p)
    (IsLocalization.mk'_spec ((Spec (CommRingCat.of A)).presheaf.stalk p) a b)
  rw [map_mul] at this
  rw [← thetaHom_toStalk K t A i hi p a, ← thetaHom_toStalk K t A i hi p b]
  exact this

include hi in
omit [Fact (t ≠ 0)] in

theorem range_thetaHom (p : Spec (CommRingCat.of A)) :
    Set.range (thetaHom K t A i p) =
      {y : L | ∃ a b : A, b ∉ p.asIdeal ∧ y = (a : L) * ((b : A) : L)⁻¹} := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl s
    exact ⟨a, b, b.2, thetaHom_mk' K t A i hi p a b⟩
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨IsLocalization.mk' _ a ⟨b, hb⟩, thetaHom_mk' K t A i hi p a ⟨b, hb⟩⟩

include comm in
omit [IsOpenImmersion ιA] in

theorem ffEquiv_symm_algebraMap_stalk (p : Spec (CommRingCat.of A))
    (s : (glued K t).presheaf.stalk (ιA.base p)) :
    (gluedFunctionFieldEquiv K t).symm
        (algebraMap ((glued K t).presheaf.stalk (ιA.base p)) (glued K t).functionField s) =
      thetaHom K t A i p ((ιA.stalkMap p) s) := by

  change (overlapFunctionFieldAlgEquiv K t).symm
      (((ιU K t).stalkMap (genericPoint (XOverlap K t)))
        (((glued K t).presheaf.stalkSpecializes
            (Inseparable.of_eq (ιU_genericPoint K t).symm).ge)
          (((glued K t).presheaf.stalkSpecializes _) s))) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply]

  rw [Scheme.Hom.stalkMap_congr_hom _ _ comm.symm]
  rw [CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_comp_apply, Scheme.Hom.stalkMap_comp]
  change (overlapFunctionFieldAlgEquiv K t).symm
      (((Spec.map (CommRingCat.ofHom i.toRingHom)).stalkMap (genericPoint (XOverlap K t)))
        ((ιA.stalkMap
            ((Spec.map (CommRingCat.ofHom i.toRingHom)).base (genericPoint (XOverlap K t))))
          (((glued K t).presheaf.stalkSpecializes _) s))) = _

  have hsp : (Spec.map (CommRingCat.ofHom i.toRingHom)).base (genericPoint (XOverlap K t)) ⤳ p := by
    rw [specMap_genericPoint]; exact genericPoint_specializes p
  erw [Scheme.Hom.stalkSpecializes_stalkMap_apply ιA _ _ hsp]
  rfl

include hi comm in

theorem range_ffEquiv_symm_comp_algebraMap_stalk (p : Spec (CommRingCat.of A)) :
    (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
        (algebraMap ((glued K t).presheaf.stalk (ιA.base p)) (glued K t).functionField)).range =
      {y : L | ∃ a b : A, b ∉ p.asIdeal ∧ y = (a : L) * ((b : A) : L)⁻¹} := by
  rw [← range_thetaHom K t A i hi p]
  ext y
  simp only [RingHom.coe_range, Set.mem_range, RingHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, (ffEquiv_symm_algebraMap_stalk K t A i ιA comm p s).symm⟩
  · rintro ⟨s', rfl⟩
    obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (ιA.stalkMap p)).2 s'
    exact ⟨s, ffEquiv_symm_algebraMap_stalk K t A i ιA comm p s⟩

end StalkRange

section PlaceMap

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

omit [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in
theorem transcendental_inv (ht : Transcendental K t) : Transcendental K t⁻¹ :=
  fun h => ht (IsAlgebraic.inv_iff.mp h)

def primeOfι₀ (ht : Transcendental K t) (x₀ : X₀ K t)
    (hx : (ι₀ K t).base x₀ ∈ closedPoints (glued K t)) :
    HeightOneSpectrum (chartRing K ({t} : Set L)) :=
  ⟨x₀.asIdeal, x₀.isPrime,
    (isMaximal_iff_ne_bot K t ht _).mp ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x₀).mp
      ((ι₀_mem_closedPoints_iff K t x₀).mp hx))⟩

def primeOfιInf (ht : Transcendental K t) (xi : XInf K t)
    (hx : (ιInf K t).base xi ∈ closedPoints (glued K t)) :
    HeightOneSpectrum (chartRing K ({t⁻¹} : Set L)) :=
  ⟨xi.asIdeal, xi.isPrime,
    (isMaximal_iff_ne_bot K t⁻¹ (transcendental_inv K t ht) _).mp
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal xi).mp
        ((ιInf_mem_closedPoints_iff K t xi).mp hx))⟩

@[simp] theorem primeOfι₀_asIdeal (ht : Transcendental K t) (x₀ : X₀ K t) (hx) :
    (primeOfι₀ K t ht x₀ hx).asIdeal = x₀.asIdeal := rfl

@[simp] theorem primeOfιInf_asIdeal (ht : Transcendental K t) (xi : XInf K t) (hx) :
    (primeOfιInf K t ht xi hx).asIdeal = xi.asIdeal := rfl

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in
theorem mem_range_ιInf_of_not_mem_range_ι₀ {x : glued K t}
    (h : x ∉ Set.range (ι₀ K t).base) : x ∈ Set.range (ιInf K t).base :=
  (mem_range_ι₀_or_mem_range_ιInf K t x).resolve_left h

open scoped Classical in

def gluedPlaceOfPoint (ht : Transcendental K t) (x : closedPoints (glued K t)) : Place K L :=
  if h : x.1 ∈ Set.range (ι₀ K t).base then
    Place.ofHeightOneSpectrum (K := K)
      (primeOfι₀ K t ht (Classical.choose h) (by rw [Classical.choose_spec h]; exact x.2))
  else
    Place.ofHeightOneSpectrum (K := K)
      (primeOfιInf K t ht (Classical.choose (mem_range_ιInf_of_not_mem_range_ι₀ K t h))
        (by rw [Classical.choose_spec (mem_range_ιInf_of_not_mem_range_ι₀ K t h)]; exact x.2))

theorem gluedPlaceOfPoint_ι₀ (ht : Transcendental K t) (x₀ : X₀ K t)
    (hx : (ι₀ K t).base x₀ ∈ closedPoints (glued K t)) :
    gluedPlaceOfPoint K t ht ⟨(ι₀ K t).base x₀, hx⟩ =
      Place.ofHeightOneSpectrum (K := K) (primeOfι₀ K t ht x₀ hx) := by
  have h : (ι₀ K t).base x₀ ∈ Set.range (ι₀ K t).base := ⟨x₀, rfl⟩
  have hc : Classical.choose h = x₀ :=
    (ι₀ K t).isOpenEmbedding.injective (Classical.choose_spec h)
  have key : ∀ (y : X₀ K t) (hy) (_ : y = x₀), primeOfι₀ K t ht y hy = primeOfι₀ K t ht x₀ hx := by
    rintro y hy rfl; rfl
  unfold gluedPlaceOfPoint
  rw [dif_pos h, key _ _ hc]

theorem gluedPlaceOfPoint_of_not_mem (ht : Transcendental K t) (x : closedPoints (glued K t))
    (h : x.1 ∉ Set.range (ι₀ K t).base) (xi : XInf K t) (hxi : (ιInf K t).base xi = x.1) :
    gluedPlaceOfPoint K t ht x =
      Place.ofHeightOneSpectrum (K := K) (primeOfιInf K t ht xi (by rw [hxi]; exact x.2)) := by
  have hc : Classical.choose (mem_range_ιInf_of_not_mem_range_ι₀ K t h) = xi :=
    (ιInf K t).isOpenEmbedding.injective
      ((Classical.choose_spec (mem_range_ιInf_of_not_mem_range_ι₀ K t h)).trans hxi.symm)
  have key : ∀ (y : XInf K t) (hy) (_ : y = xi),
      primeOfιInf K t ht y hy = primeOfιInf K t ht xi (by rw [hxi]; exact x.2) := by
    rintro y hy rfl; rfl
  unfold gluedPlaceOfPoint
  rw [dif_neg h, key _ _ hc]

theorem t_mem_of_ι₀ (ht : Transcendental K t) (x₀ : X₀ K t) (hx) :
    t ∈ (Place.ofHeightOneSpectrum (K := K) (primeOfι₀ K t ht x₀ hx)).toValuationSubring :=
  mem_ofHeightOneSpectrum K t _

theorem t_not_mem_of_ιInf (ht : Transcendental K t) (xi : XInf K t) (hx)
    (hxi : tInvChart K t ∈ xi.asIdeal) :
    t ∉ (Place.ofHeightOneSpectrum (K := K) (primeOfιInf K t ht xi hx)).toValuationSubring := by
  intro htmem
  set 𝔮 := primeOfιInf K t ht xi hx
  have h1 : 𝔮.valuation L ((tInvChart K t : chartRing K ({t⁻¹} : Set L)) : L) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) 𝔮 (tInvChart K t)).mpr hxi
  have h2 : 𝔮.valuation L t ≤ 1 := by
    rwa [Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
      at htmem
  have h3 : 𝔮.valuation L (t * t⁻¹) < 1 := by
    rw [map_mul]
    calc 𝔮.valuation L t * 𝔮.valuation L t⁻¹
        ≤ 1 * 𝔮.valuation L t⁻¹ := mul_le_mul' h2 le_rfl
      _ = 𝔮.valuation L ((tInvChart K t : chartRing K ({t⁻¹} : Set L)) : L) := by
          rw [one_mul, coe_tInvChart]
      _ < 1 := h1
  rw [mul_inv_cancel₀ (Fact.out : t ≠ 0), map_one] at h3
  exact lt_irrefl _ h3

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem tInvChart_mem_of_not_mem_range (xi : XInf K t)
    (h : (ιInf K t).base xi ∉ Set.range (ι₀ K t).base) : tInvChart K t ∈ xi.asIdeal := by
  by_contra hne
  exact h ((ιInf_mem_range_ι₀_iff K t xi).mpr hne)

theorem gluedPlaceOfPoint_injective (ht : Transcendental K t) :
    Function.Injective (gluedPlaceOfPoint K t ht) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  by_cases h₁ : x ∈ Set.range (ι₀ K t).base <;> by_cases h₂ : y ∈ Set.range (ι₀ K t).base
  · obtain ⟨x₀, rfl⟩ := h₁
    obtain ⟨y₀, rfl⟩ := h₂
    rw [gluedPlaceOfPoint_ι₀, gluedPlaceOfPoint_ι₀] at hxy
    have h' := ofHeightOneSpectrum_injective K t hxy
    have hxy' : x₀ = y₀ := PrimeSpectrum.ext (congrArg HeightOneSpectrum.asIdeal h')
    subst hxy'
    rfl
  · exfalso
    obtain ⟨x₀, rfl⟩ := h₁
    obtain ⟨yi, hyi⟩ := mem_range_ιInf_of_not_mem_range_ι₀ K t h₂
    rw [gluedPlaceOfPoint_ι₀, gluedPlaceOfPoint_of_not_mem K t ht ⟨y, hy⟩ h₂ yi hyi] at hxy
    refine t_not_mem_of_ιInf K t ht yi _ (tInvChart_mem_of_not_mem_range K t yi ?_)
      (hxy ▸ t_mem_of_ι₀ K t ht x₀ hx)
    rwa [hyi]
  · exfalso
    obtain ⟨y₀, rfl⟩ := h₂
    obtain ⟨xi, hxi⟩ := mem_range_ιInf_of_not_mem_range_ι₀ K t h₁
    rw [gluedPlaceOfPoint_ι₀, gluedPlaceOfPoint_of_not_mem K t ht ⟨x, hx⟩ h₁ xi hxi] at hxy
    refine t_not_mem_of_ιInf K t ht xi _ (tInvChart_mem_of_not_mem_range K t xi ?_)
      (hxy ▸ t_mem_of_ι₀ K t ht y₀ hy)
    rwa [hxi]
  · obtain ⟨xi, hxi⟩ := mem_range_ιInf_of_not_mem_range_ι₀ K t h₁
    obtain ⟨yi, hyi⟩ := mem_range_ιInf_of_not_mem_range_ι₀ K t h₂
    rw [gluedPlaceOfPoint_of_not_mem K t ht ⟨x, hx⟩ h₁ xi hxi,
      gluedPlaceOfPoint_of_not_mem K t ht ⟨y, hy⟩ h₂ yi hyi] at hxy
    have h' := ofHeightOneSpectrum_injective K t⁻¹ hxy
    have hxy' : xi = yi := PrimeSpectrum.ext (congrArg HeightOneSpectrum.asIdeal h')
    subst hxy'
    exact Subtype.ext (hxi.symm.trans hyi)

theorem gluedPlaceOfPoint_surjective (ht : Transcendental K t) :
    Function.Surjective (gluedPlaceOfPoint K t ht) := by
  intro v
  by_cases hv : t ∈ v.toValuationSubring
  · obtain ⟨𝔭, h𝔭⟩ := exists_ofHeightOneSpectrum_eq K t v hv
    let x₀ : X₀ K t := ⟨𝔭.asIdeal, 𝔭.isPrime⟩
    have hx₀ : x₀ ∈ closedPoints (X₀ K t) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal x₀).mpr 𝔭.isMaximal
    refine ⟨⟨(ι₀ K t).base x₀, (ι₀_mem_closedPoints_iff K t x₀).mpr hx₀⟩, ?_⟩
    rw [gluedPlaceOfPoint_ι₀, ← h𝔭]
    rfl
  · have hv' : t⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem t).resolve_left hv
    obtain ⟨𝔮, h𝔮⟩ := exists_ofHeightOneSpectrum_eq K t⁻¹ v hv'
    let xi : XInf K t := ⟨𝔮.asIdeal, 𝔮.isPrime⟩
    have hxi : xi ∈ closedPoints (XInf K t) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal xi).mpr 𝔮.isMaximal
    have hmem : tInvChart K t ∈ xi.asIdeal := by
      change tInvChart K t ∈ 𝔮.asIdeal
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
      have hvt : ¬ 𝔮.valuation L t ≤ 1 := by
        rwa [← Valuation.mem_valuationSubring_iff,
          ← Place.ofHeightOneSpectrum_toValuationSubring (K := K) 𝔮, h𝔮]
      have hprod : 𝔮.valuation L ((tInvChart K t : chartRing K ({t⁻¹} : Set L)) : L) *
          𝔮.valuation L t = 1 := by
        rw [← map_mul, coe_tInvChart, inv_mul_cancel₀ (Fact.out : t ≠ 0), map_one]
      by_contra hge
      have hge' : 1 ≤ 𝔮.valuation L ((tInvChart K t : chartRing K ({t⁻¹} : Set L)) : L) :=
        not_lt.mp hge
      have : (1 : WithZero (Multiplicative ℤ)) < 1 :=
        calc (1 : WithZero (Multiplicative ℤ)) < 𝔮.valuation L t := not_le.mp hvt
          _ = 1 * 𝔮.valuation L t := (one_mul _).symm
          _ ≤ 𝔮.valuation L ((tInvChart K t : chartRing K ({t⁻¹} : Set L)) : L) *
                𝔮.valuation L t := mul_le_mul' hge' le_rfl
          _ = 1 := hprod
      exact lt_irrefl _ this
    have hnot : (ιInf K t).base xi ∉ Set.range (ι₀ K t).base :=
      fun hr => ((ιInf_mem_range_ι₀_iff K t xi).mp hr) hmem
    refine ⟨⟨(ιInf K t).base xi, (ιInf_mem_closedPoints_iff K t xi).mpr hxi⟩, ?_⟩
    rw [gluedPlaceOfPoint_of_not_mem K t ht _ hnot xi rfl, ← h𝔮]
    rfl

theorem gluedPlaceOfPoint_bijective (ht : Transcendental K t) :
    Function.Bijective (gluedPlaceOfPoint K t ht) :=
  ⟨gluedPlaceOfPoint_injective K t ht, gluedPlaceOfPoint_surjective K t ht⟩

theorem range_stalk_eq_gluedPlaceOfPoint (ht : Transcendental K t) (x : closedPoints (glued K t)) :
    (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
        (algebraMap ((glued K t).presheaf.stalk x.1) (glued K t).functionField)).range =
      (gluedPlaceOfPoint K t ht x).toValuationSubring.toSubring := by
  obtain ⟨x, hx⟩ := x
  by_cases h : x ∈ Set.range (ι₀ K t).base
  · obtain ⟨x₀, rfl⟩ := h
    rw [gluedPlaceOfPoint_ι₀, Place.ofHeightOneSpectrum_toValuationSubring,
      ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
        (K := L) (v := primeOfι₀ K t ht x₀ hx),
      HeightOneSpectrum.valuationSubringAtPrime_toSubring]
    apply SetLike.ext'
    erw [range_ffEquiv_symm_comp_algebraMap_stalk K t (chartRing K ({t} : Set L)) (incl₀ K t)
      (fun a => coe_chartIncl K _ a) (ι₀ K t) rfl x₀]
    ext y
    constructor
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩
  · obtain ⟨xi, rfl⟩ := mem_range_ιInf_of_not_mem_range_ι₀ K t h
    rw [gluedPlaceOfPoint_of_not_mem K t ht _ h xi rfl,
      Place.ofHeightOneSpectrum_toValuationSubring,
      ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
        (K := L) (v := primeOfιInf K t ht xi hx),
      HeightOneSpectrum.valuationSubringAtPrime_toSubring]
    apply SetLike.ext'
    erw [range_ffEquiv_symm_comp_algebraMap_stalk K t (chartRing K ({t⁻¹} : Set L)) (inclInf K t)
      (fun a => coe_chartIncl K _ a) (ιInf K t) (glue_condition K t).symm xi]
    ext y
    constructor
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩
    · rintro ⟨a, b, hb, rfl⟩
      exact ⟨a, b, hb, rfl⟩

end PlaceMap

open IsLocalRing

section Compact

variable [Fact (t ≠ 0)]

instance compactSpace_glued : CompactSpace (glued K t) := by
  refine ⟨?_⟩
  have h : Set.range (ι₀ K t).base ∪ Set.range (ιInf K t).base = Set.univ :=
    Set.eq_univ_of_forall fun x => mem_range_ι₀_or_mem_range_ιInf K t x
  rw [← h]
  exact (isCompact_range (ι₀ K t).base.hom.continuous).union
    (isCompact_range (ιInf K t).base.hom.continuous)

instance quasiCompact_gluedToBase : QuasiCompact (gluedToBase K t) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

end Compact

section Noetherian

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

instance isLocallyNoetherian_glued : IsLocallyNoetherian (glued K t) := by
  refine (isLocallyNoetherian_iff_openCover (X := glued K t)
    (Scheme.IsLocallyDirected.openCover (span (f₀ K t) (fInf K t)))).mpr ?_
  rintro (_ | _ | _)
  · change IsLocallyNoetherian (XOverlap K t)
    haveI : IsNoetherianRing (chartRing K ({t, t⁻¹} : Set L)) := by
      letI := (incl₀ K t).toRingHom.toAlgebra
      haveI := isLocalization_away_incl₀ K t (Fact.out : t ≠ 0)
      exact IsLocalization.isNoetherianRing (Submonoid.powers (tChart K t)) _ inferInstance
    infer_instance
  · change IsLocallyNoetherian (X₀ K t)
    infer_instance
  · change IsLocallyNoetherian (XInf K t)
    infer_instance

instance quasiSeparated_gluedToBase : QuasiSeparated (gluedToBase K t) :=
  QuasiSeparated.of_quasiSeparatedSpace _

end Noetherian

section RingLemmas

variable {B R F : Type*} [CommRing B] [CommRing R] [CommRing F]

def liftOfRange (j : R →+* F) (hj : Function.Injective j) (g : B →+* F)
    (h : ∀ b, g b ∈ j.range) : B →+* R :=
  (RingEquiv.ofBijective j.rangeRestrict
      ⟨fun _ _ e => hj (congrArg Subtype.val e), j.rangeRestrict_surjective⟩).symm.toRingHom.comp
    (g.codRestrict j.range h)

theorem liftOfRange_spec (j : R →+* F) (hj : Function.Injective j) (g : B →+* F)
    (h : ∀ b, g b ∈ j.range) (b : B) : j (liftOfRange j hj g h b) = g b := by
  set e := RingEquiv.ofBijective j.rangeRestrict
      ⟨fun _ _ e => hj (congrArg Subtype.val e), j.rangeRestrict_surjective⟩
  have : e (e.symm ⟨g b, h b⟩) = ⟨g b, h b⟩ := e.apply_symm_apply _
  exact congrArg Subtype.val this

theorem comp_liftOfRange (j : R →+* F) (hj : Function.Injective j) (g : B →+* F)
    (h : ∀ b, g b ∈ j.range) : j.comp (liftOfRange j hj g h) = g :=
  RingHom.ext (liftOfRange_spec j hj g h)

end RingLemmas

section SpecLemmas

theorem SpecMap_cancel {R F Y : CommRingCat.{u}} (j : R ⟶ F) (hj : Function.Injective j)
    (u v : Spec R ⟶ Spec Y) (h : Spec.map j ≫ u = Spec.map j ≫ v) : u = v := by
  haveI : Mono j := ConcreteCategory.mono_of_injective j hj
  rw [← Spec.map_preimage u, ← Spec.map_preimage v, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  rw [cancel_mono] at h'
  rw [← Spec.map_preimage u, ← Spec.map_preimage v, h']

theorem fromSpecStalk_comp {X : Scheme.{u}} {A : CommRingCat.{u}} (f : X ⟶ Spec A) (x : X) :
    X.fromSpecStalk x ≫ f =
      Spec.map (StructureSheaf.toStalk A (f.base x) ≫ f.stalkMap x) := by
  rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq']
  rfl

end SpecLemmas

section LiftLemma

variable [Fact (t ≠ 0)]

theorem exists_eq_SpecMap_comp_fromSpecStalk {F : Type u} [Field F] (f : Spec (.of F) ⟶ glued K t)
    {x : glued K t} (hx : f.base (closedPoint F) = x) :
    ∃ φ : (glued K t).presheaf.stalk x ⟶ CommRingCat.of F,
      IsLocalHom φ.hom ∧ f = Spec.map φ ≫ (glued K t).fromSpecStalk x := by
  subst hx
  exact ⟨_, inferInstance, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk f).symm⟩

theorem hasLift_of_range (S : ValuativeCommSq (gluedToBase K t)) {x P : glued K t} (hsp : x ⤳ P)
    (φ : (glued K t).presheaf.stalk x ⟶ CommRingCat.of S.K)
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk x)
    (hrange : ∀ s : (glued K t).presheaf.stalk P,
      φ ((glued K t).presheaf.stalkSpecializes hsp s) ∈ (algebraMap S.R S.K).range) :
    S.commSq.HasLift := by
  let ψ : (glued K t).presheaf.stalk P →+* S.R :=
    liftOfRange (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K)
      (φ.hom.comp ((glued K t).presheaf.stalkSpecializes hsp).hom) hrange
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap S.R S.K) =
      (glued K t).presheaf.stalkSpecializes hsp ≫ φ := by
    ext s
    exact liftOfRange_spec (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K) _ hrange s
  let l : Spec (.of S.R) ⟶ glued K t := Spec.map (CommRingCat.ofHom ψ) ≫ (glued K t).fromSpecStalk P
  have fac_left : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l = S.i₁ := by
    rw [h₁, ← Spec.map_comp_assoc, hψ, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  refine CommSq.HasLift.mk' ⟨l, fac_left, ?_⟩
  apply SpecMap_cancel (CommRingCat.ofHom (algebraMap S.R S.K)) (IsFractionRing.injective S.R S.K)
  rw [← Category.assoc, fac_left, S.commSq.w]

theorem ringCompat (S : ValuativeCommSq (gluedToBase K t)) {x : glued K t}
    (φ : (glued K t).presheaf.stalk x ⟶ CommRingCat.of S.K)
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk x) :
    (StructureSheaf.toStalk (CommRingCat.of K) ((gluedToBase K t).base x) ≫
        (gluedToBase K t).stalkMap x) ≫ φ =
      Spec.preimage S.i₂ ≫ CommRingCat.ofHom (algebraMap S.R S.K) := by
  apply Spec.map_injective
  rw [Spec.map_comp, ← fromSpecStalk_comp, Spec.map_comp, Spec.map_preimage, ← Category.assoc,
    ← h₁]
  exact S.commSq.w

end LiftLemma

section Generic

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem stalkMap_toStalk_genericPoint (a : K) :
    (gluedToBase K t).stalkMap (genericPoint (glued K t))
        (StructureSheaf.toStalk (CommRingCat.of K) _ a) =
      baseToFunctionField (gluedToBase K t) a := by
  change (gluedToBase K t).stalkMap (genericPoint (glued K t))
      ((Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) = _
  rw [Scheme.Hom.germ_stalkMap_apply]
  rfl

variable (S : ValuativeCommSq (gluedToBase K t))
  (φ : (glued K t).presheaf.stalk (genericPoint (glued K t)) ⟶ CommRingCat.of S.K)

def gL : L →+* S.K := φ.hom.comp (gluedFunctionFieldEquiv K t).toRingHom

omit [CharZero K] [FiniteDimensional K⟮t⁻¹⟯ L] in
theorem gL_ffEquiv_symm (y : (glued K t).functionField) :
    gL K t S φ ((gluedFunctionFieldEquiv K t).symm y) = φ y :=
  congrArg φ.hom ((gluedFunctionFieldEquiv K t).apply_symm_apply y)

def pullbackVS : ValuationSubring L where
  toSubring := (algebraMap S.R S.K).range.comap (gL K t S φ)
  mem_or_inv_mem' y := by
    rcases ValuationRing.isInteger_or_isInteger S.R (gL K t S φ y) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r, hr⟩
    · exact Or.inr ⟨r, by rw [map_inv₀]; exact hr⟩

omit [CharZero K] [FiniteDimensional K⟮t⁻¹⟯ L] in
theorem mem_pullbackVS_iff (y : L) :
    y ∈ pullbackVS K t S φ ↔ gL K t S φ y ∈ (algebraMap S.R S.K).range := Iff.rfl

omit [CharZero K] [FiniteDimensional K⟮t⁻¹⟯ L] in
theorem algebraMap_mem_pullbackVS
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (genericPoint (glued K t))) (a : K) :
    algebraMap K L a ∈ pullbackVS K t S φ := by
  rw [mem_pullbackVS_iff]
  refine ⟨(Spec.preimage S.i₂).hom a, ?_⟩
  have h : φ ((gluedToBase K t).stalkMap (genericPoint (glued K t))
      (StructureSheaf.toStalk (CommRingCat.of K) _ a)) =
      algebraMap S.R S.K ((Spec.preimage S.i₂).hom a) :=
    congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of S.K => f a) (ringCompat K t S φ h₁)
  rw [stalkMap_toStalk_genericPoint] at h
  change _ = φ ((gluedFunctionFieldEquiv K t) (algebraMap K L a))
  rw [gluedFunctionFieldEquiv_algebraMap, h]

omit [CharZero K] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem hasLift_generic_top
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (genericPoint (glued K t)))
    (hO : pullbackVS K t S φ = ⊤) : S.commSq.HasLift := by
  refine hasLift_of_range K t S (specializes_refl _) φ h₁ fun u => ?_
  have hu : (gluedFunctionFieldEquiv K t).symm
      ((glued K t).presheaf.stalkSpecializes (specializes_refl _) u) ∈ pullbackVS K t S φ := by
    rw [hO]; trivial
  rwa [mem_pullbackVS_iff, gL_ffEquiv_symm] at hu

omit [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem hasLift_generic_centre (s : L) [FiniteDimensional K⟮s⟯ L]
    (i : chartRing K ({s} : Set L) →ₐ[K] chartRing K ({t, t⁻¹} : Set L))
    (hi : ∀ a : chartRing K ({s} : Set L), (i a : L) = a)
    (ιA : Spec (CommRingCat.of (chartRing K ({s} : Set L))) ⟶ glued K t) [IsOpenImmersion ιA]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom i.toRingHom))]
    (comm : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ιA = ιU K t)
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (genericPoint (glued K t)))
    (hO : pullbackVS K t S φ ≠ ⊤) (hs : s ∈ pullbackVS K t S φ) : S.commSq.HasLift := by
  let 𝔮 := primeOfValuationSubring K s (pullbackVS K t S φ) (algebraMap_mem_pullbackVS K t S φ h₁)
    hs hO
  let q : Spec (CommRingCat.of (chartRing K ({s} : Set L))) := ⟨𝔮.asIdeal, 𝔮.isPrime⟩
  refine hasLift_of_range K t S (genericPoint_specializes (ιA.base q)) φ h₁ fun u => ?_

  have hmem : (gluedFunctionFieldEquiv K t).symm
      (algebraMap ((glued K t).presheaf.stalk (ιA.base q)) (glued K t).functionField u) ∈
        pullbackVS K t S φ := by
    have hr : (gluedFunctionFieldEquiv K t).symm
        (algebraMap ((glued K t).presheaf.stalk (ιA.base q)) (glued K t).functionField u) ∈
        ((((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
          (algebraMap ((glued K t).presheaf.stalk (ιA.base q)) (glued K t).functionField)).range :
            Set L) := ⟨u, rfl⟩
    rw [range_ffEquiv_symm_comp_algebraMap_stalk K t (chartRing K ({s} : Set L)) i hi ιA comm q]
      at hr
    obtain ⟨a, b, hb, e⟩ := hr
    rw [e]
    apply valuationSubringAtPrime_le K s (pullbackVS K t S φ)
      (algebraMap_mem_pullbackVS K t S φ h₁) hs hO
    exact ⟨a, b, hb, rfl⟩
  rw [mem_pullbackVS_iff, gL_ffEquiv_symm] at hmem
  exact hmem

theorem hasLift_generic (hgen : S.i₁.base (closedPoint S.K) = genericPoint (glued K t)) :
    S.commSq.HasLift := by
  obtain ⟨φ, -, h₁⟩ := exists_eq_SpecMap_comp_fromSpecStalk K t S.i₁ hgen
  by_cases hO : pullbackVS K t S φ = ⊤
  · exact hasLift_generic_top K t S φ h₁ hO
  · rcases (pullbackVS K t S φ).mem_or_inv_mem t with ht | ht
    · exact hasLift_generic_centre K t S φ t (incl₀ K t) (fun a => coe_chartIncl K _ a) (ι₀ K t)
        rfl h₁ hO ht
    · exact hasLift_generic_centre K t S φ t⁻¹ (inclInf K t) (fun a => coe_chartIncl K _ a)
        (ιInf K t) (glue_condition K t).symm h₁ hO ht

end Generic

section Closed

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

variable (A : Subalgebra K L) (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
  (ιA_toBase : ιA ≫ gluedToBase K t = Spec.map (CommRingCat.ofHom (algebraMap K A)))
  (S : ValuativeCommSq (gluedToBase K t)) (p : Spec (CommRingCat.of A))
  (φ : (glued K t).presheaf.stalk (ιA.base p) ⟶ CommRingCat.of S.K)

def stalkChartEquiv :
    (glued K t).presheaf.stalk (ιA.base p) ≃+* (Spec (CommRingCat.of A)).presheaf.stalk p :=
  (asIso (ιA.stalkMap p)).commRingCatIsoToRingEquiv

def φA : (Spec (CommRingCat.of A)).presheaf.stalk p →+* S.K :=
  φ.hom.comp (stalkChartEquiv K t A ιA p).symm.toRingHom

def gA : A →+* S.K := (φA K t A ιA S p φ).comp (StructureSheaf.toStalk A p).hom

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in
theorem φA_stalkMap (y : (glued K t).presheaf.stalk (ιA.base p)) :
    φA K t A ιA S p φ (ιA.stalkMap p y) = φ y := by
  change φ ((stalkChartEquiv K t A ιA p).symm ((stalkChartEquiv K t A ιA p) y)) = φ y
  rw [RingEquiv.symm_apply_apply]

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] [IsOpenImmersion ιA] in
include ιA_toBase in

theorem stalkMap_chart_toStalk (a : K) :
    ιA.stalkMap p ((gluedToBase K t).stalkMap (ιA.base p)
        (StructureSheaf.toStalk (CommRingCat.of K) _ a)) =
      StructureSheaf.toStalk A p (algebraMap K A a) := by
  change ιA.stalkMap p ((gluedToBase K t).stalkMap (ιA.base p)
      ((Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))) = _
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
  change (Spec (CommRingCat.of A)).presheaf.germ ⊤ p trivial
      ((ιA ≫ gluedToBase K t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) = _
  rw [ιA_toBase]
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap K A a) := by
    have := congrArg (fun f : CommRingCat.of K ⟶ Γ(Spec (CommRingCat.of A), ⊤) => f a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K A)))
    exact this.symm
  rw [h1]
  rfl

include ιA_toBase in
omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem gA_algebraMap (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (ιA.base p)) (a : K) :
    gA K t A ιA S p φ (algebraMap K A a) =
      algebraMap S.R S.K ((Spec.preimage S.i₂).hom a) := by
  have h : φ ((gluedToBase K t).stalkMap (ιA.base p)
      (StructureSheaf.toStalk (CommRingCat.of K) _ a)) =
      algebraMap S.R S.K ((Spec.preimage S.i₂).hom a) :=
    congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of S.K => f a) (ringCompat K t S φ h₁)
  rw [← h, ← φA_stalkMap K t A ιA S p φ, stalkMap_chart_toStalk K t A ιA ιA_toBase p a]
  rfl

variable [hmax : p.asIdeal.IsMaximal]

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] hmax in

theorem gA_eq_zero [IsLocalHom φ.hom] (m : A) (hm : m ∈ p.asIdeal) : gA K t A ιA S p φ m = 0 := by
  have hloc₁ : IsLocalHom (stalkChartEquiv K t A ιA p).symm.toRingHom :=
    isLocalHom_of_leftInverse (stalkChartEquiv K t A ιA p).toRingHom
      fun x => (stalkChartEquiv K t A ιA p).apply_symm_apply x
  have hloc : IsLocalHom (φA K t A ιA S p φ) :=
    @RingHom.isLocalHom_comp _ _ _ _ _ _ φ.hom (stalkChartEquiv K t A ιA p).symm.toRingHom _ hloc₁
  by_contra h
  have hu : IsUnit (φA K t A ιA S p φ
      (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk p) m)) :=
    isUnit_iff_ne_zero.mpr h
  have hu' : IsUnit (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk p) m) :=
    @IsUnit.of_map _ _ _ _ _ _ (φA K t A ιA S p φ) hloc _ hu
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal m).mp hu' hm

include ιA_toBase in
omit [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem gA_mem_range [Algebra.FiniteType K A] [IsLocalHom φ.hom]
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (ιA.base p)) (a : A) :
    gA K t A ιA S p φ a ∈ (algebraMap S.R S.K).range := by
  letI := Ideal.Quotient.field p.asIdeal
  haveI : Module.Finite K (A ⧸ p.asIdeal) := finite_of_finite_type_of_isJacobsonRing K _
  haveI : IsIntegrallyClosed S.R := GCDMonoid.toIsIntegrallyClosed
  let β : K →+* S.R := (Spec.preimage S.i₂).hom
  let gbar : A ⧸ p.asIdeal →+* S.K :=
    Ideal.Quotient.lift p.asIdeal (gA K t A ιA S p φ) (gA_eq_zero K t A ιA S p φ)
  have hg : gA K t A ιA S p φ a = gbar (Ideal.Quotient.mk p.asIdeal a) :=
    (Ideal.Quotient.lift_mk _ _ _).symm
  have hcomp : (algebraMap S.R S.K).comp β = gbar.comp (algebraMap K (A ⧸ p.asIdeal)) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.lift_mk]
    exact (gA_algebraMap K t A ιA ιA_toBase S p φ h₁ c).symm
  obtain ⟨f, hf, hfa⟩ : IsIntegral K (Ideal.Quotient.mk p.asIdeal a) :=
    Algebra.IsIntegral.isIntegral _
  have hint : IsIntegral S.R (gA K t A ιA S p φ a) := by
    refine ⟨f.map β, hf.map β, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, hg, ← Polynomial.hom_eval₂]
    change gbar (Polynomial.eval₂ (algebraMap K (A ⧸ p.asIdeal)) _ f) = 0
    rw [hfa, map_zero]
  exact IsIntegrallyClosed.algebraMap_eq_of_integral hint

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem exists_gA_mul_gA_eq_one [IsLocalHom φ.hom] (b : A) (hb : b ∉ p.asIdeal) :
    ∃ c : A, gA K t A ιA S p φ b * gA K t A ιA S p φ c = 1 := by
  letI := Ideal.Quotient.field p.asIdeal
  have hb0 : Ideal.Quotient.mk p.asIdeal b ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk p.asIdeal b)⁻¹
  refine ⟨c, ?_⟩
  let gbar : A ⧸ p.asIdeal →+* S.K :=
    Ideal.Quotient.lift p.asIdeal (gA K t A ιA S p φ) (gA_eq_zero K t A ιA S p φ)
  have e : ∀ x : A, gA K t A ιA S p φ x = gbar (Ideal.Quotient.mk p.asIdeal x) := fun x =>
    (Ideal.Quotient.lift_mk _ _ _).symm
  rw [e, e, ← map_mul, hc, mul_inv_cancel₀ hb0, map_one]

include ιA_toBase in
omit [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem φ_mem_range [Algebra.FiniteType K A] [IsLocalHom φ.hom]
    (h₁ : S.i₁ = Spec.map φ ≫ (glued K t).fromSpecStalk (ιA.base p))
    (s : (glued K t).presheaf.stalk (ιA.base p)) : φ s ∈ (algebraMap S.R S.K).range := by
  obtain ⟨y, rfl⟩ : ∃ y, (stalkChartEquiv K t A ιA p).symm y = s :=
    ⟨stalkChartEquiv K t A ιA p s, RingEquiv.symm_apply_apply _ _⟩
  change φA K t A ιA S p φ y ∈ _
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl y
  obtain ⟨c, hc⟩ := exists_gA_mul_gA_eq_one K t A ιA S p φ b b.2
  have hspec := congrArg (φA K t A ιA S p φ)
    (IsLocalization.mk'_spec ((Spec (CommRingCat.of A)).presheaf.stalk p) a b)
  rw [map_mul] at hspec
  have hspec' : φA K t A ιA S p φ (IsLocalization.mk' _ a b) * gA K t A ιA S p φ b =
      gA K t A ιA S p φ a := hspec
  have key : φA K t A ιA S p φ (IsLocalization.mk' _ a b) =
      gA K t A ιA S p φ a * gA K t A ιA S p φ c := by
    calc φA K t A ιA S p φ (IsLocalization.mk' _ a b)
        = φA K t A ιA S p φ (IsLocalization.mk' _ a b) *
            (gA K t A ιA S p φ b * gA K t A ιA S p φ c) := by rw [hc, mul_one]
      _ = (φA K t A ιA S p φ (IsLocalization.mk' _ a b) * gA K t A ιA S p φ b) *
            gA K t A ιA S p φ c := by ring
      _ = gA K t A ιA S p φ a * gA K t A ιA S p φ c := by rw [hspec']
  rw [key]
  exact Subring.mul_mem _ (gA_mem_range K t A ιA ιA_toBase S p φ h₁ a)
    (gA_mem_range K t A ιA ιA_toBase S p φ h₁ c)

end Closed

section ClosedLift

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

omit [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

theorem hasLift_closed (A : Subalgebra K L) [Algebra.FiniteType K A]
    (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
    (ιA_toBase : ιA ≫ gluedToBase K t = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (S : ValuativeCommSq (gluedToBase K t)) (p : Spec (CommRingCat.of A))
    (hp : S.i₁.base (closedPoint S.K) = ιA.base p) (hmax : p.asIdeal.IsMaximal) :
    S.commSq.HasLift := by
  obtain ⟨φ, hloc, h₁⟩ := exists_eq_SpecMap_comp_fromSpecStalk K t S.i₁ hp
  haveI := hloc
  haveI := hmax
  exact hasLift_of_range K t S (specializes_refl _) φ h₁ fun s =>
    φ_mem_range K t A ιA ιA_toBase S p φ h₁ _

theorem valuativeCriterion_existence : ValuativeCriterion.Existence (gluedToBase K t) := by
  intro S
  rcases mem_range_ι₀_or_mem_range_ιInf K t (S.i₁.base (closedPoint S.K)) with ⟨p, hp⟩ | ⟨q, hq⟩
  · by_cases hbot : p.asIdeal = ⊥
    · refine hasLift_generic K t S ?_
      have hη : p = genericPoint (X₀ K t) := by
        rw [genericPoint_eq_bot_of_affine]; exact PrimeSpectrum.ext hbot
      rw [← hp, hη]
      exact genericPoint_eq_of_isOpenImmersion (ι₀ K t)
    · exact hasLift_closed K t (chartRing K ({t} : Set L)) (ι₀ K t) (ι₀_gluedToBase K t) S p
        hp.symm (Ideal.IsPrime.isMaximal p.isPrime hbot)
  · by_cases hbot : q.asIdeal = ⊥
    · refine hasLift_generic K t S ?_
      have hη : q = genericPoint (XInf K t) := by
        rw [genericPoint_eq_bot_of_affine]; exact PrimeSpectrum.ext hbot
      rw [← hq, hη]
      exact genericPoint_eq_of_isOpenImmersion (ιInf K t)
    · exact hasLift_closed K t (chartRing K ({t⁻¹} : Set L)) (ιInf K t) (ιInf_gluedToBase K t) S q
        hq.symm (Ideal.IsPrime.isMaximal q.isPrime hbot)

end ClosedLift

section Uniqueness

variable [Fact (t ≠ 0)]

theorem range_subset_of_closedPoint_mem {R : Type u} [CommRing R] [IsLocalRing R]
    (l : Spec (CommRingCat.of R) ⟶ glued K t) {X : Scheme.{u}} (ι : X ⟶ glued K t)
    [IsOpenImmersion ι] (h : l.base (closedPoint R) ∈ Set.range ι.base) :
    Set.range l.base ⊆ Set.range ι.base := by
  rintro _ ⟨z, rfl⟩
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem l (U := ι.opensRange) h
  have hz : z ∈ l ⁻¹ᵁ ι.opensRange := by rw [htop]; trivial
  exact hz

theorem liftStruct_eq_of_mem_range {A : Type u} [CommRing A]
    (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
    (S : ValuativeCommSq (gluedToBase K t)) (l₁ l₂ : S.commSq.LiftStruct)
    (h₁ : l₁.l.base (closedPoint S.R) ∈ Set.range ιA.base)
    (h₂ : l₂.l.base (closedPoint S.R) ∈ Set.range ιA.base) : l₁ = l₂ := by
  have H₁ := range_subset_of_closedPoint_mem K t l₁.l ιA h₁
  have H₂ := range_subset_of_closedPoint_mem K t l₂.l ιA h₂
  let m₁ := IsOpenImmersion.lift ιA l₁.l H₁
  let m₂ := IsOpenImmersion.lift ιA l₂.l H₂
  have e₁ : m₁ ≫ ιA = l₁.l := IsOpenImmersion.lift_fac _ _ _
  have e₂ : m₂ ≫ ιA = l₂.l := IsOpenImmersion.lift_fac _ _ _

  have hF : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ m₁ =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ m₂ := by
    rw [← cancel_mono ιA, Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]

  haveI : Mono (CommRingCat.ofHom (algebraMap S.R S.K)) :=
    ConcreteCategory.mono_of_injective _ (IsFractionRing.injective S.R S.K)
  have hm : m₁ = m₂ := by
    rw [← Spec.map_preimage m₁, ← Spec.map_preimage m₂, ← Spec.map_comp, ← Spec.map_comp] at hF
    have := Spec.map_injective hF
    rw [cancel_mono] at this
    rw [← Spec.map_preimage m₁, ← Spec.map_preimage m₂, this]
  ext
  rw [← e₁, ← e₂, hm]

theorem incl₀_tChart_mul_inclInf_tInvChart :
    incl₀ K t (tChart K t) * inclInf K t (tInvChart K t) = 1 :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_chartIncl, coe_chartIncl, coe_tChart, coe_tInvChart,
      Subalgebra.coe_one, mul_inv_cancel₀ (Fact.out : t ≠ 0)])

theorem false_of_liftStruct_cross (S : ValuativeCommSq (gluedToBase K t))
    (l₁ l₂ : S.commSq.LiftStruct)
    (h₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ι₀ K t).base)
    (h₁' : l₁.l.base (closedPoint S.R) ∉ Set.range (ιInf K t).base)
    (h₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ιInf K t).base)
    (h₂' : l₂.l.base (closedPoint S.R) ∉ Set.range (ι₀ K t).base) : False := by

  have H₁ := range_subset_of_closedPoint_mem K t l₁.l (ι₀ K t) h₁
  have H₂ := range_subset_of_closedPoint_mem K t l₂.l (ιInf K t) h₂
  let G₁ : CommRingCat.of (chartRing K ({t} : Set L)) ⟶ CommRingCat.of S.R :=
    Spec.preimage (IsOpenImmersion.lift (ι₀ K t) l₁.l H₁)
  let G₂ : CommRingCat.of (chartRing K ({t⁻¹} : Set L)) ⟶ CommRingCat.of S.R :=
    Spec.preimage (IsOpenImmersion.lift (ιInf K t) l₂.l H₂)
  have e₁ : Spec.map G₁ ≫ ι₀ K t = l₁.l := by
    rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  have e₂ : Spec.map G₂ ≫ ιInf K t = l₂.l := by
    rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _

  have ht₁ : G₁ (tChart K t) ∈ maximalIdeal S.R := by
    by_contra hn
    apply h₁'
    rw [← e₁, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, ι₀_mem_range_ιInf_iff]
    exact hn
  have ht₂ : G₂ (tInvChart K t) ∈ maximalIdeal S.R := by
    by_contra hn
    apply h₂'
    rw [← e₂, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, ιInf_mem_range_ι₀_iff]
    exact hn

  let alg := CommRingCat.ofHom (algebraMap S.R S.K)
  have hov : Set.range (Spec.map alg ≫ Spec.map G₁).base ⊆ Set.range (f₀ K t).base := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = closedPoint S.K := Subsingleton.elim _ _
    have hx : (ι₀ K t).base ((Spec.map alg ≫ Spec.map G₁).base (closedPoint S.K)) ∈
        Set.range (ιInf K t).base := by
      refine ⟨(Spec.map alg ≫ Spec.map G₂).base (closedPoint S.K), ?_⟩
      change ((Spec.map alg ≫ Spec.map G₂) ≫ ιInf K t).base (closedPoint S.K) =
        ((Spec.map alg ≫ Spec.map G₁) ≫ ι₀ K t).base (closedPoint S.K)
      rw [Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]
    rw [ι₀_mem_range_ιInf_iff] at hx
    rw [range_f₀]
    exact hx
  let u := IsOpenImmersion.lift (f₀ K t) (Spec.map alg ≫ Spec.map G₁) hov
  have hu₀ : u ≫ f₀ K t = Spec.map alg ≫ Spec.map G₁ := IsOpenImmersion.lift_fac _ _ _
  have hui : u ≫ fInf K t = Spec.map alg ≫ Spec.map G₂ := by
    rw [← cancel_mono (ιInf K t), Category.assoc, ← glue_condition, ← Category.assoc, hu₀,
      Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]

  let W := Spec.preimage u
  have hW₀ : CommRingCat.ofHom (incl₀ K t).toRingHom ≫ W = G₁ ≫ alg := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact hu₀
  have hWi : CommRingCat.ofHom (inclInf K t).toRingHom ≫ W = G₂ ≫ alg := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact hui
  have k₁ : W (incl₀ K t (tChart K t)) = algebraMap S.R S.K (G₁ (tChart K t)) :=
    congrArg (fun f : CommRingCat.of (chartRing K ({t} : Set L)) ⟶ CommRingCat.of S.K =>
      f (tChart K t)) hW₀
  have k₂ : W (inclInf K t (tInvChart K t)) = algebraMap S.R S.K (G₂ (tInvChart K t)) :=
    congrArg (fun f : CommRingCat.of (chartRing K ({t⁻¹} : Set L)) ⟶ CommRingCat.of S.K =>
      f (tInvChart K t)) hWi
  have hone : algebraMap S.R S.K (G₁ (tChart K t) * G₂ (tInvChart K t)) = algebraMap S.R S.K 1 := by
    rw [map_mul, map_one, ← k₁, ← k₂, ← map_mul, incl₀_tChart_mul_inclInf_tInvChart, map_one]
  have hone' := IsFractionRing.injective S.R S.K hone
  exact (maximalIdeal S.R).ne_top_iff_one.mp (maximalIdeal.isMaximal S.R).ne_top
    (hone' ▸ Ideal.mul_mem_right _ _ ht₁)

theorem valuativeCriterion_uniqueness : ValuativeCriterion.Uniqueness (gluedToBase K t) := by
  intro S
  refine ⟨fun l₁ l₂ => ?_⟩
  by_cases a₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ι₀ K t).base <;>
    by_cases a₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ι₀ K t).base
  · exact liftStruct_eq_of_mem_range K t (ι₀ K t) S l₁ l₂ a₁ a₂
  · have b₂ := mem_range_ιInf_of_not_mem_range_ι₀ K t a₂
    by_cases b₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ιInf K t).base
    · exact liftStruct_eq_of_mem_range K t (ιInf K t) S l₁ l₂ b₁ b₂
    · exact (false_of_liftStruct_cross K t S l₁ l₂ a₁ b₁ b₂ a₂).elim
  · have b₁ := mem_range_ιInf_of_not_mem_range_ι₀ K t a₁
    by_cases b₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ιInf K t).base
    · exact liftStruct_eq_of_mem_range K t (ιInf K t) S l₁ l₂ b₁ b₂
    · exact (false_of_liftStruct_cross K t S l₂ l₁ a₂ b₂ b₁ a₁).elim
  · exact liftStruct_eq_of_mem_range K t (ιInf K t) S l₁ l₂
      (mem_range_ιInf_of_not_mem_range_ι₀ K t a₁) (mem_range_ιInf_of_not_mem_range_ι₀ K t a₂)

end Uniqueness

section Proper

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

instance isProper_gluedToBase : IsProper (gluedToBase K t) :=
  IsProper.of_valuativeCriterion (gluedToBase K t)
    ((ValuativeCriterion.iff).mpr
      ⟨valuativeCriterion_existence K t, valuativeCriterion_uniqueness K t⟩)

end Proper

open TopologicalSpace

section ChartGerms

variable (A : Subalgebra K L)

def secTop (r : A) : Γ(Spec (CommRingCat.of A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv r

theorem mem_basicOpen_secTop (r : A) (p : Spec (CommRingCat.of A)) :
    p ∈ (Spec (CommRingCat.of A)).basicOpen (secTop K A r) ↔ r ∉ p.asIdeal := by
  rw [secTop, basicOpen_eq_of_affine]
  exact Iff.rfl

theorem germ_res_secTop (r : A) (V : (Spec (CommRingCat.of A)).Opens) (p : Spec (CommRingCat.of A))
    (hp : p ∈ V) :
    (Spec (CommRingCat.of A)).presheaf.germ V p hp
        ((Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (secTop K A r)) =
      algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk p) r := by
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

variable [Fact (t ≠ 0)] (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]

theorem stalkMap_germ_appIso_inv (V : (Spec (CommRingCat.of A)).Opens)
    (τ : Γ(Spec (CommRingCat.of A), V)) (p : Spec (CommRingCat.of A)) (hp : p ∈ V) :
    ιA.stalkMap p ((glued K t).presheaf.germ (ιA ''ᵁ V) (ιA.base p) ⟨p, hp, rfl⟩
        ((ιA.appIso V).inv τ)) = (Spec (CommRingCat.of A)).presheaf.germ V p hp τ := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  have : ιA.app (ιA ''ᵁ V) ((ιA.appIso V).inv τ) =
      (Spec (CommRingCat.of A)).presheaf.map (eqToHom (ιA.preimage_image_eq V)).op τ := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_app]
  rw [this, TopCat.Presheaf.germ_res_apply]

def cSec (a : K) (W : (glued K t).Opens) : Γ(glued K t, W) :=
  (glued K t).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
    ((gluedToBase K t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))

omit [IsOpenImmersion ιA] in

theorem stalkMap_germ_cSec
    (ιA_toBase : ιA ≫ gluedToBase K t = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (a : K) (W : (glued K t).Opens) (p : Spec (CommRingCat.of A)) (hp : ιA.base p ∈ W) :
    ιA.stalkMap p ((glued K t).presheaf.germ W (ιA.base p) hp (cSec K t a W)) =
      algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk p) (algebraMap K A a) := by
  rw [cSec, TopCat.Presheaf.germ_res_apply]
  have : (glued K t).presheaf.germ ⊤ (ιA.base p) trivial
      ((gluedToBase K t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
      (gluedToBase K t).stalkMap (ιA.base p)
        (StructureSheaf.toStalk (CommRingCat.of K) _ a) :=
    (Scheme.Hom.germ_stalkMap_apply (gluedToBase K t) ⊤ (ιA.base p) trivial _).symm
  rw [this]
  exact stalkMap_chart_toStalk K t A ιA ιA_toBase p a

theorem isUnit_stalkMap_iff (p : Spec (CommRingCat.of A))
    (y : (glued K t).presheaf.stalk (ιA.base p)) : IsUnit (ιA.stalkMap p y) ↔ IsUnit y := by
  change IsUnit (stalkChartEquiv K t A ιA p y) ↔ IsUnit y
  exact ⟨fun h => by simpa using h.map (stalkChartEquiv K t A ιA p).symm, fun h => h.map _⟩

variable [FiniteDimensional K⟮t⟯ L]
variable (i : A →ₐ[K] chartRing K ({t, t⁻¹} : Set L)) (hi : ∀ a : A, (i a : L) = a)
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom i.toRingHom))]
  (comm : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ιA = ιU K t)

include hi in
omit [Fact (t ≠ 0)] [IsOpenImmersion ιA] in
theorem thetaHom_algebraMap (p : Spec (CommRingCat.of A)) (r : A) :
    thetaHom K t A i p (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk p) r) = r :=
  thetaHom_toStalk K t A i hi p r

include hi comm in

theorem ffEquiv_symm_germ_appIso_inv (V : (Spec (CommRingCat.of A)).Opens)
    (τ : Γ(Spec (CommRingCat.of A), V)) (p : Spec (CommRingCat.of A)) (hp : p ∈ V)
    (hη : genericPoint (glued K t) ∈ ιA ''ᵁ V) :
    (gluedFunctionFieldEquiv K t).symm
        ((glued K t).presheaf.germ (ιA ''ᵁ V) (genericPoint (glued K t)) hη ((ιA.appIso V).inv τ)) =
      thetaHom K t A i p ((Spec (CommRingCat.of A)).presheaf.germ V p hp τ) := by
  have _ := hi
  have hsp : genericPoint (glued K t) ⤳ ιA.base p := genericPoint_specializes _
  have e := CategoryTheory.ConcreteCategory.congr_hom
    (TopCat.Presheaf.germ_stalkSpecializes (glued K t).presheaf (U := ιA ''ᵁ V) ⟨p, hp, rfl⟩ hsp)
    ((ιA.appIso V).inv τ)
  rw [CommRingCat.comp_apply] at e
  rw [← e]
  have h2 := ffEquiv_symm_algebraMap_stalk K t A i ιA comm p
    ((glued K t).presheaf.germ (ιA ''ᵁ V) (ιA.base p) ⟨p, hp, rfl⟩ ((ιA.appIso V).inv τ))
  rw [stalkMap_germ_appIso_inv] at h2
  exact h2

end ChartGerms

section LocalSections

variable (a : K)

def tma : chartRing K ({t} : Set L) := tChart K t - algebraMap K _ a

def gInf : chartRing K ({t⁻¹} : Set L) := 1 - algebraMap K _ a * tInvChart K t

@[simp] theorem coe_tma : (tma K t a : L) = t - algebraMap K L a := by
  rw [tma, Subalgebra.coe_sub, coe_tChart, Subalgebra.coe_algebraMap]

@[simp] theorem coe_gInf : (gInf K t a : L) = 1 - algebraMap K L a * t⁻¹ := by
  rw [gInf, Subalgebra.coe_sub, Subalgebra.coe_one, Subalgebra.coe_mul, coe_tInvChart,
    Subalgebra.coe_algebraMap]

theorem incl₀_tma [Fact (t ≠ 0)] :
    incl₀ K t (tma K t a) = incl₀ K t (tChart K t) * inclInf K t (gInf K t a) := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_chartIncl, coe_chartIncl, coe_chartIncl, coe_tma, coe_tChart,
    coe_gInf, mul_sub, mul_one, mul_left_comm, mul_inv_cancel₀ (Fact.out : t ≠ 0), mul_one]

theorem gInf_add : gInf K t a + algebraMap K _ a * tInvChart K t = 1 := by
  rw [gInf, sub_add_cancel]

theorem tma_add : tma K t a + algebraMap K _ a = tChart K t := by
  rw [tma, sub_add_cancel]

def U₁ : (X₀ K t).Opens := (X₀ K t).basicOpen (secTop K (chartRing K ({t} : Set L)) (tma K t a))

def U₂ : (XInf K t).Opens :=
  (XInf K t).basicOpen (secTop K (chartRing K ({t⁻¹} : Set L)) (gInf K t a))

theorem mem_U₁_iff (p : X₀ K t) : p ∈ U₁ K t a ↔ tma K t a ∉ p.asIdeal :=
  mem_basicOpen_secTop K _ _ p

theorem mem_U₂_iff (q : XInf K t) : q ∈ U₂ K t a ↔ gInf K t a ∉ q.asIdeal :=
  mem_basicOpen_secTop K _ _ q

theorem isUnit_res_tma : IsUnit ((X₀ K t).presheaf.map
    (homOfLE ((X₀ K t).basicOpen_le (secTop K (chartRing K ({t} : Set L)) (tma K t a)))).op
    (secTop K (chartRing K ({t} : Set L)) (tma K t a))) :=
  RingedSpace.isUnit_res_basicOpen (X := (X₀ K t).toLocallyRingedSpace.toSheafedSpace) _

theorem isUnit_res_gInf : IsUnit ((XInf K t).presheaf.map
    (homOfLE ((XInf K t).basicOpen_le (secTop K (chartRing K ({t⁻¹} : Set L)) (gInf K t a)))).op
    (secTop K (chartRing K ({t⁻¹} : Set L)) (gInf K t a))) :=
  RingedSpace.isUnit_res_basicOpen (X := (XInf K t).toLocallyRingedSpace.toSheafedSpace) _

def σ₁ : Γ(X₀ K t, U₁ K t a) := (((isUnit_res_tma K t a).unit⁻¹ : (Γ(X₀ K t, U₁ K t a))ˣ) : _)

def σ₂ : Γ(XInf K t, U₂ K t a) :=
  (XInf K t).presheaf.map (homOfLE (le_top : U₂ K t a ≤ ⊤)).op
      (secTop K (chartRing K ({t⁻¹} : Set L)) (tInvChart K t)) *
    (((isUnit_res_gInf K t a).unit⁻¹ : (Γ(XInf K t, U₂ K t a))ˣ) : _)

theorem germ_σ₁_mul (p : X₀ K t) (hp : p ∈ U₁ K t a) :
    (X₀ K t).presheaf.germ (U₁ K t a) p hp (σ₁ K t a) *
      algebraMap _ ((X₀ K t).presheaf.stalk p) (tma K t a) = 1 := by
  have hu : σ₁ K t a * (X₀ K t).presheaf.map (homOfLE (le_top : U₁ K t a ≤ ⊤)).op
      (secTop K (chartRing K ({t} : Set L)) (tma K t a)) = 1 := Units.inv_mul _
  rw [← germ_res_secTop K (chartRing K ({t} : Set L)) (tma K t a) (U₁ K t a) p hp, ← map_mul, hu,
    map_one]

theorem germ_σ₂_mul (q : XInf K t) (hq : q ∈ U₂ K t a) :
    (XInf K t).presheaf.germ (U₂ K t a) q hq (σ₂ K t a) *
      algebraMap _ ((XInf K t).presheaf.stalk q) (gInf K t a) =
    algebraMap _ ((XInf K t).presheaf.stalk q) (tInvChart K t) := by
  have hu : ((((isUnit_res_gInf K t a).unit⁻¹ : (Γ(XInf K t, U₂ K t a))ˣ) : Γ(XInf K t, U₂ K t a)) *
      (XInf K t).presheaf.map (homOfLE (le_top : U₂ K t a ≤ ⊤)).op
        (secTop K (chartRing K ({t⁻¹} : Set L)) (gInf K t a))) = 1 := Units.inv_mul _
  rw [← germ_res_secTop K (chartRing K ({t⁻¹} : Set L)) (gInf K t a) (U₂ K t a) q hq,
    ← germ_res_secTop K (chartRing K ({t⁻¹} : Set L)) (tInvChart K t) (U₂ K t a) q hq, ← map_mul,
    σ₂, mul_assoc, hu, mul_one]

end LocalSections

section Values

variable [Fact (t ≠ 0)] (a : K)

def V₁ : (glued K t).Opens := ι₀ K t ''ᵁ U₁ K t a

def V₂ : (glued K t).Opens := ιInf K t ''ᵁ U₂ K t a

def Ua : (glued K t).Opens := V₁ K t a ⊔ V₂ K t a

theorem isAffineOpen_V₁ : IsAffineOpen (V₁ K t a) :=
  ((isAffineOpen_top (X₀ K t)).basicOpen _).image_of_isOpenImmersion (ι₀ K t)

theorem isAffineOpen_V₂ : IsAffineOpen (V₂ K t a) :=
  ((isAffineOpen_top (XInf K t)).basicOpen _).image_of_isOpenImmersion (ιInf K t)

def f₁' : Γ(glued K t, V₁ K t a) := ((ι₀ K t).appIso (U₁ K t a)).inv (σ₁ K t a)

def f₂' : Γ(glued K t, V₂ K t a) := ((ιInf K t).appIso (U₂ K t a)).inv (σ₂ K t a)

variable (ha : (t - algebraMap K L a) ≠ 0)

include ha in
omit [Fact (t ≠ 0)] in
theorem one_sub_ne_zero [Fact (t ≠ 0)] : (1 - algebraMap K L a * t⁻¹) ≠ 0 := by
  intro h
  apply ha
  have : t * (1 - algebraMap K L a * t⁻¹) = t - algebraMap K L a := by
    rw [mul_sub, mul_one, mul_left_comm, mul_inv_cancel₀ (Fact.out : t ≠ 0), mul_one]
  rw [← this, h, mul_zero]

include ha in
omit [Fact (t ≠ 0)] in

theorem genericPoint_mem_U₁ : genericPoint (X₀ K t) ∈ U₁ K t a := by
  rw [mem_U₁_iff, genericPoint_eq_bot_of_affine]
  intro h
  apply ha
  have h' : (tma K t a : L) = 0 := by
    rw [(Ideal.mem_bot.mp h : tma K t a = 0)]; rfl
  rwa [coe_tma] at h'

include ha in
theorem genericPoint_mem_U₂ : genericPoint (XInf K t) ∈ U₂ K t a := by
  rw [mem_U₂_iff, genericPoint_eq_bot_of_affine]
  intro h
  apply one_sub_ne_zero K t a ha
  have h' : (gInf K t a : L) = 0 := by
    rw [(Ideal.mem_bot.mp h : gInf K t a = 0)]; rfl
  rwa [coe_gInf] at h'

include ha in

theorem genericPoint_mem : genericPoint (glued K t) ∈ V₁ K t a ⊓ V₂ K t a :=
  ⟨⟨genericPoint (X₀ K t), genericPoint_mem_U₁ K t a ha,
    genericPoint_eq_of_isOpenImmersion (ι₀ K t)⟩,
   ⟨genericPoint (XInf K t), genericPoint_mem_U₂ K t a ha,
    genericPoint_eq_of_isOpenImmersion (ιInf K t)⟩⟩

variable [FiniteDimensional K⟮t⟯ L]

include ha in

theorem val_f₁' (hη : genericPoint (glued K t) ∈ V₁ K t a) :
    (gluedFunctionFieldEquiv K t).symm
        ((glued K t).presheaf.germ (V₁ K t a) (genericPoint (glued K t)) hη (f₁' K t a)) =
      (t - algebraMap K L a)⁻¹ := by
  have hp := genericPoint_mem_U₁ K t a ha
  have h1 : (gluedFunctionFieldEquiv K t).symm
        ((glued K t).presheaf.germ (V₁ K t a) (genericPoint (glued K t)) hη (f₁' K t a)) =
      thetaHom K t (chartRing K ({t} : Set L)) (incl₀ K t) (genericPoint (X₀ K t))
        ((X₀ K t).presheaf.germ (U₁ K t a) _ hp (σ₁ K t a)) :=
    ffEquiv_symm_germ_appIso_inv K t (chartRing K ({t} : Set L)) (ι₀ K t) (incl₀ K t)
      (fun b => coe_chartIncl K _ b) rfl (U₁ K t a) (σ₁ K t a) _ hp hη
  rw [h1]
  have h := congrArg (thetaHom K t (chartRing K ({t} : Set L)) (incl₀ K t) (genericPoint (X₀ K t)))
    (germ_σ₁_mul K t a _ hp)
  rw [map_mul, map_one, thetaHom_algebraMap K t _ (incl₀ K t) (fun b => coe_chartIncl K _ b),
    coe_tma] at h
  exact eq_inv_of_mul_eq_one_left h

include ha in

theorem val_f₂' (hη : genericPoint (glued K t) ∈ V₂ K t a) :
    (gluedFunctionFieldEquiv K t).symm
        ((glued K t).presheaf.germ (V₂ K t a) (genericPoint (glued K t)) hη (f₂' K t a)) =
      t⁻¹ * (1 - algebraMap K L a * t⁻¹)⁻¹ := by
  have hq := genericPoint_mem_U₂ K t a ha
  have h1 : (gluedFunctionFieldEquiv K t).symm
        ((glued K t).presheaf.germ (V₂ K t a) (genericPoint (glued K t)) hη (f₂' K t a)) =
      thetaHom K t (chartRing K ({t⁻¹} : Set L)) (inclInf K t) (genericPoint (XInf K t))
        ((XInf K t).presheaf.germ (U₂ K t a) _ hq (σ₂ K t a)) :=
    ffEquiv_symm_germ_appIso_inv K t (chartRing K ({t⁻¹} : Set L)) (ιInf K t) (inclInf K t)
      (fun b => coe_chartIncl K _ b) (glue_condition K t).symm (U₂ K t a) (σ₂ K t a) _ hq hη
  rw [h1]
  have h := congrArg (thetaHom K t (chartRing K ({t⁻¹} : Set L)) (inclInf K t)
    (genericPoint (XInf K t))) (germ_σ₂_mul K t a _ hq)
  rw [map_mul, thetaHom_algebraMap K t _ (inclInf K t) (fun b => coe_chartIncl K _ b),
    thetaHom_algebraMap K t _ (inclInf K t) (fun b => coe_chartIncl K _ b), coe_gInf,
    coe_tInvChart] at h
  exact (eq_mul_inv_iff_mul_eq₀ (one_sub_ne_zero K t a ha)).mpr h

include ha in

theorem res_f₁'_eq_res_f₂' (W : (glued K t).Opens) (h₁ : W ≤ V₁ K t a) (h₂ : W ≤ V₂ K t a)
    (hη : genericPoint (glued K t) ∈ W) :
    (glued K t).presheaf.map (homOfLE h₁).op (f₁' K t a) =
    (glued K t).presheaf.map (homOfLE h₂).op (f₂' K t a) := by
  apply germ_injective_of_isIntegral (glued K t) (genericPoint (glued K t)) hη
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  apply (gluedFunctionFieldEquiv K t).symm.injective
  rw [val_f₁' K t a ha, val_f₂' K t a ha, ← mul_inv, mul_sub, mul_one, mul_left_comm,
    mul_inv_cancel₀ (Fact.out : t ≠ 0), mul_one]

def cover : Bool → (glued K t).Opens := fun b => cond b (V₁ K t a) (V₂ K t a)

include ha in

theorem exists_glued_section : ∃ f : Γ(glued K t, Ua K t a),
    (glued K t).presheaf.map (homOfLE (le_sup_left : V₁ K t a ≤ Ua K t a)).op f = f₁' K t a ∧
    (glued K t).presheaf.map (homOfLE (le_sup_right : V₂ K t a ≤ Ua K t a)).op f = f₂' K t a := by
  have hη := genericPoint_mem K t a ha
  let sf : ∀ b : Bool, Γ(glued K t, cover K t a b) := fun b =>
    match b with
    | true => f₁' K t a
    | false => f₂' K t a
  have hcompat : TopCat.Presheaf.IsCompatible (glued K t).sheaf.1 (cover K t a) sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · exact (res_f₁'_eq_res_f₂' K t a ha (V₂ K t a ⊓ V₁ K t a) inf_le_right inf_le_left
        ⟨hη.2, hη.1⟩).symm
    · exact res_f₁'_eq_res_f₂' K t a ha (V₁ K t a ⊓ V₂ K t a) inf_le_left inf_le_right hη
    · rfl
  obtain ⟨f, hf, -⟩ := (glued K t).sheaf.existsUnique_gluing' (cover K t a) (Ua K t a)
    (fun b => match b with
      | true => homOfLE le_sup_left
      | false => homOfLE le_sup_right)
    (by change V₁ K t a ⊔ V₂ K t a ≤ iSup (cover K t a); rw [iSup_bool_eq]; exact le_rfl) sf hcompat
  exact ⟨f, hf true, hf false⟩

end Values

section Affine

variable [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] (a : K) (ha : (t - algebraMap K L a) ≠ 0)

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in

theorem f₀_appTop_secTop (r : chartRing K ({t} : Set L)) :
    (f₀ K t).appTop (secTop K _ r) = secTop K _ (incl₀ K t r) := by
  have := congrArg (fun g : CommRingCat.of (chartRing K ({t} : Set L)) ⟶ Γ(XOverlap K t, ⊤) => g r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (incl₀ K t).toRingHom))
  exact this.symm

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in
theorem fInf_appTop_secTop (r : chartRing K ({t⁻¹} : Set L)) :
    (fInf K t).appTop (secTop K _ r) = secTop K _ (inclInf K t r) := by
  have := congrArg (fun g : CommRingCat.of (chartRing K ({t⁻¹} : Set L)) ⟶ Γ(XOverlap K t, ⊤) =>
    g r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclInf K t).toRingHom))
  exact this.symm

omit [FiniteDimensional K⟮t⟯ L] in

theorem tma_not_mem_iff (p : X₀ K t) (q : XInf K t) (h : (ι₀ K t).base p = (ιInf K t).base q) :
    tma K t a ∉ p.asIdeal ↔ gInf K t a ∉ q.asIdeal := by
  obtain ⟨u, hu₀, hui⟩ := (ι₀_eq_ιInf_iff K t p q).mp h
  have key : incl₀ K t (tma K t a) ∉ u.asIdeal ↔ inclInf K t (gInf K t a) ∉ u.asIdeal := by
    rw [incl₀_tma]
    have ht : incl₀ K t (tChart K t) ∉ u.asIdeal := fun hmem =>
      u.isPrime.ne_top (u.asIdeal.eq_top_of_isUnit_mem hmem
        (IsUnit.of_mul_eq_one _ (incl₀_tChart_mul_inclInf_tInvChart K t)))
    constructor
    · exact fun hn hg => hn (u.asIdeal.mul_mem_left _ hg)
    · intro hg hn
      rcases u.isPrime.mem_or_mem hn with h' | h'
      · exact ht h'
      · exact hg h'

  rw [← hu₀, ← hui, ← mem_U₁_iff, ← mem_U₂_iff, ← Scheme.Hom.mem_preimage (f₀ K t),
    ← Scheme.Hom.mem_preimage (fInf K t), U₁, U₂, Scheme.preimage_basicOpen_top,
    Scheme.preimage_basicOpen_top, f₀_appTop_secTop, fInf_appTop_secTop, mem_basicOpen_secTop,
    mem_basicOpen_secTop]
  exact key

variable (f : Γ(glued K t, Ua K t a))
  (hf₁ : (glued K t).presheaf.map (homOfLE (le_sup_left : V₁ K t a ≤ Ua K t a)).op f = f₁' K t a)
  (hf₂ : (glued K t).presheaf.map (homOfLE (le_sup_right : V₂ K t a ≤ Ua K t a)).op f = f₂' K t a)

def fTwo : Γ(glued K t, Ua K t a) := 1 + cSec K t a (Ua K t a) * f

omit [FiniteDimensional K⟮t⟯ L] in
theorem span_eq_top : Ideal.span ({f, fTwo K t a f} : Set Γ(glued K t, Ua K t a)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
  exact ⟨-cSec K t a (Ua K t a), 1, by rw [fTwo]; ring⟩

include hf₁ in
omit [FiniteDimensional K⟮t⟯ L] in

theorem stalkMap_germ_f_V₁ (p : X₀ K t) (hp : p ∈ U₁ K t a) :
    (ι₀ K t).stalkMap p ((glued K t).presheaf.germ (Ua K t a) ((ι₀ K t).base p)
        (le_sup_left (α := (glued K t).Opens) ⟨p, hp, rfl⟩) f) =
      (X₀ K t).presheaf.germ (U₁ K t a) p hp (σ₁ K t a) := by
  have e : (glued K t).presheaf.germ (V₁ K t a) ((ι₀ K t).base p) ⟨p, hp, rfl⟩
      ((glued K t).presheaf.map (homOfLE (le_sup_left : V₁ K t a ≤ Ua K t a)).op f) =
      (glued K t).presheaf.germ (Ua K t a) ((ι₀ K t).base p)
        (le_sup_left (α := (glued K t).Opens) ⟨p, hp, rfl⟩) f :=
    TopCat.Presheaf.germ_res_apply (glued K t).presheaf _ _ _ f
  rw [← e, hf₁]
  exact stalkMap_germ_appIso_inv K t _ (ι₀ K t) (U₁ K t a) (σ₁ K t a) p hp

include hf₂ in
omit [FiniteDimensional K⟮t⟯ L] in

theorem stalkMap_germ_f_V₂ (q : XInf K t) (hq : q ∈ U₂ K t a) :
    (ιInf K t).stalkMap q ((glued K t).presheaf.germ (Ua K t a) ((ιInf K t).base q)
        (le_sup_right (α := (glued K t).Opens) ⟨q, hq, rfl⟩) f) =
      (XInf K t).presheaf.germ (U₂ K t a) q hq (σ₂ K t a) := by
  have e : (glued K t).presheaf.germ (V₂ K t a) ((ιInf K t).base q) ⟨q, hq, rfl⟩
      ((glued K t).presheaf.map (homOfLE (le_sup_right : V₂ K t a ≤ Ua K t a)).op f) =
      (glued K t).presheaf.germ (Ua K t a) ((ιInf K t).base q)
        (le_sup_right (α := (glued K t).Opens) ⟨q, hq, rfl⟩) f :=
    TopCat.Presheaf.germ_res_apply (glued K t).presheaf _ _ _ f
  rw [← e, hf₂]
  exact stalkMap_germ_appIso_inv K t _ (ιInf K t) (U₂ K t a) (σ₂ K t a) q hq

include hf₁ in
omit [FiniteDimensional K⟮t⟯ L] in

theorem stalkMap_germ_fTwo_V₁ (p : X₀ K t) (hp : p ∈ U₁ K t a) :
    (ι₀ K t).stalkMap p ((glued K t).presheaf.germ (Ua K t a) ((ι₀ K t).base p)
        (le_sup_left (α := (glued K t).Opens) ⟨p, hp, rfl⟩) (fTwo K t a f)) =
      1 + algebraMap (chartRing K ({t} : Set L)) ((X₀ K t).presheaf.stalk p) (algebraMap K _ a) *
        (X₀ K t).presheaf.germ (U₁ K t a) p hp (σ₁ K t a) := by
  simp only [fTwo, map_add, map_one, map_mul]
  rw [stalkMap_germ_cSec K t _ (ι₀ K t) (ι₀_gluedToBase K t), stalkMap_germ_f_V₁ K t a f hf₁ p hp]

include hf₂ in
omit [FiniteDimensional K⟮t⟯ L] in

theorem stalkMap_germ_fTwo_V₂ (q : XInf K t) (hq : q ∈ U₂ K t a) :
    (ιInf K t).stalkMap q ((glued K t).presheaf.germ (Ua K t a) ((ιInf K t).base q)
        (le_sup_right (α := (glued K t).Opens) ⟨q, hq, rfl⟩) (fTwo K t a f)) =
      1 + algebraMap (chartRing K ({t⁻¹} : Set L)) ((XInf K t).presheaf.stalk q)
          (algebraMap K _ a) * (XInf K t).presheaf.germ (U₂ K t a) q hq (σ₂ K t a) := by
  simp only [fTwo, map_add, map_one, map_mul]
  rw [stalkMap_germ_cSec K t _ (ιInf K t) (ιInf_gluedToBase K t),
    stalkMap_germ_f_V₂ K t a f hf₂ q hq]

include hf₁ hf₂ in
omit [FiniteDimensional K⟮t⟯ L] in

theorem basicOpen_f : (glued K t).basicOpen f = V₁ K t a := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU, hunit⟩ := (Scheme.mem_basicOpen'' _ _ _).mp hx
    rcases Opens.mem_sup.mp hxU with h₁ | h₂
    · exact h₁
    ·

      obtain ⟨q, hq, hqx⟩ := h₂
      have hq' : q ∈ U₂ K t a := hq
      have hunit' : IsUnit ((glued K t).presheaf.germ (Ua K t a) ((ιInf K t).base q)
          (le_sup_right (α := (glued K t).Opens) ⟨q, hq', rfl⟩) f) := by
        subst hqx; exact hunit
      have hu := (isUnit_stalkMap_iff K t _ (ιInf K t) q _).mpr hunit'
      rw [stalkMap_germ_f_V₂ K t a f hf₂ q hq'] at hu
      have hg : IsUnit (algebraMap (chartRing K ({t⁻¹} : Set L)) ((XInf K t).presheaf.stalk q)
          (gInf K t a)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff ((XInf K t).presheaf.stalk q) q.asIdeal
          (gInf K t a)).mpr ((mem_U₂_iff K t a q).mp hq')
      have hu' := hu.mul hg
      rw [germ_σ₂_mul] at hu'
      have htinv : tInvChart K t ∉ q.asIdeal :=
        (IsLocalization.AtPrime.isUnit_to_map_iff ((XInf K t).presheaf.stalk q) q.asIdeal _).mp hu'
      obtain ⟨p, hp⟩ := (ιInf_mem_range_ι₀_iff K t q).mpr htinv
      rw [← hqx]
      refine ⟨p, ?_, hp⟩
      rw [SetLike.mem_coe, mem_U₁_iff, tma_not_mem_iff K t a p q hp, ← mem_U₂_iff]
      exact hq'
  · rintro x ⟨p, hp, hpx⟩
    have hp' : p ∈ U₁ K t a := hp
    subst hpx
    show (ι₀ K t).base p ∈ (glued K t).basicOpen f
    refine (Scheme.mem_basicOpen'' _ _ _).mpr
      ⟨le_sup_left (α := (glued K t).Opens) ⟨p, hp', rfl⟩, ?_⟩
    refine (isUnit_stalkMap_iff K t _ (ι₀ K t) p _).mp ?_
    rw [stalkMap_germ_f_V₁ K t a f hf₁ p hp']
    exact IsUnit.of_mul_eq_one _ (germ_σ₁_mul K t a p hp')

include hf₁ hf₂ in
omit [FiniteDimensional K⟮t⟯ L] in

theorem basicOpen_fTwo : (glued K t).basicOpen (fTwo K t a f) = V₂ K t a := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU, hunit⟩ := (Scheme.mem_basicOpen'' _ _ _).mp hx
    rcases Opens.mem_sup.mp hxU with h₁ | h₂
    ·

      obtain ⟨p, hp, hpx⟩ := h₁
      have hp' : p ∈ U₁ K t a := hp
      have hunit' : IsUnit ((glued K t).presheaf.germ (Ua K t a) ((ι₀ K t).base p)
          (le_sup_left (α := (glued K t).Opens) ⟨p, hp', rfl⟩) (fTwo K t a f)) := by
        subst hpx; exact hunit
      have hu := (isUnit_stalkMap_iff K t _ (ι₀ K t) p _).mpr hunit'
      rw [stalkMap_germ_fTwo_V₁ K t a f hf₁ p hp'] at hu
      have htma : IsUnit (algebraMap (chartRing K ({t} : Set L)) ((X₀ K t).presheaf.stalk p)
          (tma K t a)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff ((X₀ K t).presheaf.stalk p) p.asIdeal
          (tma K t a)).mpr ((mem_U₁_iff K t a p).mp hp')
      have hu' := hu.mul htma
      rw [add_mul, one_mul, mul_assoc, germ_σ₁_mul, mul_one, ← map_add, tma_add] at hu'
      have htc : tChart K t ∉ p.asIdeal :=
        (IsLocalization.AtPrime.isUnit_to_map_iff ((X₀ K t).presheaf.stalk p) p.asIdeal _).mp hu'
      obtain ⟨q, hq⟩ := (ι₀_mem_range_ιInf_iff K t p).mpr htc
      rw [← hpx]
      refine ⟨q, ?_, hq⟩
      rw [SetLike.mem_coe, mem_U₂_iff, ← tma_not_mem_iff K t a p q hq.symm, ← mem_U₁_iff]
      exact hp'
    · exact h₂
  · rintro x ⟨q, hq, hqx⟩
    have hq' : q ∈ U₂ K t a := hq
    subst hqx
    show (ιInf K t).base q ∈ (glued K t).basicOpen (fTwo K t a f)
    refine (Scheme.mem_basicOpen'' _ _ _).mpr
      ⟨le_sup_right (α := (glued K t).Opens) ⟨q, hq', rfl⟩, ?_⟩
    refine (isUnit_stalkMap_iff K t _ (ιInf K t) q _).mp ?_
    rw [stalkMap_germ_fTwo_V₂ K t a f hf₂ q hq']

    refine IsUnit.of_mul_eq_one (algebraMap _ ((XInf K t).presheaf.stalk q) (gInf K t a)) ?_
    rw [add_mul, one_mul, mul_assoc, germ_σ₂_mul, ← map_mul, ← map_add, gInf_add, map_one]

include hf₁ hf₂ in
omit [FiniteDimensional K⟮t⟯ L] in

theorem isAffineOpen_Ua_of : IsAffineOpen (Ua K t a) := by
  apply isAffineOpen_of_isAffineOpen_basicOpen (Ua K t a) {f, fTwo K t a f} (span_eq_top K t a f)
  intro g hg
  rcases hg with hg | hg
  · rw [hg, basicOpen_f K t a f hf₁ hf₂]; exact isAffineOpen_V₁ K t a
  · rw [Set.mem_singleton_iff.mp hg, basicOpen_fTwo K t a f hf₁ hf₂]; exact isAffineOpen_V₂ K t a

include ha in
theorem isAffineOpen_Ua : IsAffineOpen (Ua K t a) := by
  obtain ⟨f, hf₁, hf₂⟩ := exists_glued_section K t a ha
  exact isAffineOpen_Ua_of K t a f hf₁ hf₂

omit [FiniteDimensional K⟮t⟯ L] in
theorem ιInf_mem_Ua (q : XInf K t) (hq : gInf K t a ∉ q.asIdeal) : (ιInf K t).base q ∈ Ua K t a :=
  Opens.mem_sup.mpr (Or.inr ⟨q, (mem_U₂_iff K t a q).mpr hq, rfl⟩)

omit [FiniteDimensional K⟮t⟯ L] in
theorem ι₀_mem_Ua (p : X₀ K t) (hp : tma K t a ∉ p.asIdeal) : (ι₀ K t).base p ∈ Ua K t a :=
  Opens.mem_sup.mpr (Or.inl ⟨p, (mem_U₁_iff K t a p).mpr hp, rfl⟩)

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in

theorem subsingleton_gInf_mem (q : XInf K t) : {a : K | gInf K t a ∈ q.asIdeal}.Subsingleton := by
  intro a ha' b hb'
  by_contra hab
  have hsub : gInf K t b - gInf K t a = algebraMap K _ (a - b) * tInvChart K t := by
    rw [gInf, gInf, map_sub]; ring
  have hmem : algebraMap K _ (a - b) * tInvChart K t ∈ q.asIdeal := hsub ▸ q.asIdeal.sub_mem hb' ha'
  have hunit : IsUnit (algebraMap K (chartRing K ({t⁻¹} : Set L)) (a - b)) :=
    (IsUnit.mk0 _ (sub_ne_zero.mpr hab)).map _
  have htinv : tInvChart K t ∈ q.asIdeal := by
    rcases q.isPrime.mem_or_mem hmem with h | h
    · exact absurd (q.asIdeal.eq_top_of_isUnit_mem h hunit) q.isPrime.ne_top
    · exact h
  have h1 : (1 : chartRing K ({t⁻¹} : Set L)) ∈ q.asIdeal := by
    have := q.asIdeal.add_mem ha' (q.asIdeal.mul_mem_left (algebraMap K _ a) htinv)
    rwa [gInf, sub_add_cancel] at this
  exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

omit [FiniteDimensional K⟮t⟯ L] in

theorem finite_setOf_not_mem_Ua (x : glued K t) : {a : K | x ∉ Ua K t a}.Finite := by
  have hInf : ∀ q : XInf K t, {a : K | (ιInf K t).base q ∉ Ua K t a}.Finite := fun q =>
    (subsingleton_gInf_mem K t q).finite.subset fun a ha' => by
      by_contra h
      exact ha' (ιInf_mem_Ua K t a q h)
  rcases mem_range_ι₀_or_mem_range_ιInf K t x with ⟨p, hpx⟩ | ⟨q, hqx⟩
  · by_cases htc : tChart K t ∈ p.asIdeal
    · refine (Set.finite_singleton (0 : K)).subset fun a ha' => ?_
      by_contra h0
      apply ha'
      rw [← hpx]
      apply ι₀_mem_Ua
      intro hmem
      have hal : algebraMap K _ a ∈ p.asIdeal := by
        have := p.asIdeal.sub_mem htc hmem
        rwa [← tma_add K t a, add_sub_cancel_left] at this
      exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hal ((IsUnit.mk0 _ h0).map _))
    · obtain ⟨q, hq⟩ := (ι₀_mem_range_ιInf_iff K t p).mpr htc
      rw [← hpx, ← hq]
      exact hInf q
  · rw [← hqx]
    exact hInf q

end Affine

section Packaging

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]

theorem finset_subset_affineOpen_glued :
    ∀ F : Finset (glued K t), ∃ U : (glued K t).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
  intro F
  have hfin : ((⋃ x ∈ (F : Set (glued K t)), {a : K | x ∉ Ua K t a}) ∪
      {a : K | t - algebraMap K L a = 0}).Finite := by
    refine (F.finite_toSet.biUnion fun x _ => finite_setOf_not_mem_Ua K t x).union ?_
    refine Set.Subsingleton.finite fun a ha' b hb' => ?_
    apply (algebraMap K L).injective
    have ha'' : t - algebraMap K L a = 0 := ha'
    have hb'' : t - algebraMap K L b = 0 := hb'
    rw [sub_eq_zero] at ha'' hb''
    rw [← ha'', ← hb'']
  haveI : Infinite K := Infinite.of_injective _ Nat.cast_injective
  obtain ⟨a, ha⟩ := hfin.exists_notMem
  refine ⟨Ua K t a, isAffineOpen_Ua K t a (fun h => ha (Or.inr h)), fun x hx => ?_⟩
  by_contra h
  exact ha (Or.inl (Set.mem_iUnion₂.mpr ⟨x, Finset.mem_coe.mpr hx, h⟩))

variable [FiniteDimensional K⟮t⁻¹⟯ L]

def ofGenerator (ht : Transcendental K t) : CurveModel K L :=
  haveI := smoothOfRelativeDimension_one_gluedToBase K t ht
  { C := glued K t
    toBase := gluedToBase K t
    ffEquiv := gluedFunctionFieldEquiv K t
    ffEquiv_algebraMap := gluedFunctionFieldEquiv_algebraMap K t
    placeOfPoint := gluedPlaceOfPoint K t ht
    placeOfPoint_bijective := gluedPlaceOfPoint_bijective K t ht
    range_stalk_eq := range_stalk_eq_gluedPlaceOfPoint K t ht
    finset_subset_affineOpen := finset_subset_affineOpen_glued K t }

end Packaging

section TowerPack

variable [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L]

def towerGenerator : L := algebraMap (RatFunc K) L RatFunc.X

omit [Algebra K L] [IsScalarTower K (RatFunc K) L] in
theorem towerGenerator_ne_zero : towerGenerator K (L := L) ≠ 0 := by
  rw [towerGenerator, map_ne_zero_iff _ (algebraMap (RatFunc K) L).injective]
  exact RatFunc.X_ne_zero

theorem transcendental_towerGenerator : Transcendental K (towerGenerator K (L := L)) := by
  rw [towerGenerator, transcendental_algebraMap_iff (algebraMap (RatFunc K) L).injective]
  exact RatFunc.transcendental_X

theorem coe_algEquivOfTranscendental_towerGenerator (u : RatFunc K) :
    ((RatFunc.algEquivOfTranscendental (towerGenerator K (L := L))
        (transcendental_towerGenerator K) u : K⟮towerGenerator K (L := L)⟯) : L) =
      algebraMap (RatFunc K) L u := by
  set e := RatFunc.algEquivOfTranscendental (towerGenerator K (L := L))
    (transcendental_towerGenerator K) with he
  let φ₁ : RatFunc K →+* L :=
    (algebraMap K⟮towerGenerator K (L := L)⟯ L).comp e.toRingEquiv.toRingHom
  suffices h : φ₁ = algebraMap (RatFunc K) L from RingHom.congr_fun h u
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial K))
  apply Polynomial.ringHom_ext
  · intro a
    simp only [φ₁, RingHom.comp_apply, Polynomial.C_eq_algebraMap]
    rw [← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
      ← IsScalarTower.algebraMap_apply K (RatFunc K) L]
    show algebraMap (↥K⟮towerGenerator K (L := L)⟯) L (e (algebraMap K (RatFunc K) a)) = _
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  · simp only [φ₁, RingHom.comp_apply, RatFunc.algebraMap_X]
    show algebraMap (↥K⟮towerGenerator K (L := L)⟯) L (e RatFunc.X) = _
    rw [IntermediateField.algebraMap_apply, he, RatFunc.algEquivOfTranscendental_X]
    rfl

omit [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L] in

theorem adjoin_simple_inv_eq (x : L) : K⟮x⁻¹⟯ = K⟮x⟯ :=
  le_antisymm (adjoin_simple_le_iff.mpr (inv_mem (mem_adjoin_simple_self K x)))
    (adjoin_simple_le_iff.mpr (by simpa using inv_mem (mem_adjoin_simple_self K x⁻¹)))

omit [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L] in
theorem finiteDimensional_congr {F F' : IntermediateField K L} (h : F = F')
    [hF : FiniteDimensional F L] : FiniteDimensional F' L := by
  subst h; exact hF

theorem finiteDimensional_adjoin_towerGenerator [FiniteDimensional (RatFunc K) L] :
    FiniteDimensional K⟮towerGenerator K (L := L)⟯ L ∧
      FiniteDimensional K⟮(towerGenerator K (L := L))⁻¹⟯ L := by
  have h₁ : FiniteDimensional K⟮towerGenerator K (L := L)⟯ L := by
    let e := RatFunc.algEquivOfTranscendental (towerGenerator K (L := L))
      (transcendental_towerGenerator K)
    letI : Algebra (RatFunc K) K⟮towerGenerator K (L := L)⟯ := e.toAlgHom.toRingHom.toAlgebra
    haveI : IsScalarTower (RatFunc K) K⟮towerGenerator K (L := L)⟯ L :=
      IsScalarTower.of_algebraMap_eq
        (fun u => (coe_algEquivOfTranscendental_towerGenerator K u).symm)
    exact Module.Finite.of_restrictScalars_finite (RatFunc K) _ L
  exact ⟨h₁, finiteDimensional_congr K (adjoin_simple_inv_eq K _).symm⟩

theorem nonempty_body (K L : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Field L]
    [Algebra K L] [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] : Nonempty (CurveModel K L) := by
  haveI : Fact (towerGenerator K (L := L) ≠ 0) := ⟨towerGenerator_ne_zero K⟩
  obtain ⟨h₁, h₂⟩ := finiteDimensional_adjoin_towerGenerator K (L := L)
  haveI := h₁
  haveI := h₂
  exact ⟨ofGenerator K (towerGenerator K (L := L)) (transcendental_towerGenerator K)⟩

end TowerPack

end CurveModel

end AlgebraicCurve

end


