-- Prove2me | Definitions.Def_OAIErdos3B114
-- name    : OAIErdos3B114
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T04:35:00.857445+00:00
-- url     : https://prove2.me/theorems/b9f71170-7353-445f-a6e3-9be6e69aefb0
-- title:
--   OpenAI Erdős-3 split, definitions bundle 115 of 132
-- statement:
--   Definitions bundle 115 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B113`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 115 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDensity_empty`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDensity_law`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDensity_mass`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDensity_measurable`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDensity_nonneg`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientLayers_law`, `OAI.Erdos3.canonicalArrayDensity_law`, `OAI.Erdos3.canonicalArrayDensity_mass`, `OAI.Erdos3.canonicalArrayDensity_measurable`, `OAI.Erdos3.canonicalArrayDensity_nonneg`, `OAI.Erdos3.canonicalMixedDensity_bound`, `OAI.Erdos3.canonicalMixedDensity_constant_cap`, `OAI.Erdos3.canonicalMixedDensity_empty`, `OAI.Erdos3.canonicalMixedDensity_law`, `OAI.Erdos3.canonicalMixedDensity_mass`, `OAI.Erdos3.canonicalMixedDensity_measurable`, `OAI.Erdos3.canonicalMixedDensity_nonneg`, `OAI.Erdos3.mixedCoefficient_quotient_law`, `OAI.Erdos3.normalizedLatticePoint_continuous`, `OAI.Erdos3.normalizedLatticeQuotient_embedding`, `OAI.Erdos3.normalizedLatticeQuotient_map_restrict`, `OAI.Erdos3.normalizedQuotientDensity_bound`, `OAI.Erdos3.normalizedQuotientDensity_law`, `OAI.Erdos3.normalizedQuotientDensity_measurable`, `OAI.Erdos3.normalizedQuotientDensity_nonneg`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B044

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module _root_.Set
open scoped ENNReal

variable {E T I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

theorem normalizedLatticePoint_continuous (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) : Continuous (normalizedLatticePoint W b) := by
  unfold normalizedLatticePoint
  fun_prop

theorem normalizedLatticeQuotient_embedding (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    MeasurableEmbedding
      (fun x : normalizedLatticePoint W b ⁻¹' Ω => normalizedLatticeQuotient W b hb x.val) :=
  translatedQuotientChart_embedding _ _ (hΩm.preimage (normalizedLatticePoint_continuous W b).measurable)
    (normalizedLatticeQuotient_injOn W b hb hΩ)

theorem normalizedLatticeQuotient_map_restrict (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Measure.map (normalizedLatticeQuotient W b hb)
      ((volume.prod (Measure.count : Measure (Fin n → ℤ))).restrict
        (normalizedLatticePoint W b ⁻¹' Ω)) =
      ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)) •
        μ.restrict (normalizedLatticeQuotient W b hb '' (normalizedLatticePoint W b ⁻¹' Ω)) :=
  translatedQuotientChart_map_restrict _ (Free.chooseBasis ℤ _) μ _
    (hΩm.preimage (normalizedLatticePoint_continuous W b).measurable)
    (normalizedLatticeQuotient_injOn W b hb hΩ)

end Erdos3

end

section

namespace Erdos3

open Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)

variable [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledArrayLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

theorem normalizedQuotientDensity_measurable (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) (hf : Measurable f) :
    Measurable (normalizedQuotientDensity W b hb Ω f) :=
  embeddingDensity_measurable _ (normalizedLatticeQuotient_embedding W b hb hΩm hΩ) _ _
    (hf.comp measurable_subtype_coe)

theorem normalizedQuotientDensity_nonneg (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) (hf : ∀ x, 0 ≤ f x) (y) :
    0 ≤ normalizedQuotientDensity W b hb Ω f y :=
  embeddingDensity_nonneg _ (normalizedLatticeQuotient_embedding W b hb hΩm hΩ).injective
    (ZLattice.covolume_pos (latticeSection (standardEuclideanLattice D) W) volume).le _
    (fun x => hf x.val) y

theorem normalizedQuotientDensity_bound (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x, ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) * f x ≤ B) (y) :
    normalizedQuotientDensity W b hb Ω f y ≤ B :=
  embeddingDensity_bound _ (normalizedLatticeQuotient_embedding W b hb hΩm hΩ).injective hB _
    (fun x => hf x.val) y

theorem normalizedQuotientDensity_law (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) (hf : ∀ x, normalizedLatticePoint W b x ∉ Ω → f x = 0) :
    Measure.map (normalizedLatticeQuotient W b hb)
      (realDensityMeasure (volume.prod (Measure.count : Measure (Fin n → ℤ))) f) =
      realDensityMeasure μ (normalizedQuotientDensity W b hb Ω f) :=
  restrictedChartDensity_law _ (normalizedLatticeQuotient_measurable W b hb)
    (hΩm.preimage (normalizedLatticePoint_continuous W b).measurable)
    (normalizedLatticeQuotient_embedding W b hb hΩm hΩ) _ μ
    (ZLattice.covolume_pos (latticeSection (standardEuclideanLattice D) W) volume).le
    (normalizedLatticeQuotient_map_restrict W b hb μ hΩm hΩ) f hf

end Erdos3

end

section

namespace Erdos3

open Module Submodule _root_.Set

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

theorem mixedCoefficient_quotient_law (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (e : OrthonormalBasis I ℝ W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : (Fin n) → PMF ℤ)
    (hsupport : ∀ x, mixedCoefficientDensity c w p x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart e x) ∈ Ω) :
    Measure.map (fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart e x))
      (mixedCoefficientLaw c w p) =
      realDensityMeasure μ (normalizedQuotientDensity W b hb Ω (orthonormalMixedDensity e c w p)) := by
  change Measure.map (normalizedLatticeQuotient W b hb ∘ orthonormalMixedChart e)
    (mixedCoefficientLaw c w p) = _
  rw [← Measure.map_map (normalizedLatticeQuotient_measurable W b hb) (orthonormalMixedChart e).measurable,
    orthonormalMixedDensity_law e c w hw p]
  apply normalizedQuotientDensity_law W b hb μ hΩm hΩ
  intro x hx
  by_contra hf
  have h := hsupport ((orthonormalMixedChart e).symm x) hf
  rw [(orthonormalMixedChart e).apply_symm_apply] at h
  exact hx h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalMixedDensity_measurable (c w : I → ℝ) (p : Fin n → PMF ℤ) :
    Measurable (canonicalMixedDensity W b hb o c w p) :=
  normalizedQuotientDensity_measurable W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) _ (orthonormalMixedDensity_measurable o c w p)

theorem canonicalMixedDensity_nonneg
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ) (y) :
    0 ≤ canonicalMixedDensity W b hb o c w p y :=
  normalizedQuotientDensity_nonneg W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) _ (orthonormalMixedDensity_nonneg o c w hw p) y

theorem canonicalMixedDensity_bound
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ) (y) :
    canonicalMixedDensity W b hb o c w p y ≤
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) * profileWidthFactor w := by
  have hv := (ZLattice.covolume_pos (latticeSection (standardEuclideanLattice D) W) volume).le
  exact normalizedQuotientDensity_bound W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) _ (mul_nonneg hv (profileWidthFactor_pos w hw).le)
    (fun x => mul_le_mul_of_nonneg_left (mixedCoefficientDensity_width_cap c w hw p ((orthonormalMixedChart o).symm x)) hv) y

theorem canonicalMixedDensity_law
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Measure.map (fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart o x))
      (mixedCoefficientLaw c w p) = realDensityMeasure μ (canonicalMixedDensity W b hb o c w p) :=
  mixedCoefficient_quotient_law W b hb o μ (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) c w hw p hs

theorem canonicalMixedDensity_mass
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Integrable (canonicalMixedDensity W b hb o c w p) μ ∧
      (∫ y, canonicalMixedDensity W b hb o c w p y ∂μ) = 1 := by
  have hlaw := canonicalMixedDensity_law W b hb o μ c w hw p hs
  let : IsProbabilityMeasure (mixedCoefficientLaw c w p) := mixedCoefficientLaw_probability c w hw p
  let : IsProbabilityMeasure (realDensityMeasure μ (canonicalMixedDensity W b hb o c w p)) := by
    rw [← hlaw]
    exact Measure.isProbabilityMeasure_map
      ((normalizedLatticeQuotient_measurable W b hb).comp (orthonormalMixedChart o).measurable).aemeasurable
  exact boundedDensity_mass μ _ (canonicalMixedDensity_measurable W b hb o c w p)
    (canonicalMixedDensity_nonneg W b hb o c w hw p) (canonicalMixedDensity_bound W b hb o c w hw p)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalConstantDensityBound
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators

theorem canonicalMixedDensity_constant_cap {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)
    {R V : ℝ} (hR : 0 < R) (hV : 0 ≤ V) (hv : mixedDensityCovolumeRatio W b ≤ V)
    (y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :
    canonicalMixedDensity W b hb o (fun _ => 0) (fun _ => R / 4)
        (latticeConstantMass W b (fun _ => R / 4) (fun _ => div_pos hR (by norm_num))) y ≤
      earlyConstantDensityCap (Fintype.card I) n R V := by
  have hvolume : ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) ≤
      V * ∏ i, (basisAxisScale b i : ℝ) :=
    (div_le_iff₀ (Finset.prod_pos (fun i _ => basisAxisScale_cast_pos b i))).mp hv
  have hbound (x : W × (Fin n → ℤ)) :
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        orthonormalMixedDensity o (fun _ => 0) (fun _ => R / 4)
          (latticeConstantMass W b (fun _ => R / 4) (fun _ => div_pos hR (by norm_num))) x ≤
        earlyConstantDensityCap (Fintype.card I) n R V := by
    change ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
      constantCoefficientDensity (fun _ : I => R / 4) (fun i => (basisAxisScale b i : ℝ))
        (fun _ => R / 4) (basisAxisScale_cast_pos b) (fun _ => div_pos hR (by norm_num))
        ((orthonormalMixedChart o).symm x) ≤ _
    have hc := constantCoefficientDensity_cap (fun _ : I => R / 4)
      (fun _ => div_pos hR (by norm_num)) (fun i => (basisAxisScale b i : ℝ))
      (fun _ => R / 4) (basisAxisScale_cast_pos b) (fun _ => div_pos hR (by norm_num))
      hV hvolume ((orthonormalMixedChart o).symm x)
    exact hc.trans_eq (by simp only [earlyConstantDensityCap, profileWidthFactor,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  exact normalizedQuotientDensity_bound W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Set.Subset.rfl) _ (earlyConstantDensityCap_nonneg _ _ hR hV) hbound y

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EmptyCoefficientDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalArrayDensity_measurable (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ) :
    Measurable (canonicalArrayDensity W b hb o c w p) :=
  Finset.measurable_prod _ (fun j _ =>
    (canonicalMixedDensity_measurable W b hb o _ _ _).comp (measurable_pi_apply j))

theorem canonicalArrayDensity_nonneg
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ) (y) :
    0 ≤ canonicalArrayDensity W b hb o c w p y :=
  Finset.prod_nonneg (fun j _ => canonicalMixedDensity_nonneg W b hb o _ _ (fun i => hw i j) _ _)

theorem canonicalArrayDensity_mass
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ)
    (hs : ∀ j x, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun i => p i j) x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Integrable (canonicalArrayDensity W b hb o c w p) (Measure.pi (fun _ : J => μ)) ∧
      (∫ y, canonicalArrayDensity W b hb o c w p y ∂Measure.pi (fun _ : J => μ)) = 1 := by
  have hslot (j) := canonicalMixedDensity_mass W b hb o μ _ _ (fun i => hw i j) _ (hs j)
  refine ⟨Integrable.fintype_prod_dep (fun j => (hslot j).1), ?_⟩
  unfold canonicalArrayDensity
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one (fun j _ => (hslot j).2)

theorem canonicalArrayDensity_law
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ)
    (hs : ∀ j x, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun i => p i j) x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Measure.map (mixedArrayQuotient W b hb o) (mixedScalarArrayLaw c w p) =
      realDensityMeasure (Measure.pi (fun _ : J => μ)) (canonicalArrayDensity W b hb o c w p) := by
  let q := fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart o x)
  have hq : Measurable q := (normalizedLatticeQuotient_measurable W b hb).comp (orthonormalMixedChart o).measurable
  have hqa : Measurable (fun x : J → (I → ℝ) × (Fin n → ℤ) => fun j => q (x j)) :=
    measurable_pi_iff.mpr (fun j => hq.comp (measurable_pi_apply j))
  change Measure.map ((fun x j => q (x j)) ∘ mixedArrayRegroup I (Fin n) J) (mixedScalarArrayLaw c w p) = _
  rw [← Measure.map_map hqa (mixedArrayRegroup I (Fin n) J).measurable, mixedScalarArrayLaw_regroup c w hw p]
  exact productDensity_pushforward _ (fun _ : J => μ) (fun _ => q) (fun _ => hq)
    (fun j => canonicalMixedDensity W b hb o (fun i => c i j) (fun i => w i j) (fun i => p i j))
    (fun j => (canonicalMixedDensity_mass W b hb o μ _ _ (fun i => hw i j) _ (hs j)).1)
    (fun j => canonicalMixedDensity_nonneg W b hb o _ _ (fun i => hw i j) _)
    (fun j => canonicalMixedDensity_law W b hb o μ _ _ (fun i => hw i j) _ (hs j))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

theorem canonicalCoefficientDensity_measurable
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)] :
    Measurable (canonicalCoefficientDensity U b hb o c w p) := by
  apply Finset.measurable_prod
  intro j _
  exact (canonicalArrayDensity_measurable _ (b j) (hb j) (o j) (c j) (w j) (p j)).comp
    ((measurable_pi_apply j).comp (euclideanCoefficientEquiv_continuous U).measurable)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem canonicalCoefficientDensity_nonneg (hw : ∀ j i d, 0 < w j i d)
    (y : CoefficientTorus (K := K) U) : 0 ≤ canonicalCoefficientDensity U b hb o c w p y :=
  Finset.prod_nonneg (fun j _ => canonicalArrayDensity_nonneg _ (b j) (hb j) (o j)
    (c j) (w j) (hw j) (p j) _)

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (hw : ∀ j i d, 0 < w j i d)
variable (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
  (fun i => p j i d) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
    (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))

include ν hw hs

theorem canonicalCoefficientDensity_mass :
    Integrable (canonicalCoefficientDensity U b hb o c w p) μ ∧
      (∫ y, canonicalCoefficientDensity U b hb o c w p y ∂μ) = 1 := by
  let f := fun j => canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
  have hm (j) := canonicalArrayDensity_mass _ (b j) (hb j) (o j) (ν j) (c j) (w j) (hw j) (p j) (hs j)
  have hi : Integrable (tensorCutoffWeight f)
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))) :=
    Integrable.fintype_prod_dep (fun j => (hm j).1)
  have hp := euclideanCoefficient_measurePreserving U μ ν
  refine ⟨hp.integrable_comp_of_integrable hi, ?_⟩
  have he := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (tensorCutoffWeight f) (Measure.map (euclideanCoefficientEquiv U) μ) from
      hp.map_eq.symm ▸ hi.aestronglyMeasurable)
  change (∫ y, tensorCutoffWeight f (euclideanCoefficientEquiv U y) ∂μ) = 1
  rw [← he, hp.map_eq]
  change (∫ y : EuclideanCoefficientLayers (K := K) U, (∏ j, f j (y j))
    ∂Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))) = 1
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one (fun j _ => (hm j).2)

omit [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)] in
theorem canonicalCoefficientLayers_law :
    Measure.map (fun a : CoefficientSamplerArrays (K := K) I n => fun j =>
      mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (a j))
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) =
      realDensityMeasure
        (Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)))
        (fun y : EuclideanCoefficientLayers (K := K) U => ∏ j,
          canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j)
            (c j) (w j) (p j) (y j)) := by
  let f := fun j => canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
  let q := fun j => mixedArrayQuotient (J := BoundedCoefficientExponent K (j.val + 1))
    (euclideanSubspace (U j)) (b j) (hb j) (o j)
  let : ∀ j, IsProbabilityMeasure
      (Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)) :=
    fun j => Measure.pi.instIsProbabilityMeasure _
  have hq (j) : Measurable (q j) := mixedArrayQuotient_measurable _ (b j) (hb j) (o j)
  have hm (j) := canonicalArrayDensity_mass _ (b j) (hb j) (o j) (ν j) (c j) (w j) (hw j) (p j) (hs j)
  exact productDensity_pushforward (fun j => mixedScalarArrayLaw (c j) (w j) (p j))
    (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)) q hq f
    (fun j => (hm j).1)
    (fun j => canonicalArrayDensity_nonneg _ (b j) (hb j) (o j) (c j) (w j) (hw j) (p j))
    (fun j => canonicalArrayDensity_law _ (b j) (hb j) (o j) (ν j) (c j) (w j) (hw j) (p j) (hs j))

theorem canonicalCoefficientDensity_law :
    Measure.map (canonicalCoefficientSample (K := K) U b hb o)
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) =
        realDensityMeasure μ (canonicalCoefficientDensity U b hb o c w p) := by
  let q := fun a : CoefficientSamplerArrays (K := K) I n => fun j =>
    mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (a j)
  let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))
  let e := euclideanCoefficientMeasurableEquiv (K := K) U
  have hq : Measurable q := measurable_pi_iff.mpr (fun j =>
    (mixedArrayQuotient_measurable _ (b j) (hb j) (o j)).comp (measurable_pi_apply j))
  have hp : Measure.map e μ = ξ := (euclideanCoefficient_measurePreserving U μ ν).map_eq
  have hinv : Measure.map e.symm ξ = μ := by rw [← hp]; exact e.map_symm_map
  change Measure.map (e.symm ∘ q) _ = _
  rw [← Measure.map_map e.symm.measurable hq,
    canonicalCoefficientLayers_law U b hb o c w p ν hw hs,
    realDensityMeasure_map_equiv, hinv]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators

theorem canonicalMixedDensity_empty
    {D I : Type*} [Fintype D] [Fintype I] [IsEmpty D] [IsEmpty I]
    {n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W)
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → ℝ) (p : Fin n → PMF ℤ)
    (y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :
    canonicalMixedDensity W b hb o c w p y = 1 := by
  let Q := W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let : Subsingleton Q := ⟨by
    intro x y
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact congrArg QuotientAddGroup.mk (Subsingleton.elim x y)⟩
  let μ : Measure Q := probabilityAddHaar Q
  let : IsProbabilityMeasure μ := probabilityAddHaar_probability Q
  let : μ.IsAddLeftInvariant := probabilityAddHaar_invariant Q
  have hmass := (canonicalMixedDensity_mass W b hb o μ c w
    (fun i => isEmptyElim i) p (fun _ _ i => isEmptyElim i)).2
  have hconst : canonicalMixedDensity W b hb o c w p =
      fun _ => canonicalMixedDensity W b hb o c w p y := by
    funext z
    exact congrArg (canonicalMixedDensity W b hb o c w p) (Subsingleton.elim z y)
  rw [hconst] at hmass
  simpa using hmass

namespace VectorPolynomial

theorem canonicalCoefficientDensity_empty
    {K : Type*} [Fintype K] {m : ℕ}
    {J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
    [∀ j, IsEmpty (J j)] [∀ j, IsEmpty (I j)]
    {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (y : CoefficientTorus (K := K) U) :
    canonicalCoefficientDensity U b hb o c w p y = 1 := by
  unfold canonicalCoefficientDensity
  apply Finset.prod_eq_one
  intro j _
  unfold canonicalArrayDensity
  apply Finset.prod_eq_one
  intro e _
  exact canonicalMixedDensity_empty _ (b j) (hb j) (o j) _ _ _ _

end VectorPolynomial
end Erdos3

end

end OAI

end


