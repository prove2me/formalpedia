-- Prove2me | Definitions.Def_OAIErdos3B160
-- name    : OAIErdos3B160
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T21:24:28.533321+00:00
-- url     : https://prove2.me/theorems/7840c2cd-a283-4b16-8b4e-ce7c26e93608
-- title:
--   OpenAI Erdős-3 split, definitions bundle 161 of 169
-- statement:
--   Definitions bundle 161 of 169 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B159`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 161 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.coefficientAmbientRowsJet`, `OAI.Erdos3.BooleanCubeKernel.coefficientAmbientRowsJet_eq`, `OAI.Erdos3.BooleanCubeKernel.coefficientAmbientRowsJet_lipschitz`, `OAI.Erdos3.BooleanCubeKernel.coefficientCoverSample_physicalRows`, `OAI.Erdos3.BooleanCubeKernel.physicalRowsCoefficient_measurePreserving`, `OAI.Erdos3.BooleanCubeKernel.physicalRowsFintype`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.frozenSingleSiteHaarReference`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.frozenSingleSiteHaarReference_integrable`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.frozenSingleSiteHaarReference_lipschitz`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.product`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.productUniform`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.productUniform_eval`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.product_eval`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.product_lipschitz_le`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSamplePhysicalMixedValue`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalSides_not_short`, `OAI.Erdos3.VectorPolynomial.exists_allocated_mixture_density_projection_law`, `OAI.Erdos3.VectorPolynomial.exists_allocated_narrow_density_projection`, `OAI.Erdos3.VectorPolynomial.nativeSingleSiteCoverObservable`, `OAI.Erdos3.VectorPolynomial.physicalDensityProjection`, `OAI.Erdos3.VectorPolynomial.physicalFactorCoverMap`, `OAI.Erdos3.VectorPolynomial.singleSiteIntegerCover`, `OAI.Erdos3.torus_nsmul_reindex_lipschitz`, `_private.Estimates.NativePhysicalHaarExpansion.0.OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.complex_dist_product`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B149
import Definitions.Def_OAIErdos3B159

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

noncomputable def allocatedOriginalSamplePhysicalMixedValue
    (j : Fin m) : (I j → ℝ) × (Fin (n j) → ℤ) :=
  mixedArrayRegroup (I j) (Fin (n j)) Unit
    (canonicalCoefficientJetArrays
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (fun (_ : Fin m) (_ : Unit) => (∅ : Finset Empty)) sample j) ()

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X K : Type*} [Fintype X] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial
open Module
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "sides" => allocatedPrincipalSides B U basis S

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

local notation "root" => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y

theorem allocatedPrincipalSides_not_short (a : Active)
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    sides ⟨a.val,p⟩ = S.value := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · rfl
  · exact allocatedPrincipalSides_active B U basis S j i (Nat.lt_of_not_ge ha) p.1 p.2

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def frozenSingleSiteHaarReference
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) : ℂ :=
  ∫ y, W.frozenTorus residue center
    (fun a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩) ∂haar

omit [∀ j, (ν j).IsAddLeftInvariant] in
theorem frozenSingleSiteHaarReference_integrable
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) :
    Integrable (fun y : EuclideanJetLayers U (fun _ => Unit) =>
      W.frozenTorus residue center
        (fun a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩)) haar := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure haar := Measure.pi.instIsProbabilityMeasure _
  apply Integrable.of_bound _ 1 (ae_of_all _ (fun _ => W.norm_frozenTorus_le _ _ _))
  apply Continuous.aestronglyMeasurable
  apply (W.frozenTorus_lipschitz residue center).continuous.comp
  apply continuous_pi
  intro a
  exact (continuous_apply (⟨a.1, (), a.2⟩ : JetAmbientIndex (fun _ : Fin m => Unit) J)).comp
    (coveredJetAmbientTorus_continuous (O := fun _ : Fin m => Unit) U 1)

omit [∀ j, (ν j).IsAddLeftInvariant] in
theorem frozenSingleSiteHaarReference_lipschitz
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) :
    LipschitzWith L (W.frozenSingleSiteHaarReference U ν residue) := by
  have : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : Unit => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  have : IsProbabilityMeasure haar := Measure.pi.instIsProbabilityMeasure _
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  exact probability_integral_approximation haar _ _
    (W.frozenSingleSiteHaarReference_integrable U ν residue x)
    (W.frozenSingleSiteHaarReference_integrable U ν residue y)
    (fun z => W.frozenTorus_spatial_error residue x y _)

end NormalizedPolynomialTwist

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped Classical NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def singleSiteIntegerCover (d : ℕ) :
    EuclideanJetLayers U (fun _ => Unit) →+ EuclideanJetLayers U (fun _ => Unit) where
  toFun y j t := quotientIntegerCover _ d (y j t)
  map_zero' := by ext j t; exact map_zero _
  map_add' x y := by ext j t; exact map_add _ _ _

variable [CompactSpace (EuclideanJetLayers U (fun _ => Unit))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset (Fin q))

noncomputable def coefficientAmbientRowsJet
    (z : CoefficientAmbientIndex (Fin q) J → UnitAddCircle) : JetAmbientIndex O J → UnitAddCircle :=
  fun t => ∑ e : BoundedCoefficientExponent (Fin q) (t.1.val + 1),
    (if rows t.1 t.2.1 = e.val.support then (1 : ℤ) else 0) • z ⟨⟨t.1, e⟩, t.2.2⟩

omit [∀ j, Fintype (O j)] in
theorem coefficientAmbientRowsJet_eq (U : ∀ j, Submodule ℝ (J j → ℝ))
    (z : CoefficientTorus (K := Fin q) U) :
    coefficientAmbientRowsJet rows (coefficientAmbientTorus U z) =
      coveredJetAmbientTorus U 1 (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows z) := by
  funext t
  rcases t with ⟨j, t, i⟩
  simp only [coefficientAmbientRowsJet,
    coveredJetAmbientTorus_coefficient, Nat.cast_one, one_mul, boundedCoefficientJetMatrix_standard]

theorem coefficientAmbientRowsJet_lipschitz :
    LipschitzWith (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0))
      (coefficientAmbientRowsJet (q := q) (J := J) rows) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, t, i⟩
  have hterm (e : BoundedCoefficientExponent (Fin q) (j.val + 1)) :
      dist ((if rows j t = e.val.support then (1 : ℤ) else 0) • z ⟨⟨j,e⟩,i⟩)
        ((if rows j t = e.val.support then (1 : ℤ) else 0) • w ⟨⟨j,e⟩,i⟩) ≤ dist z w := by
    split_ifs
    · simpa only [one_zsmul] using dist_le_pi_dist z w ⟨⟨j,e⟩,i⟩
    · simp only [zero_zsmul, dist_self]
      exact dist_nonneg
  have hc : (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0) ≤
      ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0) :=
    Finset.single_le_sum (f := fun j : Fin m => (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0)) (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    _ ≤ ∑ _e : BoundedCoefficientExponent (Fin q) (j.val + 1), dist z w :=
      (dist_sum_sum_le _ _ _).trans (Finset.sum_le_sum (fun e _ => hterm e))
    _ = (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ) * dist z w := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3
open scoped NNReal

theorem torus_nsmul_reindex_lipschitz {A B : Type*} [Fintype A] [Fintype B]
    (r : B → A) (n : ℕ) : LipschitzWith (n : ℝ≥0)
      (fun z : A → UnitAddCircle => fun i : B => n • z (r i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  calc
    _ = ‖n • (x (r i) - y (r i))‖ := by rw [dist_eq_norm, nsmul_sub]
    _ ≤ n * ‖x (r i) - y (r i)‖ := norm_nsmul_le
    _ ≤ (n : ℝ≥0) * dist x y := by
      rw [← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y (r i)) (Nat.cast_nonneg _)

namespace VectorPolynomial
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def physicalFactorCoverMap (period gridPeriod : ℕ)
    (z : (Σ j, J j) → UnitAddCircle) :
    (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
      ((Σ j, J j) → UnitAddCircle)) :=
  ((fun a => (period * gridPeriod) • z ⟨a.1, a.2.2⟩, fun a => gridPeriod • z a),
    fun a => period • z a)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

variable {X : Type*} {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

include hp in
theorem coefficientCoverSample_physicalRows {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin q)) (v : X → (Unit ⊕ Fin q) → ℤ) :
    euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows
      (affineCoefficientCoverSample U p hm d (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))) =
      physicalCubeRowSample U d rows p hm v := by
  let D : Fin q → Fin q → ℤ := fun i j => if i = j then 1 else 0
  have hD : Matrix.of D = (1 : Matrix (Fin q) (Fin q) ℤ) := by
    ext i j
    simp [D, Matrix.one_apply]
  have h := coefficientCoverSample_sites U (fun _ : Fin q => 0) D d p hp hm
    (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))
  rw [affineCoveredSiteSample_zero_base_physical, hD,
    physicalCubeRootDifferences_standard, standardPhysicalCubeOutput_frame] at h
  have hjet := congrArg (fun t : SiteTorus (Finset (Fin q)) U =>
    euclideanJetEquiv U (siteBooleanJetTorusMap U rows t)) h
  change euclideanCoefficientJetMap U (fun _ : Fin q => 0) (Matrix.of D) rows
    (affineCoefficientCoverSample U p hm d (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))) =
      physicalCubeRowSample U d rows p hm v at hjet
  simpa only [hD] using hjet

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped BigOperators Classical NNReal

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {pw cw pv cv : ℝ} {Lw Lv : ℝ≥0}

theorem complex_dist_product (a b c d : ℂ) :
    dist (a * b) (c * d) ≤ ‖a‖ * dist b d + dist a c * ‖d‖ := by
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  calc
    _ = ‖a * (b - d) + (a - c) * d‖ := by congr 1; ring
    _ ≤ ‖a * (b - d)‖ + ‖(a - c) * d‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul]

noncomputable def product
    (W : NormalizedPolynomialTwist X Y pw cw Lw)
    (V : NormalizedPolynomialTwist X Y pv cv Lv) :
    NormalizedPolynomialTwist X Y (pw * pv) (cw * cv)
      (Lw * max 1 (V.cover : ℝ≥0) + Lv * max 1 (W.cover : ℝ≥0)) where
  modulus := W.modulus * V.modulus
  modulus_pos := Nat.mul_pos W.modulus_pos V.modulus_pos
  modulus_bound := by
    rw [Nat.cast_mul]
    exact mul_le_mul W.modulus_bound V.modulus_bound (Nat.cast_nonneg _)
      ((Nat.cast_nonneg _).trans W.modulus_bound)
  cover := W.cover * V.cover
  cover_pos := Nat.mul_pos W.cover_pos V.cover_pos
  cover_bound := by
    rw [Nat.cast_mul]
    exact mul_le_mul W.cover_bound V.cover_bound (Nat.cast_nonneg _)
      ((Nat.cast_nonneg _).trans W.cover_bound)
  mask := fun r => W.mask (fun x => ZMod.castHom (dvd_mul_right W.modulus V.modulus)
      (ZMod W.modulus) (r x)) *
    V.mask (fun x => ZMod.castHom (dvd_mul_left V.modulus W.modulus) (ZMod V.modulus) (r x))
  mask_bound := by
    intro r
    rw [norm_mul]
    exact (mul_le_mul (W.mask_bound _) (V.mask_bound _) (norm_nonneg _) zero_le_one).trans_eq
      (mul_one 1)
  smooth := fun z => W.smooth (z.1, fun y => V.cover • z.2 y) *
    V.smooth (z.1, fun y => W.cover • z.2 y)
  smooth_bound := by
    intro z
    rw [norm_mul]
    exact (mul_le_mul (W.smooth_bound _) (V.smooth_bound _) (norm_nonneg _) zero_le_one).trans_eq
      (mul_one 1)
  smooth_lipschitz := by
    have hmap (n : ℕ) : LipschitzWith (max 1 (n : ℝ≥0))
        (fun z : (X → ℝ) × (Y → UnitAddCircle) => (z.1, fun y => n • z.2 y)) := by
      have hn : LipschitzWith (n : ℝ≥0)
          (fun z : (X → ℝ) × (Y → UnitAddCircle) => fun y => n • z.2 y) := by
        simpa only [mul_one, Function.comp_def] using
          (torus_nsmul_reindex_lipschitz (fun y : Y => y) n).comp
            (LipschitzWith.prod_snd (α := X → ℝ))
      exact LipschitzWith.prod_fst.prodMk hn
    have hf := W.smooth_lipschitz.comp (hmap V.cover)
    have hg := V.smooth_lipschitz.comp (hmap W.cover)
    apply LipschitzWith.of_dist_le_mul
    intro z w
    calc
      _ ≤ ‖W.smooth (z.1, fun y => V.cover • z.2 y)‖ *
          dist (V.smooth (z.1, fun y => W.cover • z.2 y))
            (V.smooth (w.1, fun y => W.cover • w.2 y)) +
        dist (W.smooth (z.1, fun y => V.cover • z.2 y))
          (W.smooth (w.1, fun y => V.cover • w.2 y)) *
          ‖V.smooth (w.1, fun y => W.cover • w.2 y)‖ := complex_dist_product _ _ _ _
      _ ≤ 1 * (((Lv * max 1 (W.cover : ℝ≥0) : ℝ≥0) : ℝ) * dist z w) +
        (((Lw * max 1 (V.cover : ℝ≥0) : ℝ≥0) : ℝ) * dist z w) * 1 := by
        exact add_le_add
          (mul_le_mul (W.smooth_bound _) (hg.dist_le_mul z w) dist_nonneg zero_le_one)
          (mul_le_mul (hf.dist_le_mul z w) (V.smooth_bound _) (norm_nonneg _)
            (by positivity))
      _ = _ := by push_cast; ring

@[simp] theorem product_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (V : NormalizedPolynomialTwist X (Σ j, J j) pv cv Lv)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.product V).eval N p u = W.eval N p u * V.eval N p u := by
  have hw : (W.cover : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr W.cover_pos.ne'
  have hv : (V.cover : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr V.cover_pos.ne'
  have hfirst : (fun a => V.cover • physicalGridFactorInput (W.cover * V.cover) p
      (fun x => (u x : ℝ)) a) = physicalGridFactorInput W.cover p (fun x => (u x : ℝ)) := by
    funext a
    simp only [physicalGridFactorInput, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1
    field_simp
  have hsecond : (fun a => W.cover • physicalGridFactorInput (W.cover * V.cover) p
      (fun x => (u x : ℝ)) a) = physicalGridFactorInput V.cover p (fun x => (u x : ℝ)) := by
    funext a
    simp only [physicalGridFactorInput, ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1
    field_simp
  have hmaskfirst : (fun x => ZMod.castHom (dvd_mul_right W.modulus V.modulus)
      (ZMod W.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus))) =
      (fun x => (u x : ZMod W.modulus)) := by
    funext x
    exact map_intCast (ZMod.castHom (dvd_mul_right W.modulus V.modulus) (ZMod W.modulus)) (u x)
  have hmasksecond : (fun x => ZMod.castHom (dvd_mul_left V.modulus W.modulus)
      (ZMod V.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus))) =
      (fun x => (u x : ZMod V.modulus)) := by
    funext x
    exact map_intCast (ZMod.castHom (dvd_mul_left V.modulus W.modulus) (ZMod V.modulus)) (u x)
  change (W.mask (fun x => ZMod.castHom (dvd_mul_right W.modulus V.modulus)
      (ZMod W.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus))) *
    V.mask (fun x => ZMod.castHom (dvd_mul_left V.modulus W.modulus)
      (ZMod V.modulus) ((u x : ℤ) : ZMod (W.modulus * V.modulus)))) *
    (W.smooth ((fun x => (u x : ℝ) / N x), fun a => V.cover •
      physicalGridFactorInput (W.cover * V.cover) p (fun x => (u x : ℝ)) a) *
    V.smooth ((fun x => (u x : ℝ) / N x), fun a => W.cover •
      physicalGridFactorInput (W.cover * V.cover) p (fun x => (u x : ℝ)) a)) = _
  rw [hmaskfirst, hmasksecond, hfirst, hsecond]
  unfold eval
  ring

theorem product_lipschitz_le
    (W : NormalizedPolynomialTwist X Y pw cw Lw)
    (V : NormalizedPolynomialTwist X Y pv cv Lv) :
    Lw * max 1 (V.cover : ℝ≥0) + Lv * max 1 (W.cover : ℝ≥0) ≤
      Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw) := by
  have hw : (W.cover : ℝ≥0) ≤ Real.toNNReal cw := by
    exact (NNReal.coe_le_coe).mp (W.cover_bound.trans (Real.le_coe_toNNReal cw))
  have hv : (V.cover : ℝ≥0) ≤ Real.toNNReal cv := by
    exact (NNReal.coe_le_coe).mp (V.cover_bound.trans (Real.le_coe_toNNReal cv))
  exact add_le_add (mul_le_mul_of_nonneg_left (max_le_max_left 1 hv) (show 0 ≤ Lw from zero_le))
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hw) (show 0 ≤ Lv from zero_le))

noncomputable def productUniform
    (W : NormalizedPolynomialTwist X Y pw cw Lw)
    (V : NormalizedPolynomialTwist X Y pv cv Lv) :
    NormalizedPolynomialTwist X Y (pw * pv) (cw * cv)
      (Lw * max 1 (Real.toNNReal cv) + Lv * max 1 (Real.toNNReal cw)) :=
  (W.product V).mono le_rfl le_rfl (W.product_lipschitz_le V)

@[simp] theorem productUniform_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (V : NormalizedPolynomialTwist X (Σ j, J j) pv cv Lv)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.productUniform V).eval N p u = W.eval N p u * V.eval N p u := by
  exact W.product_eval V N p u

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})
noncomputable local instance physicalRowsFintype (j : Fin m) : Fintype (Row j) :=
  Finset.Subtype.fintype (boundedBooleanJetRows (Fin q) (j.val + 1))
local notation "rows" => (fun j => (Subtype.val : Row j → Finset (Fin q)))
local notation "jet" => euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : Row j => ν j))

theorem physicalRowsCoefficient_measurePreserving (a : ℕ) (ha : 0 < a) :
    MeasurePreserving (fun z => jet (quotientIntegerCover (coefficientIntegerLattice U) a z)) μ ξ := by
  have hperiod : integerScalarLattice (Fin q) (1 : ℤ) ≤
      (1 : Matrix (Fin q) (Fin q) ℤ).mulVecLin.range := by
    intro v _
    exact ⟨v, by simp⟩
  exact (euclideanCoefficientJetMap_measurePreserving U (fun _ => 0)
    (1 : Matrix (Fin q) (Fin q) ℤ) 1 one_ne_zero hperiod rows
    (fun _ => Subtype.val_injective)
    (fun j s => (mem_boundedBooleanJetRows (j.val + 1) s.val).mp s.property) μ ν).comp
      (coefficientCover_measurePreserving U μ a ha)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {X : Type*} [Fintype X] {pw cw : ℝ} {Lw : ℝ≥0}

noncomputable def nativeSingleSiteCoverObservable
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ)
    (y : EuclideanJetLayers U (fun _ => Unit)) : ℂ :=
  W.frozenTorus (fun i => (u i : ZMod W.modulus)) (fun i => (u i : ℝ) / physicalN i)
    (fun a => coveredJetAmbientTorus U (Q / W.cover) y ⟨a.1, (), a.2⟩)

variable [CompactSpace (EuclideanJetLayers U (fun _ => Unit))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedOriginalSourceProjection
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

def physicalDensityProjection.{uK, uJ, uX, uF} {K : Type uK} [Fintype K] {m q : ℕ}
    {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (dirs : Fin q → K → ℤ) (d : ℕ)
    (density : CoefficientTorus (K := K) U → ℝ)
    (f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ) : Prop :=
  ∀ {X : Type uX} {F : Type uF} [Fintype F]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : F → ℂ) {η : ℝ},
    (∀ z, ‖coefficientTorusFourierSum U frequency coeff z - (density z : ℂ)‖ ≤ η) →
    ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
    ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : Option K → X → ℝ),
      ‖affineCubeFourierProjection U root dirs frequency p coeff v -
        (f (euclideanCoefficientJetMap U root (Matrix.of dirs)
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
          (affineCoefficientCoverSample U p hm d v)) : ℂ)‖ ≤ η

universe uK uJ uX uF

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators

theorem exists_allocated_narrow_density_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S))
    {X : Type*} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    {F : Type*} [Fintype F]
    (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P)
    (coeff : F → ℂ) (_hcoeff : (∑ a, ‖coeff a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ ε : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : ε⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (density : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ)
    (D : ℕ) (f : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ v, ‖(density v : ℂ) - coefficientTorusFourierSum U frequency coeff v‖ ≤ η)
    {Z : ℝ} (_hZnorm : 0 < Z),
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let pa := fun j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    ∀ (_hpositive : ∀ z : Option (LayerSamplerVariables G I n B) × X → ℤ,
      ‖affineCubeFourierProjection U root dirs frequency pa coeff (fun k d => (z (k, d) : ℝ)) -
        (f (euclideanCoefficientJetMap U root dirs
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
          (affineCoefficientCoverSample U pa hma D (fun k d => (z (k, d) : ℝ)))) : ℂ)‖ ≤ η),
    ∃ (hV : ∀ z, 0 < V z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
      ‖(∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) *
          (density (affineSampleCoefficientTorus U pa hma (fun k d => (z (k, d) : ℝ))) : ℂ))) / (Z : ℂ) -
        (∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
          physicalCubePositiveTest U D p hm f test (physicalCubeRootDifferences root dirs base z)) /
          (Z : ℂ)‖ ≤ (2 * η + ε) / Z := by
  obtain ⟨A₀, _, hprojection⟩ := exists_affine_cube_fourier_projection m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    ((8 * Polynomial.X + Polynomial.C (q + 130 + A₀)) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ _ J _ U basis R σ S c x P W hP hK hW hroot hWP hL M hperiod y
    X _ _ hX hdim F _ frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
    τ ξ ε hτ hτP hξ hξ1 hξP hε hεP N hsize rank hrank hRank test htest T hT density D f η hη happrox Z hZnorm
    V root dirs pa hma hpositive
  let Q := spatialSamplingBudget (2 * P) + (q + 2 : ℕ)
  have hP2 : 0 ≤ 2 * P := by positivity
  have hPQ : P ≤ Q := by dsimp [Q, spatialSamplingBudget]; linarith [Nat.cast_nonneg (α := ℝ) (q + 2)]
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hsiteQ : P + (q + 2 : ℕ) ≤ Q := by dsimp [Q, spatialSamplingBudget]; linarith
  have heval : Q + A₀ = 8 * P + (q + 130 + A₀ : ℕ) := by
    dsimp [Q, spatialSamplingBudget]
    push_cast
    ring
  have hcost : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    rw [heval]
    simpa [Polynomial.eval₂_pow] using hbudget P hP
  have hExp := Real.exp_le_exp.mpr hPQ
  obtain ⟨a, ha, _, hperiod⟩ := hperiod
  have hlin : LinearIndependent ℝ (fun i k => (dirs i k : ℝ)) :=
    linearIndependent_of_fixed_kernel_period (scalarCubeDifferenceMatrix x) dirs Sum.inl
      (fun _ _ => rfl) (by exact_mod_cast ha.ne') hperiod
  have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa j) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have hra (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa j) :=
    (hasLayerSamplingRank_translate_iff (fun d => (base d : ℝ)) (j.val + 1)
      (fun d => (N d : ℝ)) rank (U j) (p j) (hp j)).mpr (hrank j)
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hV : ∀ z, 0 < V z := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
  have hξτ : 0 < ξ * τ := mul_pos hξ hτ
  have hξτP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← two_mul]
  have hρP : 1 / spatialWidthFraction (2 * P) (ξ * τ) ≤ Real.exp Q :=
    (spatialWidthFraction_inv_le hP2 hξτ hξτP).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  have hwidth (z) : spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ V z :=
    (spatialWidthFraction_le_allocated_width hP2 hW
      (hWP.trans (Real.exp_le_exp.mpr (by linarith))) hξτ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  obtain ⟨hZ, hraw⟩ := hprojection hQ (hX.trans hPQ) (hdim.trans hPQ) U root dirs hlin
    (Real.exp_nonneg Q) (Real.exp_nonneg Q) le_rfl le_rfl
    (fun s k => (allocatedPhysicalCube_site_le_exp B U basis S c x y (hroot.trans hWP) hL s k).trans
      (Real.exp_le_exp.mpr hsiteQ)) frequency (fun a j d hd t => (hfrequency a j d hd t).trans hExp)
    coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans hExp) pa hpa hma stride hs
    (Real.exp_nonneg Q) le_rfl (spatialWidthFraction_pos (2 * P) hξτ) hε hρP
    (by simpa only [one_div] using hεP.trans hExp) (fun d => (hsP d).trans hExp)
    (fun d => (N d : ℝ)) (fun d => (Real.exp_le_exp.mpr hcost).trans (hsize d)) hra
    ((Real.exp_le_exp.mpr hcost).trans hRank) 0 (by simp)
    (fun s u => test s ((fun d => (base d : ℝ)) + u)) (fun s u => htest s _)
    T hT V hV hwidth
  have hweight (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      layeredSiteWeight 0 (fun s => affineSite root dirs s)
        (fun s u => test s ((fun d => (base d : ℝ)) + u)) (fun k d => (z (k, d) : ℝ)) =
        physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) :=
    layeredSiteWeight_physicalCube root dirs base test z
  have hdirs : Matrix.of dirs = dirs := rfl
  have hfirst := selectedResidue_positive_density_projection_error U root dirs D p hp hm
    frequency coeff test htest base stride T V hV hZ density f hη happrox hpositive
    (by simpa only [hweight, hdirs, pa] using hraw)
  refine ⟨hV, hZ, ?_⟩
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZnorm]
  exact div_le_div_of_nonneg_right hfirst hZnorm.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical

universe uX uF

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical

universe uX uF

theorem exists_allocated_mixture_density_projection_law (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    {F : Type uF} [Fintype F]
    (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P)
    (coeff : F → ℂ) (_hcoeff : (∑ a, ‖coeff a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ ε : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : ε⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (density : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, uF} U
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (f y))
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ v, ‖(density v : ℂ) - coefficientTorusFourierSum U frequency coeff v‖ ≤ η)
    {Z : ℝ} (_hZnorm : 0 < Z),
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hV : ∀ z, 0 < V z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
    let source := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T V hV hmass z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z) *
          (density (affineSampleCoefficientTorus U
            (fun j => translate (fun t => (base t : ℝ)) (p j))
            (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
            (fun k t => (z (k, t) : ℝ))) : ℂ))
    let projected := fun y => ∑' z,
      ((selectedResidueSmoothPMF stride T V hV hmass z).toReal : ℂ) *
        physicalCubePositiveTest U D p hm (f y) test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) base z)
    ‖law.complexMean source / (Z : ℂ) - law.complexMean projected / (Z : ℂ)‖ ≤ (2 * η + ε) / Z := by
  obtain ⟨A, hA, hprojection⟩ := exists_allocated_narrow_density_projection m q
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U basis R σ S c x P W hP hK hW hroot hWP hL M hperiod
    X _ _ hX hdim F _ frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
    τ ξ ε hτ hτP hξ hξ1 hξP hε hεP N hsize rank hrank hRank test htest T hT density D f
    hproject η hη happrox Z hZnorm V hV hmass law source projected
  have hpoint (y) : ‖source y / (Z : ℂ) - projected y / (Z : ℂ)‖ ≤ (2 * η + ε) / Z := by
    obtain ⟨_, _, he⟩ := hprojection B U basis S c x hP hK hW hroot hWP hL hperiod y
      hX hdim frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
      hτ hτP hξ hξ1 hξP hε hεP N hsize hrank hRank test htest T hT density D (f y)
      hη happrox hZnorm
      (fun z => (hproject y) frequency coeff
        (fun v => by rw [norm_sub_rev]; exact happrox v)
        (fun j => translate (fun t => (base t : ℝ)) (p j))
        (fun j => degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
        (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hm j))
        (fun k t => (z (k, t) : ℝ)))
    exact he
  have hmean := law.norm_complexMean_sub_le
    (fun y => source y / (Z : ℂ)) (fun y => projected y / (Z : ℂ))
    (fun _ => (2 * η + ε) / Z) (fun y _ => hpoint y)
  rw [law.mean_const] at hmean
  simpa only [FiniteProbabilityWeights.complexMean, mul_div_assoc, Finset.sum_div] using hmean

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))) (d : ℕ)
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
  EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

end Erdos3.VectorPolynomial

end

end OAI

end


