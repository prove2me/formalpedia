-- Prove2me | Definitions.Def_OAIE3v2B057
-- name    : OAIE3v2B057
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:14:12.929406+00:00
-- url     : https://prove2.me/theorems/9a72b12c-7402-4ef1-8a8a-023a53944fd0
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 58 of 311
-- statement:
--   Definitions bundle 58 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B006`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B013`, `OAIE3v2B015`, `OAIE3v2B016`, `OAIE3v2B017`, `OAIE3v2B018`, `OAIE3v2B025`, `OAIE3v2B026`, `OAIE3v2B027` of this split.
--
--   Modules: `Dynamics/NormalizedTwistExtractionBudget.lean`, `Dynamics/TranslationMajorCorrelationBudget.lean`, `Dynamics/TranslationMajorDetectedPotential.lean`, `Estimates/FiniteTriangularRationalCorrection.lean`, `Estimates/FourBalancedRelations.lean`, `Estimates/MajorTranslationJointLower.lean`, `Estimates/NativeRoundedGraphEnergy.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/RealifiedReconstruction.lean`, `Estimates/VectorAlgebraicMajorDecomposition.lean`, `Estimates/VectorSubspaceCorrectionRepresentatives.lean`, `Geometry/ControlledGradedBaseCoordinates.lean`, `Geometry/DenseRealBoxCell.lean`, `Geometry/FiniteNormalizedChartCorrection.lean`, `Geometry/FullTaggedChartCoefficientRange.lean`, `Geometry/LowTaggedCoordinateRestriction.lean`, `Lattices/NaturalScaleIntegerWindow.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/ProperAffineBoxRestriction.lean`, `Lattices/SharedFreeAffineBudget.lean`, `Linear/FiniteRankTriangularFinset.lean`, `Linear/ProperCyclicKernelBasis.lean`, `Linear/RationalTagConstraintBasis.lean`, `Linear/RealFourBalancedDual.lean`, `Linear/TaggedSubmoduleBasis.lean`, `Linear/WeightedLinearBaseProjection.lean`, `Nilpotent/CanonicalReducedMajorTwistedNiltest.lean`, `Nilpotent/LocalMajorDenseSliceNiltest.lean`, `Nilpotent/RealFunctionalBCH.lean`, `Polynomial/AlgebraicMajorWeightedDegree.lean`, `Polynomial/BoundedRealPolynomialBasis.lean`, `Polynomial/ControlledLinearPolynomialRestriction.lean`, `Polynomial/FiniteSupportedPolynomialSubstitution.lean`, `Polynomial/JointPolynomialDilationGrid.lean`, `Polynomial/LowTaggedPolynomialCoordinates.lean`, `Polynomial/MajorTranslationPolynomialSymbolDegree.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Polynomial/NormalizedRealPolynomialChart.lean`, `Polynomial/PolynomialCoefficientGridDenominator.lean`, `Polynomial/PolynomialKernelValues.lean`, `Polynomial/PolynomialParameterContinuity.lean`, `Polynomial/PolynomialTagRestrictionBudget.lean`, `Polynomial/VectorPolynomialReconstruction.lean`, `Sampling/BoundedKernelGridEnumerationBudget.lean`, `Sampling/FiniteNormalizedRealGridCorrection.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B016
import Definitions.Def_OAIE3v2B017
import Definitions.Def_OAIE3v2B018
import Definitions.Def_OAIE3v2B025
import Definitions.Def_OAIE3v2B026
import Definitions.Def_OAIE3v2B027

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTwistExtractionBudget
namespace OAI

section

namespace Erdos3

theorem exists_normalizedTwistExtractionBudget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + a) ^ a + 3 * p + 16
      q + (q + b) ^ b + 3 * p + 16 ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a + 3 * X + 16
  let P := Q + (Q + Polynomial.C b) ^ b + 3 * X + 16
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Q, X, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ ι R S V : Type*} [CommRing R] [CommRing S]
  [AddCommGroup V] [Module R V]

variable [Fintype ι] [Module S V]

noncomputable def coordinatesEquiv (e : Module.Basis ι S V) :
    VectorPolynomial σ R V ≃ (ι → MvPolynomial σ S) where
  toFun p i := coordinate (e.coord i).toAddMonoidHom p
  invFun := ofCoordinates e
  left_inv := ofCoordinates_coordinate e
  right_inv p := funext (coordinate_ofCoordinates e p)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem eval₂_eq_of_weightedSupport (φ : R →+* S)
    {w : σ → ℕ} {d : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLE w d) (x y : σ → S)
    (hxy : ∀ i, w i ≤ d → x i = y i) :
    eval₂ φ x P = eval₂ φ y P := by
  apply MvPolynomial.eval₂_congr φ x y
  intro i α hi hα
  exact hxy i ((Finsupp.le_weight_of_ne_zero' w
    (Finsupp.mem_support_iff.mp hi)).trans (hP (MvPolynomial.mem_support_iff.mpr hα)))

theorem aeval_eq_of_weightedSupportLE [Algebra R S]
    {w : σ → ℕ} {d : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLE w d) (x y : σ → S)
    (hxy : ∀ i, w i ≤ d → x i = y i) : aeval x P = aeval y P :=
  eval₂_eq_of_weightedSupport (algebraMap R S) hP x y hxy

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R : Type*} [CommRing R]

theorem weightedSupportLE_rename_inl_ring (v : U → ℕ) (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial U R} (hP : P ∈ weightedSupportLE v d) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLE (Sum.elim v w) d := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro i
  exact weightedSupportLE_X (Sum.elim v w) (Sum.inl i)

theorem weightedSupportLE_rename_inr_ring (v : U → ℕ) (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial B R} (hP : P ∈ weightedSupportLE w d) :
    rename (Sum.inr : B → U ⊕ B) P ∈ weightedSupportLE (Sum.elim v w) d := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro i
  exact weightedSupportLE_X (Sum.elim v w) (Sum.inr i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedRealPolynomialBasis
namespace OAI

section

namespace Erdos3

theorem boundedExponentSet_card_le {K : Type*} [Fintype K] (s : Finset (K →₀ ℕ)) (h : ℕ)
    (hs : ∀ m ∈ s, m.sum (fun _ n => n) ≤ h) : s.card ≤ (Fintype.card K + 1) ^ h := by
  classical
  let f : s → List.Vector (Option K) h := fun m => paddedExponentWord m.val h (hs m.val m.property)
  have hf : Function.Injective f := by
    intro m n he
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    have hc := congrArg (fun v : List.Vector (Option K) h => (v.val : Multiset (Option K)).count (some k)) he
    simpa only [f, paddedExponentWord_count] using hc
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, card_vector, Fintype.card_option] using hc

theorem monomialArray_card_le {K T : Type*} [Fintype K] (s : Finset T)
    (exponent : T → K →₀ ℕ) (hinj : Set.InjOn exponent s) (h : ℕ)
    (hs : ∀ t ∈ s, (exponent t).sum (fun _ n => n) ≤ h) : s.card ≤ (Fintype.card K + 1) ^ h := by
  classical
  rw [← Finset.card_image_of_injOn hinj]
  apply boundedExponentSet_card_le
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨t, ht, rfl⟩
  exact hs t ht

theorem mvPolynomial_support_card_le_totalDegree {K : Type*} [Fintype K]
    (p : MvPolynomial K ℝ) {h : ℕ} (hp : p.totalDegree ≤ h) :
    p.support.card ≤ (Fintype.card K + 1) ^ h :=
  boundedExponentSet_card_le p.support h (fun _ hm => (MvPolynomial.le_totalDegree hm).trans hp)

open scoped BigOperators

theorem monomialArray_abs_sum_le {K T : Type*} [Fintype K] (s : Finset T)
    (exponent : T → K →₀ ℕ) (hinj : Set.InjOn exponent s) (h : ℕ)
    (hs : ∀ t ∈ s, (exponent t).sum (fun _ n => n) ≤ h)
    (weight : T → ℝ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ t ∈ s, |weight t| ≤ M) :
    (∑ t ∈ s, |weight t|) ≤ ((Fintype.card K : ℝ) + 1) ^ h * M := by
  have hc : (s.card : ℝ) ≤ ((Fintype.card K : ℝ) + 1) ^ h := by
    exact_mod_cast monomialArray_card_le s exponent hinj h hs
  calc
    _ ≤ ∑ _t ∈ s, M := Finset.sum_le_sum hw
    _ = (s.card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hM

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerBox_expect_eq_zmod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) [NeZero N] (f : (ι → ℤ) → ℂ) :
    (𝔼 x ∈ integerBox (fun _ : ι => N), f x) =
      𝔼 t : ι → ZMod N, f (fun i => ((t i).val : ℤ)) := by
  symm
  apply Finset.expect_bij (fun t _ i => ((t i).val : ℤ))
  · intro t _
    rw [mem_integerBox]
    exact fun i => ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).val_lt⟩
  · intro t _
    rfl
  · intro t _ u _ h
    funext i
    apply ZMod.val_injective N
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox (fun _ : ι => N) x).mp hx
    refine ⟨(fun i => (x i : ZMod N)), Finset.mem_univ _, ?_⟩
    funext i
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (hx' i).1 (hx' i).2]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators ContDiff

theorem realPolynomialMass_pderiv_degreeOf {I : Type*} (p : MvPolynomial I ℝ)
    (i : I) {d : ℕ} (hd : p.degreeOf i ≤ d) :
    realPolynomialMass (pderiv i p) ≤ (d : ℝ) * realPolynomialMass p := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff, map_sum]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ p.support, (d : ℝ) * |p.coeff m| := by
      apply Finset.sum_le_sum
      intro m hm
      rw [pderiv_monomial, realPolynomialMass_monomial, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (m i : ℝ) from Nat.cast_nonneg _)]
      have hmi : (m i : ℝ) ≤ d := by exact_mod_cast (monomial_le_degreeOf i hm).trans hd
      nlinarith [abs_nonneg (p.coeff m)]
    _ = _ := by rw [realPolynomialMass, Finset.mul_sum]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

theorem eval₂_ofCoordinates {ι : Type*} [Fintype ι] (e : Module.Basis ι S V)
    (p : ι → MvPolynomial σ S) (x : σ → S) :
    eval₂ x (ofCoordinates (R := R) e p) =
      e.equivFun.symm (fun i => MvPolynomial.eval x (p i)) := by
  apply e.equivFun.injective
  funext i
  rw [e.equivFun.apply_symm_apply]
  change e.coord i (eval₂ x (ofCoordinates (R := R) e p)) = _
  rw [coordinate_eval₂]
  exact congrArg (MvPolynomial.eval x) (coordinate_ofCoordinates e p i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FourBalancedRelations
namespace OAI

section

namespace Erdos3

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem fourBalancedDependent_le_refined (C D : Submodule R V)
    (K : Submodule R (Fin 4 → V)) : fourBalancedDependent D ≤ fourRefinedRelation C D K :=
  le_sup_right

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

def realPolynomialCoefficientGrid (q : ℕ) (P : MvPolynomial σ ℝ) : Prop :=
  (fun m => P.coeff m) ∈ realDenominatorGrid q

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R : Type*} [CommRing R]

noncomputable def majorSlowPolynomial (D0 : MvPolynomial B R)
    (E : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (e : B → MvPolynomial U R) : MvPolynomial (U ⊕ B) R :=
  rename Sum.inr D0 + eval₂Hom C (majorShiftSubstitution e) E -
    eval₂Hom C (majorShiftCoordinates e) V

noncomputable def majorRationalPolynomial (Q : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (a : B → MvPolynomial U R) :
    MvPolynomial (U ⊕ B) R :=
  Q + eval₂Hom C (majorShiftCoordinates (-a)) V

theorem majorShiftCoordinates_map {T : Type*} [CommRing T]
    (φ : R →+* T) (e : B → MvPolynomial U R) (j : B) :
    map φ (majorShiftCoordinates e j) =
      majorShiftCoordinates (fun i => map φ (e i)) j := by
  simp [majorShiftCoordinates, map_rename]

theorem majorRationalPolynomial_map {T : Type*} [CommRing T]
    (φ : R →+* T) (Q : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (a : B → MvPolynomial U R) :
    map φ (majorRationalPolynomial Q V a) =
      majorRationalPolynomial (map φ Q) (map φ V) (fun i => map φ (a i)) := by
  unfold majorRationalPolynomial
  rw [map_add, map_eval₂Hom]
  simp only [coe_eval₂Hom, eval₂_map_comp_C, majorShiftCoordinates_map,
    Pi.neg_apply, map_neg]
  rfl

theorem majorRationalPolynomial_eval₂ {T : Type*} [CommRing T]
    (φ : R →+* T) (Q : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (a : B → MvPolynomial U R)
    (u : U → T) (b : B → T) :
    eval₂ φ (Sum.elim u b) (majorRationalPolynomial Q V a) =
      eval₂ φ (Sum.elim u b) Q + eval₂ φ (fun i => b i - eval₂ φ u (a i)) V := by
  simp only [majorRationalPolynomial, eval₂_add, coe_eval₂Hom, ← eval₂_assoc,
    majorShiftCoordinates_eval₂, Pi.neg_apply, eval₂_neg, sub_eq_add_neg]

theorem majorSlowPolynomial_eval (D0 : MvPolynomial B R)
    (E : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (e : B → MvPolynomial U R) (u : U → R) (b : B → R) :
    eval (Sum.elim u b) (majorSlowPolynomial D0 E V e) =
      eval b D0 + eval (Sum.elim u (fun i => b i + eval u (e i))) E -
        eval (fun i => b i + eval u (e i)) V := by
  unfold majorSlowPolynomial
  simp only [map_sub, map_add, eval_rename]
  congr 1
  · congr 1
    change eval (Sum.elim u b) (eval₂ C (majorShiftSubstitution e) E) = _
    rw [← eval_assoc]
    simp only [Function.comp_def, majorShiftSubstitution_eval]
  · change eval (Sum.elim u b) (eval₂ C (majorShiftCoordinates e) V) = _
    rw [← eval_assoc]
    simp only [Function.comp_def, majorShiftCoordinates_eval]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {σ J R : Type*} [Fintype J] [CommRing R] [Module R ℝ]

theorem coefficients_ofCoordinates_mem_realDenominatorGrid
    (Q : J → MvPolynomial σ ℝ) (q : ℕ)
    (hQ : ∀ j, realPolynomialCoefficientGrid q (Q j)) (α : σ →₀ ℕ) :
    coefficients (ofCoordinates (R := R) (Pi.basisFun ℝ J) Q) α ∈
      realDenominatorGrid q := by
  classical
  choose z hz using hQ
  refine ⟨fun j => z j α, funext fun j => ?_⟩
  change (z j α : ℝ) = (q : ℝ) *
    coefficients (ofCoordinates (R := R) (Pi.basisFun ℝ J) Q) α j
  rw [coefficients_ofCoordinates_basisFun]
  exact congrFun (hz j) α

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem realPolynomialCoefficientGrid_ratCast_iff
    (q : ℕ) (P : MvPolynomial σ ℚ) :
    realPolynomialCoefficientGrid q (map (algebraMap ℚ ℝ) P) ↔
      (fun m => P.coeff m) ∈ denominatorGrid q := by
  simp only [realPolynomialCoefficientGrid, coeff_map]
  exact real_cast_mem_denominatorGrid_iff q (fun m => P.coeff m)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NormalizedRealPolynomialChart
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem normalizedRealPolynomialChart_eval_comp (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (b : B → ℝ) :
    eval (Sum.elim u b) ∘ normalizedRealPolynomialChart H A =
      Sum.elim (fun i => u i / H i) (fun i => b i - eval u (A i)) := by
  funext j
  exact normalizedRealPolynomialChart_eval H A u b j

theorem eval_normalizedRealPolynomialChart_substitution (H : U → ℝ)
    (A : B → MvPolynomial U ℝ) (u : U → ℝ) (b : B → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    eval (Sum.elim u b) (eval₂Hom C (normalizedRealPolynomialChart H A) p) =
      eval (Sum.elim (fun i => u i / H i) (fun i => b i - eval u (A i))) p := by
  rw [coe_eval₂Hom, ← eval_assoc, normalizedRealPolynomialChart_eval_comp]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorAlgebraicMajorDecomposition
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R T : Type*} [CommRing R] [CommRing T]

noncomputable def specializeMajorParameters (φ : R →+* T)
    (P : MvPolynomial (U ⊕ B) R) (u : U → T) : MvPolynomial B T :=
  eval₂Hom (C.comp φ) (Sum.elim (fun i => C (u i)) X) P

theorem specializeMajorParameters_eval (φ : R →+* T)
    (P : MvPolynomial (U ⊕ B) R) (u : U → T) (b : B → T) :
    eval b (specializeMajorParameters φ P u) = eval₂ φ (Sum.elim u b) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [specializeMajorParameters]
  | add p q hp hq => simpa only [specializeMajorParameters, map_add, eval₂_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    simp only [specializeMajorParameters, coe_eval₂Hom] at hp
    cases i <;> simp [specializeMajorParameters, hp]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointPolynomialDilationGrid
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

noncomputable def scaleMvPolynomialAxes {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ :=
  ∑ α ∈ P.support, monomial α (P.coeff α * monomialScale T α)

theorem scaleMvPolynomialAxes_coeff {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ)
    (α : σ →₀ ℕ) :
    (scaleMvPolynomialAxes T P).coeff α = P.coeff α * monomialScale T α := by
  classical
  rw [scaleMvPolynomialAxes, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [notMem_support_iff.mp h, zero_mul]

theorem scaleMvPolynomialAxes_support_subset {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ) :
    (scaleMvPolynomialAxes T P).support ⊆ P.support := by
  intro α hα
  rw [mem_support_iff, scaleMvPolynomialAxes_coeff] at hα
  exact mem_support_iff.mpr (left_ne_zero_of_mul hα)

theorem scaleMvPolynomialAxes_totalDegree_le {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ) :
    (scaleMvPolynomialAxes T P).totalDegree ≤ P.totalDegree :=
  totalDegree_le_of_support_subset (scaleMvPolynomialAxes_support_subset T P)

theorem scaleMvPolynomialAxes_eval {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ)
    (x : σ → ℝ) :
    eval x (scaleMvPolynomialAxes T P) = eval (fun i => T i * x i) P := by
  classical
  rw [scaleMvPolynomialAxes, eval_sum, eval_eq]
  apply Finset.sum_congr rfl
  intro α _
  rw [eval_monomial]
  simp only [monomialScale, Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  ring

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

theorem scaleMvPolynomialAxes_mem_weightedSupportLE {σ : Type*} (T : σ → ℝ)
    (w : σ → ℕ) (d : ℕ) {P : MvPolynomial σ ℝ}
    (hP : P ∈ weightedSupportLE w d) :
    scaleMvPolynomialAxes T P ∈ weightedSupportLE w d := by
  intro α hα
  exact hP (scaleMvPolynomialAxes_support_subset T P hα)

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

noncomputable def jointRationalPolynomialDilation (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ) :
    MvPolynomial (U ⊕ B) ℚ :=
  aeval (fun i => C (Sum.elim (fun _ : U => (q : ℚ)⁻¹) (fun _ : B => 1) i) * X i) R

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedLinearBaseProjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ τ : Type*} [Fintype τ] [DecidableEq τ]

theorem linearMap_coordinateGradeProjection
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (n : ℕ) (z : τ → ℚ) :
    A (fun j => if v j = n then z j else 0) =
      fun i => if w i = n then A z i else 0 := by
  classical
  funext i
  rw [← linearMap_apply_sum_coordinates A _ i]
  by_cases hi : w i = n
  · rw [if_pos hi, ← linearMap_apply_sum_coordinates A z i]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : v j = n
    · rw [if_pos hj]
    · rw [if_neg hj, mul_zero, hweight j i (by omega), zero_mul]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : v j = n
    · rw [if_pos hj, hweight j i (by omega), zero_mul]
    · rw [if_neg hj, mul_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedReconstruction
namespace OAI

section

namespace Erdos3

variable {σ τ : Type*}

theorem weightedLinearInverseMask_apply [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ))
    (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hBA : ∀ x, B (A x) = x) (x : τ → ℚ) :
    weightedLinearInverseMask B v w (A x) = x := by
  funext j
  change B (fun i => if w i = v j then A x i else 0) j = x j
  rw [← linearMap_coordinateGradeProjection A v w hweight, hBA]
  simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem real_four_alternating (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
    (fourAlternatingMap (R := ℚ)).baseChange ℝ x =
      fourAlternatingMap (R := ℝ) ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)) x) := by
  simp only [fourAlternatingMap, LinearMap.baseChange_sub, LinearMap.baseChange_add,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.proj_apply, real_four_projection]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationPolynomialSymbolDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem polynomialParameterEval_monomial (t : σ → R)
    (α : σ →₀ ℕ) (β : τ →₀ ℕ) (c : R) :
    aeval (Sum.elim (fun i => C (t i)) X) (monomial (α.sumElim β) c) =
      monomial β (aeval t (monomial α c)) := by
  classical
  simp only [aeval_monomial, Finsupp.prod_sumElim, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  simp only [← map_pow, ← map_finsuppProd, Algebra.algebraMap_self, RingHom.id_apply]
  rw [← mul_assoc, ← map_mul]
  rw [← monomial_eq]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

noncomputable def majorTranslationJointPolynomial
    (D : MvPolynomial (U ⊕ B) ℝ) (x : B → MvPolynomial U ℝ) :
    MvPolynomial (U ⊕ B) ℝ :=
  D - eval₂Hom C (fun j => X (Sum.inr j) - rename Sum.inl (x j))
    (specializeMajorParameters (RingHom.id ℝ) D 0)

theorem majorTranslationJointPolynomial_eq_sub_aeval
    (D : MvPolynomial (U ⊕ B) ℝ) (x : B → MvPolynomial U ℝ) :
    majorTranslationJointPolynomial D x =
      D - aeval (Sum.elim (fun _ : U => 0)
        (fun j => X (Sum.inr j) - rename Sum.inl (x j))) D := by
  have hfreeze : specializeMajorParameters (RingHom.id ℝ) D 0 =
      aeval (R := ℝ) (Sum.elim (fun _ : U => 0) (X : B → MvPolynomial B ℝ)) D := by
    simp only [specializeMajorParameters, RingHom.comp_id, Pi.zero_apply, map_zero]
    rfl
  rw [majorTranslationJointPolynomial, hfreeze]
  congr 1
  change aeval (R := ℝ) (fun j => X (Sum.inr j) - rename Sum.inl (x j))
      (aeval (Sum.elim (fun _ : U => 0) X) D) = _
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => aeval f D)
  funext i
  cases i <;> simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorCorrelationBudget
namespace OAI

section

namespace Erdos3

def translationMajorPairBudget (a : ℕ) (p : ℝ) : ℝ :=
  (raisedNiltestBudget p + (a : ℝ)) ^ a

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledGradedBaseCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module

variable {σ : Type*} [fintypeSigma : Fintype σ]

omit fintypeSigma in
@[simp] theorem submoduleBasisCoordinates_range [Fintype σ] {τ : Type*} [Fintype τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) :
    (submoduleBasisCoordinates K b).range = K := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact (b.equivFun.symm z).property
  · intro hx
    refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
    change (b.equivFun.symm (b.equivFun ⟨x, hx⟩)).val = x
    rw [b.equivFun.symm_apply_apply]

omit fintypeSigma in
@[simp] theorem submoduleBasisCoordinates_single [Fintype σ] {τ : Type*}
    [Fintype τ] [DecidableEq τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) (j : τ) :
    submoduleBasisCoordinates K b (Pi.single j 1) = (b j).val := by
  change (b.equivFun.symm (Pi.single j 1)).val = _
  rw [b.equivFun_symm_apply]
  simp [Pi.single_apply]

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DenseRealBoxCell
namespace OAI

section

namespace Erdos3

theorem exists_dense_real_box_cell {ι α : Type} [Fintype ι]
    (S : Finset α) (hS : S.Nonempty) (y : α → ι → ℝ)
    {C : ℝ} (hbound : ∀ a ∈ S, ∀ i, |y a i| ≤ C)
    (q : ℕ) (hq : 0 < q) :
    ∃ T ⊆ S, T.Nonempty ∧ S.card ≤ realBoxCellCount C q ^ Fintype.card ι * T.card ∧
      ∃ c : ι → ℝ, (∀ i, |c i| ≤ C + (1 / 2 : ℝ) / q) ∧
        ∀ a ∈ T, ∀ i, |y a i - c i| ≤ (1 / 2 : ℝ) / q := by
  classical
  let m := realBoxCellCount C q
  have hm : 0 < m := realBoxCellCount_pos C q
  let : NeZero m := ⟨hm.ne'⟩
  let label (a : α) (i : ι) : Fin m :=
    ⟨⌊(q : ℝ) * (y a i + C)⌋₊ % m, Nat.mod_lt _ hm⟩
  obtain ⟨b, hT, hcard⟩ := FreimanModel.exists_nonempty_large_fiber S hS label
  let T := S.filter (fun a => label a = b)
  let c : ι → ℝ := fun i => realBoxCellCenter C q (b i).val
  have hclose : ∀ a ∈ T, ∀ i, |y a i - c i| ≤ (1 / 2 : ℝ) / q := by
    intro a ha i
    have haS := (Finset.mem_filter.mp ha).1
    have he := congrArg Fin.val (congrFun (Finset.mem_filter.mp ha).2 i)
    change ⌊(q : ℝ) * (y a i + C)⌋₊ % m = (b i).val at he
    rw [Nat.mod_eq_of_lt (realBoxCell_floor_lt q (y a i) (hbound a haS i))] at he
    dsimp only [c]
    rw [← he]
    exact realBoxCell_offset q hq (y a i) (hbound a haS i)
  refine ⟨T, Finset.filter_subset _ _, hT, ?_, c, ?_, hclose⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hcard
  · obtain ⟨a, ha⟩ := hT
    intro i
    calc
      |c i| = |y a i - (y a i - c i)| := by congr 1; ring
      _ ≤ |y a i| + |y a i - c i| := abs_sub _ _
      _ ≤ C + (1 / 2 : ℝ) / q := add_le_add
        (hbound a (Finset.mem_filter.mp ha).1 i) (hclose a ha i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NaturalScaleIntegerWindow
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G]

theorem kernel_eq_zero_of_dense_integer_box (φ : (ι → ℤ) →+ G)
    (S : Finset (ι → ℤ)) (R : ι → ℕ) (k : ℕ)
    (hS : S ⊆ centeredIntegerBox R) (hinj : Set.InjOn φ (S : Set _))
    (hlarge : (centeredIntegerBox (fun i => 2 * R i)).card < S.card * k)
    (v : ι → ℤ) (hker : φ v = 0) (hshort : ∀ i, (k : ℤ) * |v i| ≤ (R i : ℤ)) :
    v = 0 := by
  by_contra hv
  apply (not_le_of_gt hlarge)
  apply card_mul_le_of_kernel_translates φ S (centeredIntegerBox (fun i => 2 * R i)) k v hv hker hinj
  intro x hx j hj
  apply (mem_centeredIntegerBox _ _).mpr
  intro i
  have hxi := (mem_centeredIntegerBox R x).mp (hS hx) i
  have hjk : (j : ℤ) ≤ k := by exact_mod_cast hj.le
  have hbound : |x i + (j : ℤ) * v i| ≤ 2 * (R i : ℤ) := by
    calc
      _ ≤ |x i| + |(j : ℤ) * v i| := abs_add_le _ _
      _ = |x i| + (j : ℤ) * |v i| := by
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg j)]
      _ ≤ (R i : ℤ) + (k : ℤ) * |v i| :=
        add_le_add hxi (mul_le_mul_of_nonneg_right hjk (abs_nonneg _))
      _ ≤ 2 * (R i : ℤ) := by linarith only [hshort i]
  change |x i + j • v i| ≤ ((2 * R i : ℕ) : ℤ)
  simpa only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hbound

theorem injOn_small_integer_box_of_dense_subset (φ : (ι → ℤ) →+ G)
    (S : Finset (ι → ℤ)) (R r : ι → ℕ) (k : ℕ)
    (hS : S ⊆ centeredIntegerBox R) (hinj : Set.InjOn φ (S : Set _))
    (hlarge : (centeredIntegerBox (fun i => 2 * R i)).card < S.card * k)
    (hscale : ∀ i, 2 * k * r i ≤ R i) :
    Set.InjOn φ (centeredIntegerBox r : Set _) := by
  intro x hx y hy hxy
  apply sub_eq_zero.mp
  apply kernel_eq_zero_of_dense_integer_box φ S R k hS hinj hlarge (x - y)
  · rw [map_sub, hxy, sub_self]
  · intro i
    have hx' := (mem_centeredIntegerBox r x).mp hx i
    have hy' := (mem_centeredIntegerBox r y).mp hy i
    have hscale' : 2 * (k : ℤ) * (r i : ℤ) ≤ R i := by exact_mod_cast hscale i
    calc
      (k : ℤ) * |(x - y) i| ≤ (k : ℤ) * (|x i| + |y i|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Int.natCast_nonneg k)
      _ ≤ (k : ℤ) * ((r i : ℤ) + (r i : ℤ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hx' hy') (Int.natCast_nonneg k)
      _ = 2 * (k : ℤ) * (r i : ℤ) := by ring
      _ ≤ (R i : ℤ) := hscale'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProperCyclicKernelBasis
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem affine_box_card_le_radius_product
    {ι G : Type} [Fintype ι] [AddCommGroup G]
    (η : (ι → ℤ) →+ G) (R : ι → ℕ) (h₀ : G) (J : Finset G)
    (hrep : ∀ h ∈ J, ∃ x : ι → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    (J.card : ℝ) ≤ (2 : ℝ) ^ Fintype.card ι * ∏ i, ((R i : ℝ) + 1) := by
  classical
  have hsub : J ⊆ (centeredIntegerBox R).image (fun x => h₀ + η x) := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := hrep h hh
    exact Finset.mem_image.mpr ⟨x, (mem_centeredIntegerBox R x).mpr hx, rfl⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  have hp : (centeredIntegerBox R).card ≤ 2 ^ Fintype.card ι * ∏ i, (R i + 1) := by
    rw [card_centeredIntegerBox]
    calc
      (∏ i, (2 * R i + 1)) ≤ ∏ i, (2 * (R i + 1)) := by
        gcongr with i
        omega
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  exact_mod_cast hc.trans hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MajorTranslationJointLower
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorTranslationJointPolynomial_sub
    (D E : MvPolynomial (U ⊕ B) ℝ) (A : B → MvPolynomial U ℝ) :
    majorTranslationJointPolynomial (D - E) A =
      majorTranslationJointPolynomial D A - majorTranslationJointPolynomial E A := by
  simp only [majorTranslationJointPolynomial_eq_sub_aeval, map_sub]
  abel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

theorem weight_le (s : ℕ) : ∀ i, weight i ≤ s := fun i => Fin.elim0 i

theorem specialize_rename {U : Type*} (P : MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) (rename (Sum.inl : U → U ⊕ Fin 0) P) u =
      C (eval u P) := by
  simp only [specializeMajorParameters, RingHom.comp_id, eval₂Hom_rename]
  change eval₂ C (fun i => C (u i)) P = C (eval u P)
  exact (eval₂_comp C u P).symm

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintBasis
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {η B κ : Type*} [Fintype η] [Fintype B]

theorem realRationalCoordinateSpan_top :
    realRationalCoordinateSpan (⊤ : Submodule ℚ (B → ℚ)) = ⊤ := by
  unfold realRationalCoordinateSpan
  rw [Submodule.baseChange_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr realRationalCoordinateEquiv.surjective

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TaggedSubmoduleBasis
namespace OAI

section

namespace Erdos3

open Module

variable {R T : Type*} [Semiring R] {J I : T → Type*}

variable [Fintype T]

theorem taggedSubmoduleBasis_of_ne
    (U : ∀ t, Submodule R (J t → R)) (b : ∀ t, Basis (I t) R (U t))
    (t : T) (i : I t) (t' : T) (j : J t') (h : t' ≠ t) :
    (taggedSubmoduleBasis U b ⟨t, i⟩ : (Σ t, J t) → R) ⟨t', j⟩ = 0 := by
  classical
  rw [taggedSubmoduleBasis_apply, Pi.single_eq_of_ne h]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRoundedGraphEnergy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteCoefficientLift_mem_Ico {I : Type*} {M : ℕ} [NeZero M]
    (l : ℕ) (hl : 0 < l) (b : I → ZMod M) (i : I) :
    finiteCoefficientLift l b i ∈ Set.Ico (0 : ℝ) (1 / l) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · change ((b i).val : ℝ) / ((M : ℝ) * l) < 1 / l
    apply (div_lt_iff₀ (mul_pos hM hlR)).mpr
    have hv : ((b i).val : ℝ) < M := by exact_mod_cast (b i).val_lt
    have heq : (1 / (l : ℝ)) * ((M : ℝ) * l) = M := by field_simp
    rwa [heq]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem variableCoefficientLift_mem_Ico {I : Type*} {M : I → ℕ} [∀ i, NeZero (M i)]
    (l : I → ℕ) (hl : ∀ i, 0 < l i) (b : ∀ i, ZMod (M i)) (i : I) :
    variableCoefficientLift l b i ∈ Set.Ico (0 : ℝ) (1 / l i) := by
  exact finiteCoefficientLift_mem_Ico (l i) (hl i) (fun _ : Unit => b i) ()

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ProperAffineBoxRestriction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem centeredScalarCenter_offset (R k : ℕ) (x : ℤ)
    (hx : |x| ≤ (R : ℤ)) :
    |x - centeredScalarCenter R k (centeredScalarBlock R k x)| ≤ (R / (2 * k) : ℕ) := by
  let t := (x + (R : ℤ)).toNat
  let L := 2 * (R / (2 * k)) + 1
  have ht : (t : ℤ) = x + R := by
    apply Int.toNat_of_nonneg
    have h := abs_le.mp hx
    omega
  have hmod : t % L < L := Nat.mod_lt t (by dsimp [L]; omega)
  have hrem : ((t % L : ℕ) : ℤ) + (L : ℤ) * (t / L : ℕ) = x + R := by
    rw [← ht]
    exact_mod_cast Nat.mod_add_div t L
  have hcancel : x - centeredScalarCenter R k (centeredScalarBlock R k x) =
      (t % L : ℕ) - (R / (2 * k) : ℕ) := by
    unfold centeredScalarCenter centeredScalarBlock
    change x - ((t / L : ℕ) * (2 * ((R / (2 * k) : ℕ) : ℤ) + 1) - R +
      ((R / (2 * k) : ℕ) : ℤ)) = ((t % L : ℕ) : ℤ) - ((R / (2 * k) : ℕ) : ℤ)
    have hL : (L : ℤ) = 2 * ((R / (2 * k) : ℕ) : ℤ) + 1 := by
      simp only [L, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [hL] at hrem
    nlinarith only [hrem]
  have hmod' : ((t % L : ℕ) : ℤ) ≤ 2 * ((R / (2 * k) : ℕ) : ℤ) := by
    have h : t % L ≤ 2 * (R / (2 * k)) := Nat.le_of_lt_succ hmod
    exact_mod_cast h
  rw [hcancel, abs_le]
  constructor <;> linarith only [hmod', Int.natCast_nonneg (t % L)]

theorem exists_dense_centered_box_block {ι α : Type*} [Fintype ι]
    (S : Finset α) (hS : S.Nonempty) (x : α → ι → ℤ) (R : ι → ℕ)
    (k : ℕ) (hk : 0 < k) (hbound : ∀ a ∈ S, ∀ i, |x a i| ≤ (R i : ℤ)) :
    ∃ T ⊆ S, T.Nonempty ∧ S.card ≤ (4 * k) ^ Fintype.card ι * T.card ∧
      ∃ c : ι → ℤ, ∀ a ∈ T, ∀ i, |x a i - c i| ≤ (R i / (2 * k) : ℕ) := by
  classical
  have hfour : 0 < 4 * k := by omega
  let : NeZero (4 * k) := ⟨hfour.ne'⟩
  let label (a : α) (i : ι) : Fin (4 * k) :=
    ⟨centeredScalarBlock (R i) k (x a i) % (4 * k), Nat.mod_lt _ hfour⟩
  obtain ⟨b, hT, hsize⟩ := FreimanModel.exists_nonempty_large_fiber S hS label
  let T := S.filter fun a => label a = b
  refine ⟨T, Finset.filter_subset _ _, hT, ?_,
    (fun i => centeredScalarCenter (R i) k (b i).val), ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hsize
  · intro a ha i
    have hmem := (Finset.mem_filter.mp ha).1
    have heq := congrArg Fin.val (congrFun (Finset.mem_filter.mp ha).2 i)
    have hlt := centeredScalarBlock_lt (R i) k hk (x a i) (hbound a hmem i)
    change centeredScalarBlock (R i) k (x a i) % (4 * k) = (b i).val at heq
    rw [Nat.mod_eq_of_lt hlt] at heq
    change |x a i - centeredScalarCenter (R i) k (b i).val| ≤ (R i / (2 * k) : ℕ)
    rw [← heq]
    exact centeredScalarCenter_offset (R i) k (x a i) (hbound a hmem i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFourBalancedDual
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

theorem real_four_diagonal (x : ℝ ⊗[ℚ] V) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V))
        ((fourDiagonalMap (R := ℚ)).baseChange ℝ x) =
      fourDiagonalMap (R := ℝ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget
namespace OAI

section

namespace Erdos3

open CyclicCrootSisask

theorem properAffineVolume_bound (P : ℝ) (n : ℕ) :
    2 * ((2 ^ 14 : ℝ) * (Real.exp (P + 13 * n)) ^ 6 * 16 ^ (n + 1)) ^ 16 ≤
      Real.exp (properAffineVolumeLog P n) := by
  calc
    _ ≤ Real.exp 2 * (Real.exp (44 + 6 * max P 0 + 94 * n)) ^ 16 := by
      gcongr
      · linarith [Real.add_one_le_exp (2 : ℝ)]
      · exact roundedModelScale_le_exp P n
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CanonicalReducedMajorTwistedNiltest
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

variable {U : Type*} {m : ℕ}

theorem majorZeroParameterSlice_eq (D : MvPolynomial (U ⊕ Fin m) ℝ) :
    specializeMajorParameters (RingHom.id ℝ) D 0 =
      aeval (Sum.elim (fun _ : U => (0 : MvPolynomial (Fin m) ℝ)) X) D := by
  simp only [specializeMajorParameters, RingHom.comp_id, Pi.zero_apply, map_zero]
  rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem rationalHeightLE_of_integral_mul_of_abs_le (q : ℚ) {Q B D : ℕ}
    (hQ : 0 < Q) (hQD : Q ≤ D) (hB : 1 ≤ B)
    (hint : ∃ z : ℤ, (Q : ℚ) * q = z) (habs : |(q : ℝ)| ≤ B) :
    RationalHeightLE q (B * D) := by
  obtain ⟨z, hz⟩ := hint
  have hzR : (Q : ℝ) * (q : ℝ) = z := by exact_mod_cast hz
  have hzbound : z.natAbs ≤ B * D := by
    apply (Nat.cast_le (α := ℝ)).mp
    simp only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_mul]
    rw [← hzR, abs_mul, abs_of_nonneg (Nat.cast_nonneg Q)]
    exact (mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg Q)).trans
      (by nlinarith [show (Q : ℝ) ≤ D by exact_mod_cast hQD])
  have he : q = (z : ℚ) / (Q : ℤ) := by
    apply (eq_div_iff (by exact_mod_cast hQ.ne' : ((Q : ℤ) : ℚ) ≠ 0)).mpr
    simpa only [Int.cast_natCast, mul_comm] using hz
  rw [he]
  exact rationalHeightLE_fraction z Q (by exact_mod_cast hQ.ne') hzbound
    (by simpa only [Int.natAbs_natCast] using hQD.trans (Nat.le_mul_of_pos_left D hB))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotential
namespace OAI

section

namespace Erdos3

theorem linearRestrictionArithmeticBudget_le_exp (n m d H K : ℕ) {p P Q : ℝ}
    (hp : 0 ≤ p) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp Q) :
    (((((n + 1) ^ d * K) * (m * H + 1) ^ d) *
      (K ^ ((n + 1) ^ d) * H ^ ((n * m) * d)) : ℕ) : ℝ) ≤
        Real.exp ((d : ℝ) * p + Q + (d : ℝ) * (p + P + 1) +
          (p + 1) ^ d * Q + p * p * d * P) := by
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p :=
    (add_le_add hn (le_refl 1)).trans (Real.add_one_le_exp p)
  have hnPow : ((n : ℝ) + 1) ^ d ≤ Real.exp ((d : ℝ) * p) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hn1 d
  have hmexp : (m : ℝ) ≤ Real.exp p := by
    exact hm.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  have hmH : (m : ℝ) * H ≤ Real.exp (p + P) := by
    rw [Real.exp_add]
    exact mul_le_mul hmexp hH (Nat.cast_nonneg H) (Real.exp_nonneg p)
  have hmH1 : (m : ℝ) * H + 1 ≤ Real.exp (p + P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (add_nonneg hp hP) hmH
  have hmPow : ((m : ℝ) * H + 1) ^ d ≤ Real.exp ((d : ℝ) * (p + P + 1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hmH1 d
  have hKPow : (K : ℝ) ^ ((n + 1) ^ d) ≤ Real.exp ((p + 1) ^ d * Q) := by
    calc
      _ ≤ (Real.exp Q) ^ ((n + 1) ^ d) := pow_le_pow_left₀ (Nat.cast_nonneg K) hK _
      _ = Real.exp ((((n : ℝ) + 1) ^ d) * Q) := by
        rw [← Real.exp_nat_mul]
        simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (add_le_add hn (le_refl 1)) d) hQ)
  have hHPow : (H : ℝ) ^ ((n * m) * d) ≤ Real.exp (p * p * d * P) := by
    calc
      _ ≤ (Real.exp P) ^ ((n * m) * d) := pow_le_pow_left₀ (Nat.cast_nonneg H) hH _
      _ = Real.exp ((n : ℝ) * m * d * P) := by
        rw [← Real.exp_nat_mul]
        simp only [Nat.cast_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul hn hm (Nat.cast_nonneg m) hp)
          (Nat.cast_nonneg d)) hP)
  have hfront := mul_le_mul hnPow hK (Nat.cast_nonneg K) (Real.exp_nonneg _)
  have hscaled := mul_le_mul hfront hmPow (by positivity) (by positivity)
  have hden := mul_le_mul hKPow hHPow (by positivity) (Real.exp_nonneg _)
  have htotal := mul_le_mul hscaled hden (by positivity) (by positivity)
  push_cast
  refine htotal.trans_eq ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end Erdos3

end

section

namespace Erdos3

def projectedPotentialHeight (N n d H : ℕ) : ℕ :=
  linearRestrictionHeight n N d (rationalKernelHeight N H)
    ((n + 1) * (d * linearRestrictionHeight N n d H H) ^ n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BoundedKernelGridEnumerationBudget
namespace OAI

section

namespace Erdos3

theorem finite_card_real_grid_window {ι : Type*} [Fintype ι]
    (S : Set (ι → ℝ)) (m N : ℕ) (hm : 0 < m) (center : ι → ℝ) {B : ℝ}
    (hgrid : S ⊆ realDenominatorGrid m)
    (hwindow : ∀ x ∈ S, ∀ i, |x i - center i| ≤ B)
    (hN : (m : ℝ) * B ≤ N) :
    S.Finite ∧ S.ncard ≤ (2 * N + 3) ^ Fintype.card ι := by
  classical
  let z : S → ι → ℤ := fun x => Classical.choose (hgrid x.property)
  have hz (x : S) (i : ι) : (m : ℝ) * x.val i = (z x i : ℝ) :=
    (congrFun (Classical.choose_spec (hgrid x.property)) i).symm
  let shift : ι → ℤ := fun i => ⌊(m : ℝ) * center i⌋
  have hzi (x : S) (i : ι) :
      z x i - shift i ∈ Set.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1) := by
    have hb := real_grid_shifted_integer_bound (hz x i) (hwindow x x.property i) hN
    apply abs_le.mp
    exact_mod_cast hb
  let f : S → (ι → Set.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)) :=
    fun x i => ⟨z x i - shift i, hzi x i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : z x i - shift i = z y i - shift i := congrArg Subtype.val (congrFun hxy i)
    have hi' : z x i = z y i := by omega
    apply mul_left_cancel₀ (show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne')
    rw [hz, hz, hi']
  let : Finite S := Finite.of_injective f hf
  have hcardI : Fintype.card (Set.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)) = 2 * N + 3 := by
    have h := Int.card_fintype_Icc_of_le (-((N : ℤ) + 1)) ((N : ℤ) + 1)
      (show -((N : ℤ) + 1) ≤ (N : ℤ) + 1 + 1 by omega)
    omega
  refine ⟨Set.toFinite S, ?_⟩
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fun, hcardI] using hc

end Erdos3

end

section

namespace Erdos3

theorem exists_scalar_rational_grid_window (q : ℕ) (hq : 0 < q) (c B : ℝ) :
    ∃ S : Finset ℚ, S.card ≤ 2 * ⌈(q : ℝ) * B⌉₊ + 3 ∧
      ∀ r : ℚ, r ∈ S ↔
        (∃ z : ℤ, (r : ℝ) = (z : ℝ) / q) ∧ |(r : ℝ) - c| ≤ B := by
  classical
  let S : Set ℚ := {r | (∃ z : ℤ, (r : ℝ) = (z : ℝ) / q) ∧ |(r : ℝ) - c| ≤ B}
  let f : ℚ → Unit → ℝ := fun r _ => r
  let V : Set (Unit → ℝ) := f '' S
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hgrid : V ⊆ realDenominatorGrid q := by
    rintro v ⟨r, ⟨⟨z, hz⟩, _⟩, rfl⟩
    refine ⟨fun _ => z, ?_⟩
    funext i
    change (z : ℝ) = (q : ℝ) * (r : ℝ)
    rw [hz]
    field_simp
  have hwindow : ∀ v ∈ V, ∀ i, |v i - c| ≤ B := by
    rintro v ⟨r, hr, rfl⟩ i
    exact hr.2
  obtain ⟨hVfin, hVcard⟩ := finite_card_real_grid_window V q ⌈(q : ℝ) * B⌉₊ hq
    (fun _ => c) hgrid hwindow (Nat.le_ceil _)
  have hinj : Function.Injective f := by
    intro r t h
    have hr : (r : ℝ) = (t : ℝ) := congrFun h ()
    exact_mod_cast hr
  have hmaps : Set.MapsTo f S V := fun r hr => ⟨r, hr, rfl⟩
  have hSfin : S.Finite := Set.Finite.of_injOn hmaps hinj.injOn hVfin
  have hcard : S.ncard ≤ 2 * ⌈(q : ℝ) * B⌉₊ + 3 := by
    have h := (Set.ncard_le_ncard_of_injOn f hmaps hinj.injOn hVfin).trans hVcard
    simpa only [Fintype.card_unit, pow_one] using h
  refine ⟨hSfin.toFinset, ?_, ?_⟩
  · simpa only [Set.ncard_eq_toFinset_card S hSfin] using hcard
  · intro r
    exact hSfin.mem_toFinset

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteTriangularRationalCorrection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_finite_triangular_correction_of_windows
    (B : ℝ) (hB : 0 ≤ B) (q W : ℕ)
    (hwindow : ∀ c : ℝ, ∃ S : Finset ℚ, S.card ≤ W ∧ ∀ r : ℚ,
      r ∈ S ↔ (∃ z : ℤ, r = (z : ℚ) / q) ∧ |(r : ℝ) - c| ≤ B) :
    ∀ n (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ),
      (∀ i j, i < j → A i j = 0) →
      (∀ i, A i i ≠ 0 ∧ |A i i| ≤ 1) →
      ∃ S : Finset ((Fin n → ℝ) × (Fin n → ℚ)), S.card ≤ W ^ n ∧
        ∀ sr, sr ∈ S ↔ sr ∈ triangularCorrectionSolutions A c B q := by
  classical
  choose window hcard hmem using hwindow
  intro n
  induction n with
  | zero =>
    intro A c htri hdiag
    let z : (Fin 0 → ℝ) × (Fin 0 → ℚ) := (0, 0)
    refine ⟨{z}, by simp, ?_⟩
    intro sr
    have he : sr = z := Subsingleton.elim _ _
    subst sr
    simp [triangularCorrectionSolutions]
  | succ n ih =>
    intro A c htri hdiag
    let A' : Matrix (Fin n) (Fin n) ℝ := fun i j => A i.castSucc j.castSucc
    let c' : Fin n → ℝ := fun i => c i.castSucc
    obtain ⟨S, hS, hSiff⟩ := ih A' c'
      (fun i j hij => htri i.castSucc j.castSucc hij) (fun i => hdiag i.castSucc)
    let center : ((Fin n → ℝ) × (Fin n → ℚ)) → ℝ :=
      fun u => c (Fin.last n) - ∑ j, A (Fin.last n) j.castSucc * u.1 j
    let extend : ((Fin n → ℝ) × (Fin n → ℚ)) → ℚ →
        ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)) := fun u r =>
      (Fin.snoc u.1 ((center u - (r : ℝ)) / A (Fin.last n) (Fin.last n)), Fin.snoc u.2 r)
    let all := S.biUnion (fun u => (window (center u)).image (extend u))
    let out := all.filter (fun sr => sr ∈ triangularCorrectionSolutions A c B q)
    have hallcard : all.card ≤ W ^ (n + 1) := by
      calc
        all.card ≤ ∑ u ∈ S, ((window (center u)).image (extend u)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ S, W := Finset.sum_le_sum
          (fun u _ => Finset.card_image_le.trans (hcard (center u)))
        _ = S.card * W := by simp
        _ ≤ W ^ n * W := Nat.mul_le_mul_right W hS
        _ = W ^ (n + 1) := (pow_succ W n).symm
    refine ⟨out, (Finset.card_filter_le _ _).trans hallcard, ?_⟩
    intro sr
    constructor
    · intro hs
      exact (Finset.mem_filter.mp hs).2
    · intro hsr
      apply Finset.mem_filter.mpr
      refine ⟨?_, hsr⟩
      let u : (Fin n → ℝ) × (Fin n → ℚ) :=
        (fun i => sr.1 i.castSucc, fun i => sr.2 i.castSucc)
      have hu : u ∈ S := (hSiff u).mpr
        (triangularCorrectionSolutions_prefix htri hsr)
      have hr : sr.2 (Fin.last n) ∈ window (center u) := by
        apply (hmem _ _).mpr
        refine ⟨hsr.2.1 (Fin.last n), ?_⟩
        exact triangularCorrectionSolutions_last_window hsr hB
          (hdiag (Fin.last n)).2
      apply Finset.mem_biUnion.mpr
      refine ⟨u, hu, Finset.mem_image.mpr ⟨sr.2 (Fin.last n), hr, ?_⟩⟩
      have hlast := triangularCorrectionSolutions_last_eq hsr
        (hdiag (Fin.last n)).1
      apply Prod.ext
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [extend, Fin.snoc_last, center, u] using hlast.symm
        · simp only [extend, Fin.snoc_castSucc, u]
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [extend, Fin.snoc_last]
        · simp only [extend, Fin.snoc_castSucc, u]

theorem exists_finite_triangular_rational_correction
    (q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (htri : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ S : Finset ((Fin n → ℝ) × (Fin n → ℚ)),
      S.card ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ n ∧
      ∀ sr, sr ∈ S ↔ sr ∈ triangularCorrectionSolutions A c B q := by
  apply exists_finite_triangular_correction_of_windows B hB q
    (2 * ⌈(q : ℝ) * B⌉₊ + 3) ?_ n A c htri (fun i => ⟨hdiag i, hdiagBound i⟩)
  intro center
  obtain ⟨S, hS, hmem⟩ := exists_scalar_rational_grid_window q hq center B
  refine ⟨S, hS, ?_⟩
  intro r
  rw [hmem]
  apply and_congr_left
  intro _
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by exact_mod_cast hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by exact_mod_cast hz⟩

theorem exists_triangular_rational_correction_enumeration
    (q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (htri : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ n ∧
      ∃ candidate : Fin m → ((Fin n → ℝ) × (Fin n → ℚ)),
        (∀ j, candidate j ∈ triangularCorrectionSolutions A c B q) ∧
        ∀ sr, sr ∈ triangularCorrectionSolutions A c B q → ∃ j, candidate j = sr := by
  classical
  obtain ⟨S, hS, hmem⟩ := exists_finite_triangular_rational_correction q hq B hB
    n A c htri hdiag hdiagBound
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, ?_, fun j => (e.symm j).val, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hS
  · intro j
    exact (hmem _).mp (e.symm j).property
  · intro sr hsr
    let v : S := ⟨sr, (hmem sr).mpr hsr⟩
    exact ⟨e v, congrArg Subtype.val (e.symm_apply_apply v)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealFunctionalBCH
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realifyFunctional_lie_eq_zero (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ x y : L, η ⁅x, y⁆ = 0) (x y : ℝ ⊗[ℚ] L) :
    realifyFunctional η ⁅x, y⁆ = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, realifyFunctional_tmul,
        hη, Rat.cast_zero, mul_zero]
    | add y z hy hz => simp only [LieRing.lie_add, map_add, hy, hz, add_zero]
  | add x z hx hz => simp only [LieRing.add_lie, map_add, hx, hz, add_zero]

attribute [local instance] LieRing.ofAssociativeRing

noncomputable def realifyFunctionalLie (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ x y : L, η ⁅x, y⁆ = 0) : (ℝ ⊗[ℚ] L) →ₗ⁅ℚ⁆ ℝ where
  toLinearMap := (realifyFunctional η).restrictScalars ℚ
  map_lie' {x y} := by
    change realifyFunctional η ⁅x, y⁆ = ⁅realifyFunctional η x, realifyFunctional η y⁆
    rw [realifyFunctional_lie_eq_zero η hη]
    simp only [Ring.lie_def, mul_comm, sub_self]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem lowTaggedIndex_property (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    (lowTaggedIndex J d i).1.val + 1 ≤ d :=
  ((Fintype.equivFin (LowTaggedIndex J d)).symm i).property

theorem lowTaggedWeight_pos (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    0 < lowTaggedWeight J d i := Nat.succ_pos _

theorem lowTaggedWeight_le (d : ℕ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedWeight J d i ≤ d := lowTaggedIndex_property J d i

theorem lowTaggedIndex_card_le (d : ℕ) :
    Fintype.card (LowTaggedIndex J d) ≤ Fintype.card (Σ j, J j) :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

variable {X : Type*}

noncomputable def lowTaggedFrequency (d : ℕ) (a : (Σ j, J j) → ℤ) :
    Fin (Fintype.card (LowTaggedIndex J d)) → ℤ :=
  fun i => a (lowTaggedIndex J d i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AlgebraicMajorWeightedDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R : Type*} [CommRing R]

theorem majorShiftCoordinates_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (e : B → MvPolynomial U R)
    (he : ∀ j, e j ∈ weightedSupportLE v (w j)) (j : B) :
    majorShiftCoordinates e j ∈ weightedSupportLE (Sum.elim v w) (w j) := by
  exact (weightedSupportLE _ _).add_mem
    (weightedSupportLE_X (Sum.elim v w) (Sum.inr j))
    (weightedSupportLE_rename_inl_ring v w (he j))

theorem majorShiftSubstitution_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (e : B → MvPolynomial U R)
    (he : ∀ j, e j ∈ weightedSupportLE v (w j)) (i : U ⊕ B) :
    majorShiftSubstitution e i ∈ weightedSupportLE (Sum.elim v w) (Sum.elim v w i) := by
  cases i with
  | inl i => exact weightedSupportLE_X (Sum.elim v w) (Sum.inl i)
  | inr j => exact majorShiftCoordinates_weightedSupportLE v w e he j

theorem majorSlowPolynomial_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (D0 : MvPolynomial B R) (E : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (e : B → MvPolynomial U R) {d : ℕ}
    (hD0 : D0 ∈ weightedSupportLE w d)
    (hE : E ∈ weightedSupportLE (Sum.elim v w) d)
    (hV : V ∈ weightedSupportLE w d)
    (he : ∀ j, e j ∈ weightedSupportLE v (w j)) :
    majorSlowPolynomial D0 E V e ∈ weightedSupportLE (Sum.elim v w) d := by
  unfold majorSlowPolynomial
  apply (weightedSupportLE _ _).sub_mem
  · apply (weightedSupportLE _ _).add_mem (weightedSupportLE_rename_inr_ring v w hD0)
    exact weightedSupportLE_aeval (Sum.elim v w) (Sum.elim v w)
      (majorShiftSubstitution e) (majorShiftSubstitution_weightedSupportLE v w e he) hE
  · exact weightedSupportLE_aeval w (Sum.elim v w) (majorShiftCoordinates e)
      (majorShiftCoordinates_weightedSupportLE v w e he) hV

theorem majorRationalPolynomial_weightedSupportLE (v : U → ℕ) (w : B → ℕ)
    (Q : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (a : B → MvPolynomial U R) {d : ℕ}
    (hQ : Q ∈ weightedSupportLE (Sum.elim v w) d)
    (hV : V ∈ weightedSupportLE w d)
    (ha : ∀ j, a j ∈ weightedSupportLE v (w j)) :
    majorRationalPolynomial Q V a ∈ weightedSupportLE (Sum.elim v w) d := by
  apply (weightedSupportLE _ _).add_mem hQ
  exact weightedSupportLE_aeval w (Sum.elim v w) (majorShiftCoordinates (-a))
    (majorShiftCoordinates_weightedSupportLE v w (-a)
      (fun j => (weightedSupportLE v (w j)).neg_mem (ha j))) hV

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LowTaggedCoordinateRestriction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem lowTaggedSlot_eq_of_tag (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (i : Fin (Fintype.card (LowTaggedIndex J d)))
    (hi : (lowTaggedIndex J d i).1 = j) :
    ∃ k : J j, lowTaggedSlot J d j hj k = i := by
  let q := (Fintype.equivFin (LowTaggedIndex J d)).symm i
  have hq : q.val.1 = j := hi
  have hqi : Fintype.equivFin (LowTaggedIndex J d) q = i :=
    (Fintype.equivFin (LowTaggedIndex J d)).apply_symm_apply i
  obtain ⟨⟨j', k⟩, h⟩ := q
  dsimp at hq
  subst j'
  exact ⟨k, hqi⟩

theorem lowTaggedEmbedding_apply_of_ne (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (v : J j → ℝ)
    (i : Fin (Fintype.card (LowTaggedIndex J d)))
    (hi : (lowTaggedIndex J d i).1 ≠ j) :
    lowTaggedEmbedding J d j hj v i = 0 := by
  classical
  rw [lowTaggedEmbedding_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply Pi.single_eq_of_ne
  intro he
  apply hi
  rw [he, lowTaggedIndex_slot]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullTaggedChartCoefficientRange
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype I]

theorem normalizedRealPolynomialChart_linear_restriction_coordinate
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (A' : I → MvPolynomial U ℝ)
    (E : B → I → ℝ) (hA : ∀ b, A b = ∑ i, C (E b i) * A' i)
    (j : U ⊕ B) :
    aeval (R := ℝ) (polynomialTagLinearEmbedding E)
        (normalizedRealPolynomialChart H A j) =
      aeval (R := ℝ) (normalizedRealPolynomialChart H A')
        (polynomialTagLinearEmbedding E j) := by
  classical
  cases j with
  | inl u => simp
  | inr b =>
    simp only [normalizedRealPolynomialChart_inr, map_sub, aeval_X,
      polynomialTagLinearEmbedding_inr, polynomialTagLinearEmbedding_rename,
      map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_eq]
    rw [hA b]
    simp only [map_sum, map_mul, rename_C]
    simp only [mul_sub, Finset.sum_sub_distrib]

theorem normalizedRealPolynomialChart_linear_restriction
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (A' : I → MvPolynomial U ℝ)
    (E : B → I → ℝ) (hA : ∀ b, A b = ∑ i, C (E b i) * A' i)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    aeval (R := ℝ) (polynomialTagLinearEmbedding E)
        (aeval (R := ℝ) (normalizedRealPolynomialChart H A) p) =
      aeval (R := ℝ) (normalizedRealPolynomialChart H A')
        (aeval (R := ℝ) (polynomialTagLinearEmbedding E) p) := by
  have h : (aeval (R := ℝ) (polynomialTagLinearEmbedding E)).comp
      (aeval (R := ℝ) (normalizedRealPolynomialChart H A)) =
      (aeval (R := ℝ) (normalizedRealPolynomialChart H A')).comp
        (aeval (R := ℝ) (polynomialTagLinearEmbedding E)) := by
    ext j : 1
    simpa only [AlgHom.comp_apply, aeval_X] using
      normalizedRealPolynomialChart_linear_restriction_coordinate H A A' E hA j
  exact AlgHom.congr_fun h p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTagRestrictionBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype I]

theorem polynomialTagRestriction_totalDegree_le (E : B → I → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    (aeval (polynomialTagLinearEmbedding E) p).totalDegree ≤ p.totalDegree := by
  change (eval₂Hom C (polynomialTagLinearEmbedding E) p).totalDegree ≤ p.totalDegree
  simpa only [mul_one] using polynomial_substitution_totalDegree_le p
    (polynomialTagLinearEmbedding E) (polynomialTagLinearEmbedding_totalDegree_le E) le_rfl

theorem polynomialSubspaceRestriction_totalDegree_le
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    (polynomialSubspaceRestriction K e p).totalDegree ≤ p.totalDegree :=
  polynomialTagRestriction_totalDegree_le _ p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteRankTriangularFinset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteRankCorrectionSolutions_reindex
    {I J : Type*} [Fintype I] [Fintype J] (e : J ≃ I)
    (A : Matrix I I ℝ) (c : I → ℝ) (B : ℝ) (q : ℕ)
    (sr : (I → ℝ) × (I → ℚ)) :
    sr ∈ finiteRankCorrectionSolutions A c B q ↔
      ((fun i => sr.1 (e i)), (fun i => sr.2 (e i))) ∈
        finiteRankCorrectionSolutions (fun i j => A (e i) (e j)) (fun i => c (e i)) B q := by
  constructor
  · intro hs
    refine ⟨fun i => hs.1 (e i), fun i => hs.2.1 (e i), ?_⟩
    intro i
    dsimp only
    have hsum : (∑ j, A (e i) (e j) * sr.1 (e j)) =
        ∑ j : I, A (e i) j * sr.1 j := e.sum_comp (fun j : I => A (e i) j * sr.1 j)
    rw [hsum]
    exact hs.2.2 (e i)
  · intro hs
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simpa only [e.apply_symm_apply] using hs.1 (e.symm i)
    · intro i
      simpa only [e.apply_symm_apply] using hs.2.1 (e.symm i)
    · intro i
      have hi := hs.2.2 (e.symm i)
      dsimp only at hi
      have hsum : (∑ j, A i (e j) * sr.1 (e j)) =
          ∑ j : I, A i j * sr.1 j := e.sum_comp (fun j : I => A i j * sr.1 j)
      simpa only [e.apply_symm_apply, hsum] using hi

theorem exists_finite_rank_triangular_correction_enumeration
    {I : Type*} [Fintype I] (q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B)
    (rank : I → ℕ) (A : Matrix I I ℝ) (c : I → ℝ)
    (htri : ∀ i j, rank j ≤ rank i → j ≠ i → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ Fintype.card I ∧
      ∃ candidate : Fin m → ((I → ℝ) × (I → ℚ)),
        (∀ j, candidate j ∈ finiteRankCorrectionSolutions A c B q) ∧
        ∀ sr, sr ∈ finiteRankCorrectionSolutions A c B q → ∃ j, candidate j = sr := by
  obtain ⟨e, _, he⟩ := exists_rank_triangular_equiv rank A htri
  let A' : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ :=
    fun i j => A (e i) (e j)
  let c' : Fin (Fintype.card I) → ℝ := fun i => c (e i)
  obtain ⟨m, hm, candidate, hmem, hcover⟩ :=
    exists_triangular_rational_correction_enumeration q hq B hB (Fintype.card I) A' c'
      he (fun i => hdiag (e i)) (fun i => hdiagBound (e i))
  let candidate' : Fin m → ((I → ℝ) × (I → ℚ)) :=
    fun j => (fun i => (candidate j).1 (e.symm i), fun i => (candidate j).2 (e.symm i))
  refine ⟨m, hm, candidate', ?_, ?_⟩
  · intro j
    apply (finiteRankCorrectionSolutions_reindex e A c B q (candidate' j)).mpr
    simpa only [candidate', e.symm_apply_apply, finiteRankCorrectionSolutions,
      triangularCorrectionSolutions, A', c'] using hmem j
  · intro sr hsr
    have hsr' := (finiteRankCorrectionSolutions_reindex e A c B q sr).mp hsr
    obtain ⟨j, hj⟩ := hcover (fun i => sr.1 (e i), fun i => sr.2 (e i)) hsr'
    refine ⟨j, ?_⟩
    dsimp only [candidate']
    rw [hj]
    simp only [e.apply_symm_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FiniteSupportedPolynomialSubstitution
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {V W R : Type*} [CommSemiring R]

theorem polynomialOfFiniteCoefficientVector_coeff (S : Finset (V →₀ ℕ))
    (c : S → R) (α : S) :
    (polynomialOfFiniteCoefficientVector S c).coeff α.val = c α := by
  classical
  rw [polynomialOfFiniteCoefficientVector, coeff_sum, Finset.sum_eq_single α]
  · simp
  · intro β _ hβα
    rw [coeff_monomial, if_neg]
    exact fun h => hβα (Subtype.ext h)
  · simp

theorem polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem
    (S : Finset (V →₀ ℕ)) (c : S → R) (β : V →₀ ℕ) (hβ : β ∉ S) :
    (polynomialOfFiniteCoefficientVector S c).coeff β = 0 := by
  classical
  rw [polynomialOfFiniteCoefficientVector, coeff_sum]
  apply Finset.sum_eq_zero
  intro α _
  rw [coeff_monomial, if_neg]
  exact fun h => hβ (h ▸ α.property)

theorem polynomialOfFiniteCoefficientVector_support_subset (S : Finset (V →₀ ℕ))
    (c : S → R) : (polynomialOfFiniteCoefficientVector S c).support ⊆ S := by
  classical
  intro β hβ
  by_contra hout
  exact (MvPolynomial.mem_support_iff.mp hβ)
    (polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem S c β hout)

theorem polynomialOfFiniteCoefficientVector_reconstruct (S : Finset (V →₀ ℕ))
    (P : MvPolynomial V R) (hP : P.support ⊆ S) :
    polynomialOfFiniteCoefficientVector S (fun exponent => P.coeff exponent.val) = P := by
  classical
  ext β
  by_cases hβ : β ∈ S
  · exact polynomialOfFiniteCoefficientVector_coeff S _ ⟨β, hβ⟩
  · rw [polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem S _ β hβ]
    exact (MvPolynomial.notMem_support_iff.mp (fun h => hβ (hP h))).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteNormalizedChartCorrection
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {U B : Type*}

noncomputable def normalizedChartTagWeight : U ⊕ B → ℕ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

noncomputable def normalizedChartDiagonal (H : U → ℝ) (α : (U ⊕ B) →₀ ℕ) : ℝ :=
  α.prod (fun i n => (Sum.elim (fun u => (H u)⁻¹) (fun _ : B => 1) i) ^ n)

theorem normalizedChart_zero_monomial (H : U → ℝ) (α : (U ⊕ B) →₀ ℕ) :
    aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ : B => 0)) (monomial α 1) =
      monomial α (normalizedChartDiagonal H α) := by
  have h : normalizedRealPolynomialChart H (fun _ : B => 0) =
      fun i => C (Sum.elim (fun u => (H u)⁻¹) (fun _ : B => 1) i) * X i := by
    funext i
    cases i <;> simp [normalizedRealPolynomialChart]
  rw [h]
  exact aeval_coordinate_scaling_monomial _ α

theorem normalizedChartDiagonal_pos_le_one (H : U → ℝ) (hH : ∀ i, 1 ≤ H i)
    (α : (U ⊕ B) →₀ ℕ) :
    0 < normalizedChartDiagonal H α ∧ normalizedChartDiagonal H α ≤ 1 := by
  classical
  have hscale (i : U ⊕ B) :
      0 < Sum.elim (fun u => (H u)⁻¹) (fun _ : B => (1 : ℝ)) i ∧
        Sum.elim (fun u => (H u)⁻¹) (fun _ : B => (1 : ℝ)) i ≤ 1 := by
    cases i with
    | inl i => exact ⟨inv_pos.mpr (lt_of_lt_of_le zero_lt_one (hH i)),
        inv_le_one_of_one_le₀ (hH i)⟩
    | inr i => exact ⟨zero_lt_one, le_rfl⟩
  unfold normalizedChartDiagonal Finsupp.prod
  refine ⟨Finset.prod_pos (fun i _ => pow_pos (hscale i).1 _), ?_⟩
  exact Finset.prod_le_one (fun i _ => pow_nonneg (hscale i).1.le _)
    (fun i _ => pow_le_one₀ (hscale i).1.le (hscale i).2)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U V : Type*}

def normalizedChartCorrectionSolutions
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ) :
    Set (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ) :=
  {sr | sr.1.support ⊆ S ∧ sr.2.support ⊆ S ∧
    (∀ α, |sr.1.coeff α| ≤ B) ∧
    (∀ α, ∃ z : ℤ, sr.2.coeff α = (z : ℚ) / q) ∧
    P = aeval (R := ℝ) (normalizedRealPolynomialChart H A) sr.1 +
      MvPolynomial.map (Rat.castHom ℝ) sr.2}

noncomputable def normalizedChartCoefficientMatrix
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) : Matrix S S ℝ :=
  fun β α =>
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α.val 1)).coeff β.val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FiniteNormalizedRealGridCorrection
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U V : Type*}

def normalizedRealGridCorrectionSolutions
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ) :
    Set (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℝ) :=
  {sr | sr.1.support ⊆ S ∧ sr.2.support ⊆ S ∧
    (∀ α, |sr.1.coeff α| ≤ B) ∧
    (∀ α, ∃ z : ℤ, sr.2.coeff α = (z : ℝ) / q) ∧
    P = aeval (R := ℝ) (normalizedRealPolynomialChart H A) sr.1 + sr.2}

theorem normalizedChartCorrectionSolutions_map
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ)
    (sr : MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ)
    (hsr : sr ∈ normalizedChartCorrectionSolutions H A S P B q) :
    (sr.1, MvPolynomial.map (Rat.castHom ℝ) sr.2) ∈
      normalizedRealGridCorrectionSolutions H A S P B q := by
  refine ⟨hsr.1, (support_map_subset (Rat.castHom ℝ) sr.2).trans hsr.2.1,
    hsr.2.2.1, ?_, hsr.2.2.2.2⟩
  intro α
  obtain ⟨z, hz⟩ := hsr.2.2.2.1 α
  refine ⟨z, ?_⟩
  rw [coeff_map, hz]
  simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorSubspaceCorrectionRepresentatives
namespace OAI

section

namespace Erdos3

theorem boundedExponentWindow_finite (K : Type*) [Fintype K] (s : ℕ) :
    ({m : K →₀ ℕ | m.sum (fun _ n => n) ≤ s} : Set (K →₀ ℕ)).Finite := by
  classical
  let S := {m : K →₀ ℕ // m.sum (fun _ n => n) ≤ s}
  let f : S → List.Vector (Option K) s := fun m => paddedExponentWord m.val s m.property
  have hf : Function.Injective f := by
    intro m n hmn
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    have hc := congrArg
      (fun v : List.Vector (Option K) s => (v.val : Multiset (Option K)).count (some k)) hmn
    simpa only [f, paddedExponentWord_count] using hc
  let _ : Finite ↥({m : K →₀ ℕ | m.sum (fun _ n => n) ≤ s} : Set (K →₀ ℕ)) :=
    Finite.of_injective f hf
  exact Set.toFinite _

noncomputable def boundedExponentWindow (K : Type*) [Fintype K] (s : ℕ) :
    Finset (K →₀ ℕ) :=
  (boundedExponentWindow_finite K s).toFinset

@[simp] theorem boundedExponentWindow_mem_iff {K : Type*} [Fintype K]
    (s : ℕ) (m : K →₀ ℕ) :
    m ∈ boundedExponentWindow K s ↔ m.sum (fun _ n => n) ≤ s :=
  (boundedExponentWindow_finite K s).mem_toFinset

theorem boundedExponentWindow_card_le (K : Type*) [Fintype K] (s : ℕ) :
    (boundedExponentWindow K s).card ≤ (Fintype.card K + 1) ^ s :=
  boundedExponentSet_card_le _ s (fun m hm => (boundedExponentWindow_mem_iff s m).mp hm)

end Erdos3

end

end OAI
end


