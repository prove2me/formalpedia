-- Prove2me | Definitions.Def_OAIE3v2B078
-- name    : OAIE3v2B078
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:19:06.749984+00:00
-- url     : https://prove2.me/theorems/699a1cad-4c6e-4962-b730-8fea2cec3a72
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 79 of 311
-- statement:
--   Definitions bundle 79 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B041`, `OAIE3v2B042`, `OAIE3v2B046`, `OAIE3v2B048`, `OAIE3v2B049`, `OAIE3v2B050`, `OAIE3v2B052`, `OAIE3v2B053`, `OAIE3v2B054`, `OAIE3v2B056`, `OAIE3v2B057`, `OAIE3v2B061` of this split.
--
--   Modules: `Dynamics/FinitePrimitiveCorrectionBudget.lean`, `Dynamics/RationalConstraintCountBudget.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/CyclicMixedReflection.lean`, `Estimates/FiniteConvolution.lean`, `Estimates/FourBalancedRelations.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/RationalTaggedConstraintHistory.lean`, `Estimates/SharedFreeComparisonLift.lean`, `Estimates/SharedFreeRoundingThreshold.lean`, `Estimates/TailReflectionInduction.lean`, `Estimates/UniformParameterNet.lean`, `Fourier/CyclicTorusCoordinates.lean`, `Fourier/QuadraticFrequencyCoordinates.lean`, `Fourier/RealQuarterTorusExtension.lean`, `Geometry/BoxCornerMean.lean`, `Geometry/FiniteNormalizedChartCorrection.lean`, `Geometry/QuotientSubgroupCoordinates.lean`, `Geometry/RealCoordinateFunctionals.lean`, `Lattices/LatticeCoordinateLifts.lean`, `Lattices/NaturalScaleIntegerWindow.lean`, `Lattices/ProperAffineBoxRestriction.lean`, `Lattices/SharedFreeAffineBudget.lean`, `Linear/FourBalancedDual.lean`, `Linear/ProperCyclicKernelBasis.lean`, `Linear/RationalTagConstraintBasis.lean`, `Linear/RealFourBalancedDual.lean`, `Linear/SharedFreeCommonProjection.lean`, `Nilpotent/LieBCHContinuity.lean`, `Polynomial/RealPolynomialEvaluationMass.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Probability/SlicedRemainderDensityFamily.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B041
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B046
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049
import Definitions.Def_OAIE3v2B050
import Definitions.Def_OAIE3v2B052
import Definitions.Def_OAIE3v2B053
import Definitions.Def_OAIE3v2B054
import Definitions.Def_OAIE3v2B056
import Definitions.Def_OAIE3v2B057
import Definitions.Def_OAIE3v2B061

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
namespace OAI

section

namespace Erdos3

variable {A : Type*} [Ring A] [Algebra ℚ A]

namespace NilpotentBCHGroup
variable {I : NonUnitalSubalgebra ℚ A} {hI : ∀ a ∈ I, IsNilpotent a}

noncomputable instance instGroup : Group (NilpotentBCHGroup I hI) :=
  Group.ofLeftAxioms
    (fun a b c => ext (nilpotentBCH_assoc I hI a.mem_coord b.mem_coord c.mem_coord))
    (fun a => ext (nilpotentBCH_zero_left (hI _ a.mem_coord)))
    (fun a => ext (nilpotentBCH_neg_left (hI _ a.mem_coord)))

end NilpotentBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem realPolynomialMass_pow_le {I : Type*} (p : MvPolynomial I ℝ) (n : ℕ) :
    realPolynomialMass (p ^ n) ≤ realPolynomialMass p ^ n := by
  induction n with
  | zero => simp only [pow_zero, realPolynomialMass_one, le_refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (realPolynomialMass_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (realPolynomialMass_nonneg _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteConvolution
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem finiteConvolution_fourier_mass_sq (f g : H → ℂ) :
    (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff f χ * finiteFourierCoeff g χ‖) ^ 2 ≤
      (𝔼 x, ‖f x‖ ^ 2) * (𝔼 x, ‖g x‖ ^ 2) := by
  simp only [norm_mul]
  rw [← finiteFourier_parseval, ← finiteFourier_parseval]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [Fintype H] in
theorem smoothedIndicator_norm_le_one (I : Finset H) {B : Finset H} (hB : B.Nonempty) (x : H) :
    ‖smoothedIndicator I B x‖ ≤ 1 := by
  exact (RCLike.norm_expect_le (K := ℂ)).trans
    ((Finset.expect_le_expect (fun h _ => finiteIndicator_norm_le_one I (x - h))).trans_eq
      (Finset.expect_const hB 1))

theorem smoothedIndicator_eq_convolution (I B : Finset H) (x : H) :
    smoothedIndicator I B x = finiteConvolution (averagingKernel B) (finiteIndicator I) x := by
  have hn : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (fun h => averagingKernel B h * finiteIndicator I (x - h)) =
      (fun h => ((Fintype.card H : ℂ) / B.card) * restrictTo B (fun h => finiteIndicator I (x - h)) h) := by
    funext h
    by_cases hh : h ∈ B <;> simp [averagingKernel, finiteIndicator, restrictTo, hh]
  rw [finiteConvolution, he, ← Finset.mul_expect, expect_restrictTo,
    smoothedIndicator, Finset.expect_eq_sum_div_card]
  by_cases hb : (B.card : ℂ) = 0
  · simp [hb]
  · field_simp

theorem smoothedIndicator_fourier_mass {B : Finset H} (hB : B.Nonempty) (I : Finset H) :
    (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff (averagingKernel B) χ * finiteFourierCoeff (finiteIndicator I) χ‖) ≤
      (Fintype.card H : ℝ) / B.card := by
  let M := ∑ χ : AddChar H ℂ,
    ‖finiteFourierCoeff (averagingKernel B) χ * finiteFourierCoeff (finiteIndicator I) χ‖
  have hn : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hm : M ^ 2 ≤ (I.card : ℝ) / B.card := by
    have hh := finiteConvolution_fourier_mass_sq (averagingKernel B) (finiteIndicator I)
    rw [mean_averagingKernel_norm_sq hB, mean_indicator_norm_sq] at hh
    calc
      _ ≤ ((Fintype.card H : ℝ) / B.card) * ((I.card : ℝ) / Fintype.card H) := hh
      _ = _ := by field_simp
  have hi : (I.card : ℝ) ≤ Fintype.card H := by exact_mod_cast Finset.card_le_univ I
  have hbr : (B.card : ℝ) ≤ Fintype.card H := by exact_mod_cast Finset.card_le_univ B
  have hR : (1 : ℝ) ≤ (Fintype.card H : ℝ) / B.card := (le_div_iff₀ hb).mpr (by simpa using hbr)
  have hm' := hm.trans (div_le_div_of_nonneg_right hi hb.le)
  change M ≤ _
  nlinarith [sq_nonneg ((Fintype.card H : ℝ) / B.card - 1)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointBooleanSource (h : D → ℕ) : Measure (JointBlockParameter B h α → ℝ) :=
  sigmaAxisMeasure (fun d => blockCubeMeasure (B d) (Fin (h d)) α)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FinitePrimitiveCorrectionBudget
namespace OAI

section

namespace Erdos3

theorem exists_finite_primitive_correction_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (u b i r q d : ℕ) (p L M : ℝ),
      0 ≤ p → (u : ℝ) ≤ p → (b : ℝ) ≤ p → (i : ℝ) ≤ p → (r : ℝ) ≤ p →
      (q : ℝ) ≤ Real.exp ((p + a) ^ a) → (d : ℝ) ≤ Real.exp ((p + a) ^ a) →
      L ≤ Real.exp ((p + a) ^ a) → 0 ≤ M → M ≤ Real.exp ((p + a) ^ a) →
      let Rcap := ((((u + b : ℕ) : ℝ) + 1) ^ s * M) * (max 1 ((i : ℝ) * L)) ^ s
      ((((2 * ⌈((q * d ^ s : ℕ) : ℝ) * Rcap⌉₊ + 3) ^ ((u + i + 1) ^ s)) ^ r : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let P := X * (2 * X + 1) ^ s + Polynomial.C s * (3 * X + 1) +
    Polynomial.C (s + 1) * (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro u b i r q d p L M hp hu hb hi hr hq hd hL hM hMcap Rcap
  let t := (p + a) ^ a
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let p' := p * (2 * p + 1) ^ s + (s : ℝ) * (3 * p + 1) + ((s : ℝ) + 1) * t
  have hp' : 0 ≤ p' := by dsimp [p']; positivity
  have hfirst0 : 0 ≤ p * (2 * p + 1) ^ s := by positivity
  have hmid0 : 0 ≤ (s : ℝ) * (3 * p + 1) := by positivity
  have hlast0 : 0 ≤ ((s : ℝ) + 1) * t := by positivity
  have hdim : ((((u + i + 1) ^ s) * r : ℕ) : ℝ) ≤ p' :=
    (primitive_correction_dimension_bound u i r s hp hu hi hr).trans (by dsimp [p']; linarith)
  have hdenom : ((q * d ^ s : ℕ) : ℝ) ≤ Real.exp p' :=
    (primitive_correction_denominator_bound q d s hq hd).trans
      (Real.exp_le_exp.mpr (by dsimp [p']; linarith))
  have hR := primitiveCorrectionRadius_le_exp s u b i hp ht hu hb hi hM hMcap hL
  have hR0 : 0 ≤ Rcap := primitiveCorrectionRadius_nonneg s u b i L hM
  have hRcap : Rcap ≤ Real.exp p' := hR.trans
    (Real.exp_le_exp.mpr (by dsimp [p']; linarith))
  have hcount := real_grid_window_count_le_exp (((u + i + 1) ^ s) * r) (q * d ^ s)
    hp' hR0 hdim hdenom hRcap
  rw [pow_mul] at hcount
  exact hcount.trans (Real.exp_le_exp.mpr (by
    simpa [P, X, p', t, Polynomial.eval₂_pow] using hbudget p hp))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuotientSubgroupCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotient_mem_map_subgroup_iff (I : LieIdeal ℚ L) (U : LieSubalgebra ℚ L)
    (g : NilpotentLieBCHGroup L s hnil) :
    quotientHom I g ∈ (subgroup (hnil := hnil) U).map (quotientHom (hnil := hnil) I) ↔
      g.coord ∈ U.toSubmodule ⊔ I.toSubmodule := by
  constructor
  · intro hg
    obtain ⟨u, hu, heq⟩ := Subgroup.mem_map.mp hg
    have hdiff : g.coord - u.coord ∈ I := by
      apply (lieQuotientMap_eq_zero I _).mp
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg coord heq).symm
    apply Submodule.mem_sup.mpr
    exact ⟨u.coord, hu, g.coord - u.coord, hdiff, by abel⟩
  · intro hg
    obtain ⟨u, hu, v, hv, heq⟩ := Submodule.mem_sup.mp hg
    apply Subgroup.mem_map.mpr
    refine ⟨⟨u⟩, hu, ?_⟩
    apply ext
    change lieQuotientMap I u = lieQuotientMap I g.coord
    rw [← heq, map_add, (lieQuotientMap_eq_zero I v).mpr hv, add_zero]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {R I J L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def lieTreeOccurrenceMultilinear :
    (a : FreeMagma I) → MultilinearMap R (fun _ : LieTreeOccurrences a => L) L
  | .of _ => MultilinearMap.ofSubsingleton R L L () LinearMap.id
  | .mul a b => bracketMultilinear (lieTreeOccurrenceMultilinear a) (lieTreeOccurrenceMultilinear b)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCornerMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boxCorner_cons_false {n : ℕ} {X : Type*} (u v : Fin (n + 1) → X) (ω : Fin n → Bool) :
    boxCorner u v (Fin.cons false ω) = Fin.cons (u 0) (boxCorner (Fin.tail u) (Fin.tail v) ω) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem boxCorner_cons_true {n : ℕ} {X : Type*} (u v : Fin (n + 1) → X) (ω : Fin n → Bool) :
    boxCorner u v (Fin.cons true ω) = Fin.cons (v 0) (boxCorner (Fin.tail u) (Fin.tail v) ω) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*}

theorem floorIntegerPolynomial_add_fractionalCoefficientPolynomial (D : MvPolynomial σ ℝ) :
    MvPolynomial.map (Int.castRingHom ℝ) (floorIntegerPolynomial D) +
      fractionalCoefficientPolynomial D = D := by
  exact add_sub_cancel _ _

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FourBalancedRelations
namespace OAI

section

namespace Erdos3

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem fourAlternatingMap_mem_dependent (C D : Submodule R V) (v : Fin 4 → V)
    (hv : v ∈ fourCommonModulo C D) : fourAlternatingMap (R := R) v ∈ D := by
  have h := (mem_fourCommonModulo C D v).mp hv
  have heq : fourAlternatingMap (R := R) v = (v 1 - v 0) - (v 2 - v 0) - (v 3 - v 0) := by
    rw [fourAlternatingMap_apply]
    abel
  rw [heq]
  exact D.sub_mem (D.sub_mem (h.2 1) (h.2 2)) (h.2 3)

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

theorem mem_realified_four_product_iff (D : Submodule ℚ V)
    (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
    x ∈ (Submodule.pi Set.univ (fun _ : Fin 4 => D)).baseChange ℝ ↔
      ∀ k, (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)) x k ∈ D.baseChange ℝ := by
  have heq : Submodule.pi Set.univ (fun _ : Fin 4 => D) =
      ⨅ k : Fin 4, D.comap (LinearMap.proj k) := by
    ext v
    simp [Submodule.mem_pi]
  rw [heq, real_baseChange_iInf]
  simp only [Submodule.mem_iInf, realification_comap, Submodule.mem_comap, real_four_projection]

theorem realification_fourCommonModulo (C D : Submodule ℚ V) :
    ((fourCommonModulo C D).baseChange ℝ).map
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap =
      fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)
  have hmem (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
      x ∈ (fourCommonModulo C D).baseChange ℝ ↔
        e x ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
    rw [fourCommonModulo, realification_inf, Submodule.mem_inf,
      mem_realified_four_product_iff, real_baseChange_iInf, mem_fourCommonModulo]
    simp only [e, Submodule.mem_iInf, realification_comap, Submodule.mem_comap,
      LinearMap.baseChange_sub, LinearMap.sub_apply, real_four_projection]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mp hx
  · intro hv
    refine ⟨e.symm v, (hmem _).mpr ?_, e.apply_symm_apply v⟩
    simpa only [e.apply_symm_apply] using hv

theorem realification_fourBalancedDependent (D : Submodule ℚ V) :
    ((fourBalancedDependent D).baseChange ℝ).map
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap =
      fourBalancedDependent (D.baseChange ℝ) := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)
  have hmem (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
      x ∈ (fourBalancedDependent D).baseChange ℝ ↔
        e x ∈ fourBalancedDependent (D.baseChange ℝ) := by
    rw [fourBalancedDependent, realification_inf, realification_ker, Submodule.mem_inf,
      mem_realified_four_product_iff, LinearMap.mem_ker, real_four_alternating,
      mem_fourBalancedDependent, fourAlternatingMap_apply]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mp hx
  · intro hv
    refine ⟨e.symm v, (hmem _).mpr ?_, e.apply_symm_apply v⟩
    simpa only [e.apply_symm_apply] using hv

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realification_petalComparisonSpace (C P K : Submodule ℚ V) :
    ((petalComparisonSpace C P K).baseChange ℝ).map
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => V)).toLinearMap =
      petalComparisonSpace (C.baseChange ℝ) (P.baseChange ℝ) (K.baseChange ℝ) := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => V)
  have hmem (x : ℝ ⊗[ℚ] (Fin 2 → V)) :
      x ∈ (petalComparisonSpace C P K).baseChange ℝ ↔
        e x ∈ petalComparisonSpace (C.baseChange ℝ) (P.baseChange ℝ) (K.baseChange ℝ) := by
    simp only [petalComparisonSpace, realification_inf, realification_comap, realification_sup,
      Submodule.mem_inf, Submodule.mem_comap, LinearMap.baseChange_sub, LinearMap.sub_apply,
      LinearMap.proj_apply, real_pair_projection, e]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mp hx
  · intro hv
    refine ⟨e.symm v, (hmem _).mpr ?_, e.apply_symm_apply v⟩
    simpa only [e.apply_symm_apply] using hv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalConstraintCountBudget
namespace OAI

section

namespace Erdos3

theorem rationalConstraint_base_count_le_exp (m n d : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) :
    ((m * (n + 1) * (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d)) : ℕ) : ℝ) ≤
      Real.exp (2 * p + 3 * p ^ 2 * (p + 2)) := by
  have hpower := rational_log_height_count_exp_bound (n * d) hp
  have hnd : (n : ℝ) * d ≤ p ^ 2 := by
    simpa only [pow_two] using mul_le_mul hn hd (Nat.cast_nonneg d) hp
  have hpower' :
      (((((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d)) : ℕ) : ℝ) ≤
        Real.exp (3 * p ^ 2 * (p + 2)) := by
    apply hpower.trans (Real.exp_le_exp.mpr _)
    rw [Nat.cast_mul]
    nlinarith [mul_le_mul_of_nonneg_right hnd (show 0 ≤ 3 * (p + 2) by positivity)]
  have hmexp : (m : ℝ) ≤ Real.exp p := hm.trans (by linarith [Real.add_one_le_exp p])
  have hnexp : ((n + 1 : ℕ) : ℝ) ≤ Real.exp p := by
    rw [Nat.cast_add, Nat.cast_one]
    exact (add_le_add hn (le_refl 1)).trans (Real.add_one_le_exp p)
  calc
    _ ≤ Real.exp p * Real.exp p * Real.exp (3 * p ^ 2 * (p + 2)) := by
      rw [Nat.cast_mul, Nat.cast_mul]
      exact mul_le_mul (mul_le_mul hmexp hnexp (by positivity) (Real.exp_nonneg _))
        hpower' (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TailReflectionInduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace TailReflectionData

noncomputable def correlation {n : ℕ} {T G : Type*} [Fintype T]
    [AddCommGroup G] [Fintype G] (D : TailReflectionData n T G) : ℂ :=
  𝔼 t, 𝔼 v : Fin n → G, 𝔼 m, 𝔼 h,
    D.signal t (m + h + ∑ i, v i) * D.kernel t h m v *
      D.leftWeight t m v * D.rightWeight t h v * ∏ i, D.tailWeight t i h m v

end TailReflectionData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealCoordinateFunctionals
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

theorem realifyCoordinateMap_tmul (ℓ : V →ₗ[ℚ] (J → ℚ)) (a : ℝ) (v : V) (j : J) :
    realifyCoordinateMap ℓ (a ⊗ₜ[ℚ] v) j = a * (ℓ v j : ℝ) :=
  realifyFunctional_tmul ((LinearMap.proj j).comp ℓ) a v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeCoordinateLifts
namespace OAI

section

namespace Erdos3

open Module

variable {ι : Type*}

variable [Fintype ι] {N : ℕ}

noncomputable def integerVectorRealEquiv :
    (ι → ℤ) ≃ₗ[ℤ] (integerCoordinateLattice (ι := ι)) :=
  LinearEquiv.ofBijective
    (integerVectorRealMap.codRestrict integerCoordinateLattice (fun x =>
      (mem_integerCoordinateLattice_iff _).mpr ⟨x, rfl⟩))
    ⟨fun _ _ h => integerVectorRealMap_injective (congrArg Subtype.val h), by
      intro y
      obtain ⟨x, hx⟩ := (mem_integerCoordinateLattice_iff _).mp y.property
      exact ⟨x, Subtype.ext hx⟩⟩

theorem cyclicIntegerKernel_le_integerCoordinateLattice
    (η : (ι → ℤ) →+ ZMod N) : cyclicIntegerKernel η ≤ integerCoordinateLattice := by
  rintro y ⟨x, _, rfl⟩
  exact (mem_integerCoordinateLattice_iff _).mpr ⟨x, rfl⟩

instance cyclicIntegerKernel_discrete (η : (ι → ℤ) →+ ZMod N) :
    DiscreteTopology (cyclicIntegerKernel η) := by
  apply isDiscrete_iff_discreteTopology.mp
  apply isDiscrete_realIntegerGrid.mono
  intro y hy
  exact (mem_integerCoordinateLattice_iff _).mp
    (cyclicIntegerKernel_le_integerCoordinateLattice η hy)

instance cyclicIntegerKernel_full [NeZero N] (η : (ι → ℤ) →+ ZMod N) :
    IsZLattice ℝ (cyclicIntegerKernel η) := by
  classical
  constructor
  apply top_unique
  rw [← (Pi.basisFun ℝ ι).span_eq]
  apply Submodule.span_le.mpr
  rintro y ⟨i, rfl⟩
  have hmem := nsmul_integerVectorRealMap_mem_cyclicIntegerKernel η (Pi.single i 1)
  have hcast : integerVectorRealMap (Pi.single i (1 : ℤ)) = Pi.basisFun ℝ ι i := by
    ext j
    simp [integerVectorRealMap, Pi.basisFun_apply, Pi.single_apply]
  rw [hcast] at hmem
  have hmemR : (N : ℝ) • Pi.basisFun ℝ ι i ∈ cyclicIntegerKernel η := by
    rw [Nat.cast_smul_eq_nsmul]
    exact hmem
  have hspan : (N : ℝ) • Pi.basisFun ℝ ι i ∈
      Submodule.span ℝ (cyclicIntegerKernel η : Set (ι → ℝ)) := Submodule.subset_span hmemR
  have hscale := (Submodule.span ℝ (cyclicIntegerKernel η : Set (ι → ℝ))).smul_mem
    ((N : ℝ)⁻¹) hspan
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [smul_smul, inv_mul_cancel₀ hN, one_smul] at hscale
  exact hscale

theorem cyclicIntegerKernel_covolume_eq_card_range [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) :
    ZLattice.covolume (cyclicIntegerKernel η) = (Nat.card η.range : ℝ) := by
  classical
  rw [integer_lattice_covolume_eq_index _ (cyclicIntegerKernel_le_integerCoordinateLattice η)]
  have hindex : (cyclicIntegerKernel η).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup = Nat.card η.range := by
    let e := (integerVectorRealEquiv (ι := ι)).toAddEquiv.toAddMonoidHom
    let H := (cyclicIntegerKernel η).toAddSubgroup.addSubgroupOf
      (integerCoordinateLattice (ι := ι)).toAddSubgroup
    have he : H.comap e = η.ker := by
      ext x
      exact integerVectorRealMap_mem_cyclicIntegerKernel η x
    change H.index = Nat.card η.range
    rw [← H.index_comap_of_surjective (f := e) (integerVectorRealEquiv (ι := ι)).surjective,
      he, AddSubgroup.index_ker]
  exact_mod_cast hindex

theorem cyclicIntegerKernel_covolume_le [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) :
    ZLattice.covolume (cyclicIntegerKernel η) ≤ (N : ℝ) := by
  rw [cyclicIntegerKernel_covolume_eq_card_range]
  have h := Nat.card_le_card_of_injective (fun x : η.range => (x : ZMod N))
    Subtype.val_injective
  have hcard : Nat.card (ZMod N) = N := by simp
  rw [hcard] at h
  exact_mod_cast h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CyclicTorusCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ : Type} [Fintype ι] [Fintype κ] {N : ℕ} [NeZero N]
  (η : (ι → ℤ) →+ ZMod N) (b : Basis κ ℤ (cyclicIntegerKernel η))

noncomputable def cyclicKernelRealCoordinates : (ι → ℝ) ≃ₗ[ℝ] (κ → ℝ) :=
  (b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)).equivFun

noncomputable def cyclicKernelCoordinateCharacter (i : κ) :
    (ι → ℤ) →+ AddCircle (1 : ℝ) where
  toFun x := (cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ)
  map_zero' := by simp
  map_add' x y := by simp only [map_add, Pi.add_apply, AddCircle.coe_add]

theorem cyclicKernelCoordinateCharacter_eq_zero (x : ι → ℤ) (hx : η x = 0) (i : κ) :
    cyclicKernelCoordinateCharacter η b i x = 0 := by
  let y : cyclicIntegerKernel η :=
    ⟨integerVectorRealMap x, (integerVectorRealMap_mem_cyclicIntegerKernel η x).mpr hx⟩
  change ((b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)).repr (y : ι → ℝ) i :
    AddCircle (1 : ℝ)) = 0
  rw [Basis.ofZLatticeBasis_repr_apply]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨b.repr y i, by simp⟩

theorem cyclicKernelCoordinateCharacters_eq_zero_iff (x : ι → ℤ) :
    (∀ i, cyclicKernelCoordinateCharacter η b i x = 0) ↔ η x = 0 := by
  refine ⟨?_, fun hx i => cyclicKernelCoordinateCharacter_eq_zero η b x hx i⟩
  intro h
  apply (integerVectorRealMap_mem_cyclicIntegerKernel η x).mp
  rw [← b.ofZLatticeBasis_span ℝ (cyclicIntegerKernel η)]
  rw [Basis.mem_span_iff_repr_mem]
  intro i
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (h i)
  exact ⟨z, by simpa [cyclicKernelRealCoordinates, Basis.equivFun_apply] using hz⟩

theorem cyclicKernelCoordinateCharacters_eq_iff (x y : ι → ℤ) :
    (∀ i, cyclicKernelCoordinateCharacter η b i x =
      cyclicKernelCoordinateCharacter η b i y) ↔ η x = η y := by
  rw [← sub_eq_zero, ← map_sub, ← cyclicKernelCoordinateCharacters_eq_zero_iff η b]
  simp only [map_sub, sub_eq_zero]

theorem exists_cyclic_kernel_real_frequencies :
    ∃ t : κ → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
      (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
      ∀ (x : ι → ℤ) (n : ℤ), η x = (n : ZMod N) → ∀ i,
        ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
          AddCircle (1 : ℝ)) = (((n : ℝ) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  have h := fun i => exists_cyclic_real_character_lift η
    (cyclicKernelCoordinateCharacter η b i)
    (fun x hx => cyclicKernelCoordinateCharacter_eq_zero η b x hx i)
  choose t ht hperiod hformula using h
  exact ⟨t, ht, hperiod, fun x n hn i => hformula i x n hn⟩

theorem cyclicKernelCoordinateCharacters_injOn
    (S : Set (ι → ℤ)) (hη : Set.InjOn η S) :
    Set.InjOn (fun x i => cyclicKernelCoordinateCharacter η b i x) S := by
  intro x hx y hy hxy
  apply hη hx hy
  exact (cyclicKernelCoordinateCharacters_eq_iff η b x y).mp (congrFun hxy)

theorem exists_affine_cyclic_kernel_real_frequencies
    (h₀ : ZMod N) :
    ∃ t : κ → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
      (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
      ∀ (h : ZMod N) (x : ι → ℤ), h = h₀ + η x → ∀ i,
        ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
          AddCircle (1 : ℝ)) =
            ((((h.val : ℝ) - h₀.val) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨t, ht, hperiod, hformula⟩ := exists_cyclic_kernel_real_frequencies η b
  refine ⟨t, ht, hperiod, ?_⟩
  intro h x hx i
  have he : η x = (((h.val : ℤ) - h₀.val : ℤ) : ZMod N) := by
    simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hx, add_sub_cancel_left]
  simpa only [Int.cast_sub, Int.cast_natCast] using hformula x _ he i

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

theorem injOn_shrunk_integer_box_of_distinct_points
    {r : ℕ} {G : Type*} [AddCommGroup G] (J : Finset G) (hJ : J.Nonempty)
    (R : Fin r → ℕ) (η : (Fin r → ℤ) →+ G) (a : G)
    (hrepr : ∀ h ∈ J, ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = a + η x) :
    let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J.card + 1
    Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) := by
  intro k
  classical
  have hall (h : {h // h ∈ J}) : ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧ h.val = a + η x :=
    hrepr h.val h.property
  choose x hx heq using hall
  have hηx : Function.Injective (η ∘ x) := by
    intro h h' hh
    apply Subtype.ext
    rw [heq h, heq h']
    exact congrArg (fun z => a + z) hh
  have hxinj : Function.Injective x := by
    intro h h' hh
    exact hηx (congrArg η hh)
  let S := Finset.univ.image x
  have hS : S ⊆ centeredIntegerBox R := by
    intro z hz
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_centeredIntegerBox R (x h)).mpr (hx h)
  have hScard : S.card = J.card := by
    rw [show S.card = (Finset.univ.image x).card from rfl,
      Finset.card_image_of_injective _ hxinj, Finset.card_univ, Fintype.card_coe]
  have hinj : Set.InjOn η (S : Set _) := by
    intro z hz w hw hzw
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨h', _, rfl⟩ := Finset.mem_image.mp hw
    exact congrArg x (hηx hzw)
  apply injOn_small_integer_box_of_dense_subset η S R (fun i => R i / (2 * k)) k hS hinj
  · apply (card_doubled_centeredIntegerBox_le R).trans_lt
    rw [card_centeredIntegerBox, Fintype.card_fin, hScard]
    exact Nat.lt_mul_div_succ (2 ^ r * ∏ i, (2 * R i + 1)) hJ.card_pos
  · intro i
    exact Nat.mul_div_le (R i) (2 * k)

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

theorem exists_lattice_basis_bounded_expansion
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {n : ℕ} (b₀ : Basis (Fin n) ℤ Λ) (v : Fin n → E)
    (hv : ∀ i, v i ∈ Λ) (hli : LinearIndependent ℝ v) :
    ∃ (b : Basis (Fin n) ℤ Λ) (a : Fin n → Fin n → ℝ),
      (∀ i j, |a i j| ≤ 1) ∧ ∀ i, (b i : E) = ∑ j, a i j • v j := by
  classical
  let B := (b₀.ofZLatticeBasis ℝ Λ).equivFun
  let w : Fin n → Λ := fun i => ⟨v i, hv i⟩
  let x : Fin n → IntegerBasisReduction.Mahler.IntegralPoint n := fun i => b₀.equivFun (w i)
  have hcoord (i) : IntegerBasisReduction.Mahler.integralEmbed (x i) = B (v i) := by
    ext j
    change (b₀.repr (w i) j : ℝ) = (b₀.ofZLatticeBasis ℝ Λ).repr (w i : E) j
    rw [Basis.ofZLatticeBasis_repr_apply]
  have hxi : LinearIndependent ℝ (fun i => IntegerBasisReduction.Mahler.integralEmbed (x i)) := by
    simpa only [hcoord, Function.comp_def, LinearEquiv.coe_coe] using
      hli.map_injOn B.toLinearMap B.injective.injOn
  obtain ⟨c, a, hred⟩ := IntegerBasisReduction.Mahler.exists_centeredReduction_of_linearIndependent x hxi
  let b := c.map b₀.equivFun.symm
  have hcast (z : Fin n → ℤ) :
      B.symm (IntegerBasisReduction.Mahler.integralEmbed z) = (b₀.equivFun.symm z : E) := by
    apply B.injective
    ext j
    rw [LinearEquiv.apply_symm_apply]
    change (z j : ℝ) = (b₀.ofZLatticeBasis ℝ Λ).repr (b₀.equivFun.symm z : E) j
    rw [Basis.ofZLatticeBasis_repr_apply]
    exact (congrArg (fun q : ℤ => (q : ℝ))
      (congrFun (b₀.equivFun.apply_symm_apply z) j)).symm
  refine ⟨b, a, hred.abs_coefficient_le_one, ?_⟩
  intro i
  have h := congrArg B.symm (hred i).1
  rw [map_sum] at h
  simp only [map_smul, hcoord, LinearEquiv.symm_apply_apply] at h
  rw [hcast] at h
  exact h

theorem exists_lattice_basis_coordinate_bound
    {ι : Type} [Fintype ι] (Λ : Submodule ℤ (ι → ℝ))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {n : ℕ} (b₀ : Basis (Fin n) ℤ Λ) (v : Fin n → ι → ℝ)
    (hv : ∀ i, v i ∈ Λ) (hli : LinearIndependent ℝ v)
    (R : ι → ℝ) (hbound : ∀ i j, |v i j| ≤ R j) :
    ∃ b : Basis (Fin n) ℤ Λ, ∀ i j, |(b i : ι → ℝ) j| ≤ (n : ℝ) * R j := by
  obtain ⟨b, a, ha, he⟩ := exists_lattice_basis_bounded_expansion Λ b₀ v hv hli
  refine ⟨b, ?_⟩
  intro i j
  rw [he]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    |∑ k, a i k * v k j| ≤ ∑ k, |a i k * v k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, R j := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_right (ha i k) (abs_nonneg (v k j))
      have h' : |a i k| * |v k j| ≤ |v k j| := by simpa only [one_mul] using h
      exact h'.trans (hbound k j)
    _ = (n : ℝ) * R j := by simp

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem cyclicIntegerKernel_normalized_covolume_le
    {ι : Type} [Fintype ι] {N : ℕ} [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ) (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : ι → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ZLattice.covolume (cyclicIntegerKernel η) * (∏ i, ((R i : ℝ) + 1))⁻¹ ≤
      (2 : ℝ) ^ Fintype.card ι / δ := by
  have hprod : 0 < ∏ i, ((R i : ℝ) + 1) := Finset.prod_pos (by intros; positivity)
  rw [← div_eq_mul_inv, div_le_div_iff₀ hprod hδ]
  have hcov := mul_le_mul_of_nonneg_left (cyclicIntegerKernel_covolume_le η) hδ.le
  have hc := affine_box_card_le_radius_product η R h₀ J hrep
  nlinarith

theorem exists_short_independent_cyclic_kernel_vectors
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ v : Fin r → Fin r → ℝ, LinearIndependent ℝ v ∧
      (∀ i, v i ∈ cyclicIntegerKernel η) ∧
      ∀ i j, |v i j| ≤
        (BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ) *
          ((R j : ℝ) + 1) := by
  classical
  let b : Basis (Fin r) ℤ (cyclicIntegerKernel η) :=
    (finiteLatticeBasis (cyclicIntegerKernel η)).reindex (finCongr (by simp))
  let B := b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)
  have hB : Submodule.span ℤ (Set.range B) = cyclicIntegerKernel η :=
    b.ofZLatticeBasis_span ℝ _
  have hdet : |(Matrix.of B).det| = ZLattice.covolume (cyclicIntegerKernel η) := by
    have he : (B : Fin r → Fin r → ℝ) = fun i => (b i : Fin r → ℝ) :=
      funext (fun i => Basis.ofZLatticeBasis_apply ℝ (cyclicIntegerKernel η) b i)
    rw [he]
    exact (ZLattice.covolume_eq_det (cyclicIntegerKernel η) b).symm
  obtain ⟨C⟩ := BohrLattice.MinkowskiSecondBox.realBox_has_minkowskiSecondCertificate
    B (fun i => (R i : ℝ) + 1) (by intro i; positivity)
  have hmem (i) : C.point i ∈ cyclicIntegerKernel η := hB ▸ C.point_mem i
  have hpoint (i j) : |C.point i j| ≤ C.scale i * ((R j : ℝ) + 1) := by
    have h := C.mem_scaledBox i
    exact abs_le.mpr ⟨h.1 j, h.2 j⟩
  have hone (i) : 1 ≤ C.scale i := by
    obtain ⟨j, hj⟩ := cyclicIntegerKernel_nonzero_large_coordinate η R hinj
      (C.point i) (hmem i) (C.independent.ne_zero i)
    have hp : 0 < (R j : ℝ) + 1 := by positivity
    nlinarith [hpoint i j]
  have hbound : ∏ i, C.scale i ≤
      BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ := by
    have hm : 0 ≤ BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r := by
      unfold BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant
      positivity
    have hc := mul_le_mul_of_nonneg_left
      (cyclicIntegerKernel_normalized_covolume_le η R h₀ J δ hδ hdense hrep) hm
    have he : ∏ i, C.scale i ≤
        BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r *
          (ZLattice.covolume (cyclicIntegerKernel η) * (∏ i, ((R i : ℝ) + 1))⁻¹) := by
      simpa only [hdet, mul_assoc] using C.product_le
    simpa only [Fintype.card_fin, mul_div_assoc] using he.trans hc
  refine ⟨C.point, C.independent, hmem, ?_⟩
  intro i j
  have hi : C.scale i ≤ ∏ k, C.scale k := by
    calc
      C.scale i ≤ C.scale i * ∏ k ∈ Finset.univ.erase i, C.scale k :=
        le_mul_of_one_le_right (C.scale_nonneg i) (Finset.one_le_prod (fun k _ => hone k))
      _ = ∏ k, C.scale k := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  exact (hpoint i j).trans (mul_le_mul_of_nonneg_right (hi.trans hbound) (by positivity))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem proper_cyclic_kernel_box_card_le_covolume
    {ι : Type} [Fintype ι] {N : ℕ} [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)}) :
    ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤ ZLattice.covolume (cyclicIntegerKernel η) := by
  classical
  let f : {x // x ∈ centeredIntegerBox R} → η.range := fun x => η.rangeRestrict x.val
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact hinj ((mem_centeredIntegerBox R x.val).mp x.property)
      ((mem_centeredIntegerBox R y.val).mp y.property) (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  have hcard : (centeredIntegerBox R).card ≤ Nat.card η.range := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc
  rw [card_centeredIntegerBox] at hcard
  rw [cyclicIntegerKernel_covolume_eq_card_range]
  exact_mod_cast hcard

theorem proper_cyclic_kernel_covolume_lower_bound
    {ι : Type} [Fintype ι] {N : ℕ} [NeZero N]
    (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)}) :
    (∏ i, ((R i : ℝ) + 1)) ≤ ZLattice.covolume (cyclicIntegerKernel η) := by
  have hp : (∏ i, (R i + 1)) ≤ ∏ i, (2 * R i + 1) := by
    gcongr with i
    omega
  have hpR : (∏ i, ((R i : ℝ) + 1)) ≤ ((∏ i, (2 * R i + 1) : ℕ) : ℝ) := by
    exact_mod_cast hp
  exact hpR.trans (proper_cyclic_kernel_box_card_le_covolume η R hinj)

theorem properCyclicKernelBasisBound_nonneg (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ properCyclicKernelBasisBound r δ := by
  unfold properCyclicKernelBasisBound BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant
  positivity

theorem exists_proper_cyclic_kernel_basis
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η), ∀ i j,
      |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1) := by
  classical
  obtain ⟨v, hli, hv, hbound⟩ :=
    exists_short_independent_cyclic_kernel_vectors η R hinj h₀ J δ hδ hdense hrep
  let b₀ : Basis (Fin r) ℤ (cyclicIntegerKernel η) :=
    (finiteLatticeBasis (cyclicIntegerKernel η)).reindex (finCongr (by simp))
  obtain ⟨b, hb⟩ := exists_lattice_basis_coordinate_bound (cyclicIntegerKernel η) b₀ v hv hli
    (fun j => (BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ) *
      ((R j : ℝ) + 1)) hbound
  refine ⟨b, ?_⟩
  intro i j
  simpa only [properCyclicKernelBasisBound, mul_div_assoc, mul_assoc] using hb i j

theorem exists_proper_affine_torus_basis
    {r N : ℕ} [NeZero N] (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N))
    (δ : ℝ) (hδ : 0 < δ) (hdense : δ * N ≤ (J.card : ℝ))
    (hrep : ∀ h ∈ J, ∃ x : Fin r → ℤ, (∀ i, |x i| ≤ (R i : ℤ)) ∧ h = h₀ + η x) :
    ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
      (∀ i j, |(b i : Fin r → ℝ) j| ≤ properCyclicKernelBasisBound r δ * ((R j : ℝ) + 1)) ∧
      ∃ t : Fin r → ℝ, (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        ∀ (h : ZMod N) (x : Fin r → ℤ), h = h₀ + η x → ∀ i,
          ((cyclicKernelRealCoordinates η b (integerVectorRealMap x) i : ℝ) :
            AddCircle (1 : ℝ)) =
              ((((h.val : ℝ) - h₀.val) * t i : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨b, hb⟩ := exists_proper_cyclic_kernel_basis η R hinj h₀ J δ hδ hdense hrep
  exact ⟨b, hb, exists_affine_cyclic_kernel_real_frequencies η b h₀⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension
namespace OAI

section

namespace Erdos3

theorem properCyclicKernelBasisBound_le_exp {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    properCyclicKernelBasisBound r (Real.exp (-p)) ≤ Real.exp ((p + 4) ^ 3) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hpow (k : ℕ) : (2 : ℝ) ^ k ≤ Real.exp (2 * (k : ℝ)) := by
    calc
      _ ≤ (Real.exp 2) ^ k := pow_le_pow_left₀ (by norm_num) htwo k
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hk : r * (r - 1) / 2 ≤ r * r :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left r (Nat.sub_le _ _))
  have hkR : ((r * (r - 1) / 2 : ℕ) : ℝ) ≤ p ^ 2 := by
    have h : ((r * (r - 1) / 2 : ℕ) : ℝ) ≤ (r : ℝ) * r := by exact_mod_cast hk
    exact h.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) r])
  have hM : BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r ≤ Real.exp (2 * p ^ 2) :=
    (hpow _).trans (Real.exp_le_exp.mpr (by linarith))
  have h2r : (2 : ℝ) ^ r ≤ Real.exp (2 * p) :=
    (hpow r).trans (Real.exp_le_exp.mpr (by linarith))
  have hrp : (r : ℝ) ≤ Real.exp p := hr.trans
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p))
  have hM0 : 0 ≤ BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r := by
    unfold BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant
    positivity
  have hmain : properCyclicKernelBasisBound r (Real.exp (-p)) ≤ Real.exp (2 * p ^ 2 + 4 * p) := by
    unfold properCyclicKernelBasisBound
    rw [Real.exp_neg, div_eq_mul_inv, inv_inv]
    calc
      _ ≤ Real.exp p * Real.exp (2 * p ^ 2) * Real.exp (2 * p) * Real.exp p := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  apply hmain.trans
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ p ^ 3 + 10 * p ^ 2 + 44 * p + 64 := by positivity
  nlinarith

end Erdos3

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

theorem realRationalCoordinateSpan_iInf (U : η → Submodule ℚ (B → ℚ)) :
    realRationalCoordinateSpan (⨅ a, U a) = ⨅ a, realRationalCoordinateSpan (U a) := by
  unfold realRationalCoordinateSpan
  rw [real_baseChange_iInf]
  apply Submodule.map_iInf_of_ker_le realRationalCoordinateEquiv.surjective
  rw [LinearMap.ker_eq_bot.mpr realRationalCoordinateEquiv.injective]
  exact bot_le

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

theorem exists_dense_proper_coordinate_restriction
    {r : ℕ} {G : Type*} [AddCommGroup G] (J : Finset G) (hJ : J.Nonempty)
    (R : Fin r → ℕ) (η : (Fin r → ℤ) →+ G) (a : G)
    (x : {h // h ∈ J} → Fin r → ℤ)
    (hx : ∀ h i, |x h i| ≤ (R i : ℤ))
    (hrepr : ∀ h, h.val = a + η (x h)) :
    let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J.card + 1
    ∃ (T : Finset G) (hTJ : T ⊆ J), T.Nonempty ∧
      J.card ≤ (4 * k) ^ r * T.card ∧
      ∃ c : Fin r → ℤ,
        Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
        ∀ h : {h // h ∈ T}, ∀ i,
          |x ⟨h.val, hTJ h.property⟩ i - c i| ≤ (R i / (2 * k) : ℕ) := by
  intro k
  classical
  let : Nonempty {h // h ∈ J} := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
  have hk : 0 < k := Nat.succ_pos _
  have hproper := injOn_shrunk_integer_box_of_distinct_points J hJ R η a
    (fun h hh => ⟨x ⟨h, hh⟩, hx ⟨h, hh⟩, hrepr ⟨h, hh⟩⟩)
  obtain ⟨U, _hUuniv, hU, hsize, c, hsmall⟩ :=
    exists_dense_centered_box_block (Finset.univ : Finset {h // h ∈ J})
      Finset.univ_nonempty x R k hk (fun h _ => hx h)
  let T := U.image Subtype.val
  have hTJ : T ⊆ J := by
    intro h hh
    obtain ⟨h', _, rfl⟩ := Finset.mem_image.mp hh
    exact h'.property
  have hcard : T.card = U.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨T, hTJ, hU.image _, ?_, c, hproper, ?_⟩
  · simpa only [Finset.card_univ, Fintype.card_coe, Fintype.card_fin, hcard] using hsize
  · intro h i
    obtain ⟨h', hh', heq⟩ := Finset.mem_image.mp h.property
    have hident : h' = ⟨h.val, hTJ h.property⟩ := Subtype.ext heq
    simpa only [hident] using hsmall h' hh' i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FourBalancedDual
namespace OAI

section

namespace Erdos3

variable {R V E : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup E] [Module R E]

theorem four_annihilator_decomposition (C D : Submodule R V)
    (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : ∀ z ∈ fourBalancedDependent D, ℓ z = 0)
    (v : Fin 4 → V) (hv : v ∈ fourCommonModulo C D) :
    ℓ v = ℓ (fourDiagonalMap (R := R) (v 0)) +
      ℓ (LinearMap.single R (fun _ : Fin 4 => V) 0 (fourAlternatingMap (R := R) v)) := by
  let a := fourAlternatingMap (R := R) v
  have ha : a ∈ D := fourAlternatingMap_mem_dependent C D v hv
  let z : Fin 4 → V := fun k => v k - v 0 - (Pi.single (0 : Fin 4) a : Fin 4 → V) k
  have hz : z ∈ fourBalancedDependent D := by
    apply (mem_fourBalancedDependent D z).mpr
    refine ⟨?_, ?_⟩
    · intro k
      apply D.sub_mem (((mem_fourCommonModulo C D v).mp hv).2 k)
      by_cases hk : k = 0
      · subst k; simpa only [Pi.single_eq_same] using ha
      · simpa only [Pi.single_eq_of_ne hk] using D.zero_mem
    · change (v 0 - v 0 - a) + (v 1 - v 0 - 0) - (v 2 - v 0 - 0) - (v 3 - v 0 - 0) = 0
      dsimp only [a]
      rw [fourAlternatingMap_apply]
      abel
  have h := hℓ z hz
  change ℓ (v - fourDiagonalMap (R := R) (v 0) -
    LinearMap.single R (fun _ : Fin 4 => V) 0 a) = 0 at h
  rw [map_sub, map_sub] at h
  calc
    ℓ v = (ℓ v - ℓ (fourDiagonalMap (R := R) (v 0))) +
        ℓ (fourDiagonalMap (R := R) (v 0)) := (sub_add_cancel _ _).symm
    _ = ℓ (LinearMap.single R (fun _ : Fin 4 => V) 0 a) +
        ℓ (fourDiagonalMap (R := R) (v 0)) := by rw [sub_eq_zero.mp h]
    _ = _ := add_comm _ _

theorem four_annihilator_common_zero (D : Submodule R V)
    (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : ∀ z ∈ fourBalancedDependent D, ℓ z = 0) (v : V) (hv : v ∈ D) :
    ℓ (fourDiagonalMap (R := R) v) = 0 := by
  apply hℓ
  apply (mem_fourBalancedDependent D _).mpr
  exact ⟨fun _ => hv, by change v + v - v - v = 0; abel⟩

theorem four_refined_annihilator_identity (C D : Submodule R V) (hDC : D ≤ C)
    (K : Submodule R (Fin 4 → V)) (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : ∀ z ∈ fourRefinedRelation C D K, ℓ z = 0)
    (v : Fin 4 → V) (hv : v ∈ fourRefinedRelation C D K) :
    ℓ (fourDiagonalMap (R := R) (v 0)) +
      ℓ (LinearMap.single R (fun _ : Fin 4 => V) 0 (v 0 + v 1 - v 2 - v 3)) = 0 := by
  have h := four_annihilator_decomposition C D ℓ
    (fun z hz => hℓ z (fourBalancedDependent_le_refined C D K hz)) v
    (fourRefinedRelation_le_common C D hDC K hv)
  rw [fourAlternatingMap_apply] at h
  exact h.symm.trans (hℓ v hv)

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

noncomputable def realFourCoordinateMap (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) :
    (Fin 4 → ℝ ⊗[ℚ] V) →ₗ[ℝ] (J → ℝ) :=
  (realifyCoordinateMap ℓ).comp
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm.toLinearMap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeRoundingThreshold
namespace OAI

section

namespace Erdos3

theorem sharedFreeRecoveryThreshold_spec (s : ℕ) {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p)
    (N : ℕ) [NeZero N] (hN : Real.exp (sharedFreeRecoveryThreshold s q p) ≤ (N : ℝ)) :
    let z := 8 * sharedRefinementInputBudget s p + 1
    let A := sharedFreeEquationInputBudget s q p
    Real.exp (separationBudget z) ≤ (N : ℝ) ∧
      ∀ (l d : ℕ), 1 ≤ d → (l : ℝ) ≤ Real.exp ((A + 2) ^ 4) →
        2 * (l : ℝ) * (Real.exp ((A + 2) ^ 3) *
          ((Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) / (N : ℝ) ^ d)) ≤ 1 := by
  intro z A
  constructor
  · exact (Real.exp_le_exp.mpr (le_max_left _ _)).trans hN
  · intro l d hd hl
    have hb := sharedFreeEquationInputBudget_bounds s hq hp
    have hz : 0 ≤ z := by
      have h := (sharedRefinementInputBudget_bounds s hp).2.2.1
      dsimp only [z]
      linarith
    exact sharedFree_rounding_small hb.1 hz hb.2.2.2 N l d hd hl
      ((Real.exp_le_exp.mpr (le_max_right _ _)).trans hN)

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

theorem sharedFreeRecoveryThreshold_coefficient_bounds (s : ℕ) {q p : ℝ}
    (hq : 0 ≤ q) (hp : 0 ≤ p) :
    let A := sharedFreeEquationInputBudget s q p
    let z := 8 * sharedRefinementInputBudget s p + 1
    (A + 2) ^ 4 ≤ sharedFreeRecoveryThreshold s q p ∧
      2 * (Real.exp ((A + 2) ^ 3) *
        (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) ≤
          Real.exp (sharedFreeRecoveryThreshold s q p) := by
  intro A z
  have hb := sharedFreeEquationInputBudget_bounds s hq hp
  have hA : 0 ≤ A := hb.1
  have hz : 0 ≤ z := by
    have hi := (sharedRefinementInputBudget_bounds s hp).2.2.1
    dsimp [z]
    linarith
  have hbudget : z + ((z + 2) ^ 3 + (z + 2) ^ 36) ≤ A := hb.2.2.2
  have hT : (A + 2) ^ 5 ≤ sharedFreeRecoveryThreshold s q p := le_max_right _ _
  refine ⟨(pow_le_pow_right₀ (by linarith : 1 ≤ A + 2) (by decide : 4 ≤ 5)).trans hT, ?_⟩
  have hzA : z ≤ A := by
    have h3 : 0 ≤ (z + 2) ^ 3 := by positivity
    have h36 : 0 ≤ (z + 2) ^ 36 := by positivity
    linarith
  have h18 : (z + 2) ^ 18 ≤ (z + 2) ^ 36 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  have hwA : (z + 2) ^ 3 + (z + 2) ^ 18 + z ≤ A := by linarith
  have hsum : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤
      2 * Real.exp A := by
    linarith [Real.exp_le_exp.mpr hzA, Real.exp_le_exp.mpr hwA]
  have hpoly : (A + 2) ^ 3 + A + 4 ≤ (A + 2) ^ 5 := by
    have hh : 0 ≤ A ^ 5 + 10 * A ^ 4 + 39 * A ^ 3 + 74 * A ^ 2 + 67 * A + 20 := by
      positivity
    nlinarith
  calc
    _ ≤ 2 * (Real.exp ((A + 2) ^ 3) * (2 * Real.exp A)) := by gcongr
    _ = 4 * Real.exp ((A + 2) ^ 3 + A) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp 4 * Real.exp ((A + 2) ^ 3 + A) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (4 : ℝ)]
    _ = Real.exp ((A + 2) ^ 3 + A + 4) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((A + 2) ^ 5) := Real.exp_le_exp.mpr hpoly
    _ ≤ _ := Real.exp_le_exp.mpr hT

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_cyclic_interval_fourier_smoothing {N : ℕ} [NeZero N]
    (a : ZMod N) (L : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (v : ZMod N → ℂ) (c : AddChar (ZMod N) ℂ → ℂ),
      (∀ x, ‖v x‖ ≤ 1) ∧
      (𝔼 x, ‖finiteIndicator (cyclicInterval a L) x - v x‖) ≤ 2 * δ ∧
      (∑ χ, ‖c χ‖) ≤ 2 / δ ∧ ∀ x, v x = ∑ χ, c χ * χ x := by
  obtain ⟨K, hK, hKN, hsmall, hratio⟩ := exists_smoothing_scale (NeZero.pos N) hδ hδ1
  let I := cyclicInterval a L
  let B := cyclicInterval (0 : ZMod N) K
  have hB : B.Nonempty := cyclicInterval_nonempty 0 hK
  have hcard : B.card = K := cyclicInterval_card 0 hKN
  refine ⟨smoothedIndicator I B,
    (fun χ => finiteFourierCoeff (averagingKernel B) χ * finiteFourierCoeff (finiteIndicator I) χ),
    smoothedIndicator_norm_le_one I hB, ?_, ?_, ?_⟩
  · apply mean_indicator_smoothing_error I hB
    intro h hh
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hh
    have hmK : m ≤ K - 1 := by have := Finset.mem_range.mp hm; omega
    have hmreal : (m : ℝ) ≤ δ * N := (Nat.cast_le.mpr hmK).trans hsmall
    have hmean := cyclicInterval_nat_shift_error a L m
    have hhcast : (m : ZMod N) = h := by simpa using he
    rw [hhcast] at hmean
    apply hmean.trans
    apply (div_le_iff₀ (by exact_mod_cast NeZero.pos N : (0 : ℝ) < N)).mpr
    nlinarith
  · have hmass := smoothedIndicator_fourier_mass hB I
    rw [ZMod.card, hcard] at hmass
    exact hmass.trans hratio
  · intro x
    rw [smoothedIndicator_eq_convolution]
    simpa only [finiteFourierCoeff_convolution] using
      (finiteFourier_inversion (finiteConvolution (averagingKernel B) (finiteIndicator I)) x).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicMixedReflection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mem_tripleCarryInterval {N : ℕ} [NeZero N] (k : Fin 3) (v : ZMod (3 * N)) :
    v ∈ tripleCarryInterval N k ↔
      tripleCarryStart N k ≤ v.val ∧ v.val < tripleCarryStart N k + N := by
  have hend : tripleCarryStart N k + N ≤ 3 * N := by
    fin_cases k <;> simp [tripleCarryStart] <;> omega
  simpa only [tripleCarryInterval, Nat.add_sub_cancel_left] using
    mem_cyclicInterval_representatives (tripleCarryStart N k) (tripleCarryStart N k + N)
      (by omega) hend v

theorem sum_tripleCarry_indicator {N : ℕ} [NeZero N] (v : ZMod (3 * N)) :
    (∑ k : Fin 3, finiteIndicator (tripleCarryInterval N k) v) = 1 := by
  have hv := v.val_lt
  have hN := NeZero.pos N
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [finiteIndicator, mem_tripleCarryInterval]
  change (if 0 ≤ v.val ∧ v.val < 0 + N then (1 : ℂ) else 0) +
    ((if 2 * N ≤ v.val ∧ v.val < 2 * N + N then 1 else 0) +
      (if N ≤ v.val ∧ v.val < N + N then 1 else 0)) = 1
  simp only [Nat.zero_le, true_and, zero_add]
  by_cases h0 : v.val < N
  · have h1 : ¬(2 * N ≤ v.val ∧ v.val < 2 * N + N) := by omega
    have h2 : ¬(N ≤ v.val ∧ v.val < N + N) := by omega
    simp [h0, h1, h2]
  · by_cases h1 : v.val < 2 * N
    · have h2 : N ≤ v.val ∧ v.val < N + N := by omega
      have h3 : ¬(2 * N ≤ v.val ∧ v.val < 2 * N + N) := by omega
      simp [h0, h2, h3]
    · have h2 : 2 * N ≤ v.val ∧ v.val < 2 * N + N := by omega
      have h3 : ¬(N ≤ v.val ∧ v.val < N + N) := by omega
      simp [h0, h2, h3]

theorem tripleCarry_representative {N : ℕ} [NeZero N] (z x y : ZMod N) (k : Fin 3)
    (hk : tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y ∈ tripleCarryInterval N k) :
    ((z - x - y).val : ℤ) = (z.val : ℤ) + (k.val : ℤ) * N - x.val - y.val := by
  let t : ℤ := (z.val : ℤ) - x.val - y.val
  have hN := NeZero.pos N
  have hz := z.val_lt
  have hx := x.val_lt
  have hy := y.val_lt
  have hm := triple_difference_val z x y
  have hk' := (mem_tripleCarryInterval k _).mp hk
  have hvalid : 0 ≤ t + (k.val : ℤ) * N ∧ t + (k.val : ℤ) * N < N := by
    change ((tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val : ℤ) =
      (if 0 ≤ t then t else t + 3 * N) at hm
    fin_cases k
    · change 0 ≤ (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val ∧
        (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val < 0 + N at hk'
      change 0 ≤ t + 0 * (N : ℤ) ∧ t + 0 * (N : ℤ) < N
      split_ifs at hm <;> dsimp [t] at * <;> omega
    · change 2 * N ≤ (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val ∧
        (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val < 2 * N + N at hk'
      change 0 ≤ t + 1 * (N : ℤ) ∧ t + 1 * (N : ℤ) < N
      split_ifs at hm <;> dsimp [t] at * <;> omega
    · change N ≤ (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val ∧
        (tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val < N + N at hk'
      change 0 ≤ t + 2 * (N : ℤ) ∧ t + 2 * (N : ℤ) < N
      split_ifs at hm <;> dsimp [t] at * <;> omega
  have hcast : ((t + (k.val : ℤ) * N : ℤ) : ZMod N) = z - x - y := by
    simp [t]
  have hv := congrArg (fun v : ZMod N => (v.val : ℤ)) hcast
  rw [ZMod.val_intCast, Int.emod_eq_of_lt hvalid.1 hvalid.2] at hv
  rw [← hv]
  dsimp [t]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformParameterNet
namespace OAI

section

namespace Erdos3

theorem exists_uniform_parameter_net {J Ω : Type*} [Fintype J] [Nonempty Ω]
    (f : Ω → J → ℝ) {B : ℝ} (hB : 0 < B) (hf : ∀ x j, |f x j| ≤ B)
    {N : ℕ} (hN : 0 < N) :
    ∃ (code : Ω → J → Fin (N + 1)) (rep : (J → Fin (N + 1)) → Ω),
      ∀ x, dist (f x) (f (rep (code x))) ≤ 4 * B / N := by
  classical
  choose code hcode using fun x => exists_uniformBoxGrid_approx hB hN (f x) (hf x)
  let rep : (J → Fin (N + 1)) → Ω := fun i =>
    if h : ∃ x, code x = i then h.choose else Classical.choice inferInstance
  have hrep (x : Ω) : code (rep (code x)) = code x := by
    have h : ∃ y, code y = code x := ⟨x, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨code, rep, fun x => ?_⟩
  calc
    dist (f x) (f (rep (code x))) ≤
        dist (f x) (uniformBoxGrid B N (code x)) +
          dist (uniformBoxGrid B N (code x)) (f (rep (code x))) := dist_triangle _ _ _
    _ ≤ 2 * B / N + 2 * B / N := by
      apply add_le_add (hcode x)
      have hr := hcode (rep (code x))
      rw [hrep x] at hr
      exact (dist_comm _ _).trans_le hr
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeCommonProjection
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem dependent_le_refined_firstProjection
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (C D : Submodule R V) (K : Submodule R (Fin 4 → V)) :
    D ≤ (fourRefinedRelation C D K).map (LinearMap.proj 0) := by
  intro v hv
  refine ⟨fun _ : Fin 4 => v, fourBalancedDependent_le_refined C D K ?_, rfl⟩
  exact (mem_fourBalancedDependent D _).mpr ⟨fun _ => hv, by abel⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3

theorem sharedFreeComparisonBasisBudget_nonneg {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) :
    0 ≤ sharedFreeComparisonBasisBudget q p := by
  have hA := add_nonneg hq (fourRefinementBasisBudget_nonneg
    (add_nonneg hq (coefficientFourHeightBudget_nonneg hp)))
  exact add_nonneg hA (preimageBasisBudget_nonneg (mul_nonneg (by norm_num) hA))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

omit [∀ j, Fintype (J j)] in
theorem fullTaggedVariableWeight_pos (v : X ⊕ (Σ j, J j)) :
    0 < fullTaggedVariableWeight J v := by
  cases v with
  | inl x => exact Nat.zero_lt_one
  | inr i => exact Nat.succ_pos _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteNormalizedChartCorrection
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U V : Type*}

theorem normalizedChartCoefficientMatrix_coeff_aeval
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (slow : MvPolynomial (U ⊕ V) ℝ)
    (hsupport : slow.support ⊆ S) (β : S) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A) slow).coeff β.val =
      ∑ α : S, normalizedChartCoefficientMatrix H A S β α * slow.coeff α.val := by
  classical
  unfold normalizedChartCoefficientMatrix
  conv_lhs => rw [← polynomialOfFiniteCoefficientVector_reconstruct S slow hsupport]
  rw [polynomialOfFiniteCoefficientVector, map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro α _
  simp only [aeval_monomial, MvPolynomial.algebraMap_eq, map_one, one_mul, coeff_C_mul]
  exact mul_comm _ _

theorem normalizedChartCorrectionSolutions_coefficients
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ)
    (sr : MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ)
    (hsr : sr ∈ normalizedChartCorrectionSolutions H A S P B q) :
    ((fun α : S => sr.1.coeff α.val), (fun α : S => sr.2.coeff α.val)) ∈
      finiteRankCorrectionSolutions (normalizedChartCoefficientMatrix H A S)
        (fun α : S => P.coeff α.val) B q := by
  classical
  rcases hsr with ⟨hslow, _, hbound, hgrid, hidentity⟩
  refine ⟨fun α => hbound α.val, fun α => hgrid α.val, ?_⟩
  intro β
  have heq := congrArg (fun polynomial : MvPolynomial (U ⊕ V) ℝ => polynomial.coeff β.val) hidentity
  rw [MvPolynomial.coeff_add, coeff_map,
    normalizedChartCoefficientMatrix_coeff_aeval H A S sr.1 hslow β] at heq
  exact heq

end Erdos3

end

end OAI
end


