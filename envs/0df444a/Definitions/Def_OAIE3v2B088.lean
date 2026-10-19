-- Prove2me | Definitions.Def_OAIE3v2B088
-- name    : OAIE3v2B088
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:19:38.518673+00:00
-- url     : https://prove2.me/theorems/86c76335-4370-40bb-a33a-7bf7686cc177
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 89 of 311
-- statement:
--   Definitions bundle 89 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B047`, `OAIE3v2B068`, `OAIE3v2B069` of this split.
--
--   Modules: `Estimates/AdaptedTranslation.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/MultidegreeDilationPair.lean`, `Estimates/QuotientInducedMark.lean`, `Estimates/RealifiedTripleLayers.lean`, `Estimates/RepresentativeWindowPatch.lean`, `Estimates/VectorAlgebraicMajorDecomposition.lean`, `Estimates/WeightedLoweringAction.lean`, `FixedDensity/OrderedRemoval.lean`, `Geometry/BoxPairDivisibility.lean`, `Geometry/LieCoordinateHeight.lean`, `Geometry/LieCoordinateScalarExtension.lean`, `Geometry/WeightedTranslationBufferedCoordinates.lean`, `Lattices/SmoothResidueWindowMass.lean`, `Linear/RealifiedTripleProjections.lean`, `Linear/WeightedLieUpperSpan.lean`, `Linear/WeightedTranslationBasisHeight.lean`, `Nilpotent/BCHChartCutoffSmooth.lean`, `Nilpotent/BCHLatticeImageGap.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/BCHQuotientChart.lean`, `Nilpotent/BCHQuotientLocalIsometry.lean`, `Nilpotent/BCHSmoothPartitionBudget.lean`, `Nilpotent/FreeNilpotentLieAlgebra.lean`, `Nilpotent/LieBCHContinuity.lean`, `Polynomial/ExtendedPolynomialValues.lean`, `Polynomial/LieCoordinatePolynomials.lean`, `Polynomial/MajorTranslationPolynomialSymbolDegree.lean`, `Polynomial/MajorWeightedDegreeTools.lean`, `Polynomial/PolynomialCoefficientNormalization.lean`, `Polynomial/PolynomialPatchShearOrbitConverse.lean`, `Polynomial/PolynomialShearAffineExponential.lean`, `Polynomial/PolynomialShearFactorialIntegrality.lean`, `Polynomial/PolynomialShearRationalFiltration.lean`, `Polynomial/PolynomialSymbolicShearWeightedDegree.lean`, `Polynomial/PolynomialTranslationActionCompatibility.lean`, `Polynomial/ShiftedPolynomialBasis.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Polynomial/WeightedPolynomialEndomorphisms.lean`, `Polynomial/WeightedPolynomialRestriction.lean`, `Probability/IntervalDivisorProbability.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B068
import Definitions.Def_OAIE3v2B069

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
namespace OAI

section

namespace Erdos3

theorem bchBracketSupport_length (s : ℕ) {w : FreeSemigroup (Fin 2)}
    (hw : w ∈ bchBracketSupport s) : w.length ≤ s := by
  have h := congrArg (fun p : WordPolynomial (Fin 2) => p.coeff w) (bchWordExpansion_truncation s)
  rw [wordTruncation_coeff] at h
  by_contra hgt
  rw [if_neg hgt] at h
  exact (Finsupp.mem_support_iff.mp hw) h.symm

noncomputable def bchCoefficientHeight (s : ℕ) : ℕ :=
  1 + (bchBracketSupport s).sup (fun w =>
    max (bchBracketCoefficient s w).num.natAbs (bchBracketCoefficient s w).den)

theorem bchBracketCoefficient_height (s : ℕ) {w : FreeSemigroup (Fin 2)}
    (hw : w ∈ bchBracketSupport s) : RationalHeightLE (bchBracketCoefficient s w) (bchCoefficientHeight s) := by
  have h := Finset.le_sup (f := fun w =>
    max (bchBracketCoefficient s w).num.natAbs (bchBracketCoefficient s w).den) hw
  constructor
  · exact (le_max_left _ _).trans (h.trans (Nat.le_add_left _ 1))
  · exact (le_max_right _ _).trans (h.trans (Nat.le_add_left _ 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LieCoordinatePolynomials
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {ι X L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def bchCoordinatePolynomial (c : ι → ι → ι → ℚ) (s : ℕ)
    (k : ι) : MvPolynomial (Fin 2 × ι) ℚ :=
  ∑ w ∈ bchBracketSupport s,
    C (bchBracketCoefficient s w) * dynkinCoordinatePolynomial c w k

theorem bchCoordinatePolynomial_totalDegree (c : ι → ι → ι → ℚ) (s : ℕ) (k : ι) :
    (bchCoordinatePolynomial c s k).totalDegree ≤ s := by
  apply totalDegree_finsetSum_le
  intro w hw
  have h := totalDegree_mul (C (bchBracketCoefficient s w)) (dynkinCoordinatePolynomial c w k)
  rw [totalDegree_C, zero_add] at h
  exact h.trans ((dynkinCoordinatePolynomial_totalDegree c w k).trans (bchBracketSupport_length s hw))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateHeight
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {ι X : Type*} [Fintype ι]

noncomputable def bchCoordinateHeight (s d H : ℕ) : ℕ :=
  ((bchBracketSupport s).card + 1) *
    (bchCoefficientHeight s * lieCoordinateHeight d H s) ^ (bchBracketSupport s).card

theorem bchCoordinatePolynomial_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (s : ℕ) (k : ι) :
    RationalPolynomialHeightLE (bchCoordinatePolynomial c s k)
      (bchCoordinateHeight s (Fintype.card ι) H) := by
  apply RationalPolynomialHeightLE.sum_finset
  intro w hw
  exact RationalPolynomialHeightLE.C_mul (bchBracketCoefficient_height s hw)
    ((dynkinCoordinatePolynomial_height c hc w k).mono
      (lieCoordinateHeight_mono_length _ _ (bchBracketSupport_length s hw)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateScalarExtension
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {ι X R L : Type*} [Fintype ι] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]

variable [LieAlgebra ℚ L]

variable [IsScalarTower ℚ R L]

theorem bchCoordinatePolynomial_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (s : ℕ) (a b : L) (k : ι) :
    aeval (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2)
      (bchCoordinatePolynomial c s k) = e.repr (lieBCH s a b) k := by
  change _ = e.coord k (lieBCH s a b)
  rw [lieBCH_bracket_formula]
  simp only [bchCoordinatePolynomial, map_sum, map_mul, aeval_C,
    dynkinCoordinatePolynomial_eval_over e c hc,
    LinearMap.map_smul_of_tower, Algebra.smul_def, Basis.coord_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

noncomputable def bchBoxCoordinateBound (s d H : ℕ) (B : ℝ) : ℝ :=
  (((s + 1) * (2 * d + 1) ^ s : ℕ) : ℝ) * bchCoordinateHeight s d H * (2 * d) * s *
    B ^ (s * (2 * d + 1))

theorem bchBoxCoordinateBound_nonneg (s d H : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ bchBoxCoordinateBound s d H B := by
  unfold bchBoxCoordinateBound
  positivity

theorem lieBCH_sub_coordinates_bound {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H s : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (x y : L) {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx : ∀ i, |e.repr x i| ≤ B) (hy : ∀ i, |e.repr y i| ≤ B)
    (hxy : ∀ i, |e.repr x i - e.repr y i| ≤ δ) (k : ι) :
    |e.repr (lieBCH s x (-y)) k| ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  classical
  let P := bchCoordinatePolynomial c s k
  let v : Fin 2 × ι → ℝ := fun z => e.repr (![x, -y] z.1) z.2
  let w : Fin 2 × ι → ℝ := fun z => e.repr (![y, -y] z.1) z.2
  have hdegree : P.totalDegree ≤ s := bchCoordinatePolynomial_totalDegree c s k
  have hv (z : Fin 2 × ι) : |v z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hx i
    · simpa [v] using hy i
  have hw (z : Fin 2 × ι) : |w z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hy i
    · simpa [w] using hy i
  have hvw (z : Fin 2 × ι) : |v z - w z| ≤ δ := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hxy i
    · simpa [v, w] using hδ
  have hcoeff (m) : |((P.coeff m : ℚ) : ℝ)| ≤ bchCoordinateHeight s (Fintype.card ι) H :=
    (bchCoordinatePolynomial_height c hc s k m).abs_real_le
  have h := abs_aeval_sub_aeval_box_bound P v w (Nat.cast_nonneg _) hB hδ hcoeff hv hw hvw hdegree
  have hyneg : lieBCH s y (-y) = 0 := by
    have hg := congrArg NilpotentLieBCHGroup.coord
      (mul_inv_cancel (⟨y⟩ : NilpotentLieBCHGroup L s hnil))
    exact hg
  have hevalv : aeval v P = e.repr (lieBCH s x (-y)) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x (-y) k
  have hevalw : aeval w P = e.repr (lieBCH s y (-y)) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s y (-y) k
  rw [hevalv, hevalw, hyneg, map_zero, Finsupp.zero_apply, sub_zero] at h
  have hcard := polynomial_support_card_le P hdegree
  apply h.trans
  dsimp only [bchBoxCoordinateBound]
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  exact_mod_cast hcard

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

theorem coefficients_translate_monomial (h : σ → R) (α β : σ →₀ ℕ) (v : V) :
    coefficients (translate h (monomial α v)) β =
      (polynomialTranslate h (MvPolynomial.monomial α 1)).coeff β • v := by
  rw [monomial, translate_tmul, coefficients_tmul]

theorem eval_translate (h x : σ → R) (p : VectorPolynomial σ R V) :
    eval x (translate h p) = eval (fun i => x i + h i) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
    simp only [translate_tmul, eval_tmul]
    congr 1
    rw [polynomialTranslate, MvPolynomial.comp_aeval_apply]
    simp
  | add p q hp hq => simp only [map_add, hp, hq]

theorem coefficients_translate (h : σ → R) (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (translate h p) α = ∑ β ∈ (coefficients p).support,
      (polynomialTranslate h (MvPolynomial.monomial β 1)).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply, coefficients_translate_monomial]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedTranslation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adapted_translate (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) : F.Adapted w (translate h p) := by
  apply (F.adapted_iff_coefficients w _).mpr
  intro α
  rw [coefficients_translate]
  apply Submodule.sum_mem
  intro β hβ
  by_cases hc : (polynomialTranslate h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ ((F.adapted_iff_coefficients w p).mp hp β)
    exact (polynomialTranslate_monomial_bounds h w hw β).1 (MvPolynomial.mem_support_iff.mpr hc)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultidegreeDilationPair
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedLayer (c : σ → ℕ) (n : ℕ) : LieIdeal ℚ L :=
  ⨆ a : {a : σ → ℕ // n ≤ multidegreeWeight c a}, F.layerIdeal a.val

theorem layer_le_weightedLayer (c a : σ → ℕ) (n : ℕ) (ha : n ≤ multidegreeWeight c a) :
    F.layerIdeal a ≤ F.weightedLayer c n :=
  le_iSup (fun b : {b : σ → ℕ // n ≤ multidegreeWeight c b} => F.layerIdeal b.val) ⟨a, ha⟩

theorem weightedLayer_antitone (c : σ → ℕ) : Antitone (F.weightedLayer c) := by
  intro m n hmn
  apply iSup_le
  intro a
  exact F.layer_le_weightedLayer c a.val m (hmn.trans a.property)

theorem weightedLayer_lie_mem (c : σ → ℕ) {i j : ℕ} {x y : L}
    (hx : x ∈ F.weightedLayer c i) (hy : y ∈ F.weightedLayer c j) :
    ⁅x, y⁆ ∈ F.weightedLayer c (i + j) := by
  change x ∈ ⨆ a : {a : σ → ℕ // i ≤ multidegreeWeight c a}, F.layerIdeal a.val at hx
  refine LieSubmodule.iSup_induction _ hx
    (motive := fun z => ⁅z, y⁆ ∈ F.weightedLayer c (i + j)) ?_ ?_ ?_
  · intro a u hu
    change y ∈ ⨆ b : {b : σ → ℕ // j ≤ multidegreeWeight c b}, F.layerIdeal b.val at hy
    refine LieSubmodule.iSup_induction _ hy
      (motive := fun z => ⁅u, z⁆ ∈ F.weightedLayer c (i + j)) ?_ ?_ ?_
    · intro b v hv
      apply F.layer_le_weightedLayer c (a.val + b.val) (i + j)
        (by rw [multidegreeWeight_add]; exact Nat.add_le_add a.property b.property)
      exact F.lie_mem hu hv
    · simpa only [lie_zero] using (F.weightedLayer c (i + j)).zero_mem
    · intro v z hv hz
      rw [LieRing.lie_add]
      exact (F.weightedLayer c (i + j)).add_mem hv hz
  · simpa only [zero_lie] using (F.weightedLayer c (i + j)).zero_mem
  · intro u v hu hv
    rw [LieRing.add_lie]
    exact (F.weightedLayer c (i + j)).add_mem hu hv

end MultidegreeLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

noncomputable def realLieSubalgebraOverRat (K : LieSubalgebra ℝ L) : LieSubalgebra ℚ L :=
  { K.toSubmodule.restrictScalars ℚ with lie_mem' := K.lie_mem }

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientChart
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem eq_one_of_subgroup_grid_of_small_coordinates (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Γ)
    (hsmall : ∀ i, |e.repr g.coord i| < 1 / (l : ℝ)) : g = 1 := by
  apply ext
  apply e.equivFun.injective
  simpa only [coord_one, map_zero] using
    eq_zero_of_mem_realDenominatorGrid_of_abs_lt hl (hgrid g hg) hsmall

variable [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem quotient_coordinate_injOn_of_radius
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hsep : bchBoxCoordinateBound s (Fintype.card ι) H 1 * (2 * r) < 1 / (l : ℝ))
    (z : NilpotentLieBCHGroup L s hnil) :
    Set.InjOn (fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ))
      {v | ∀ i, |v i| ≤ r} := by
  intro x hx y hy hxy
  let u := (basisHomeomorph (hnil := hnil) e).symm x
  let v := (basisHomeomorph (hnil := hnil) e).symm y
  have hu : e.equivFun u.coord = x := (basisHomeomorph (hnil := hnil) e).apply_symm_apply x
  have hv : e.equivFun v.coord = y := (basisHomeomorph (hnil := hnil) e).apply_symm_apply y
  have hur (i) : |e.repr u.coord i| ≤ r := by simpa only [← hu, Basis.equivFun_apply] using hx i
  have hvr (i) : |e.repr v.coord i| ≤ r := by simpa only [← hv, Basis.equivFun_apply] using hy i
  have hmem : u⁻¹ * v ∈ Γ := by
    have h := QuotientGroup.eq.mp hxy
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h
  have hone : u⁻¹ * v = 1 := by
    apply eq_one_of_subgroup_grid_of_small_coordinates e Γ l hl hgrid _ hmem
    intro k
    have hbound := lieBCH_sub_coordinates_bound e c hstructure hc hnil (-u.coord) (-v.coord)
      (B := 1) (δ := 2 * r) le_rfl (by positivity)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using (hur i).trans hr1)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using (hvr i).trans hr1)
      (fun i => by
        simp only [map_neg, Finsupp.neg_apply, neg_sub_neg]
        exact (abs_sub _ _).trans (by linarith [hur i, hvr i])) k
    simpa only [coord_mul, coord_inv, neg_neg] using hbound.trans_lt hsep
  have huv : u = v := inv_mul_eq_one.mp hone
  exact hu.symm.trans ((congrArg (fun g => e.equivFun g.coord) huv).trans hv)

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def bchLogMetricConstant (s d H : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨bchBoxCoordinateBound s d H B + 1,
    add_nonneg (bchBoxCoordinateBound_nonneg _ _ _ B.coe_nonneg) zero_le_one⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem realificationMap_realificationHom_ofSteps (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup L s hnil) :
    realificationMap (hnil := hnil) (hM := hM) φ (realificationHom g) =
      realificationHom (mapOfSteps (hM := hM) φ g) := by
  apply ext
  rfl

theorem realificationMap_subgroup (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (Λ : Subgroup (NilpotentLieBCHGroup M t hM)) (hφ : Γ ≤ Λ.comap (mapOfSteps φ)) :
    Γ.map realificationHom ≤ (Λ.map realificationHom).comap
      (realificationMap (hnil := hnil) (hM := hM) φ) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  change realificationMap (hnil := hnil) (hM := hM) φ (realificationHom y) ∈ Λ.map realificationHom
  rw [realificationMap_realificationHom_ofSteps (hM := hM)]
  exact Subgroup.mem_map.mpr ⟨mapOfSteps φ y, hφ hy, rfl⟩

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTripleLayers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedLayer_le_ordinary (c : σ → ℕ) (hc : ∀ i, c i ≤ 1) (n : ℕ) :
    (F.weightedLayer c n).toSubmodule ≤ F.ordinary.layer n := by
  change (⨆ a : {a : σ → ℕ // n ≤ multidegreeWeight c a}, F.layerIdeal a.val).toSubmodule ≤ _
  rw [LieSubmodule.iSup_toSubmodule]
  apply iSup_le
  intro a
  exact (F.layer_le_ordinary a.val).trans
    (F.ordinary.antitone (a.property.trans (multidegreeWeight_le_sum c a.val hc)))

theorem coordinateIdeal_abelian [DecidableEq σ] (i : σ) (hi : bound i ≤ 1)
    {x y : L} (hx : x ∈ F.layerIdeal (Pi.single i 1))
    (hy : y ∈ F.layerIdeal (Pi.single i 1)) : ⁅x, y⁆ = 0 := by
  have hnot : ¬(Pi.single i 1 + Pi.single i 1 : σ → ℕ) ≤ bound := by
    intro h
    have hh := h i
    simp only [Pi.add_apply, Pi.single_eq_same] at hh
    omega
  have h := F.lie_mem hx hy
  simpa only [F.terminal _ hnot, Submodule.mem_bot] using h

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def coordinateActiveLayer (i : σ) (n : ℕ) : Submodule ℚ L :=
  F.layer (Pi.single i 1) ⊓ F.ordinary.layer n

theorem coordinateActiveLayer_antitone (i : σ) : Antitone (F.coordinateActiveLayer i) :=
  fun _ _ h _ hx => ⟨hx.1, F.ordinary.antitone h hx.2⟩

theorem weighted_lie_active (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {m n : ℕ} {x y : L} (hx : x ∈ F.weightedLayer c m) (hy : y ∈ F.coordinateActiveLayer i n) :
    ⁅x, y⁆ ∈ F.coordinateActiveLayer i (m + n) :=
  ⟨(F.layerIdeal (Pi.single i 1)).lie_mem hy.1,
    F.ordinary.lie_mem (F.weightedLayer_le_ordinary c hc m hx) hy.2⟩

theorem active_lie_weighted (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {m n : ℕ} {x y : L} (hx : x ∈ F.coordinateActiveLayer i m) (hy : y ∈ F.weightedLayer c n) :
    ⁅x, y⁆ ∈ F.coordinateActiveLayer i (m + n) :=
  ⟨lie_mem_left (R := ℚ) (L := L) (F.layerIdeal (Pi.single i 1)) x y hx.1,
    F.ordinary.lie_mem hx.2 (F.weightedLayer_le_ordinary c hc n hy)⟩

noncomputable def additiveTripleLayer (i : σ) (c : σ → ℕ) (n : ℕ) :
    Submodule ℚ (L × L × L) :=
  ((F.weightedLayer c n).toSubmodule.comap tripleNeutral) ⊓
    ((F.coordinateActiveLayer i n).comap tripleLeft ⊓
      (F.coordinateActiveLayer i n).comap tripleRight)

theorem mem_additiveTripleLayer (i : σ) (c : σ → ℕ) (n : ℕ) (x : L × L × L) :
    x ∈ F.additiveTripleLayer i c n ↔
      tripleNeutral x ∈ F.weightedLayer c n ∧
      tripleLeft x ∈ F.coordinateActiveLayer i n ∧
      tripleRight x ∈ F.coordinateActiveLayer i n := Iff.rfl

theorem additiveTripleLayer_antitone (i : σ) (c : σ → ℕ) : Antitone (F.additiveTripleLayer i c) := by
  intro m n h x hx
  exact ⟨F.weightedLayer_antitone c h hx.1,
    F.coordinateActiveLayer_antitone i h hx.2.1, F.coordinateActiveLayer_antitone i h hx.2.2⟩

theorem additiveTripleLayer_lie_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {m n : ℕ} {x y : L × L × L}
    (hx : x ∈ F.additiveTripleLayer i c m) (hy : y ∈ F.additiveTripleLayer i c n) :
    ⁅x, y⁆ ∈ F.additiveTripleLayer i c (m + n) := by
  have heq : ⁅x, y⁆ = tripleAssemble ⁅tripleNeutral x, tripleNeutral y⁆
      (⁅tripleNeutral x, tripleLeft y⁆ + ⁅tripleLeft x, tripleNeutral y⁆)
      (⁅tripleNeutral x, tripleRight y⁆ + ⁅tripleRight x, tripleNeutral y⁆) := by
    calc
      ⁅x, y⁆ = ⁅tripleAssemble (tripleNeutral x) (tripleLeft x) (tripleRight x),
          tripleAssemble (tripleNeutral y) (tripleLeft y) (tripleRight y)⁆ := by
        rw [tripleAssemble_decompose, tripleAssemble_decompose]
      _ = _ := tripleAssemble_lie _ _ _ _ _ _
        (F.coordinateIdeal_abelian i hi hx.2.1.1 hy.2.1.1)
        (F.coordinateIdeal_abelian i hi hx.2.1.1 hy.2.2.1)
        (F.coordinateIdeal_abelian i hi hx.2.2.1 hy.2.1.1)
        (F.coordinateIdeal_abelian i hi hx.2.2.1 hy.2.2.1)
  rw [heq, F.mem_additiveTripleLayer, tripleNeutral_assemble, tripleLeft_assemble, tripleRight_assemble]
  exact ⟨F.weightedLayer_lie_mem c hx.1 hy.1,
    (F.coordinateActiveLayer i (m + n)).add_mem
      (F.weighted_lie_active i c hc hx.1 hy.2.1) (F.active_lie_weighted i c hc hx.2.1 hy.1),
    (F.coordinateActiveLayer i (m + n)).add_mem
      (F.weighted_lie_active i c hc hx.1 hy.2.2) (F.active_lie_weighted i c hc hx.2.2 hy.1)⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleSubalgebra (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) : LieSubalgebra ℚ (L × L × L) :=
  { F.additiveTripleLayer i c 1 with
    lie_mem' := fun hx hy => F.additiveTripleLayer_antitone i c (by decide : 1 ≤ 1 + 1)
      (F.additiveTripleLayer_lie_mem i hi c hc hx hy) }

noncomputable def additiveTripleFirst (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L (L × L)).comp (F.additiveTripleSubalgebra i hi c hc).incl

noncomputable def additiveTripleSecond (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L L).comp
    ((LieHom.snd ℚ L (L × L)).comp (F.additiveTripleSubalgebra i hi c hc).incl)

noncomputable def additiveTripleThird (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (LieHom.snd ℚ L L).comp
    ((LieHom.snd ℚ L (L × L)).comp (F.additiveTripleSubalgebra i hi c hc).incl)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def tripleToPi : (L × L × L) →ₗ⁅ℚ⁆ (Fin 3 → L) :=
  liePiMap ![LieHom.fst ℚ L (L × L),
    (LieHom.fst ℚ L L).comp (LieHom.snd ℚ L (L × L)),
    (LieHom.snd ℚ L L).comp (LieHom.snd ℚ L (L × L))]

@[simp] theorem tripleToPi_zero (x : L × L × L) : tripleToPi x 0 = x.1 := rfl

@[simp] theorem tripleToPi_one (x : L × L × L) : tripleToPi x 1 = x.2.1 := rfl

@[simp] theorem tripleToPi_two (x : L × L × L) : tripleToPi x 2 = x.2.2 := rfl

namespace MultidegreeLieFiltration

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleToPi (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ (Fin 3 → L) :=
  tripleToPi.comp (F.additiveTripleSubalgebra i hi c hc).incl

end MultidegreeLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem adapted_ordinary {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    F.ordinary.Adapted (fun _ => 1) p := by
  apply (F.ordinary.adapted_iff_coefficients _ _).mpr
  intro a
  have h := F.layer_le_ordinary (fun i => a i) (hp a)
  simpa only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one] using h

theorem PolynomialOrbit.adapted (p : F.PolynomialOrbit) : F.Adapted (p.log F) := p.property

noncomputable def toOrdinaryOrbit : F.PolynomialOrbit →* F.ordinary.PolynomialOrbit (fun _ : σ => 1) where
  toFun p := ⟨p.val, (F.ordinary.mem_adaptedSubmodule _ _).mpr (F.adapted_ordinary p.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientInducedMark
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

theorem quotientLie_mem (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
    {j : ℕ} {x : L} (hx : x ∈ F.layer j) :
    lieQuotientMap I x ∈ (F.quotientLie I hI).layer j := ⟨x, hx, rfl⟩

def quotientTop (F : NilpotentLieFiltration L (s + 1)) :
    NilpotentLieFiltration (L ⧸ F.layerIdeal (s + 1)) s :=
  F.quotientLie (F.layerIdeal (s + 1)) le_rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealifiedTripleProjections
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleProjection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (liePiEval j).comp (F.additiveTripleToPi i hi c hc)

@[simp] theorem additiveTripleProjection_zero (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleProjection i hi c hc 0 = F.additiveTripleFirst i hi c hc := rfl

@[simp] theorem additiveTripleProjection_one (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleProjection i hi c hc 1 = F.additiveTripleSecond i hi c hc := rfl

@[simp] theorem additiveTripleProjection_two (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleProjection i hi c hc 2 = F.additiveTripleThird i hi c hc := rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3

open Module

namespace NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def realBCHLine (v : L) (r : ℝ) : NilpotentLieBCHGroup L s hnil := ⟨r • v⟩

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

noncomputable def bchInjectivityRadius (s d H l : ℕ) : ℝ :=
  1 / (4 * ((l : ℝ) + 1) * (bchBoxCoordinateBound s d H 1 + 1))

theorem bchInjectivityRadius_pos (s d H l : ℕ) : 0 < bchInjectivityRadius s d H l := by
  have := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  unfold bchInjectivityRadius
  positivity

theorem bchInjectivityRadius_le_one (s d H l : ℕ) : bchInjectivityRadius s d H l ≤ 1 := by
  have hA := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  unfold bchInjectivityRadius
  apply (div_le_one (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) l]

theorem bchInjectivityRadius_separation (s d H l : ℕ) (hl : 0 < l) :
    bchBoxCoordinateBound s d H 1 * (2 * bchInjectivityRadius s d H l) < 1 / (l : ℝ) := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hl1 : (0 : ℝ) < l + 1 := by positivity
  have hA := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  have hA1 : 0 < bchBoxCoordinateBound s d H 1 + 1 := by linarith
  have hr := bchInjectivityRadius_pos s d H l
  calc
    _ ≤ (bchBoxCoordinateBound s d H 1 + 1) * (2 * bchInjectivityRadius s d H l) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / (2 * ((l : ℝ) + 1)) := by
      unfold bchInjectivityRadius
      field_simp
      ring
    _ < 1 / (l : ℝ) := one_div_lt_one_div_of_lt hl' (by linarith)

namespace NilpotentLieBCHGroup

open Module

theorem quotient_coordinate_injOn
    {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
    [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
    [ContinuousSMul ℝ L] [T2Space L]
    {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    (z : NilpotentLieBCHGroup L s hnil) :
    Set.InjOn (fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ))
      {v | ∀ i, |v i| ≤ bchInjectivityRadius s (Fintype.card ι) H l} :=
  quotient_coordinate_injOn_of_radius e c hstructure hc Γ l hl hgrid
    (bchInjectivityRadius_pos _ _ _ _).le (bchInjectivityRadius_le_one _ _ _ _)
    (bchInjectivityRadius_separation _ _ _ _ hl) z

end NilpotentLieBCHGroup

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem mem_squareFiltration_top (x : F.squareLieSubalgebra) :
    x ∈ F.squareFiltration.layer s ↔ x.val.1 ∈ F.layer s ∧ x.val.1 = x.val.2 := by
  change x.val ∈ F.squareLayer s ↔ _
  rw [mem_squareLayer, F.terminal, Submodule.mem_bot, sub_eq_zero]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, h.2 ▸ h.1, h.2⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def selectedResidueFiniteLaw {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) :
    FiniteProbabilityWeights (rectangularWeightIndices 0 V 1) :=
  finiteSupportProbability (selectedResidueSmoothWeight modulus G V) (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IntervalDivisorProbability
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def intervalUniformWeights (a b : ℤ) (hab : a < b) :
    FiniteProbabilityWeights (Finset.Ico a b) := by
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  exact FiniteProbabilityWeights.uniform _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

noncomputable def patch {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1) :
    PolynomialPatch σ s 1 :=
  PolynomialPatch.ofCoordinates (fun _ => 1) (fun _ => le_rfl) (fun _ => hs)
    (fun _ _ _ => le_rfl) (fun _ => P - C w.center)
    (fun _ => (weightedSupportLE _ _).sub_mem hP (weightedSupportLE_C _ _ _)) w.kernel

@[simp] theorem patch_lip {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1) :
    (w.patch s hs P hP).kernel.lip = w.lip := rfl

end RepresentativeWindow
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

variable {R B : Type*} [CommRing R]

theorem polynomialTranslate_comp_ring (h k : B → R) (P : MvPolynomial B R) :
    polynomialTranslate h (polynomialTranslate k P) = polynomialTranslate (h + k) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, polynomialTranslate_X, map_add, polynomialTranslate_C, Pi.add_apply]
    rw [add_assoc]

@[simp] theorem polynomialTranslate_zero_ring (P : MvPolynomial B R) :
    polynomialTranslate (0 : B → R) P = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [hp]

namespace PolynomialTranslationGroupOver

noncomputable instance instMul : Mul (PolynomialTranslationGroupOver R B) where
  mul a b := ⟨a.base + b.base, polynomialTranslate (-b.base) a.polynomial + b.polynomial⟩

noncomputable instance instInv : Inv (PolynomialTranslationGroupOver R B) where
  inv a := ⟨-a.base, -polynomialTranslate a.base a.polynomial⟩

@[simp] theorem base_mul (a b : PolynomialTranslationGroupOver R B) :
    (a * b).base = a.base + b.base := rfl

@[simp] theorem polynomial_mul (a b : PolynomialTranslationGroupOver R B) :
    (a * b).polynomial = polynomialTranslate (-b.base) a.polynomial + b.polynomial := rfl

@[simp] theorem base_one : (1 : PolynomialTranslationGroupOver R B).base = 0 := rfl
@[simp] theorem polynomial_one : (1 : PolynomialTranslationGroupOver R B).polynomial = 0 := rfl
@[simp] theorem base_inv (a : PolynomialTranslationGroupOver R B) : (a⁻¹).base = -a.base := rfl
@[simp] theorem polynomial_inv (a : PolynomialTranslationGroupOver R B) :
    (a⁻¹).polynomial = -polynomialTranslate a.base a.polynomial := rfl

noncomputable instance instGroup : Group (PolynomialTranslationGroupOver R B) :=
  Group.ofLeftAxioms
    (by
      intro a b c
      apply PolynomialTranslationGroupOver.ext
      · exact add_assoc _ _ _
      · simp only [polynomial_mul, base_mul, map_add, polynomialTranslate_comp_ring,
          neg_add_rev, add_assoc])
    (by intro a; apply PolynomialTranslationGroupOver.ext <;> simp)
    (by
      intro a
      apply PolynomialTranslationGroupOver.ext
      · simp
      · simp [polynomialTranslate_comp_ring])

end PolynomialTranslationGroupOver

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorWeightedDegreeTools
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ τ ι R : Type*} [CommRing R]

theorem polynomialHom_preserves_weightedDegree (v : σ → ℕ) (w : τ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p ∈ weightedSupportLE v n) :
    F p ∈ weightedSupportLE w n := by
  rw [MvPolynomial.aeval_unique F]
  exact weightedSupportLE_aeval v w _ hF hp

theorem coordinateShearHom_degree (w : τ → ℕ) (i : τ) (f : σ → τ)
    (Q : MvPolynomial σ R) (hQ : rename f Q ∈ weightedSupportLE w (w i))
    {P : MvPolynomial τ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    coordinateShearHom i f Q P ∈ weightedSupportLE w n := by
  classical
  apply polynomialHom_preserves_weightedDegree w w _ _ hP
  intro j
  rw [coordinateShearHom_X]
  by_cases h : j = i
  · subst j
    rw [Function.update_self]
    exact (weightedSupportLE w (w i)).add_mem (weightedSupportLE_X w i) hQ
  · rw [Function.update_of_ne h]
    exact weightedSupportLE_X w j

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

theorem exists_triangularPolynomialEquiv_prefix (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) (n : ℕ) :
    n ≤ d → ∃ E : MvPolynomial (Fin d) R ≃ₐ[R] MvPolynomial (Fin d) R,
      (∀ i, E (X i) = if i.val < n then X i + rename (earlierSlot i) (Q i) else X i) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E.symm p ∈ weightedSupportLE w m) := by
  classical
  induction n with
  | zero =>
      intro _
      refine ⟨AlgEquiv.refl, ?_, ?_, ?_⟩
      · intro i
        rw [if_neg (Nat.not_lt_zero _)]
        rfl
      · intro m p hp
        exact hp
      · intro m p hp
        exact hp
  | succ n ih =>
      intro hn
      obtain ⟨E, hE, hEdeg, hEinv⟩ := ih (Nat.le_of_succ_le hn)
      let k : Fin d := ⟨n, Nat.lt_of_succ_le hn⟩
      let H := coordinateShearEquiv k (earlierSlot k) (earlierSlot_ne_self k) (Q k)
      have hHself : H (X k) = X k + rename (earlierSlot k) (Q k) := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X k) = _
        rw [coordinateShearHom_X, Function.update_self]
      have hHfix (i : Fin d) (hi : i ≠ k) : H (X i) = X i := by
        change coordinateShearHom k (earlierSlot k) (Q k) (X i) = _
        rw [coordinateShearHom_X, Function.update_of_ne hi]
      refine ⟨E.trans H, ?_, ?_, ?_⟩
      · intro i
        rw [AlgEquiv.trans_apply, hE i]
        by_cases hik : i = k
        · subst i
          rw [if_neg (by change ¬ n < n; omega),
            if_pos (by change n < n + 1; omega)]
          exact hHself
        · by_cases hi : i.val < n
          · have hfix : H (rename (earlierSlot i) (Q i)) = rename (earlierSlot i) (Q i) := by
              change coordinateShearHom k (earlierSlot k) (Q k) (rename (earlierSlot i) (Q i)) = _
              apply coordinateShearHom_rename
              intro j hj
              have hv := congrArg Fin.val hj
              have hji := j.isLt
              change j.val = n at hv
              omega
            rw [if_pos hi, if_pos (by omega), map_add, hHfix i hik, hfix]
          · have hne : i.val ≠ n := by
              intro he
              exact hik (Fin.ext he)
            rw [if_neg hi, if_neg (by omega), hHfix i hik]
      · intro m p hp
        change coordinateShearHom k (earlierSlot k) (Q k) (E p) ∈ weightedSupportLE w m
        exact coordinateShearHom_degree w k (earlierSlot k) (Q k) (hQ k) (hEdeg m p hp)
      · intro m p hp
        change E.symm (H.symm p) ∈ weightedSupportLE w m
        apply hEinv
        change coordinateShearHom k (earlierSlot k) (-Q k) p ∈ weightedSupportLE w m
        apply coordinateShearHom_degree w k (earlierSlot k) (-Q k) _ hp
        simpa only [map_neg] using (weightedSupportLE w (w k)).neg_mem (hQ k)

theorem exists_triangularPolynomialEquiv (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) :
    ∃ E : MvPolynomial (Fin d) R ≃ₐ[R] MvPolynomial (Fin d) R,
      (∀ i, E (X i) = X i + rename (earlierSlot i) (Q i)) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E p ∈ weightedSupportLE w m) ∧
      (∀ m p, p ∈ weightedSupportLE w m → E.symm p ∈ weightedSupportLE w m) := by
  obtain ⟨E, hE, hd, hi⟩ := exists_triangularPolynomialEquiv_prefix w Q hQ d le_rfl
  refine ⟨E, ?_, hd, hi⟩
  intro i
  simpa only [if_pos i.isLt] using hE i

noncomputable def triangularPolynomialEquiv (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i)) :
    MvPolynomial (Fin d) R ≃ₐ[R] MvPolynomial (Fin d) R :=
  Classical.choose (exists_triangularPolynomialEquiv w Q hQ)

theorem triangularPolynomialEquiv_degree (w : Fin d → ℕ)
    (Q : (i : Fin d) → MvPolynomial (Fin i.val) R)
    (hQ : ∀ i, rename (earlierSlot i) (Q i) ∈ weightedSupportLE w (w i))
    {m : ℕ} {p : MvPolynomial (Fin d) R} (hp : p ∈ weightedSupportLE w m) :
    triangularPolynomialEquiv w Q hQ p ∈ weightedSupportLE w m :=
  (Classical.choose_spec (exists_triangularPolynomialEquiv w Q hQ)).2.1 m p hp

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientNormalization
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weightedTopPart_preserves_degree (v w : σ → ℕ) (n : ℕ)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    weightedHomogeneousComponent v n p ∈ weightedSupportLE w d := by
  intro a ha
  change a ∈ (weightedHomogeneousComponent v n p).support at ha
  rw [support_weightedHomogeneousComponent] at ha
  exact hp (Finset.mem_filter.mp ha).1

namespace PolynomialSlots

variable {d : ℕ} {w : Fin d → ℕ}

noncomputable def topPart (A : PolynomialSlots σ d w) : PolynomialSlots σ d w where
  center i := weightedHomogeneousComponent (patchSlotWeight w i) (w i) (A.center i)
  degree i := weightedTopPart_preserves_degree _ _ _ (A.degree i)

end PolynomialSlots

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] {d : ℕ}

namespace PolynomialSlots

variable {w : Fin d → ℕ}

theorem specializeCenter_degree (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    A.specializeCenter t i ∈ weightedSupportLE (fun j => w (earlierSlot i j)) (w i) := by
  apply weightedSupportLE_aeval _ _ _ _ (A.degree i)
  intro a
  cases a with
  | inl j => exact weightedSupportLE_C _ 1 (t j)
  | inr j => exact weightedSupportLE_X _ j

theorem specializeCenter_full_degree (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    rename (earlierSlot i) (A.specializeCenter t i) ∈ weightedSupportLE w (w i) := by
  apply polynomialHom_preserves_weightedDegree _ _ (rename (earlierSlot i)) _
    (A.specializeCenter_degree t i)
  intro j
  rw [rename_X]
  exact weightedSupportLE_X w (earlierSlot i j)

end PolynomialSlots

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationActionCompatibility
namespace OAI


namespace Erdos3.PolynomialTranslationGroupOver

open _root_.MvPolynomial
variable {R σ : Type*} [CommRing R]

noncomputable def actionHom (g : PolynomialTranslationGroupOver R σ) :
    MvPolynomial (σ ⊕ Unit) R →ₐ[R] MvPolynomial (σ ⊕ Unit) R :=
  aeval (Sum.elim (fun i => X (Sum.inl i) + C (g.base i))
    (fun u => X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial)))

@[simp] theorem actionHom_X_inl (g : PolynomialTranslationGroupOver R σ) (i : σ) :
    actionHom g (X (Sum.inl i)) = X (Sum.inl i) + C (g.base i) := by simp [actionHom]

@[simp] theorem actionHom_X_inr (g : PolynomialTranslationGroupOver R σ) (u : Unit) :
    actionHom g (X (Sum.inr u)) =
      X (Sum.inr u) + rename Sum.inl (polynomialTranslate g.base g.polynomial) := by simp [actionHom]

@[simp] theorem actionHom_C (g : PolynomialTranslationGroupOver R σ) (r : R) :
    actionHom g (C r) = C r := by simp [actionHom]

theorem actionHom_rename (g : PolynomialTranslationGroupOver R σ) (P : MvPolynomial σ R) :
    actionHom g (rename Sum.inl P) = rename Sum.inl (polynomialTranslate g.base P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP => simp only [map_mul,rename_X,actionHom_X_inl,hP,polynomialTranslate_X,
      map_add,rename_C]

@[simp] theorem actionHom_one (P : MvPolynomial (σ ⊕ Unit) R) : actionHom 1 P = P := by
  have hh : actionHom (1 : PolynomialTranslationGroupOver R σ) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp
  exact DFunLike.congr_fun hh P

theorem actionHom_mul (g h : PolynomialTranslationGroupOver R σ)
    (P : MvPolynomial (σ ⊕ Unit) R) :
    actionHom (g*h) P = actionHom g (actionHom h P) := by
  have hh : actionHom (g*h) = (actionHom g).comp (actionHom h) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i => simp [Pi.add_apply, add_assoc]
    | inr u =>
      simp only [actionHom_X_inr,base_mul,polynomial_mul,map_add,polynomialTranslate_comp_ring,
        AlgHom.comp_apply,actionHom_rename]
      rw [show g.base + h.base + -h.base = g.base by abel]
      abel
  exact DFunLike.congr_fun hh P

noncomputable def action (g : PolynomialTranslationGroupOver R σ) :
    MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R :=
  { actionHom g with
    invFun := actionHom g⁻¹
    left_inv := fun P => by
      change actionHom g⁻¹ (actionHom g P) = P
      rw [← actionHom_mul, inv_mul_cancel, actionHom_one]
    right_inv := fun P => by
      change actionHom g (actionHom g⁻¹ P) = P
      rw [← actionHom_mul, mul_inv_cancel, actionHom_one] }

noncomputable def actionMonoidHom : PolynomialTranslationGroupOver R σ →*
    (MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R) where
  toFun := action
  map_one' := by apply AlgEquiv.ext; intro P; exact actionHom_one P
  map_mul' g h := by apply AlgEquiv.ext; intro P; exact actionHom_mul g h P

theorem actionMonoidHom_injective : Function.Injective (actionMonoidHom (R := R) (σ := σ)) := by
  intro g h heq
  have hb : g.base = h.base := by
    funext i
    have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R]
      MvPolynomial (σ ⊕ Unit) R => f (X (Sum.inl i))) heq
    change actionHom g (X (Sum.inl i)) = actionHom h (X (Sum.inl i)) at hh
    rw [actionHom_X_inl,actionHom_X_inl] at hh
    exact MvPolynomial.C_injective (σ ⊕ Unit) R (add_left_cancel hh)
  apply PolynomialTranslationGroupOver.ext hb
  have hh := congrArg (fun f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R]
    MvPolynomial (σ ⊕ Unit) R => f (X (Sum.inr ()))) heq
  change actionHom g (X (Sum.inr ())) = actionHom h (X (Sum.inr ())) at hh
  rw [actionHom_X_inr,actionHom_X_inr] at hh
  have hp := MvPolynomial.rename_injective Sum.inl Sum.inl_injective (add_left_cancel hh)
  have hp' := congrArg (polynomialTranslate (-g.base)) hp
  simpa only [hb, polynomialTranslate_comp_ring, neg_add_cancel, polynomialTranslate_zero_ring] using hp'

end Erdos3.PolynomialTranslationGroupOver


namespace Erdos3

open _root_.MvPolynomial

variable {B R S : Type*} [CommRing R] [CommRing S]

theorem polynomialTranslate_map_ring (φ : R →+* S) (h : B → R)
    (P : MvPolynomial B R) :
    MvPolynomial.map φ (polynomialTranslate h P) =
      polynomialTranslate (fun i => φ (h i)) (MvPolynomial.map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, polynomialTranslate_X, map_add, map_X, map_C]

namespace PolynomialTranslationGroupOver

noncomputable def map (φ : R →+* S) :
    PolynomialTranslationGroupOver R B →* PolynomialTranslationGroupOver S B where
  toFun g := ⟨fun i => φ (g.base i), MvPolynomial.map φ g.polynomial⟩
  map_one' := by ext <;> simp
  map_mul' g h := by
    apply PolynomialTranslationGroupOver.ext
    · ext i; simp
    · simp only [polynomial_mul, map_add, polynomialTranslate_map_ring]
      congr 1
      congr 1
      exact congrArg polynomialTranslate (funext (fun i => map_neg φ (h.base i)))

@[simp] theorem map_base (φ : R →+* S) (g : PolynomialTranslationGroupOver R B) (i : B) :
    (PolynomialTranslationGroupOver.map φ g).base i = φ (g.base i) := rfl

@[simp] theorem map_polynomial (φ : R →+* S) (g : PolynomialTranslationGroupOver R B) :
    (PolynomialTranslationGroupOver.map φ g).polynomial = MvPolynomial.map φ g.polynomial := rfl

end PolynomialTranslationGroupOver

end Erdos3


namespace Erdos3.PolynomialTranslationGroupOver

open _root_.MvPolynomial
variable {σ R : Type*} [CommRing R]

noncomputable def actionElement (x : σ → R) (Q : MvPolynomial σ R) :
    PolynomialTranslationGroupOver R σ := ⟨x, polynomialTranslate (-x) Q⟩

@[simp] theorem actionElement_X_inl (x : σ → R) (Q : MvPolynomial σ R) (i : σ) :
    actionMonoidHom (actionElement x Q) (X (Sum.inl i)) = X (Sum.inl i) + C (x i) :=
  actionHom_X_inl _ i

@[simp] theorem actionElement_X_inr (x : σ → R) (Q : MvPolynomial σ R) (u : Unit) :
    actionMonoidHom (actionElement x Q) (X (Sum.inr u)) = X (Sum.inr u) + rename Sum.inl Q := by
  change actionHom (actionElement x Q) (X (Sum.inr u)) = _
  rw [actionHom_X_inr]
  change X (Sum.inr u) + rename Sum.inl (polynomialTranslate x (polynomialTranslate (-x) Q)) = _
  rw [polynomialTranslate_comp_ring, add_neg_cancel, polynomialTranslate_zero_ring]

theorem action_eq_of_shape
    (f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R)
    (x : σ → R) (Q : MvPolynomial σ R)
    (hbase : ∀ i, f (X (Sum.inl i)) = X (Sum.inl i) + C (x i))
    (hextra : f (X (Sum.inr ())) = X (Sum.inr ()) + rename Sum.inl Q) :
    actionMonoidHom (actionElement x Q) = f := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i => exact (actionElement_X_inl x Q i).trans (hbase i).symm
  | inr u => cases u; exact (actionElement_X_inr x Q ()).trans hextra.symm

theorem existsUnique_action_of_shape
    (f : MvPolynomial (σ ⊕ Unit) R ≃ₐ[R] MvPolynomial (σ ⊕ Unit) R)
    (x : σ → R) (Q : MvPolynomial σ R)
    (hbase : ∀ i, f (X (Sum.inl i)) = X (Sum.inl i) + C (x i))
    (hextra : f (X (Sum.inr ())) = X (Sum.inr ()) + rename Sum.inl Q) :
    ∃! g : PolynomialTranslationGroupOver R σ, actionMonoidHom g = f := by
  refine ⟨actionElement x Q, action_eq_of_shape f x Q hbase hextra, ?_⟩
  intro g hg
  exact actionMonoidHom_injective (hg.trans (action_eq_of_shape f x Q hbase hextra).symm)

end Erdos3.PolynomialTranslationGroupOver


namespace Erdos3.PolynomialTranslationGroupOver

open _root_.MvPolynomial
variable {σ R S : Type*} [CommRing R] [CommRing S]

noncomputable def rationalEquiv : PolynomialTranslationGroup σ ≃* PolynomialTranslationGroupOver ℚ σ where
  toFun g := ⟨g.base,g.polynomial⟩
  invFun g := ⟨g.base,g.polynomial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Erdos3.PolynomialTranslationGroupOver

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {B U : Type*}

noncomputable def translationPhaseArgument (D₀ : MvPolynomial B ℝ)
    (g : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) : ℝ :=
  eval β g.polynomial + eval (β - g.base) D₀

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {B : Type*}

noncomputable def integerPolynomialTranslationSubgroup :
    Subgroup (PolynomialTranslationGroupOver ℝ B) :=
  (PolynomialTranslationGroupOver.map (B := B) (Int.castRingHom ℝ)).range

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedLoweringAction
namespace OAI

section

namespace Erdos3.WeightedLoweringAut

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

noncomputable def degreeAction (e : WeightedLoweringAut w R) (n : ℕ) :
    weightedSupportLE (R := R) w n ≃ₗ[R] weightedSupportLE (R := R) w n where
  toFun p := ⟨e.val p, e.preserves_degree p.property⟩
  invFun p := ⟨e.val.symm p, (e⁻¹).preserves_degree p.property⟩
  left_inv p := Subtype.ext (e.val.symm_apply_apply p)
  right_inv p := Subtype.ext (e.val.apply_symm_apply p)
  map_add' p q := Subtype.ext (map_add e.val (p : MvPolynomial σ R) (q : MvPolynomial σ R))
  map_smul' c p := Subtype.ext (map_smul e.val c (p : MvPolynomial σ R))

theorem degreeAction_apply_coe (e : WeightedLoweringAut w R) (n : ℕ)
    (p : weightedSupportLE (R := R) w n) :
    (e.degreeAction n p : MvPolynomial σ R) = e.val p := rfl

noncomputable def degreeActionHom (n : ℕ) :
    WeightedLoweringAut w R →*
      (weightedSupportLE (R := R) w n ≃ₗ[R] weightedSupportLE (R := R) w n) where
  toFun e := e.degreeAction n
  map_one' := by
    apply LinearEquiv.ext
    intro p
    rfl
  map_mul' e f := by
    apply LinearEquiv.ext
    intro p
    rfl

theorem degreeAction_difference_pow_coe (e : WeightedLoweringAut w R) (n k : ℕ)
    (p : weightedSupportLE (R := R) w n) :
    ((((e.degreeAction n).toLinearMap - 1) ^ k) p : MvPolynomial σ R) =
      (polynomialHomDifference e.val.toAlgHom ^ k) (p : MvPolynomial σ R) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl

theorem degreeAction_difference_pow_zero (e : WeightedLoweringAut w R) (n : ℕ) :
    ((e.degreeAction n).toLinearMap - 1) ^ (n + 1) = 0 := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change ((((e.degreeAction n).toLinearMap - 1) ^ (n + 1)) p : MvPolynomial σ R) = 0
  rw [degreeAction_difference_pow_coe]
  exact polynomialHomDifference_pow_eq_zero w e.val.toAlgHom e.property p.property

theorem degreeAction_difference_nilpotent (e : WeightedLoweringAut w R) (n : ℕ) :
    IsNilpotent ((e.degreeAction n).toLinearMap - 1) :=
  ⟨n + 1, e.degreeAction_difference_pow_zero n⟩

theorem degreeActionHom_injective (n : ℕ) (hw : ∀ i, w i ≤ n) :
    Function.Injective (degreeActionHom (w := w) (R := R) n) := by
  intro e f h
  have he : e.val.toAlgHom = f.val.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    have hi := congrArg (fun L : weightedSupportLE (R := R) w n ≃ₗ[R]
        weightedSupportLE (R := R) w n =>
      (L ⟨X i, weightedSupportLE_mono (hw i) (weightedSupportLE_X w i)⟩ :
        MvPolynomial σ R)) h
    exact hi
  apply Subtype.ext
  apply DFunLike.ext
  intro p
  exact congrArg (fun F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R => F p) he

end Erdos3.WeightedLoweringAut

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace SimplexHypergraph

noncomputable def normalizedDeletionCost {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) : ℝ :=
  (deletionCount deleted : ℝ) / (deletionCapacity V : ℝ)

end SimplexHypergraph

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxPairDivisibility
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def integerBoxUniformWeights {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j) :
    FiniteProbabilityWeights (∀ j, Finset.Ico (lo j) (hi j)) :=
  FiniteProbabilityWeights.pi (fun j => intervalUniformWeights (lo j) (hi j) (hlen j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialShearFiltration (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    NilpotentLieFiltration (PolynomialShearLieAlgebra w ℚ) s where
  layer := polynomialShearLayer w
  antitone := polynomialShearLayer_antitone w
  one_eq_top := polynomialShearLayer_one w
  lie_mem := polynomialShearLayer_bracket w _ _
  terminal := polynomialShearLayer_terminal w s hw

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

noncomputable def weightedPolynomialMul (w : σ → ℕ) (m n : ℕ) :
    weightedSupportLE (R := R) w m →ₗ[R]
      weightedSupportLE (R := R) w n →ₗ[R] weightedSupportLE (R := R) w (m + n) where
  toFun P :=
    { toFun := fun Q => ⟨P.val * Q.val, weightedSupportLE_mul P.property Q.property⟩
      map_add' := fun Q T => Subtype.ext (mul_add P.val Q.val T.val)
      map_smul' := fun c Q => Subtype.ext (mul_smul_comm c P.val Q.val) }
  map_add' P Q := by
    apply LinearMap.ext
    intro T
    exact Subtype.ext (add_mul P.val Q.val T.val)
  map_smul' c P := by
    apply LinearMap.ext
    intro Q
    exact Subtype.ext (smul_mul_assoc c P.val Q.val)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree
namespace OAI

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem topResidualShift_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    rename (earlierSlot i) (-A.topPart.specializeCenter 0 i) ∈ weightedSupportLE w (w i) := by
  simpa only [map_neg] using (weightedSupportLE w (w i)).neg_mem
    (A.topPart.specializeCenter_full_degree 0 i)

noncomputable def topResidualEquiv (A : PolynomialSlots σ d w) :
    MvPolynomial (Fin d) ℝ ≃ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  triangularPolynomialEquiv w (fun i => -A.topPart.specializeCenter 0 i) A.topResidualShift_degree

theorem topResidualEquiv_degree (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.topResidualEquiv p ∈ weightedSupportLE w n :=
  triangularPolynomialEquiv_degree w _ A.topResidualShift_degree hp

end Erdos3.PolynomialSlots

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} {d : ℕ} (w : Fin d → ℕ)

theorem symbolic_rename_degree {ι κ : Type*} (v : ι → ℕ) (z : κ → ℕ)
    (f : ι → κ) (hf : ∀ i, z (f i) = v i)
    {P : MvPolynomial ι ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE v n) :
    rename f P ∈ weightedSupportLE z n := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval v z _ _ hP
  intro i
  simpa only [Function.comp_apply, hf] using weightedSupportLE_X (R := ℝ) z (f i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearFactorialIntegrality
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

theorem WeightedLoweringAut.difference_pow_degree (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    (polynomialHomDifference e.val.toAlgHom ^ k) P ∈ weightedSupportLE w n := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact weightedSupportLT_le (e.difference_lower ih)

theorem WeightedLoweringAut.difference_pow_lower (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    (polynomialHomDifference e.val.toAlgHom ^ (k + 1)) P ∈ weightedSupportLT w n := by
  rw [pow_succ', Module.End.mul_apply]
  exact e.difference_lower (e.difference_pow_degree hP k)

variable [Algebra ℚ R]

noncomputable def polynomialShearLogOn (e : WeightedLoweringAut w R) (n : ℕ) :
    Module.End R (weightedSupportLE (R := R) w n) :=
  nilpotentLog ((e.degreeAction n).toLinearMap - 1)

theorem polynomialShearLogOn_sum (e : WeightedLoweringAut w R) (n : ℕ)
    (P : weightedSupportLE (R := R) w n) :
    (polynomialShearLogOn e n P : MvPolynomial σ R) =
      ∑ k ∈ Finset.range (n + 1), ((-1 : ℚ) ^ (k + 1) / k) •
        (polynomialHomDifference e.val.toAlgHom ^ k) (P : MvPolynomial σ R) := by
  simp [polynomialShearLogOn,
    nilpotentLog_eq_sum (a := (e.degreeAction n).toLinearMap - 1)
      (e.degreeAction_difference_pow_zero n), e.degreeAction_difference_pow_coe]

theorem polynomialShearLogOn_mono (e : WeightedLoweringAut w R)
    {m n : ℕ} (hmn : m ≤ n) (P : weightedSupportLE (R := R) w m) :
    (polynomialShearLogOn e n ⟨P.val, weightedSupportLE_mono hmn P.property⟩ :
      MvPolynomial σ R) = (polynomialShearLogOn e m P : MvPolynomial σ R) := by
  let inc : weightedSupportLE (R := R) w m →ₗ[R] weightedSupportLE (R := R) w n :=
    Submodule.inclusion (fun _ h => weightedSupportLE_mono hmn h)
  have hc : ((e.degreeAction n).toLinearMap - 1) ∘ₗ inc =
      inc ∘ₗ ((e.degreeAction m).toLinearMap - 1) := by
    apply LinearMap.ext
    intro Q
    rfl
  have h := nilpotentLog_intertwine (e.degreeAction_difference_nilpotent m)
    (e.degreeAction_difference_nilpotent n) hc
  exact congrArg Subtype.val (LinearMap.congr_fun h P)

theorem polynomialShearLogOn_leibniz (e : WeightedLoweringAut w R) (m n : ℕ)
    (P : weightedSupportLE (R := R) w m) (Q : weightedSupportLE (R := R) w n) :
    (polynomialShearLogOn e (m + n) (weightedPolynomialMul w m n P Q) : MvPolynomial σ R) =
      (polynomialShearLogOn e m P : MvPolynomial σ R) * Q.val +
        P.val * (polynomialShearLogOn e n Q : MvPolynomial σ R) := by
  have h := nilpotentLog_bilinear (weightedPolynomialMul (R := R) w m n)
    (e.degreeAction m).toLinearMap (e.degreeAction n).toLinearMap
    (e.degreeAction (m + n)).toLinearMap
    (e.degreeAction_difference_nilpotent m) (e.degreeAction_difference_nilpotent n)
    (e.degreeAction_difference_nilpotent (m + n))
    (fun x y => Subtype.ext (map_mul e.val x.val y.val)) P Q
  exact congrArg Subtype.val h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

noncomputable def polynomialShearLogValue (e : WeightedLoweringAut w R)
    (P : MvPolynomial σ R) : MvPolynomial σ R :=
  polynomialShearLogOn e (P.weightedTotalDegree w)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩

theorem polynomialShearLogValue_eq_on (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearLogValue e P = (polynomialShearLogOn e n ⟨P, hP⟩ : MvPolynomial σ R) :=
  (polynomialShearLogOn_mono e ((mem_weightedSupportLE_iff w n P).mp hP)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩).symm

theorem polynomialShearLogValue_eq_sum (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearLogValue e P = ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℚ) ^ (k + 1) / k) • (polynomialHomDifference e.val.toAlgHom ^ k) P := by
  rw [polynomialShearLogValue_eq_on e hP]
  exact polynomialShearLogOn_sum e n ⟨P, hP⟩

theorem polynomialShearLogValue_add (e : WeightedLoweringAut w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearLogValue e (P + Q) = polynomialShearLogValue e P + polynomialShearLogValue e Q := by
  let n := P.weightedTotalDegree w + Q.weightedTotalDegree w
  have hp : P ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n P).mpr (Nat.le_add_right _ _)
  have hq : Q ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n Q).mpr (Nat.le_add_left _ _)
  rw [polynomialShearLogValue_eq_on e ((weightedSupportLE w n).add_mem hp hq),
    polynomialShearLogValue_eq_on e hp, polynomialShearLogValue_eq_on e hq]
  exact congrArg Subtype.val ((polynomialShearLogOn e n).map_add ⟨P, hp⟩ ⟨Q, hq⟩)

theorem polynomialShearLogValue_smul (e : WeightedLoweringAut w R)
    (c : R) (P : MvPolynomial σ R) :
    polynomialShearLogValue e (c • P) = c • polynomialShearLogValue e P := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  rw [polynomialShearLogValue_eq_on e ((weightedSupportLE w _).smul_mem c hp),
    polynomialShearLogValue_eq_on e hp]
  exact congrArg Subtype.val ((polynomialShearLogOn e _).map_smul c ⟨P, hp⟩)

theorem polynomialShearLogValue_mul (e : WeightedLoweringAut w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearLogValue e (P * Q) =
      polynomialShearLogValue e P * Q + P * polynomialShearLogValue e Q := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  have hq : Q ∈ weightedSupportLE w (Q.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ Q).mpr le_rfl
  rw [polynomialShearLogValue_eq_on e (weightedSupportLE_mul hp hq),
    polynomialShearLogValue_eq_on e hp, polynomialShearLogValue_eq_on e hq]
  exact polynomialShearLogOn_leibniz e _ _ ⟨P, hp⟩ ⟨Q, hq⟩

theorem polynomialShearLogValue_C (e : WeightedLoweringAut w R) (c : R) :
    polynomialShearLogValue e (C c) = 0 := by
  rw [polynomialShearLogValue_eq_sum e (weightedSupportLE_C w 0 c)]
  simp

noncomputable def polynomialShearLogDerivation (e : WeightedLoweringAut w R) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) where
  toFun := polynomialShearLogValue e
  map_add' := polynomialShearLogValue_add e
  map_smul' := polynomialShearLogValue_smul e
  map_one_eq_zero' := by simpa using polynomialShearLogValue_C e 1
  leibniz' P Q := by
    change polynomialShearLogValue e (P * Q) =
      P • polynomialShearLogValue e Q + Q • polynomialShearLogValue e P
    rw [polynomialShearLogValue_mul]
    simp only [smul_eq_mul]
    ring

theorem polynomialShearLogValue_lower (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearLogValue e P ∈ weightedSupportLT w n := by
  rw [polynomialShearLogValue_eq_sum e hP, Finset.sum_range_succ']
  simp only [Nat.cast_zero, div_zero, zero_smul, add_zero]
  apply (weightedSupportLT w n).sum_mem
  intro k hk
  exact (weightedSupportLT (R := R) w n).restrictScalars ℚ |>.smul_mem _
    (e.difference_pow_lower hP k)

noncomputable def polynomialShearLog (e : WeightedLoweringAut w R) :
    PolynomialShearLieAlgebra w R :=
  ⟨polynomialShearLogDerivation e, fun i => by
    change polynomialShearLogValue e (X i) ∈ weightedSupportDrop w (w i) 1
    rw [weightedSupportDrop_one]
    exact polynomialShearLogValue_lower e (weightedSupportLE_X w i)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialEndomorphisms
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def weightedPolynomialEndDrop (w : σ → ℕ) (s k : ℕ) :
    Submodule R (Module.End R (weightedSupportLE (R := R) w s)) where
  carrier := {F | ∀ n r (P : weightedSupportLE (R := R) w s),
    (P : MvPolynomial σ R) ∈ weightedSupportDrop w n r →
      (F P : MvPolynomial σ R) ∈ weightedSupportDrop w n (r + k)}
  zero_mem' := fun n r _P _h => (weightedSupportDrop w n (r + k)).zero_mem
  add_mem' := fun hF hG n r P h => (weightedSupportDrop w n (r + k)).add_mem
    (hF n r P h) (hG n r P h)
  smul_mem' := fun c _F hF n r P h => (weightedSupportDrop w n (r + k)).smul_mem c
    (hF n r P h)

theorem weightedPolynomialEndDrop_antitone (w : σ → ℕ) (s : ℕ) :
    Antitone (weightedPolynomialEndDrop (R := R) w s) := by
  intro a b hab F hF n r P hP
  exact weightedSupportDrop_antitone (Nat.add_le_add_left hab r) (hF n r P hP)

theorem weightedPolynomialEndDrop_mul (w : σ → ℕ) (s a b : ℕ)
    {F G : Module.End R (weightedSupportLE (R := R) w s)}
    (hF : F ∈ weightedPolynomialEndDrop w s a) (hG : G ∈ weightedPolynomialEndDrop w s b) :
    F * G ∈ weightedPolynomialEndDrop w s (a + b) := by
  intro n r P hP
  have h := hF n (r + b) (G P) (hG n r P hP)
  change (F (G P) : MvPolynomial σ R) ∈ weightedSupportDrop w n (r + (a + b))
  simpa only [Nat.add_assoc, Nat.add_comm b a] using h

theorem weightedPolynomialEndDrop_one (w : σ → ℕ) (s : ℕ) :
    (1 : Module.End R (weightedSupportLE (R := R) w s)) ∈ weightedPolynomialEndDrop w s 0 := by
  intro n r P hP
  change (P : MvPolynomial σ R) ∈ weightedSupportDrop w n (r + 0)
  simpa only [Nat.add_zero] using hP

theorem weightedPolynomialEndDrop_terminal (w : σ → ℕ) (s : ℕ)
    {F : Module.End R (weightedSupportLE (R := R) w s)}
    (hF : F ∈ weightedPolynomialEndDrop w s (s + 1)) : F = 0 := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  have h := hF s 0 P (by simpa only [weightedSupportDrop_zero] using P.property)
  exact weightedSupportDrop_eq_zero (by omega) h

noncomputable def weightedPolynomialEndAlgebra (w : σ → ℕ) (s : ℕ) :
    Subalgebra R (Module.End R (weightedSupportLE (R := R) w s)) :=
  (weightedPolynomialEndDrop w s 0).toSubalgebra (weightedPolynomialEndDrop_one w s)
    (fun _ _ hF hG => weightedPolynomialEndDrop_mul w s 0 0 hF hG)

noncomputable instance weightedPolynomialEndAlgebraRing (w : σ → ℕ) (s : ℕ) :
    Ring (weightedPolynomialEndAlgebra (R := R) w s) :=
  @Subalgebra.toRing R (Module.End R (weightedSupportLE (R := R) w s)) _ _ _
    (weightedPolynomialEndAlgebra w s)

noncomputable def weightedPolynomialEndLayer (w : σ → ℕ) (s k : ℕ) :
    Submodule ℚ (weightedPolynomialEndAlgebra (R := ℚ) w s) :=
  (weightedPolynomialEndDrop w s k).comap (weightedPolynomialEndAlgebra w s).val.toLinearMap

noncomputable def weightedPolynomialEndFiltration (w : σ → ℕ) (s : ℕ) :
    NilpotentAlgebraFiltration (weightedPolynomialEndAlgebra (R := ℚ) w s) s where
  layer := weightedPolynomialEndLayer w s
  antitone := by
    intro a b hab F hF
    exact weightedPolynomialEndDrop_antitone w s hab hF
  zero_eq_top := by
    apply top_unique
    intro F hF
    exact F.property
  mul_mem := by
    intro a b F G hF hG
    exact weightedPolynomialEndDrop_mul w s a b hF hG
  terminal := by
    apply bot_unique
    intro F hF
    change F = 0
    exact Subtype.ext (weightedPolynomialEndDrop_terminal w s hF)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearRationalFiltration
namespace OAI

section

namespace Erdos3

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] (w : σ → ℕ)

noncomputable def polynomialShearRatFiltration (s : ℕ) (hw : ∀ i, w i ≤ s) :
    NilpotentLieFiltration (PolynomialShearLieAlgebra w R) s where
  layer i := (polynomialShearLayer (R := R) w i).restrictScalars ℚ
  antitone := polynomialShearLayer_antitone w
  one_eq_top := by rw [polynomialShearLayer_one]; rfl
  lie_mem := polynomialShearLayer_bracket w _ _
  terminal := by rw [polynomialShearLayer_terminal w s hw]; rfl

noncomputable def weightedPolynomialEndRatLayer (s k : ℕ) :
    Submodule ℚ (weightedPolynomialEndAlgebra (R := R) w s) :=
  ((weightedPolynomialEndDrop w s k).comap
    (weightedPolynomialEndAlgebra (R := R) w s).val.toLinearMap).restrictScalars ℚ

noncomputable def weightedPolynomialEndRatFiltration (s : ℕ) :
    NilpotentAlgebraFiltration (weightedPolynomialEndAlgebra (R := R) w s) s where
  layer := weightedPolynomialEndRatLayer w s
  antitone := by
    intro a b hab F hF
    exact weightedPolynomialEndDrop_antitone w s hab hF
  zero_eq_top := by
    apply top_unique
    intro F hF
    exact F.property
  mul_mem := by
    intro a b F G hF hG
    exact weightedPolynomialEndDrop_mul w s a b hF hG
  terminal := by
    apply bot_unique
    intro F hF
    change F = 0
    exact Subtype.ext (weightedPolynomialEndDrop_terminal w s hF)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ]

abbrev WeightedBasisIndex (w : σ → ℕ) (d : ℕ) :=
  σ ⊕ {a : σ →₀ ℕ | Finsupp.weight w a < d}

noncomputable def weightedBasisGrade (w : σ → ℕ) (d : ℕ) : WeightedBasisIndex w d → ℕ :=
  Sum.elim w (fun a => d - Finsupp.weight w a.val)

omit [Fintype σ] in
@[simp] theorem weightedBasisGrade_inl (w : σ → ℕ) (d : ℕ) (i : σ) :
    weightedBasisGrade w d (Sum.inl i) = w i := rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem positive_weight_of_ne_zero (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    {α : σ →₀ ℕ} (hα : α ≠ 0) : 0 < Finsupp.weight w α := by
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hα
  exact (hw i).trans_le (Finsupp.le_weight_of_ne_zero' w hi)

end Erdos3.NilpotentLieFiltration

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

theorem sumExponent_weight (v : σ → ℕ) (w : τ → ℕ) (α : σ →₀ ℕ) (β : τ →₀ ℕ) :
    Finsupp.weight (Sum.elim v w) (α.sumElim β) =
      Finsupp.weight v α + Finsupp.weight w β := by
  simp only [Finsupp.weight_apply, Finsupp.sum_sumElim, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr]

theorem polynomialSlotCoefficient_degree (v : σ → ℕ) (w : τ → ℕ)
    {n : ℕ} {P : MvPolynomial (σ ⊕ τ) R}
    (hP : P ∈ weightedSupportLE (Sum.elim v w) n) (β : τ →₀ ℕ) :
    polynomialSlotCoefficient β P ∈ weightedSupportLE v (n - Finsupp.weight w β) := by
  intro α hα
  change α ∈ (polynomialSlotCoefficient β P).support at hα
  have hne : (polynomialSlotCoefficient β P).coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  rw [polynomialSlotCoefficient_coeff] at hne
  have h : Finsupp.weight (Sum.elim v w) (α.sumElim β) ≤ n :=
    hP (MvPolynomial.mem_support_iff.mpr hne)
  rw [sumExponent_weight] at h
  change Finsupp.weight v α ≤ n - Finsupp.weight w β
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbitConverse
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*} {s d : ℕ}

theorem symbolicShearPrefixSubstitution_degree (w : Fin d → ℕ) (i : Fin d)
    (v : τ ⊕ Fin d) :
    symbolicShearPrefixSubstitution i v ∈
      weightedSupportLE (patchVariableWeight w i) (Sum.elim (fun _ : τ => 1) w v) := by
  classical
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
      dsimp only [symbolicShearPrefixSubstitution, Sum.elim_inr]
      split_ifs with h
      · have hj : earlierSlot i ⟨j.val, h⟩ = j := Fin.ext rfl
        have hx := weightedSupportLE_X (R := ℝ)
          (patchVariableWeight (σ := τ) w i) (Sum.inr ⟨j.val, h⟩)
        change _ ∈ weightedSupportLE _ (w (earlierSlot i ⟨j.val, h⟩)) at hx
        rw [hj] at hx
        exact hx
      · exact Submodule.zero_mem _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedTranslationBufferedCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ]

section Metric

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  [Fintype (WeightedBasisIndex w d)]
  [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

noncomputable def weightedTranslationDisplacementConstant (d n m : ℕ) : ℝ :=
  2 * ((polynomialShearDisplacementBound d (n+1) 1 : ℝ) + 1) *
    ((bchLogMetricConstant d m (2*d+1) 1 : ℝ) + 1)

theorem weightedTranslationDisplacementConstant_pos (d n m : ℕ) :
    0 < weightedTranslationDisplacementConstant d n m := by
  unfold weightedTranslationDisplacementConstant
  positivity

end Metric

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedLieUpperSpan
namespace OAI

section

namespace Erdos3

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem weightedLieTree_eval_mem_layer {s : ℕ} (F : NilpotentLieFiltration M s)
    (v : I → M) (w : I → ℕ) (hv : ∀ i, v i ∈ F.layer (w i)) (a : FreeMagma I) :
    lieTreeEval v a ∈ F.layer (lieTreeWeight w a) := by
  induction a using FreeMagma.rec with
  | of i => exact hv i
  | mul a b ha hb => exact F.lie_mem ha hb

theorem weightedLieUpperSpan_le_comap {s : ℕ} (F : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (v : I → L) (w : I → ℕ)
    (hv : ∀ i, φ (v i) ∈ F.layer (w i)) (d : ℕ) :
    weightedLieUpperSpan v w d ≤ (F.layer d).comap φ.toLinearMap := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, rfl⟩
  change φ (lieTreeEval v a) ∈ F.layer d
  rw [map_lieTreeEval]
  exact F.antitone ha (weightedLieTree_eval_mem_layer F (fun i => φ (v i)) w hv a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeNilpotentLieAlgebra
namespace OAI

section

namespace Erdos3

variable (X : Type*) (s : ℕ)

namespace FreeNilpotentLieAlgebra

variable {X s} {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def lift (f : X → L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ L :=
  lieQuotientDescend _ (FreeLieAlgebra.lift ℚ f) (lowerCentralSeries_le_lift_ker f hnil)

end FreeNilpotentLieAlgebra

end Erdos3

end

end OAI
end


