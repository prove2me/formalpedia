-- Prove2me | Definitions.Def_OAIE3v2B120
-- name    : OAIE3v2B120
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:48:13.752321+00:00
-- url     : https://prove2.me/theorems/426aae9b-218e-47a5-a3cf-4f82258a4283
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 122 of 311
-- statement:
--   Definitions bundle 122 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B102`, `OAIE3v2B104`, `OAIE3v2B105`, `OAIE3v2B106`, `OAIE3v2B107` of this split.
--
--   Modules: `Estimates/DerivativeHorizontalLifts.lean`, `Estimates/DerivativeIndexBounds.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/RealSubspaceIntersectionCorrections.lean`, `Estimates/SquareGradedRelative.lean`, `Estimates/StepDropTerminalContainment.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Estimates/WeightedOrbitNormalization.lean`, `Geometry/FilteredSymbolMapCoordinates.lean`, `Geometry/HorizontalSeparationTransport.lean`, `Geometry/RealFastCoefficientCoordinates.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Lattices/EuclideanLatticeGraph.lean`, `Linear/BoundedSpanningPadding.lean`, `Linear/ControlledKernelSplitTransport.lean`, `Linear/RationalTagConstraintChartBasis.lean`, `Linear/RationalTaggedSpanProjection.lean`, `Linear/ReindexGradedBasis.lean`, `Linear/WeightedTranslationBasisHeight.lean`, `Nilpotent/BCHUniformQuotientCharts.lean`, `Polynomial/FormalPolynomialCorrectionStep.lean`, `Polynomial/PolynomialSymbolBounds.lean`, `Polynomial/RankPolynomialFactorization.lean`, `Polynomial/RealAdaptedPolynomialGroup.lean`, `Polynomial/RealPolynomialChartSubstitution.lean`, `Polynomial/ScaledPolynomialDualBounds.lean`, `Polynomial/ShiftedPolynomialBasis.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B102
import Definitions.Def_OAIE3v2B104
import Definitions.Def_OAIE3v2B105
import Definitions.Def_OAIE3v2B106
import Definitions.Def_OAIE3v2B107

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem eval₂_dualAdjoint (t : σ → ℝ) (P : PolynomialGroup σ hnil)
    (Q : VectorPolynomial σ ℚ L) :
    eval₂ t (dualAdjoint P Q) = dualAdjoint (realPolynomialValueHom t P) (eval₂ t Q) := by
  have h := map_dualAdjoint (hM := hnil) (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t) P Q
  simp only [eval₂Lie_apply] at h
  exact h

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

noncomputable def constantDirection : PolynomialTranslationLie σ := ⟨0, 1⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3

open Module

theorem exists_bch_fixed_product_exp_bound (s a k : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (rs : List (NilpotentLieBCHGroup L s hnil)),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → rs.length ≤ k →
      (H : ℝ) ≤ Real.exp p → (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ r ∈ rs, ∀ i, |e.repr r.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ i, |e.repr rs.prod.coord i| ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hbox⟩ := exists_bch_product_box_bound s
  refine ⟨C + 3 * (s + k) + a + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil rs hstructure hp hd hn hH hc hrs i
  let f : Fin rs.length → L := fun j => (rs.get j).coord
  let xs := List.finRange rs.length
  have hlen : (xs.length : ℝ) ≤ p + k := by
    have hn' : (rs.length : ℝ) ≤ k := by exact_mod_cast hn
    simpa only [xs, List.length_finRange] using hn'.trans (by linarith)
  have hlabels : (Fintype.card (Fin rs.length) : ℝ) ≤ p + k := by
    simpa only [Fintype.card_fin, xs, List.length_finRange] using hlen
  have hbound := hbox e c H (p + k) xs f (Real.exp ((p + 2) ^ a)) hstructure hnil
    (by positivity) (hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) k])) hlabels hlen
    (hH.trans (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k]))) hc
    (Real.one_le_exp (by positivity)) (fun j z => hrs (rs.get j) (List.get_mem _ _) z) i
  have hmap : xs.map (fun j => (⟨f j⟩ : NilpotentLieBCHGroup L s hnil)) = rs := by
    change (List.finRange rs.length).map rs.get = rs
    exact List.map_get_finRange rs
  have hcoord := lieBCHList_group_prod s hnil f xs
  rw [hmap] at hcoord
  rw [← hcoord, Fintype.card_fin] at hbound
  exact hbound.trans (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      bch_bounded_product_box_expression_le_exp s a C rs.length k (Fintype.card ι) hC hn hp hd)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem mem_squareLattice (Γ : Subgroup F.Group) (g : F.squareFiltration.Group) :
    g ∈ F.squareLattice Γ ↔ F.squareFstHom g ∈ Γ ∧ F.squareSndHom g ∈ Γ := Iff.rfl

theorem squareLattice_le_snd (Γ : Subgroup F.Group) : F.squareLattice Γ ≤ Γ.comap F.squareSndHom :=
  fun _ h => h.2

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialBasis
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem eval_normalizedShiftLog (s : ℕ) (h x : σ → ℚ) (a b : L)
    (p : VectorPolynomial σ ℚ L) :
    eval x (normalizedShiftLog s h a b p) = lieBCH s a (lieBCH s (eval (fun i => x i + h i) p) b) := by
  simp only [normalizedShiftLog, eval_lieBCH, eval_translate, eval_monomial,
    Finsupp.prod_zero_index, one_smul]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem normalizedShiftLog_adapted (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (a b : L) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) :
    F.Adapted w (normalizedShiftLog s h a b p) :=
  F.adapted_bch w (F.adapted_constant w a)
    (F.adapted_bch w (F.adapted_translate w hw h hp) (F.adapted_constant w b))

theorem normalizedShiftLog_sub_coefficient_mem (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (a b : L) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) (α : σ →₀ ℕ) :
    coefficients (normalizedShiftLog s h a b p - p) α ∈ F.layer (Finsupp.weight w α + 1) := by
  let p₀ : F.adaptedLieSubalgebra w := ⟨p, (F.mem_adaptedSubmodule w p).mpr hp⟩
  let p₁ : F.adaptedLieSubalgebra w :=
    ⟨translate h p, (F.mem_adaptedSubmodule w _).mpr (F.adapted_translate w hw h hp)⟩
  let c₁ := F.adaptedConstant w a
  let c₂ := F.adaptedConstant w b
  let I := F.shiftedAdaptedIdeal w
  let z := lieBCH s c₁ (lieBCH s p₁ c₂)
  have hz₁ : z - lieBCH s p₁ c₂ ∈ I :=
    lieBCH_sub_right_mem_of_mem_ideal (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot I
      (F.adaptedConstant_mem_shiftedIdeal w a) _
  have hz₂ : lieBCH s p₁ c₂ - p₁ ∈ I :=
    lieBCH_sub_left_mem_of_mem_ideal (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot I _
      (F.adaptedConstant_mem_shiftedIdeal w b)
  have hz₃ : p₁ - p₀ ∈ I := F.translate_sub_coefficient_mem w hw h hp
  have hz : z - p₀ ∈ I := by
    have hh := I.add_mem (I.add_mem hz₁ hz₂) hz₃
    have he : (z - lieBCH s p₁ c₂ + (lieBCH s p₁ c₂ - p₁)) + (p₁ - p₀) = z - p₀ := by abel
    rw [he] at hh
    exact hh
  have he : (F.adaptedLieSubalgebra w).incl z = normalizedShiftLog s h a b p := by
    dsimp only [z]
    rw [map_lieBCH, map_lieBCH]
    rfl
  have hh := hz α
  change coefficients ((F.adaptedLieSubalgebra w).incl (z - p₀)) α ∈ _ at hh
  rw [map_sub, he] at hh
  exact hh

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem exists_normalized_shift_square (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (a b : L) (p : VectorPolynomial σ ℚ L) (hp : F.Adapted w p)
    (hzero : coefficients (normalizedShiftLog s h a b p - p) 0 ∈ F.layer 2) :
    ∃ r : VectorPolynomial σ ℚ F.squareLieSubalgebra,
      F.squareFiltration.Adapted w r ∧
      VectorPolynomial.map F.squareFst.toLinearMap r = normalizedShiftLog s h a b p ∧
      VectorPolynomial.map F.squareSnd.toLinearMap r = p :=
  F.exists_square_polynomial w hw _ _ (F.normalizedShiftLog_adapted w hw h a b hp) hp
    (F.normalizedShiftLog_sub_coefficient_mem w hw h a b hp) hzero

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

section Structure

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem adaptedMonomialBasis_bracket [DecidableEq σ] (u v z : AdaptedBasisIndex w ω) :
    (F.adaptedMonomialBasis b ω hlayers w).repr
      ⁅F.adaptedMonomialBasis b ω hlayers w u, F.adaptedMonomialBasis b ω hlayers w v⁆ z =
      if u.val.1 + v.val.1 = z.val.1 then b.repr ⁅b u.val.2, b v.val.2⁆ z.val.2 else 0 := by
  classical
  rw [F.adaptedMonomialBasis_repr]
  change b.repr (coefficients
    ⁅(F.adaptedMonomialBasis b ω hlayers w u : VectorPolynomial σ ℚ L),
      (F.adaptedMonomialBasis b ω hlayers w v : VectorPolynomial σ ℚ L)⁆ z.val.1) z.val.2 = _
  rw [F.adaptedMonomialBasis_coe, F.adaptedMonomialBasis_coe, lie_monomial, coefficients_monomial]
  by_cases h : u.val.1 + v.val.1 = z.val.1
  · simp only [h, Finsupp.single_eq_same, ite_true]
  · simp only [Finsupp.single_eq_of_ne (Ne.symm h), map_zero, Finsupp.zero_apply, h, ite_false]

theorem adaptedMonomialBasis_bracket_height {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) :
    ∀ i j k, RationalHeightLE ((F.adaptedMonomialBasis b ω hlayers w).repr
      ⁅F.adaptedMonomialBasis b ω hlayers w i, F.adaptedMonomialBasis b ω hlayers w j⁆ k) H := by
  classical
  intro i j k
  rw [F.adaptedMonomialBasis_bracket]
  split_ifs
  · exact hb _ _ _
  · exact rationalHeightLE_zero hH

end Structure

section Dimension

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) (s : ℕ)
  (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

include hw hω

variable [Fintype σ] [Fintype ι]

theorem adaptedBasisIndex_card_le [Fintype (AdaptedBasisIndex w ω)] :
    Fintype.card (AdaptedBasisIndex w ω) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  have hc := Fintype.card_le_of_injective (adaptedBasisCode w ω s hw hω)
    (adaptedBasisCode_injective w ω s hw hω)
  simp only [Fintype.card_prod, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  apply hc.trans
  calc
    (∑ n : Fin (s + 1), Fintype.card σ ^ n.val) * Fintype.card ι ≤
        (∑ _ : Fin (s + 1), (Fintype.card σ + 1) ^ s) * Fintype.card ι := by
      apply Nat.mul_le_mul_right
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp; ring

end Dimension
end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

open Module

theorem symbolRationalGrid_inv {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (l : ℕ) {g : F.RealPolynomialSymbolGroup w}
    (hg : F.SymbolRationalGrid b ω hlayers w l g) :
    F.SymbolRationalGrid b ω hlayers w l g⁻¹ := by
  change (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr (-g.coord) z)
    ∈ realDenominatorGrid l
  have heq : (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr (-g.coord) z) =
      -(fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z) := by
    funext z
    simp only [map_neg, Finsupp.neg_apply, Pi.neg_apply]
  rw [heq]
  exact realDenominatorGrid_neg l hg

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_symbol_slow_product_bound (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ rs : List (F.RealPolynomialSymbolGroup w), rs.length ≤ k →
      (∀ r ∈ rs, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) r) →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_bch_fixed_product_exp_bound s a k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT rs hlen hrs
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.polynomialSymbolBasis b ω hlayers w
  let E := F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hstruct : ∀ i j z, algebraMap ℚ ℝ (lieStructureConstants B i j z) = E.repr ⁅E i, E j⁆ z :=
    fun i j z => (F.scaledRealPolynomialSymbolBasis_structure b ω hlayers w T hT i j z).symm
  have hheight : ∀ i j z, RationalHeightLE (lieStructureConstants B i j z) H :=
    F.polynomialSymbolBasis_bracket_height b ω hlayers w hH hb
  have hinput : ∀ r ∈ rs, ∀ z, |E.repr r.coord z| ≤ Real.exp ((q + 2) ^ a) := by
    intro r hr z
    have hscaled := (F.scaledRealPolynomialSymbolBasis_bound_iff b ω hlayers w T hT
      r.coord z (Real.exp ((p + 2) ^ a))).mpr (hrs r hr z)
    exact hscaled.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  intro z
  apply (F.scaledRealPolynomialSymbolBasis_bound_iff b ω hlayers w T hT
    rs.prod.coord z (Real.exp ((p + C) ^ C))).mp
  exact (hK E (lieStructureConstants B) H q
    (realification_lowerCentralSeries_eq_bot (F.polynomialSymbol_lowerCentralSeries_eq_bot w))
    rs hstruct hq hdim hlen (hHp.trans (Real.exp_le_exp.mpr hpq)) hheight hinput z).trans
      (Real.exp_le_exp.mpr hpoly)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

include hlayers

theorem symbolBasisIndex_monomial_ne_zero (z : SymbolBasisIndex w ω) : z.val.1 ≠ 0 := by
  intro hz
  have hd := z.property
  rw [hz, map_zero] at hd
  have hp := F.adaptedBasis_weight_pos b ω hlayers z.val.2
  omega

theorem symbolSlowBound_log_norm [Fintype (SymbolBasisIndex w ω)]
    (T : σ → ℝ) {R M : ℝ} (hR : 1 ≤ R) (hT : ∀ i, R ≤ T i) (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hlayers w T M g) :
    ‖((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).equivFun g.coord‖ ≤ M / R := by
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hM (zero_le_one.trans hR))).mpr
  intro z
  change |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z| ≤ M / R
  have hscale := le_monomialScale_of_ne_zero T hR hT
    (F.symbolBasisIndex_monomial_ne_zero b ω hlayers w z)
  exact (hg z).trans (div_le_div_of_nonneg_left hM (zero_lt_one.trans_le hR) hscale)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem sub_realGradeTruncation_mem (j : ℕ) (x : ℝ ⊗[ℚ] L) :
    x - basisBelowProjection (b.baseChange ℝ) w j x ∈ F.realification.layer j := by
  change x - basisBelowProjection (b.baseChange ℝ) w j x ∈ (F.realLayer j).toSubmodule
  rw [F.realLayer_eq_span_basis b j {i | j ≤ w i} (hlayers j)]
  exact sub_basisBelowProjection_mem (b.baseChange ℝ) w j x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ : Type*}

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : ι ≃ κ)
  (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)}))
  (w : σ → ℕ)

theorem symbolRationalGrid_reindex_iff (l : ℕ) (g : F.RealPolynomialSymbolGroup w) :
    F.SymbolRationalGrid (b.reindex e) (fun k => ω (e.symm k)) hF' w l g ↔
      F.SymbolRationalGrid b ω hF w l g := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun z => a (reindexSymbolBasisIndex w ω e z), ?_⟩
    funext z
    have hz := congrFun ha (reindexSymbolBasisIndex w ω e z)
    change (a (reindexSymbolBasisIndex w ω e z) : ℝ) = (l : ℝ) *
      ((F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).baseChange ℝ).repr
        g.coord (reindexSymbolBasisIndex w ω e z) at hz
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w,
      Equiv.symm_apply_apply] at hz
    exact hz
  · rintro ⟨a, ha⟩
    refine ⟨fun z => a ((reindexSymbolBasisIndex w ω e).symm z), ?_⟩
    funext z
    change (a ((reindexSymbolBasisIndex w ω e).symm z) : ℝ) = (l : ℝ) *
      ((F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).baseChange ℝ).repr
        g.coord z
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w]
    exact congrFun ha ((reindexSymbolBasisIndex w ω e).symm z)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_symbol_slow_mul_inv_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ E A : F.RealPolynomialSymbolGroup w,
      F.SymbolSlowBound b ω hF w T (Real.exp (p + 2)) E →
      F.SymbolSlowBound b ω hF w T (Real.exp (p + 2)) A →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + C) ^ C)) (E * A⁻¹) := by
  obtain ⟨C, hC, hprod⟩ := exists_symbol_slow_product_bound s 1 2
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hc T hT E A hE hA
  have hinputs : ∀ x ∈ [E, A⁻¹], F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ 1)) x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simpa only [pow_one] using hE
    · simpa only [pow_one] using (F.symbolSlowBound_inv_iff b ω hF w T _ A).mpr hA
  simpa only [List.prod_cons, List.prod_nil, mul_one] using
    hprod F b ω hF w hw H p hH hp hι hσ hHp hc T hT [E, A⁻¹] (by simp) hinputs

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanLatticeGraph
namespace OAI

section

namespace Erdos3

theorem exists_euclidean_lattice_graph_identity
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (Λ : Submodule ℤ Z) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (hinteger : ∀ x ∈ Λ,
      euclideanDerivativeShiftMap T (fun i => (hT i).ne') x.val ∈ realIntegerGrid)
    (hsurj : Function.Surjective
      ((euclideanDerivativeShiftMap T (fun i => (hT i).ne')).comp Z.subtype)) :
    let π : Z →ₗ[ℝ] (σ → ℝ) :=
      (euclideanDerivativeShiftMap T (fun i => (hT i).ne')).comp Z.subtype
    ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ = ZLattice.covolume (latticeKernel Λ π)
        (MeasureTheory.volume (α := LinearMap.ker π)) *
        (((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) /
          ∏ i, T i) *
        Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det := by
  let π := (euclideanDerivativeShiftMap T (fun i => (hT i).ne')).comp Z.subtype
  obtain ⟨G, hright, hsection, hcov⟩ :=
    exists_scaled_lattice_covolume_identity Λ π hinteger hsurj T hT
  refine ⟨G, ?_, ?_, hcov⟩
  · intro y i
    have he := congrFun (hright y) i
    change T i * (G y).val (Sum.inl i) = T i * y i at he
    exact mul_left_cancel₀ (hT i).ne' he
  · intro x
    have he : (fun i => π x i / T i) = fun i => x.val (Sum.inl i) := by
      funext i
      exact mul_div_cancel_left₀ _ (hT i).ne'
    simpa only [he] using hsection x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeIndexBounds
namespace OAI

section

namespace Erdos3

theorem euclideanDerivative_covolume_factorization
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hscale Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup
    0 < I ∧ ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume (shortVectorLattice Λ ρ) =
        ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
          (MeasureTheory.volume (α := LinearMap.ker π)) *
          ((I : ℝ) / ∏ i, T i) *
          Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det := by
  let hTpos : ∀ i, 0 < T i := fun i => lt_of_lt_of_le zero_lt_one (hT i)
  let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T (fun i => (hTpos i).ne') scale hscale Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T (fun i => (hTpos i).ne')).comp Z.subtype
  have hproj := euclideanDerivativeLattice_shortSpan_projection
    T hT scale hscale Y A l hl R δ hR H r hr hnorm hdense hlarge
  have hsurj : Function.Surjective π :=
    euclidean_shift_subspace_surjective Z T (fun i => (hTpos i).ne') hproj
  have hinteger : ∀ x ∈ shortVectorLattice Λ ρ, π x ∈ realIntegerGrid := by
    intro x hx
    exact euclideanDerivativeShiftMap_integer T (fun i => (hTpos i).ne')
      scale hscale Y A l hl x.val hx
  exact ⟨latticeImage_index_pos _ π hinteger hsurj,
    exists_euclidean_lattice_graph_identity Z (shortVectorLattice Λ ρ) T hTpos hinteger hsurj⟩

end Erdos3

end

section

namespace Erdos3

open Module

theorem euclideanDerivative_covolume_product_bound
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hscale Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup
    0 < I ∧ ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
        (MeasureTheory.volume (α := LinearMap.ker π)) * (I : ℝ) *
        Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det ≤
        (((finrank ℝ Z : ℝ) + 2) * ρ) ^ finrank ℝ Z / δ := by
  obtain ⟨hI, G, hG, hsection, hfactor⟩ := euclideanDerivative_covolume_factorization
    T hT scale hscale Y A l hl R δ hR H r hr hnorm hdense hlarge
  refine ⟨hI, G, hG, hsection, ?_⟩
  have hTpos (i) : 0 < T i := lt_of_lt_of_le zero_lt_one (hT i)
  have hbound := euclideanDerivative_covolume_density_bound T hTpos scale hscale
    Y A l hl R δ (zero_le_one.trans hR) hδ H r hr hnorm hdense
  exact scaled_covolume_product_le (Finset.prod_pos (fun i _ => hTpos i)) hδ hfactor hbound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedOrbitNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem normalizedShift_horizontal_zero (h : σ → ℚ) (p : VectorPolynomial σ ℚ L)
    (ε γ : F.Group)
    (heq : (⟨eval h p⟩ : F.Group) * (⟨eval (fun _ => 0) p⟩ : F.Group)⁻¹ = ε * γ) :
    coefficients (normalizedShiftLog s h (-ε.coord) (-γ.coord) p - p) 0 ∈ F.layer 2 := by
  have hh := congrArg F.horizontalLog heq
  simp only [horizontalLog_mul, horizontalLog_inv] at hh
  rw [← sub_eq_add_neg] at hh
  change lieQuotientMap (F.layerIdeal 2) (eval h p) -
    lieQuotientMap (F.layerIdeal 2) (eval (fun _ => 0) p) =
    lieQuotientMap (F.layerIdeal 2) ε.coord + lieQuotientMap (F.layerIdeal 2) γ.coord at hh
  have hsolve := (sub_eq_iff_eq_add).mp hh
  apply (lieQuotientMap_eq_zero (F.layerIdeal 2) _).mp
  rw [← eval_zero_eq_coefficient]
  simp only [map_sub, eval_normalizedShiftLog, F.horizontal_bch, map_neg, zero_add]
  rw [hsolve]
  abel

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareGradedRelative
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem associatedGradedFiltration_layer (j : ℕ) :
    F.associatedGradedFiltration.layer j =
      Submodule.span ℚ (F.associatedGradedBasis b ω hlayers '' {i | j ≤ ω i}) := by
  rw [associatedGradedFiltration, F.polynomialSymbolFiltration_layer b ω hlayers]
  congr 1
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.val.2, hz, ?_⟩
    rw [F.associatedGradedBasis_apply]
    congr 1
    exact (associatedGradedIndexEquiv ω).left_inv z
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩, hi, ?_⟩
    exact (F.associatedGradedBasis_apply b ω hlayers i).symm

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def squareGradedRelativePiece (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.AssociatedGraded :=
  (F.squareFiltration.associatedGradedPieceMap j).comp (F.squareRelativeLayer j hj)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem squareGradedPiece_decomposition (j : ℕ) (hj : 1 ≤ j)
    (x : F.squareFiltration.layer j) :
    F.squareFiltration.associatedGradedPieceMap j x =
      F.squareGradedDiagonalPiece j ⟨x.val.val.2, x.property.2.1⟩ +
      F.squareGradedRelativePiece j hj ⟨x.val.val.1 - x.val.val.2, x.property.2.2⟩ := by
  change F.squareFiltration.associatedGradedPieceMap j x =
    F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j _) +
      F.squareFiltration.associatedGradedPieceMap j (F.squareRelativeLayer j hj _)
  rw [← map_add]
  apply congrArg (F.squareFiltration.associatedGradedPieceMap j)
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val = (x.val.val.2, x.val.val.2) + (x.val.val.1 - x.val.val.2, 0)
  apply Prod.ext
  · change x.val.val.1 = x.val.val.2 + (x.val.val.1 - x.val.val.2)
    abel
  · exact (add_zero _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem gradedSymbolPolynomial_block_coefficient [DecidableEq σ]
    (α β : σ →₀ ℕ) (x : F.PolynomialSymbol w) :
    coefficients (F.gradedSymbolPolynomial b ω hlayers w
      (basisCoordinateProjection (F.polynomialSymbolBasis b ω hlayers w)
        {z | z.val.1 = α} x)) β =
      if β = α then coefficients (F.gradedSymbolPolynomial b ω hlayers w x) β else 0 := by
  classical
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  by_cases hβ : β = α
  · rw [if_pos hβ]
    by_cases hd : Finsupp.weight w β = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(β, i), hd⟩,
        F.gradedSymbolPolynomial_coefficient b ω hlayers w x ⟨(β, i), hd⟩,
        basisCoordinateProjection_repr]
      exact if_pos hβ
    · rw [F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ β i hd,
        F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w x β i hd]
  · rw [if_neg hβ, map_zero, Finsupp.zero_apply]
    by_cases hd : Finsupp.weight w β = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(β, i), hd⟩,
        basisCoordinateProjection_repr]
      exact if_neg hβ
    · exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ β i hd

theorem symbolPointwiseSubalgebra_blockInvariant (U : LieSubalgebra ℚ F.AssociatedGraded) :
    BasisBlockInvariant (F.polynomialSymbolBasis b ω hlayers w) (fun z => z.val.1)
      (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule := by
  classical
  intro α x hx
  apply (F.mem_symbolPointwiseSubalgebra_iff b ω hlayers w U _).mpr
  intro β
  rw [F.gradedSymbolPolynomial_block_coefficient]
  split_ifs
  · exact (F.mem_symbolPointwiseSubalgebra_iff b ω hlayers w U x).mp hx β
  · exact U.zero_mem

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem symbolPointwiseSubalgebra_eq_ker (U : LieSubalgebra ℚ F.AssociatedGraded) :
    (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule =
      LinearMap.ker (F.symbolSubalgebraQuotientMap b ω hlayers w U) := by
  ext x
  change x ∈ F.symbolPointwiseSubalgebra b ω hlayers w U ↔
    F.symbolSubalgebraQuotientMap b ω hlayers w U x = 0
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  constructor
  · intro hx
    apply coefficients.injective
    ext α
    change coefficients (VectorPolynomial.map U.toSubmodule.mkQ
      (F.gradedSymbolPolynomial b ω hlayers w x)) α = _
    rw [coefficients_map, map_zero, Finsupp.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero U.toSubmodule).mpr (hx α)
  · intro hx α
    have hc := congrArg (fun p => coefficients p α) hx
    change coefficients (VectorPolynomial.map U.toSubmodule.mkQ
      (F.gradedSymbolPolynomial b ω hlayers w x)) α = _ at hc
    rw [coefficients_map, map_zero, Finsupp.zero_apply] at hc
    exact (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp hc

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedMonomialBasis_bracket_support (u v z : AdaptedBasisIndex w ω)
    (h : ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr
      ⁅(F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ u,
        (F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ v⁆ z ≠ 0) :
    u.val.1 + v.val.1 = z.val.1 := by
  classical
  by_contra hn
  apply h
  rw [realLieBasis_structure]
  change (((F.adaptedMonomialBasis b ω hlayers w).repr
    ⁅F.adaptedMonomialBasis b ω hlayers w u,
      F.adaptedMonomialBasis b ω hlayers w v⁆ z : ℚ) : ℝ) = 0
  simp only [F.adaptedMonomialBasis_bracket, hn, ite_false, Rat.cast_zero]

noncomputable def scaledRealAdaptedMonomialBasis (T : σ → ℝ) (hT : ∀ i, 0 < T i) :
    Basis (AdaptedBasisIndex w ω) ℝ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
  inverseScaledBasis ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ)
    (fun z => monomialScale T z.val.1) (fun z => monomialScale_pos T hT z.val.1)

theorem scaledRealAdaptedMonomialBasis_repr (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (z : AdaptedBasisIndex w ω) :
    (F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT).repr x z =
      monomialScale T z.val.1 *
        ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr x z :=
  inverseScaledBasis_repr _ _ _ _ _

theorem scaledRealAdaptedMonomialBasis_structure (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (u v z : AdaptedBasisIndex w ω) :
    (F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT).repr
      ⁅F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT u,
        F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT v⁆ z =
      (lieStructureConstants (F.adaptedMonomialBasis b ω hlayers w) u v z : ℝ) := by
  apply Eq.trans (inverseScaledBasis_bracket _ _ _ ?_ u v z)
  · exact realLieBasis_structure _ u v z
  · intro i j k h
    have he := F.realAdaptedMonomialBasis_bracket_support b ω hlayers w i j k h
    rw [← he, monomialScale_add]

theorem scaledRealAdaptedMonomialBasis_bound_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (z : AdaptedBasisIndex w ω) (M : ℝ) :
    |(F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT).repr x z| ≤ M ↔
      |((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr x z| ≤
        M / monomialScale T z.val.1 := by
  rw [F.scaledRealAdaptedMonomialBasis_repr, abs_mul,
    abs_of_pos (monomialScale_pos T hT z.val.1), le_div_iff₀ (monomialScale_pos T hT z.val.1)]
  rw [mul_comm]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realAdaptedPolynomialGroupHom_coordinate (g : F.RealAdaptedPolynomialGroup w)
    (z : AdaptedBasisIndex w ω) :
    (b.baseChange ℝ).repr (coefficients
      ((F.realAdaptedPolynomialGroupHom w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.val.1) z.val.2 =
      ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr g.coord z :=
  F.realAdaptedPolynomialTensor_coordinates w b ω hlayers g.coord z

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScaledPolynomialDualBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem polynomial_factor_middle_constant
    (g e p r : (F.adaptedPolynomialFiltration w).Group) (h : e * p * r = g)
    (he : coefficients (e.coord : VectorPolynomial σ ℚ L) 0 = 0)
    (hr : coefficients (r.coord : VectorPolynomial σ ℚ L) 0 = 0) :
    coefficients (p.coord : VectorPolynomial σ ℚ L) 0 =
      coefficients (g.coord : VectorPolynomial σ ℚ L) 0 := by
  have he' : F.adaptedPolynomialConstantHom w e = 1 := by
    apply NilpotentLieBCHGroup.ext
    rw [F.adaptedPolynomialConstantHom_coord, NilpotentLieBCHGroup.coord_one, he]
  have hr' : F.adaptedPolynomialConstantHom w r = 1 := by
    apply NilpotentLieBCHGroup.ext
    rw [F.adaptedPolynomialConstantHom_coord, NilpotentLieBCHGroup.coord_one, hr]
  have h' := congrArg (F.adaptedPolynomialConstantHom w) h
  rw [map_mul, map_mul, he', hr', one_mul, mul_one] at h'
  have hc := congrArg NilpotentLieBCHGroup.coord h'
  simpa only [F.adaptedPolynomialConstantHom_coord] using hc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialRationalGrid_groupHom_iff (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (l : ℕ) (g : F.RealAdaptedPolynomialGroup w) :
    F.PolynomialRationalGrid b w l (F.realAdaptedPolynomialGroupHom w g) ↔
      (fun z : AdaptedBasisIndex w ω =>
        ((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr g.coord z) ∈ realDenominatorGrid l := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun z => a z.val, ?_⟩
    funext z
    have hz := congrFun ha z.val
    change (a z.val : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
      (coefficients ((F.realAdaptedPolynomialGroupHom w g).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.val.1) z.val.2 at hz
    rw [F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g z] at hz
    exact hz
  · rintro ⟨a, ha⟩
    refine ⟨fun z => if h : Finsupp.weight w z.1 ≤ ω z.2 then a ⟨z, h⟩ else 0, ?_⟩
    funext z
    change ((if h : Finsupp.weight w z.1 ≤ ω z.2 then a ⟨z, h⟩ else 0 : ℤ) : ℝ) =
      (l : ℝ) * (b.baseChange ℝ).repr (coefficients
        ((F.realAdaptedPolynomialGroupHom w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
    by_cases h : Finsupp.weight w z.1 ≤ ω z.2
    · rw [dif_pos h, F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g ⟨z, h⟩]
      exact congrFun ha ⟨z, h⟩
    · have hz := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
        ((F.realAdaptedPolynomialGroupHom w g).coord.property z.1) z.2 h
      rw [dif_neg h, Int.cast_zero, hz, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialSlowBound_groupHom_iff (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealAdaptedPolynomialGroup w) :
    F.PolynomialSlowBound b w T M (F.realAdaptedPolynomialGroupHom w g) ↔
      ∀ z : AdaptedBasisIndex w ω,
        |((F.adaptedMonomialBasis b ω hlayers w).baseChange ℝ).repr g.coord z| ≤
          M / monomialScale T z.val.1 := by
  constructor
  · intro hg z
    rw [← F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g z]
    exact hg z.val.1 z.val.2
  · intro hg α i
    by_cases h : Finsupp.weight w α ≤ ω i
    · rw [F.realAdaptedPolynomialGroupHom_coordinate w b ω hlayers g ⟨(α, i), h⟩]
      exact hg ⟨(α, i), h⟩
    · have hz := (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
        ((F.realAdaptedPolynomialGroupHom w g).coord.property α) i h
      rw [hz, abs_zero]
      exact div_nonneg hM (monomialScale_pos T hT α).le

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem realAdapted_factor_middle_constant
    (g a b c : F.RealAdaptedPolynomialGroup w) (h : a * b * c = g)
    (ha : coefficients (F.realAdaptedPolynomialMap w a.coord) 0 = 0)
    (hc : coefficients (F.realAdaptedPolynomialMap w c.coord) 0 = 0) :
    coefficients (F.realAdaptedPolynomialMap w b.coord) 0 =
      coefficients (F.realAdaptedPolynomialMap w g.coord) 0 := by
  have hp : F.realAdaptedPolynomialGroupHom w a * F.realAdaptedPolynomialGroupHom w b *
      F.realAdaptedPolynomialGroupHom w c = F.realAdaptedPolynomialGroupHom w g := by
    rw [← map_mul, ← map_mul, h]
  exact F.realification.polynomial_factor_middle_constant w
    (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialGroupHom w a)
    (F.realAdaptedPolynomialGroupHom w b) (F.realAdaptedPolynomialGroupHom w c) hp ha hc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem polynomialSlowBound_linear (b : Basis ι ℚ L)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (a : σ → ℝ ⊗[ℚ] L) (ha : ∀ i j, |(b.baseChange ℝ).repr (a i) j| ≤ M / T i) :
    F.PolynomialSlowBound b (fun _ => 1) T M (F.realification.linearPolynomialGroup a) := by
  classical
  intro α j
  rw [F.realification.linearPolynomialGroup_log]
  by_cases h : ∃ i, Finsupp.single i 1 = α
  · obtain ⟨i, rfl⟩ := h
    rw [coefficients_linearPolynomial_single]
    simpa [monomialScale] using ha i j
  · rw [coefficients_linearPolynomial_of_ne a α (by simpa only [not_exists] using h),
      map_zero, Finsupp.zero_apply, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem polynomialRationalGrid_linear (b : Basis ι ℚ L) (m : ℕ) (a : σ → ℝ ⊗[ℚ] L)
    (ha : (fun z : σ × ι => (b.baseChange ℝ).repr (a z.1) z.2) ∈ realDenominatorGrid m) :
    F.PolynomialRationalGrid b (fun _ => 1) m (F.realification.linearPolynomialGroup a) := by
  classical
  obtain ⟨n, hn⟩ := ha
  refine ⟨fun z => if h : ∃ i, Finsupp.single i 1 = z.1 then n (h.choose, z.2) else 0, ?_⟩
  funext z
  change ((if h : ∃ i, Finsupp.single i 1 = z.1 then n (h.choose, z.2) else 0 : ℤ) : ℝ) =
    (m : ℝ) * (b.baseChange ℝ).repr
      (coefficients ((F.realification.linearPolynomialGroup a).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  rw [F.realification.linearPolynomialGroup_log]
  by_cases h : ∃ i, Finsupp.single i 1 = z.1
  · rw [dif_pos h]
    have hc := coefficients_linearPolynomial_single (R := ℚ) a h.choose
    rw [h.choose_spec] at hc
    rw [hc]
    exact congrFun hn (h.choose, z.2)
  · rw [dif_neg h, Int.cast_zero,
      coefficients_linearPolynomial_of_ne a z.1 (by simpa only [not_exists] using h),
      map_zero, Finsupp.zero_apply, mul_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem basisGradeProjection_other {R L ι : Type*} [Field R] [AddCommGroup L] [Module R L]
    (b : Basis ι R L) (w : ι → ℕ) {i j : ℕ} (hij : i ≠ j) (x : L) :
    basisGradeProjection b w i (basisGradeProjection b w j x) = 0 := by
  apply b.repr.injective
  apply Finsupp.ext
  intro k
  simp only [basisGradeProjection_repr, map_zero, Finsupp.zero_apply]
  by_cases hi : w k = i
  · rw [if_pos hi, if_neg (fun hj => hij (hi.symm.trans hj))]
  · rw [if_neg hi]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix BigOperators

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]
  (b : Basis ι ℚ V) (e : Basis κ ℚ V)

theorem real_basis_coordinates_grid (l : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (fun j => (b.baseChange ℝ).repr x j) ∈ realDenominatorGrid l) :
    (fun i => (e.baseChange ℝ).repr x i) ∈
      realDenominatorGrid (matrixDenominator (fun i j => e.repr (b j) i) * l) := by
  rw [real_basis_coordinates_transfer b e x]
  exact real_matrix_denominator_grid (fun i j => e.repr (b j) i) l _ hx

theorem real_basis_transfer_denominator {H : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (hentries : ∀ i j, RationalHeightLE (e.repr (b j) i) H) :
    (matrixDenominator (fun i j => e.repr (b j) i) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  apply matrixDenominator_le_exp_power (fun i j => e.repr (b j) i) hp 1 hκ hι
  intro i j
  exact (show ((e.repr (b j) i).den : ℝ) ≤ H by exact_mod_cast (hentries i j).2).trans
    (hHp.trans (Real.exp_le_exp.mpr (by simp)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections
namespace OAI

section

namespace Erdos3

theorem realDenominatorGrid_sub {ι : Type*} (l : ℕ) (x y : ι → ℝ)
    (hx : x ∈ realDenominatorGrid l) (hy : y ∈ realDenominatorGrid l) :
    x - y ∈ realDenominatorGrid l := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a - b, ?_⟩
  funext i
  change ((a i - b i : ℤ) : ℝ) = (l : ℝ) * (x i - y i)
  rw [Int.cast_sub, mul_sub]
  exact congrArg₂ (· - ·) (congrFun ha i) (congrFun hb i)

theorem realDenominatorGrid_sub_product {ι : Type*} (l m : ℕ) (x y : ι → ℝ)
    (hx : x ∈ realDenominatorGrid l) (hy : y ∈ realDenominatorGrid m) :
    x - y ∈ realDenominatorGrid (l * m) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨fun i => (m : ℤ) * a i - (l : ℤ) * b i, ?_⟩
  funext i
  change (((m : ℤ) * a i - (l : ℤ) * b i : ℤ) : ℝ) =
    (l * m : ℕ) * (x i - y i)
  have h1 : (a i : ℝ) = (l : ℝ) * x i := congrFun ha i
  have h2 : (b i : ℝ) = (m : ℝ) * y i := congrFun hb i
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, h1, h2]
  ring

theorem realDenominatorGrid_linear_combination {ι κ : Type*} [Fintype κ]
    (l m : ℕ) (c : κ → ℝ) (v : κ → ι → ℝ)
    (hc : c ∈ realDenominatorGrid l) (hv : ∀ k, v k ∈ realDenominatorGrid m) :
    (∑ k, c k • v k) ∈ realDenominatorGrid (m * l) := by
  classical
  obtain ⟨a, ha⟩ := hc
  choose b hb using hv
  refine ⟨fun i => ∑ k, a k * b k i, ?_⟩
  funext i
  change ((∑ k, a k * b k i : ℤ) : ℝ) = (m * l : ℕ) * (∑ k, c k • v k) i
  simp only [Int.cast_sum, Int.cast_mul, Nat.cast_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h1 : (a k : ℝ) = (l : ℝ) * c k := congrFun ha k
  have h2 : (b k i : ℝ) = (m : ℝ) * v k i := congrFun (hb k) i
  rw [h1, h2]
  ring

theorem linear_lift_grid_of_coefficients {ι κ K : Type*} [Fintype κ]
    [AddCommGroup K] [Module ℝ K]
    (R : K →ₗ[ℝ] (ι → ℝ)) (v : κ → K) (c : κ → ℝ) (l m : ℕ)
    (hc : c ∈ realDenominatorGrid l) (hR : ∀ k, R (v k) ∈ realDenominatorGrid m) :
    R (∑ k, c k • v k) ∈ realDenominatorGrid (m * l) := by
  simp only [map_sum, map_smul]
  exact realDenominatorGrid_linear_combination l m c (fun k => R (v k)) hc hR

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

theorem exists_controlled_kernel_split {ι κ ν τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (U K : Submodule ℝ (ι → ℝ)) (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K)
    (b : ν → K) (hb : ∀ j, (b j).val = (B.map (Rat.castHom ℝ)).col j)
    (R : K →ₗ[ℝ] (τ → ℝ)) (n : ℕ) (hR : ∀ j, R (b j) ∈ realDenominatorGrid n)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ split : (ι → ℝ) →ₗ[ℝ] K,
        (∀ x, x ∈ U ⊔ K → x - (split x).val ∈ U) ∧
        (∀ x, ‖split x‖ ≤ Real.exp ((p + 2) ^ 19) * ‖x‖) ∧
        ∀ x, x ∈ realDenominatorGrid l → R (split x) ∈ realDenominatorGrid (n * m) := by
  classical
  obtain ⟨m, hm, hmp, u, v, hdecomp, hnorm, hgrid⟩ :=
    exists_controlled_sum_coordinates A B hH hl hA hB hp hι hcols hHp hlp
  have hν : (Fintype.card ν : ℝ) ≤ p := by
    have hsum : (Fintype.card κ : ℝ) + Fintype.card ν ≤ p := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hcols
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card κ)]
  let C : (ν → ℝ) →ₗ[ℝ] K := {
    toFun := fun c => ∑ j, c j • b j
    map_add' := by intros; simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hC (c : ν → ℝ) : (C c).val = B.map (Rat.castHom ℝ) *ᵥ c := by
    change K.subtype (∑ j, c j • b j) = _
    rw [map_sum]
    simp only [map_smul]
    change (∑ j, c j • (b j).val) = _
    simp only [hb]
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨m, hm, hmp, C.comp v, ?_, ?_, ?_⟩
  · intro x hx
    have hd := hdecomp x (by simpa only [hAspan, hBspan] using hx)
    have hu : A.map (Rat.castHom ℝ) *ᵥ u x ∈ U := by
      rw [← hAspan]
      exact (real_column_span_mem_iff A _).mpr ⟨u x, rfl⟩
    change x - (C (v x)).val ∈ U
    have he : x - B.map (Rat.castHom ℝ) *ᵥ v x = A.map (Rat.castHom ℝ) *ᵥ u x :=
      (eq_sub_iff_add_eq.mpr hd).symm
    rw [hC, he]
    exact hu
  · intro x
    change ‖(C (v x)).val‖ ≤ _
    rw [hC]
    have hmat := norm_matrix_mulVec_le (B.map (Rat.castHom ℝ)) (H : ℝ≥0)
      (fun i j => (hB i j).abs_real_le) (v x)
    calc
      _ ≤ (((Fintype.card ν : ℝ) + 1) * (H + 1)) * ‖v x‖ := hmat
      _ ≤ (((Fintype.card ν : ℝ) + 1) * (H + 1)) * (Real.exp ((p + 2) ^ 18) * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hnorm x).2 (by positivity)
      _ = (((Fintype.card ν : ℝ) + 1) * (H + 1) * Real.exp ((p + 2) ^ 18)) * ‖x‖ :=
        (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (kernel_split_factor_le_exp (Fintype.card ν) H hp hν hHp) (norm_nonneg x)
  · intro x hx
    exact linear_lift_grid_of_coefficients R b (v x) m n (hgrid x hx).2 hR

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FilteredSymbolMapCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem filteredPolynomialSymbolMap_basis_repr [DecidableEq σ]
    (a : SymbolBasisIndex w ω) (b : SymbolBasisIndex w ν) :
    (G.polynomialSymbolBasis f ν hG w).repr
      (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis e ω hF w a)) b =
      if a.val.1 = b.val.1 then f.repr (φ (e a.val.2)) b.val.2 else 0 := by
  rw [F.polynomialSymbolBasis_apply, F.filteredPolynomialSymbolMap_symbol,
    G.polynomialSymbolBasis_repr_map, F.filteredPolynomialMap_coefficient,
    F.adaptedMonomialBasis_coe, coefficients_monomial]
  by_cases hab : a.val.1 = b.val.1
  · simp only [hab, Finsupp.single_eq_same, ite_true]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hab), map_zero, map_zero, Finsupp.zero_apply,
      if_neg hab]

theorem filteredPolynomialSymbolMap_monomial_blocks
    (a : SymbolBasisIndex w ω) (b : SymbolBasisIndex w ν) (hab : b.val.1 ≠ a.val.1) :
    (G.polynomialSymbolBasis f ν hG w).repr
      (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis e ω hF w a)) b = 0 := by
  classical
  rw [F.filteredPolynomialSymbolMap_basis_repr G e ω hF f ν hG φ hφ w a b,
    if_neg (Ne.symm hab)]

theorem filteredPolynomialSymbolMap_basis_height {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (a : SymbolBasisIndex w ω) (b : SymbolBasisIndex w ν) :
    RationalHeightLE ((G.polynomialSymbolBasis f ν hG w).repr
      (F.filteredPolynomialSymbolMap G φ hφ w (F.polynomialSymbolBasis e ω hF w a)) b) H := by
  classical
  rw [F.filteredPolynomialSymbolMap_basis_repr G e ω hF f ν hG φ hφ w a b]
  split_ifs
  · exact hentries b.val.2 a.val.2
  · exact rationalHeightLE_zero hH

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix NNReal

variable {ι κ δ V W : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W)
  (D : Matrix κ ι ℚ) (hD : LinearMap.toMatrix e f q = D.map (Rat.castHom ℝ))

include hD

theorem rational_coordinate_map_grid (l : ℕ) (x : V)
    (hx : e.equivFun x ∈ realDenominatorGrid l) :
    f.equivFun (q x) ∈ realDenominatorGrid (matrixDenominator D * l) := by
  rw [rational_coordinate_map e f q D hD]
  exact real_matrix_denominator_grid D l _ hx

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ δ V : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V] (e : Basis ι ℝ V) (S : Matrix ι κ ℚ)

theorem rationalCoordinateSection_grid (l : ℕ) (y : κ → ℝ)
    (hy : y ∈ realDenominatorGrid l) :
    e.equivFun (rationalCoordinateSection e S y) ∈
      realDenominatorGrid (matrixDenominator S * l) := by
  rw [rationalCoordinateSection_coordinates]
  exact real_matrix_denominator_grid S l y hy

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem polynomialSlowBound_symbol (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) :
    F.SymbolSlowBound b ω hlayers w T M (F.realPolynomialSymbolHom b ω hlayers w g) := by
  intro z
  change |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
    (F.realSymbolOfPolynomial b ω hlayers w g.coord) z| ≤ _
  rw [F.realSymbolOfPolynomial_coordinate]
  exact hg z.val.1 z.val.2

theorem polynomialRationalGrid_symbol (m : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w m g) :
    F.SymbolRationalGrid b ω hlayers w m (F.realPolynomialSymbolHom b ω hlayers w g) := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => a z.val, ?_⟩
  funext z
  change (a z.val : ℝ) = (m : ℝ) *
    ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
      (F.realSymbolOfPolynomial b ω hlayers w g.coord) z
  rw [F.realSymbolOfPolynomial_coordinate]
  exact congrFun ha z.val

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepDropTerminalContainment
namespace OAI

section

namespace Erdos3

open Module

variable {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]

noncomputable def stepDropSubmodule (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L) : Submodule R L :=
  U.toSubmodule ⊓ (K.comap (basisGradeProjection b w 1) ⊓
    ((stepDropBracketKernel K V).comap (basisGradeProjection b w 1) ⊓
      V.comap (LinearMap.id - basisGradeProjection b w 1)))

theorem mem_stepDropSubmodule (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L) (x : L) :
    x ∈ stepDropSubmodule b w U V K ↔
      x ∈ U ∧ basisGradeProjection b w 1 x ∈ K ∧
      (∀ k ∈ K, ⁅basisGradeProjection b w 1 x, k⁆ ∈ V) ∧
      x - basisGradeProjection b w 1 x ∈ V := Iff.rfl

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {R L μ : Type*} [Field R] [AddCommGroup L] [Module R L]

noncomputable def homogeneousIntersection (b : Basis μ R L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule R L) : Submodule R L :=
  U ⊓ (V ⊓ LinearMap.ker (basisGradeProjection b w j - LinearMap.id))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintChartBasis
namespace OAI

section

namespace Erdos3

theorem euclideanDerivative_rational_lift_matrix_data
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let k := Module.finrank ℝ V
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      ∃ b : Module.Basis (Fin k) ℤ L, ∃ B : Matrix (Fin m) (Fin k) ℝ,
        ∃ p : Fin k → Fin a,
          (∀ j, B.col j ∈ realDenominatorGrid l) ∧
          (∀ j, (b j).val.val.val = euclideanVerticalMap scale hs0 A (B.col j)) ∧
          (B.submatrix (Fin.castLE ha ∘ p) id).det ≠ 0 ∧
          ∃ D : ℕ, 0 < D ∧ D ≤ Nat.ceil (C * (l : ℝ) ^ k) ∧
            ∃ Q : Matrix (Fin m) (Fin k) ℚ,
              (∀ j, Q.col j ∈ denominatorGrid D) ∧
              Q.map (Rat.castHom ℝ) = B * (B.submatrix (Fin.castLE ha ∘ p) id)⁻¹ ∧
              Q.submatrix (Fin.castLE ha ∘ p) id = 1 ∧
              (∀ i j, RationalHeightLE (Q (Fin.castLE ha i) j)
                (Nat.ceil (C * (l : ℝ) ^ k))) := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  dsimp only
  intro hupper
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, _, hgrid, hrep, p, _, hdet⟩ := euclideanDerivative_horizontal_basis_data
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hfar hlarge hupper
  refine ⟨b, B, p, hgrid, hrep, hdet, ?_⟩
  apply exists_partially_bounded_grid_normalization B l hl hgrid (Fin.castLE ha) p hdet C
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let e : Fin a → σ ⊕ Fin m := fun i => Sum.inr (Fin.castLE ha i)
  have he : Function.Injective e := by
    intro i j hij
    have h : Fin.castLE ha i = Fin.castLE ha j := Sum.inr.inj hij
    exact Fin.ext (congrArg (fun u : Fin m => u.val) h)
  let H := B.submatrix (Fin.castLE ha) id
  have hH (i j) : H i j = f (b j).val (e i) := by
    change B (Fin.castLE ha i) j = (b j).val.val.val (Sum.inr (Fin.castLE ha i))
    rw [hrep]
    exact (euclideanVerticalMap_horizontal scale hs0 hscalehor A hA hblock (B.col j)
      (Fin.castLE ha i) i.isLt).symm
  intro q
  exact (lattice_projection_all_minors_bound L b f e he H hH q).trans hupper

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeHorizontalLifts
namespace OAI

section

namespace Erdos3

structure RationalHorizontalLift {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m a : ℕ} (k : ℕ) (P : E →ₗ[ℝ] (Fin a → ℝ)) (ha : a ≤ m)
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (scale : Fin m → ℝ)
    (normBound : ℝ) (heightBound : ℕ) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_le : denominator ≤ heightBound
  basisMatrix : Matrix (Fin a) (Fin k) ℚ
  basis_height : ∀ i j, RationalHeightLE (basisMatrix i j) heightBound
  independent_rat : LinearIndependent ℚ basisMatrix.col
  independent_real : LinearIndependent ℝ (basisMatrix.map (Rat.castHom ℝ)).col
  span_eq : LinearMap.range P =
    Submodule.span ℝ (Set.range (basisMatrix.map (Rat.castHom ℝ)).col)
  rationalLift : LinearMap.range P →ₗ[ℝ] (Fin m → ℝ)
  geometricLift : LinearMap.range P →ₗ[ℝ] (Fin m → ℝ)
  factorization : geometricLift = A.toLinearMap.comp rationalLift
  rational_horizontal : ∀ x i, rationalLift x (Fin.castLE ha i) = x.val i
  geometric_horizontal : ∀ x i, geometricLift x (Fin.castLE ha i) = x.val i
  norm_scaled : ∀ x,
    ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * geometricLift x j)‖ ≤
      normBound * ‖x‖
  rational_on_basis : ∀ j, ∃ x : LinearMap.range P,
    x.val = (basisMatrix.map (Rat.castHom ℝ)).col j ∧
    rationalLift x ∈ realDenominatorGrid denominator

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_norm_bound
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      ∀ v : V, ‖v‖ ≤ (Fintype.card (σ ⊕ Fin m) : ℝ) * k *
        (C * (l : ℝ) ^ k) * ‖P v‖ := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  change ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
    ∀ v : V, ‖v‖ ≤ (Fintype.card (σ ⊕ Fin m) : ℝ) * k *
      (C * (l : ℝ) ^ k) * ‖P v‖
  intro hupper v
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, _, hgrid, hrep, p, _, hdet⟩ := euclideanDerivative_horizontal_basis_data
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hfar hlarge hupper
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let e : Fin a → σ ⊕ Fin m := fun i => Sum.inr (Fin.castLE ha i)
  let H := B.submatrix (Fin.castLE ha) id
  have hH (i j) : H i j = f (b j).val (e i) := by
    change B (Fin.castLE ha i) j = (b j).val.val.val (Sum.inr (Fin.castLE ha i))
    rw [hrep]
    exact (euclideanVerticalMap_horizontal scale hs0 hscalehor A hA hblock (B.col j)
      (Fin.castLE ha i) i.isLt).symm
  have hHgrid (j) : H.col j ∈ realDenominatorGrid l := by
    obtain ⟨z, hz⟩ := hgrid j
    refine ⟨fun i => z (Fin.castLE ha i), ?_⟩
    funext i
    exact congrFun hz (Fin.castLE ha i)
  have hdetH : (H.submatrix p id).det ≠ 0 := hdet
  have hn := lattice_norm_le_projection_of_grid_minor
    (ι := σ ⊕ Fin m) (κ := Fin a) (E := V) (k := k)
    L b f e l hl H hH hHgrid p hdetH C hupper v
  have heP : (fun i => f v (e i)) = P v := rfl
  rw [heP] at hn
  exact hn

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledKernelSplitTransport
namespace OAI

section

namespace Erdos3

theorem exists_controlled_kernel_split_equiv {H ι κ ν τ : Type*}
    [AddCommGroup H] [Module ℝ H] [Fintype ι] [Fintype κ] [Fintype ν]
    (e : H ≃ₗ[ℝ] (ι → ℝ)) (U K : Submodule ℝ H)
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U.map e.toLinearMap)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K.map e.toLinearMap)
    (b : ν → K) (hb : ∀ j, e (b j).val = (B.map (Rat.castHom ℝ)).col j)
    (R : K →ₗ[ℝ] (τ → ℝ)) (n : ℕ) (hR : ∀ j, R (b j) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) J) (hB : ∀ i j, RationalHeightLE (B i j) J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ split : H →ₗ[ℝ] K,
        (∀ x, x ∈ U ⊔ K → x - (split x).val ∈ U) ∧
        (∀ x, ‖e (split x).val‖ ≤ Real.exp ((p + 2) ^ 19) * ‖e x‖) ∧
        ∀ x, e x ∈ realDenominatorGrid l → R (split x) ∈ realDenominatorGrid (n * m) := by
  let eK : K ≃ₗ[ℝ] K.map e.toLinearMap := e.submoduleMap K
  let R' := R.comp eK.symm.toLinearMap
  have hb' : ∀ j, (eK (b j)).val = (B.map (Rat.castHom ℝ)).col j := hb
  have hR' : ∀ j, R' (eK (b j)) ∈ realDenominatorGrid n := by
    intro j
    simpa only [R', LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply] using hR j
  obtain ⟨m, hm, hmp, split', hsplit', hnorm, hgrid⟩ :=
    exists_controlled_kernel_split (U.map e.toLinearMap) (K.map e.toLinearMap)
      A B hAspan hBspan (fun j => eK (b j)) hb' R' n hR' hJ hl hA hB hp hι hcols hJp hlp
  let split : H →ₗ[ℝ] K := eK.symm.toLinearMap.comp (split'.comp e.toLinearMap)
  have hsplit (x : H) : e (split x).val = (split' (e x)).val :=
    congrArg Subtype.val (eK.apply_symm_apply (split' (e x)))
  refine ⟨m, hm, hmp, split, ?_, ?_, ?_⟩
  · intro x hx
    have hex : e x ∈ U.map e.toLinearMap ⊔ K.map e.toLinearMap := by
      rw [← Submodule.map_sup]
      exact ⟨x, hx, rfl⟩
    have hmem : e (x - (split x).val) ∈ U.map e.toLinearMap := by
      rw [map_sub, hsplit]
      exact hsplit' (e x) hex
    simpa only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hmem
  · intro x
    rw [hsplit]
    exact hnorm (e x)
  · intro x hx
    exact hgrid (e x) hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalSeparationTransport
namespace OAI

section

namespace Erdos3

theorem horizontal_parts_separation_equiv {H ι κ ν σ : Type*}
    [AddCommGroup H] [Module ℝ H] [Fintype ι] [Fintype κ] [Fintype ν]
    (e : H ≃ₗ[ℝ] (ι → ℝ)) (U K : Submodule ℝ H)
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U.map e.toLinearMap)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K.map e.toLinearMap)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) J) (hB : ∀ i j, RationalHeightLE (B i j) J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) (i : σ)
    (y small rational : H) (k : K) (hsystem : y = small + rational + k.val)
    (hy : y ∈ U) (hs : ‖e small‖ ≤ Real.exp p / T i)
    (hr : e rational ∈ realDenominatorGrid l) :
    small ∈ U ⊔ K ∧ rational ∈ U ⊔ K := by
  classical
  let M := Matrix.fromCols A B
  have hM : ∀ i j, RationalHeightLE (M i j) J := by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr j => exact hB i j
  have hspan : Submodule.span ℝ (Set.range (fun j i => (M i j : ℝ))) =
      U.map e.toLinearMap ⊔ K.map e.toLinearMap := by
    change Submodule.span ℝ (Set.range ((Matrix.fromCols A B).map (Rat.castHom ℝ)).col) = _
    rw [real_column_span_fromCols, hAspan, hBspan]
  have heq : e y = e small + e rational + e k.val := by rw [hsystem, map_add, map_add]
  have hs' : ‖e small‖ ≤ Real.exp p / monomialScale T (Finsupp.single i 1) := by
    simpa [monomialScale] using hs
  have hparts := horizontal_parts_separation (U.map e.toLinearMap) (K.map e.toLinearMap)
    M hspan hJ hl hM hp hι hcols hJp hlp T hT
    (show (Finsupp.single i 1 : σ →₀ ℕ) ≠ 0 by simp) (e y) (e small) (e rational) (e k.val)
    heq ⟨y, hy, rfl⟩ ⟨k.val, k.property, rfl⟩ hs' hr
  have hmem (x : H) (hx : e x ∈ U.map e.toLinearMap ⊔ K.map e.toLinearMap) : x ∈ U ⊔ K := by
    rw [← Submodule.map_sup, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] at hx
    exact hx
  exact ⟨hmem small hparts.1, hmem rational hparts.2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates
namespace OAI

section

namespace Erdos3

theorem realDenominatorGrid_single {ι : Type*} [DecidableEq ι] (l : ℕ) (i : ι) :
    Pi.single i (1 : ℝ) ∈ realDenominatorGrid l := by
  refine ⟨Pi.single i (l : ℤ), ?_⟩
  funext j
  change ((Pi.single i (l : ℤ) : ι → ℤ) j : ℝ) =
    (l : ℝ) * (Pi.single i (1 : ℝ) : ι → ℝ) j
  by_cases h : j = i <;> simp [h]

theorem extendInitialCoordinates_grid {a d : ℕ} (l : ℕ) (x : Fin a → ℝ)
    (hx : x ∈ realDenominatorGrid l) :
    (extendInitialCoordinates x : Fin d → ℝ) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => if hi : i.val < a then z ⟨i.val, hi⟩ else 0, ?_⟩
  funext i
  change ((if hi : i.val < a then z ⟨i.val, hi⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * (if hi : i.val < a then x ⟨i.val, hi⟩ else 0)
  by_cases hi : i.val < a
  · simpa only [hi, dite_true, Pi.smul_apply, smul_eq_mul] using congrFun hz ⟨i.val, hi⟩
  · simp only [hi, dite_false, Int.cast_zero, mul_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedSpanningPadding
namespace OAI

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L)

theorem exists_bounded_ambient_spanning (v : η → K)
    (hspan : Submodule.span ℚ (Set.range v) = ⊤) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a : L) i) H) :
    ∃ w : Fin (Fintype.card ι) → L,
      Submodule.span ℚ (Set.range w) = K.toSubmodule ∧
        ∀ a i, RationalHeightLE (e.repr (w a) i) H := by
  classical
  obtain ⟨b, hb⟩ := exists_bounded_lie_subalgebra_basis e K v hspan hv
  have hr := lie_subalgebra_finrank_le e K
  let w : Fin (Fintype.card ι) → L := fun a =>
    if ha : a.val < Module.finrank ℚ K then (b ⟨a.val, ha⟩ : L) else 0
  have hw (i : Fin (Module.finrank ℚ K)) :
      w ⟨i.val, lt_of_lt_of_le i.isLt hr⟩ = (b i : L) := by
    simp only [w, dif_pos i.isLt]
  refine ⟨w, ?_, ?_⟩
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨a, rfl⟩
      dsimp only [w]
      split_ifs with ha
      · exact (b ⟨a.val, ha⟩).property
      · exact K.zero_mem
    · have htop : (⊤ : Submodule ℚ K) ≤
          (Submodule.span ℚ (Set.range w)).comap K.incl.toLinearMap := by
        rw [← b.span_eq]
        apply Submodule.span_le.mpr
        rintro y ⟨i, rfl⟩
        change (b i : L) ∈ Submodule.span ℚ (Set.range w)
        rw [← hw i]
        exact Submodule.subset_span ⟨_, rfl⟩
      intro x hx
      exact htop (show (⟨x, hx⟩ : K) ∈ (⊤ : Submodule ℚ K) by trivial)
  · intro a i
    dsimp only [w]
    split_ifs with ha
    · exact hb ⟨a.val, ha⟩ i
    · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReindexGradedBasis
namespace OAI

section

namespace Erdos3

open Module

theorem basisGradeProjection_reindex {K V ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (ω : ι → ℕ) (e : ι ≃ κ) (j : ℕ) :
    basisGradeProjection (b.reindex e) (fun k => ω (e.symm k)) j = basisGradeProjection b ω j := by
  apply LinearMap.ext
  intro x
  apply (b.reindex e).repr.injective
  ext k
  simp only [basisGradeProjection_repr, Basis.repr_reindex_apply]

theorem basisGradedSubmodule_reindex_iff {K V ι κ : Type*} [Field K]
    [AddCommGroup V] [Module K V] (b : Basis ι K V) (ω : ι → ℕ) (e : ι ≃ κ)
    (U : Submodule K V) :
    BasisGradedSubmodule (b.reindex e) (fun k => ω (e.symm k)) U ↔ BasisGradedSubmodule b ω U := by
  simp only [BasisGradedSubmodule, basisGradeProjection_reindex]

end Erdos3

end

end OAI
end


