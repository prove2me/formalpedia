-- Prove2me | Definitions.Def_OAIE3v2B076
-- name    : OAIE3v2B076
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:18:39.015569+00:00
-- url     : https://prove2.me/theorems/de7d0a11-05b6-435d-8e28-ce878aedd485
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 77 of 311
-- statement:
--   Definitions bundle 77 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B041`, `OAIE3v2B047`, `OAIE3v2B048`, `OAIE3v2B049`, `OAIE3v2B050`, `OAIE3v2B051`, `OAIE3v2B052`, `OAIE3v2B053`, `OAIE3v2B054`, `OAIE3v2B055` of this split.
--
--   Modules: `Dynamics/CurrentLayerBudget.lean`, `Dynamics/FastCoefficientGeneratorBudget.lean`, `Dynamics/FormalGeometryBudget.lean`, `Dynamics/FormalStageBudget.lean`, `Dynamics/NativeHorizontalLiftBudget.lean`, `Dynamics/SquarefreeModelBudget.lean`, `Dynamics/UniformFormalInductionIteration.lean`, `Estimates/CubicAntisymmetricTransfer.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/DenseCorrelationPairs.lean`, `Estimates/DerivativeIndexBounds.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeBinaryAssignments.lean`, `Estimates/NativeSelectedCorrelators.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/NormalizedCommonFamily.lean`, `Estimates/PartiallyBoundedNormalization.lean`, `Estimates/PositiveCyclicCorrelation.lean`, `Estimates/RationalFormalStageGeometry.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/NativeTernaryCoordinate.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Lattices/DerivativeLatticeDivision.lean`, `Lattices/ScaledLatticeCovolume.lean`, `Linear/BasisGradedCoordinateBasis.lean`, `Linear/CommonRankCoefficientCorrections.lean`, `Linear/EuclideanDerivativeProjection.lean`, `Linear/QuotientProjectionCoordinates.lean`, `Linear/ScaledPairBasisHeight.lean`, `Linear/SortedBasisTriangular.lean`, `Nilpotent/AmbientBracketCorrectionPolynomials.lean`, `Nilpotent/BCHSubgroupGridExistence.lean`, `Nilpotent/BracketStepBudget.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`, `Sampling/DerivativeGridPoints.lean`, `Sampling/GridNormalizationDenominator.lean`, `Sampling/IntegralGridFunctional.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B040
import Definitions.Def_OAIE3v2B041
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049
import Definitions.Def_OAIE3v2B050
import Definitions.Def_OAIE3v2B051
import Definitions.Def_OAIE3v2B052
import Definitions.Def_OAIE3v2B053
import Definitions.Def_OAIE3v2B054
import Definitions.Def_OAIE3v2B055

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

section

namespace Erdos3
variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieFiltration
variable {L} {s : ℕ} (F : NilpotentLieFiltration L s)
include F

theorem subgroup_one : F.subgroup 1 = ⊤ := by
  apply top_unique
  intro a _
  change a.coord ∈ F.layer 1
  simp [F.one_eq_top]

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DerivativeGridPoints
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {σ κ : Type*} [Fintype κ]

theorem exists_bounded_derivativeGridPoint_family [Fintype σ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ) (l : ℕ)
    (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (R : ℝ)
    (hexists : ∀ h ∈ H, ∃ r : κ → ℝ, r ∈ realDenominatorGrid l ∧
      ‖derivativeGridPoint T scale Y M (h - h₀) r‖ ≤ R) :
    ∃ P : Finset ((σ → ℝ) × (κ → ℝ)), P.card = H.card ∧
      ∀ v ∈ P, v ∈ derivativeGridPoints T scale Y M l ∧ ‖v‖ ≤ R := by
  classical
  let r : (σ → ℤ) → κ → ℝ := fun h => if hh : h ∈ H then (hexists h hh).choose else 0
  have hr (h : σ → ℤ) (hh : h ∈ H) : r h ∈ realDenominatorGrid l ∧
      ‖derivativeGridPoint T scale Y M (h - h₀) (r h)‖ ≤ R := by
    simpa only [r, dif_pos hh] using (hexists h hh).choose_spec
  refine ⟨H.image (fun h => derivativeGridPoint T scale Y M (h - h₀) (r h)), ?_, ?_⟩
  · apply Finset.card_image_iff.mpr
    intro h _ k _ heq
    have hd := derivativeGridPoint_eq_imp_shift_eq T hT scale Y M (h - h₀) (k - h₀) (r h) (r k) heq
    simpa only [sub_add_cancel] using congrArg (fun z => z + h₀) hd
  · intro v hv
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨derivativeGridPoint_mem T scale Y M l (h - h₀) (r h) (hr h hh).1, (hr h hh).2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseCorrelationPairs
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_anchor_branch {I G : Type*} [Fintype I] [Fintype G] [Nonempty G]
    (anchor : I → G) (branch : I → Bool) {α : ℝ} (hα : 0 < α)
    (hsize : α * (Fintype.card G : ℝ) ^ 3 ≤ Fintype.card I) :
    ∃ (k : G) (b : Bool) (T : Finset I), T.Nonempty ∧
      α / 2 * (Fintype.card G : ℝ) ^ 2 ≤ (T.card : ℝ) ∧
      ∀ t ∈ T, anchor t = k ∧ branch t = b := by
  classical
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hb : Fintype.card (G × Bool) • (α / 2 * (Fintype.card G : ℝ) ^ 2) ≤
      (Fintype.card I : ℝ) := by
    calc
      _ = α * (Fintype.card G : ℝ) ^ 3 := by
        simp only [nsmul_eq_mul, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ ≤ _ := hsize
  obtain ⟨⟨k, b⟩, hkb⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card
    (fun i => (anchor i, branch i)) hb
  let T := Finset.univ.filter (fun i => (anchor i, branch i) = (k, b))
  have hTsize : α / 2 * (Fintype.card G : ℝ) ^ 2 ≤ (T.card : ℝ) := hkb
  have hTpos : (0 : ℝ) < T.card := lt_of_lt_of_le (by positivity) hTsize
  refine ⟨k, b, T, Finset.card_pos.mp (by exact_mod_cast hTpos), hTsize, ?_⟩
  intro t ht
  exact Prod.mk.inj (Finset.mem_filter.mp ht).2

theorem exists_dense_anchored_fibers {I G : Type*} [Fintype I] [Fintype G]
    [Nonempty G] [DecidableEq G] (a h k : I → G) (branch : I → Bool)
    (hinj : Function.Injective (fun i => (a i, h i, k i)))
    {α : ℝ} (hα : 0 < α) (hsize : α * (Fintype.card G : ℝ) ^ 3 ≤ Fintype.card I) :
    ∃ (anchor : G) (b : Bool) (T : Finset I) (A : Finset G), A.Nonempty ∧
      α / 4 * (Fintype.card G : ℝ) ≤ (A.card : ℝ) ∧
      (∀ t ∈ T, k t = anchor ∧ branch t = b) ∧
      Set.InjOn (fun i => (a i, h i)) (T : Set I) ∧
      ∀ x ∈ A, α / 4 * (Fintype.card G : ℝ) ≤ ((T.filter (fun i => a i = x)).card : ℝ) := by
  classical
  obtain ⟨anchor, b, T, _, hTsize, hT⟩ := exists_large_anchor_branch k branch hα hsize
  have hpair : Set.InjOn (fun i => (a i, h i)) (T : Set I) := by
    intro u hu v hv huv
    have hau : a u = a v := congrArg (fun z : G × G => z.1) huv
    have hhu : h u = h v := congrArg (fun z : G × G => z.2) huv
    apply hinj
    exact Prod.ext hau (Prod.ext hhu ((hT u hu).1.trans (hT v hv).1.symm))
  obtain ⟨A, hA, hAsize, hAfiber⟩ := exists_dense_first_fibers T a h hpair (by positivity) hTsize
  refine ⟨anchor, b, T, A, hA, ?_, hT, hpair, ?_⟩
  · convert hAsize using 1; ring
  · intro x hx
    convert hAfiber x hx using 1; ring

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

theorem norm_finiteCorrelation_mul_indicator (I : Finset H) (f u : H → ℂ) :
    ‖finiteCorrelation Finset.univ f (fun x => u x * finiteIndicator I x)‖ =
      ((I.card : ℝ) / Fintype.card H) * ‖finiteCorrelation I f u‖ := by
  rw [finiteCorrelation_mul_indicator, norm_mul, norm_div]
  simp only [Complex.norm_natCast]

theorem retained_restricted_correlation (I : Finset H) (f u : H → ℂ)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hf : ∀ x ∈ I, ‖f x‖ ≤ 1) (hu : ∀ x ∈ I, ‖u x‖ ≤ B)
    (hc : ρ ≤ ‖finiteCorrelation Finset.univ f (fun x => u x * finiteIndicator I x)‖) :
    I.Nonempty ∧ ρ ≤ ‖finiteCorrelation I f u‖ ∧
      ρ / B ≤ (I.card : ℝ) / Fintype.card H := by
  rw [norm_finiteCorrelation_mul_indicator] at hc
  have hI : I.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he] at hc
    simp only [Finset.card_empty, Nat.cast_zero, zero_div, zero_mul] at hc
    linarith
  have hv0 : 0 ≤ (I.card : ℝ) / Fintype.card H := by positivity
  have hv1 : (I.card : ℝ) / Fintype.card H ≤ 1 := by
    apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
    exact_mod_cast Finset.card_le_univ I
  have hb := norm_finiteCorrelation_le hI f u hf hu
  refine ⟨hI, hc.trans ?_, (div_le_iff₀ hB).mpr ?_⟩
  · exact (mul_le_mul_of_nonneg_right hv1 (norm_nonneg _)).trans_eq (one_mul _)
  · exact hc.trans (mul_le_mul_of_nonneg_left hb hv0)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

theorem mem_cyclicQuarter {N : ℕ} [NeZero N] (i : Fin 4) (x : ZMod N) :
    x ∈ cyclicQuarter N i ↔ quarterLower N i ≤ x.val ∧ x.val < quarterUpper N i :=
  mem_cyclicInterval_representatives _ _ (quarter_bounds N i).1 (quarter_bounds N i).2 x

theorem sum_cyclicQuarter_indicator {N : ℕ} [NeZero N] (x : ZMod N) :
    (∑ i : Fin 4, finiteIndicator (cyclicQuarter N i) x) = 1 := by
  have hx := x.val_lt
  simp only [finiteIndicator, mem_cyclicQuarter, Fin.sum_univ_succ, Fin.sum_univ_zero,
    quarterLower, quarterUpper, Fin.val_zero, Fin.val_succ, add_zero]
  split_ifs <;> norm_num at * <;> omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisCoordinateProjection_eq_iff (b : Basis ι K V) (S : Set ι) (x y : V) :
    basisCoordinateProjection b S x = basisCoordinateProjection b S y ↔
      x - y ∈ Submodule.span K (b '' Sᶜ) := by
  rw [← basisCoordinateProjection_eq_zero_iff, map_sub, sub_eq_zero]

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisBelowProjection_eq_iff (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x y : V) :
    basisBelowProjection b w j x = basisBelowProjection b w j y ↔
      x - y ∈ Submodule.span K (b '' {i | j ≤ w i}) := by
  simpa only [basisBelowProjection, Set.compl_ofPred, not_lt] using
    basisCoordinateProjection_eq_iff b {i | w i < j} x y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.IntegralGridFunctional
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem linearFunctional_coordinate_height {ι L : Type*} [Fintype ι]
    [AddCommGroup L] [Module ℚ L] (b : Basis ι ℚ L) (η : L →ₗ[ℚ] ℚ)
    {H K : ℕ} (hη : ∀ i, RationalHeightLE (η (b i)) H)
    (x : L) (hx : ∀ i, RationalHeightLE (b.repr x i) K) :
    RationalHeightLE (η x) ((Fintype.card ι + 1) * (K * H) ^ Fintype.card ι) := by
  classical
  have heq : η x = ∑ i, b.repr x i * η (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [heq]
  exact rationalHeightLE_sum _ (fun i => (hx i).mul (hη i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeHorizontalLiftBudget
namespace OAI

section

namespace Erdos3

theorem exists_extractedInitialParameter_budget (C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      separationBudget (extractedInitialParameter p) ≤ (p + D) ^ D ∧
      absorbedInitialParameter (extractedInitialParameter p) ≤ (p + D) ^ D ∧
      (absorbedInitialParameter (extractedInitialParameter p) + 2) ^ 2 ≤ (p + D) ^ D ∧
      (absorbedInitialParameter (extractedInitialParameter p) + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 3 * Polynomial.X + 3
  let A : Polynomial ℕ := 3 * Q + 1 + (Q + 2) ^ 36 + (Q + 2) ^ 19
  let S : Polynomial ℕ := (Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (S + A + (A + 2) ^ 2 + (A + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  have hq : 0 ≤ extractedInitialParameter p := hp.trans (extractedInitialParameter_controls hp).1
  have ha := absorbedInitialParameter_nonneg hq
  have hs := separationBudget_nonneg hq
  have h2 : 0 ≤ (absorbedInitialParameter (extractedInitialParameter p) + 2) ^ 2 := sq_nonneg _
  have hc : 0 ≤ (absorbedInitialParameter (extractedInitialParameter p) + C) ^ C := by positivity
  have hsum : separationBudget (extractedInitialParameter p) +
      absorbedInitialParameter (extractedInitialParameter p) +
      (absorbedInitialParameter (extractedInitialParameter p) + 2) ^ 2 +
      (absorbedInitialParameter (extractedInitialParameter p) + C) ^ C ≤ (p + D) ^ D := by
    simpa [Q, A, S, extractedInitialParameter, absorbedInitialParameter, separationBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem imageDefiningHeight_pos (d n H : ℕ) (hH : 1 ≤ H) :
    0 < imageDefiningHeight d n H := by
  have hHp : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
  have hK := rationalKernelHeight_pos n hH
  unfold imageDefiningHeight
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CurrentLayerBudget
namespace OAI

section

namespace Erdos3

theorem exists_current_layer_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      separationBudget (currentLayerConstructionBudget p) +
        separationBudget (currentLayerRemovalBudget p) + currentLayerRemovalBudget p ≤ (p + C) ^ C := by
  let T : Polynomial ℕ := 2 * Polynomial.X + 2
  let Q : Polynomial ℕ := 2 * (Polynomial.X + 2) ^ 3 + (T + 2) ^ 36 + (T + 2) ^ 18 + T + 5 * Polynomial.X + 10
  let B : Polynomial ℕ := ((T + 2) ^ 48 + (T + 2) ^ 24 + T + 1) +
    ((Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1) + Q
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, Q, T, separationBudget, currentLayerConstructionBudget, currentLayerRemovalBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastCoefficientGeneratorBudget
namespace OAI

section

namespace Erdos3

theorem fastCoefficientGeneratorHeight_pos (n m r H : ℕ) (hH : 1 ≤ H) :
    0 < fastCoefficientGeneratorHeight n m r H := by
  have hHp : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
  have hB : 1 ≤ (n + 1) * H ^ n := Nat.succ_le_of_lt (by positivity)
  have hK := rationalKernelHeight_pos r hB
  unfold fastCoefficientGeneratorHeight fastKernelGeneratorHeight
  positivity

theorem fastKernelGeneratorHeight_le_exp (n m r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (fastKernelGeneratorHeight n m r H : ℝ) ≤ Real.exp ((p + 2) ^ 38) := by
  have hp1 : p ≤ (p + 2) ^ 1 := le_power_budget hp (by decide)
  have hB : (((n + 1) * H ^ n : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    exact rational_sum_cost_le_exp n H hp 1 1
      (hH.trans (Real.exp_le_exp.mpr hp1)) (hn.trans hp1)
  have hK : (rationalKernelHeight r ((n + 1) * H ^ n) : ℝ) ≤
      Real.exp ((p + 2) ^ 35) := by
    have hk := rationalKernelHeight_le_budget r ((n + 1) * H ^ n)
      (by positivity : 0 ≤ (p + 2) ^ 3)
      (hr.trans (le_power_budget hp (by decide : 1 ≤ 3))) hB
    exact exponential_budget_comp hp (by positivity) 3 7 le_rfl hk
  have hH' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 35) :=
    hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 35)))
  have hprod : ((rationalKernelHeight r ((n + 1) * H ^ n) * H : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 36) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 35) * Real.exp ((p + 2) ^ 35) :=
        mul_le_mul hK hH' (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (2 * (p + 2) ^ 35) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          2 * (p + 2) ^ 35 ≤ (p + 2) * (p + 2) ^ 35 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = (p + 2) ^ 36 := by rw [pow_succ (p + 2) 35]; ring
  exact rational_sum_cost_le_exp m _ hp 36 1 hprod (hm.trans hp1)

theorem fastCoefficientGeneratorHeight_le_exp (n m r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (fastCoefficientGeneratorHeight n m r H : ℝ) ≤ Real.exp ((p + 2) ^ 40) :=
  rational_sum_cost_le_exp n _ hp 38 1
    (fastKernelGeneratorHeight_le_exp n m r H hp hn hm hr hH)
    (hn.trans (le_power_budget hp (by decide : 1 ≤ 1)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SortedBasisTriangular
namespace OAI

section

namespace Erdos3

open Module

theorem basis_reindex_grid {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (b : Basis ι ℝ E) (e : Equiv.Perm ι) (l : ℕ) (x : E)
    (hx : b.equivFun x ∈ realDenominatorGrid l) :
    (b.reindex e.symm).equivFun x ∈ realDenominatorGrid l := by
  rw [basis_reindex_equivFun]
  exact realDenominatorGrid_comp l (b.equivFun x) hx e

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AmbientBracketCorrectionPolynomials
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L μ ν : Type*} [LieRing L] [LieAlgebra ℚ L] {E : Submodule ℚ L}

theorem bracketSystemLift_norm_bound [Fintype μ] [Fintype ν]
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) {H : ℕ}
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H) (x : ν → ℝ) :
    ‖(b.baseChange ℝ).equivFun (bracketSystemLift e x)‖ ≤
      ((Fintype.card ν : ℝ) + 1) * (H + 1) * ‖x‖ := by
  rw [bracketSystemLift_coordinates]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (he i j).abs_real_le) x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

theorem subspaceQuotientMatrix_real_apply [Fintype ν]
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (x : ν → ℝ) :
    (fun i n => (subspaceQuotientMatrix e f i n : ℝ)) *ᵥ x =
      realQuotientCoordinateMap f (bracketSystemLift e x) := by
  classical
  have h : Matrix.mulVecLin (fun i n => (subspaceQuotientMatrix e f i n : ℝ)) =
      (realQuotientCoordinateMap f).comp (bracketSystemLift e) := by
    apply (Pi.basisFun ℝ ν).ext
    intro n
    change Matrix.of (fun i t => (subspaceQuotientMatrix e f i t : ℝ)) *ᵥ Pi.single n 1 =
      realQuotientCoordinateMap f (bracketSystemLift e (Pi.single n 1))
    rw [Matrix.mulVec_single_one, bracketSystemLift_single]
    funext i
    exact (realQuotientCoordinateMap_tmul_one f (e n : L) i).symm
  exact DFunLike.congr_fun h x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℝ W]
  (U : Submodule ℚ V)

theorem realQuotientEquiv_mk (x : ℝ ⊗[ℚ] V) :
    realQuotientEquiv U (U.mkQ.baseChange ℝ x) = (U.baseChange ℝ).mkQ x := by
  dsimp only [realQuotientEquiv, LinearEquiv.trans_apply]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

noncomputable def realTransportedQuotientEquiv (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) :
    (ℝ ⊗[ℚ] (V ⧸ U)) ≃ₗ[ℝ] (W ⧸ (U.baseChange ℝ).map E.toLinearMap) :=
  (realQuotientEquiv U).trans (Submodule.Quotient.equiv _ _ E rfl)

theorem realTransportedQuotientEquiv_mk (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (x : ℝ ⊗[ℚ] V) :
    realTransportedQuotientEquiv U E (U.mkQ.baseChange ℝ x) =
      ((U.baseChange ℝ).map E.toLinearMap).mkQ (E x) := by
  change Submodule.Quotient.equiv _ _ E rfl (realQuotientEquiv U (U.mkQ.baseChange ℝ x)) = _
  rw [realQuotientEquiv_mk]
  rfl

noncomputable def realTransportedQuotientBasis {κ : Type*}
    (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (b : Basis κ ℚ (V ⧸ U)) :
    Basis κ ℝ (W ⧸ (U.baseChange ℝ).map E.toLinearMap) :=
  (b.baseChange ℝ).map (realTransportedQuotientEquiv U E)

theorem realTransportedQuotientBasis_repr_mk {κ : Type*}
    (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (b : Basis κ ℚ (V ⧸ U)) (x : ℝ ⊗[ℚ] V) (i : κ) :
    (realTransportedQuotientBasis U E b).repr
      (((U.baseChange ℝ).map E.toLinearMap).mkQ (E x)) i =
      (b.baseChange ℝ).repr (U.mkQ.baseChange ℝ x) i := by
  rw [← realTransportedQuotientEquiv_mk]
  simp only [realTransportedQuotientBasis, Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

theorem realTransportedQuotientBasis_repr_basis {ι κ : Type*}
    (E : (ℝ ⊗[ℚ] V) ≃ₗ[ℝ] W) (e : Basis ι ℚ V) (b : Basis κ ℚ (V ⧸ U)) (i : ι) (j : κ) :
    (realTransportedQuotientBasis U E b).repr
      (((U.baseChange ℝ).map E.toLinearMap).mkQ (E ((e.baseChange ℝ) i))) j =
      (b.repr (U.mkQ (e i)) j : ℝ) := by
  rw [realTransportedQuotientBasis_repr_mk]
  simp only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix NNReal

variable {ι κ δ V W : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W)
  (D : Matrix κ ι ℚ) (hD : LinearMap.toMatrix e f q = D.map (Rat.castHom ℝ))

include hD

theorem rational_coordinate_map_weighted_exp (c : ι → δ) (r : κ → δ)
    (hblock : ∀ i j, r i ≠ c j → D i j = 0) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (hH : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (scale : δ → ℝ) (hscale : ∀ d, 0 < scale d) {M : ℝ} (hM : 0 ≤ M)
    (x : V) (hx : ∀ j, |e.equivFun x j| ≤ M / scale (c j)) (i : κ) :
    |f.equivFun (q x) i| ≤ Real.exp ((p + 2) ^ (a + 2)) * M / scale (r i) := by
  have h := rational_coordinate_map_weighted e f q D hD c r hblock
    ⟨Real.exp ((p + 2) ^ a), Real.exp_nonneg _⟩ hH scale hscale hM x hx i
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (matrix_weighted_factor_le_exp_power _ hp hι a ha) hM)
    (hscale _).le)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ δ V : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V] (e : Basis ι ℝ V) (S : Matrix ι κ ℚ)

theorem rationalCoordinateSection_weighted (c : ι → δ) (r : κ → δ)
    (hblock : ∀ i j, c i ≠ r j → S i j = 0) {p : ℝ} (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (hH : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (scale : δ → ℝ) (hscale : ∀ d, 0 < scale d) {M : ℝ} (hM : 0 ≤ M)
    (y : κ → ℝ) (hy : ∀ j, |y j| ≤ M / scale (r j)) (i : ι) :
    |e.equivFun (rationalCoordinateSection e S y) i| ≤
      Real.exp ((p + 2) ^ (a + 2)) * M / scale (c i) := by
  rw [rationalCoordinateSection_coordinates]
  have h := weighted_matrix_mulVec_bound c r (S.map (Rat.castHom ℝ))
    (fun i j h => by change (S i j : ℝ) = 0; rw [hblock i j h, Rat.cast_zero])
    ⟨Real.exp ((p + 2) ^ a), Real.exp_nonneg _⟩
    (fun i j => (rational_abs_real_le_numerator (S i j)).trans (hH i j))
    scale hscale hM y hy i
  exact h.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (matrix_weighted_factor_le_exp_power _ hp hκ a ha) hM)
    (hscale _).le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveCyclicCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] {N : ℕ}

theorem quarterLower_mem_commonCyclicCuts (h : ι → ZMod N) (i : Fin 4) :
    quarterLower N i ∈ commonCyclicCuts h := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl ⟨i, rfl⟩)

theorem quarterUpper_mem_commonCyclicCuts (h : ι → ZMod N) (i : Fin 4) :
    quarterUpper N i ∈ commonCyclicCuts h := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨i, rfl⟩)

theorem wrap_mem_commonCyclicCuts (h : ι → ZMod N) (i : ι) :
    N - (h i).val ∈ commonCyclicCuts h := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, rfl⟩

theorem zero_mem_commonCyclicCuts (h : ι → ZMod N) : 0 ∈ commonCyclicCuts h := by
  simpa only [quarterLower, Fin.val_zero, zero_mul, Nat.zero_div] using
    quarterLower_mem_commonCyclicCuts h 0

theorem commonCyclicCuts_le (h : ι → ZMod N) {a : ℕ} (ha : a ∈ commonCyclicCuts h) : a ≤ N := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at ha
  rcases ha with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact (quarter_bounds N i).1.trans (quarter_bounds N i).2
  · exact (quarter_bounds N i).2
  · exact Nat.sub_le _ _

theorem commonCyclicCuts_card_le (h : ι → ZMod N) :
    (commonCyclicCuts h).card ≤ Fintype.card ι + 8 := by
  have hL := Finset.card_image_le (s := Finset.univ) (f := quarterLower N)
  have hU := Finset.card_image_le (s := Finset.univ) (f := quarterUpper N)
  have hW := Finset.card_image_le (s := Finset.univ) (f := fun i => N - (h i).val)
  have hLU := Finset.card_union_le (Finset.univ.image (quarterLower N)) (Finset.univ.image (quarterUpper N))
  have hAll := Finset.card_union_le
    ((Finset.univ.image (quarterLower N)) ∪ (Finset.univ.image (quarterUpper N)))
    (Finset.univ.image (fun i => N - (h i).val))
  simp only [Finset.card_univ, Fintype.card_fin] at hL hU hW
  unfold commonCyclicCuts
  omega

theorem exists_mem_cyclicQuarter [NeZero N] (x : ZMod N) : ∃ i, x ∈ cyclicQuarter N i := by
  by_contra hn
  push Not at hn
  have hz (i : Fin 4) : finiteIndicator (cyclicQuarter N i) x = 0 := by
    simp only [finiteIndicator, hn i, ite_false]
  have hs := sum_cyclicQuarter_indicator x
  simp only [hz, Finset.sum_const_zero] at hs
  norm_num at hs

theorem commonCyclicCut_short [NeZero N] (h : ι → ZMod N) {a : ℕ}
    (ha : a ∈ commonCyclicCuts h) :
    2 * (((intervalCutUpper (commonCyclicCuts h) N a - a : ℕ) : ℤ) - 1) < N ∧
    3 * (((intervalCutUpper (commonCyclicCuts h) N a - a : ℕ) : ℤ) - 1) < N := by
  have haN := commonCyclicCuts_le h ha
  have huN := intervalCutUpper_le_end (commonCyclicCuts h) N a
  by_cases he : a = N
  · have hN := NeZero.pos N
    constructor <;> omega
  · have haN' : a < N := by omega
    obtain ⟨i, hi⟩ := exists_mem_cyclicQuarter (a : ZMod N)
    rw [mem_cyclicQuarter, ZMod.val_natCast_of_lt haN'] at hi
    have hub := intervalCutUpper_le_cut (commonCyclicCuts h) N
      (quarterUpper_mem_commonCyclicCuts h i) hi.2
    have h2 := quarter_short N (NeZero.pos N) i
    have h3 := quarter_diameter_lt_third N (NeZero.pos N) i
    constructor <;> omega

theorem sum_commonCyclicCut_indicator [NeZero N] (h : ι → ZMod N) (x : ZMod N) :
    (∑ a : commonCyclicCuts h, finiteIndicator (cyclicCutCell (commonCyclicCuts h) N a) x) = 1 :=
  sum_cyclicCutCell_indicator _ (zero_mem_commonCyclicCuts h)
    (fun _ ha => commonCyclicCuts_le h ha) x

theorem commonCyclicCut_representative [NeZero N] (h : ι → ZMod N) {a : ℕ}
    (ha : a ∈ commonCyclicCuts h) (i : ι) {x : ZMod N}
    (hx : x ∈ cyclicCutCell (commonCyclicCuts h) N a) :
    (((h i + x).val : ℕ) : ℤ) = (x.val : ℤ) + cyclicTranslationOffset (h i) a := by
  have hxi := (mem_cyclicCutCell _ (commonCyclicCuts_le h ha) x).mp hx
  have hw : (N - (h i).val ≤ x.val) ↔ (N - (h i).val ≤ a) := by
    constructor
    · intro hwx
      by_contra hwa
      have hu := intervalCutUpper_le_cut (commonCyclicCuts h) N
        (wrap_mem_commonCyclicCuts h i) (by omega : a < N - (h i).val)
      omega
    · intro hwa
      omega
  rw [cyclic_representative_add, cyclicTranslationOffset]
  simp only [hw]
  ring

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]

theorem translatedCyclicProduct_on_cut (h : ι → ZMod N) (u : ι → ℤ → ℂ) {a : ℕ}
    (ha : a ∈ commonCyclicCuts h) {x : ZMod N}
    (hx : x ∈ cyclicCutCell (commonCyclicCuts h) N a) :
    translatedCyclicProduct h u x = ∏ i, u i ((x.val : ℤ) + cyclicTranslationOffset (h i) a) := by
  unfold translatedCyclicProduct
  apply Finset.prod_congr rfl
  intro i _
  rw [commonCyclicCut_representative h ha i hx]

theorem translatedCyclicProduct_cut_correlation (h : ι → ZMod N) (u : ι → ℤ → ℂ)
    (f : ZMod N → ℂ) {a : ℕ} (ha : a ∈ commonCyclicCuts h) :
    finiteCorrelation (cyclicCutCell (commonCyclicCuts h) N a) f (translatedCyclicProduct h u) =
      finiteCorrelation (Finset.Ico (a : ℤ) (a + (intervalCutUpper (commonCyclicCuts h) N a - a : ℕ)))
        (fun x => f (x : ZMod N)) (fun x => ∏ i, u i (x + cyclicTranslationOffset (h i) a)) := by
  have haN := commonCyclicCuts_le h ha
  have hupper := intervalCutUpper_le_end (commonCyclicCuts h) N a
  have hle := le_intervalCutUpper (commonCyclicCuts h) N haN
  calc
    _ = finiteCorrelation (cyclicCutCell (commonCyclicCuts h) N a) f
        (fun x => ∏ i, u i ((x.val : ℤ) + cyclicTranslationOffset (h i) a)) := by
      unfold finiteCorrelation
      apply Finset.expect_congr rfl
      intro x hx
      rw [translatedCyclicProduct_on_cut h u ha hx]
    _ = _ := cyclicInterval_representative_correlation (N := N) a
      (intervalCutUpper (commonCyclicCuts h) N a - a) (by omega)
      (commonCyclicCut_short h ha).1 f (fun x => ∏ i, u i (x + cyclicTranslationOffset (h i) a))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalFormalStageGeometry
namespace OAI

section

namespace Erdos3

def formalGeometryHeight (n r H : ℕ) : ℕ :=
  let M := max H (homogeneousIntersectionBasisHeight n r H)
  max M (max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FormalGeometryBudget
namespace OAI

section

namespace Erdos3

theorem formalGeometryHeight_ge_input (n r H : ℕ) : H ≤ formalGeometryHeight n r H :=
  (Nat.le_max_left H _).trans (Nat.le_max_left _ _)

theorem formalGeometryHeight_le_exp (n r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (formalGeometryHeight n r H : ℝ) ≤ Real.exp ((((p + 2) ^ 9) + 2) ^ 5) := by
  let q := (p + 2) ^ 9
  let M := max H (homogeneousIntersectionBasisHeight n r H)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 9)
  have hMq : (M : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_max]
    exact max_le (hH.trans (Real.exp_le_exp.mpr hpq)) (stepDrop_basis_height_budget n r H hp hn hr hH)
  have hq5 : q ≤ (q + 2) ^ 5 := le_power_budget hq (by decide : 1 ≤ 5)
  have h35 : (q + 2) ^ 3 ≤ (q + 2) ^ 5 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ q + 2) (by decide : 3 ≤ 5)
  change ((max M (max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M)) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max M (max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M)),
    Nat.cast_max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M)]
  exact max_le (hMq.trans (Real.exp_le_exp.mpr hq5))
    (max_le ((formalCurrentMatrixHeight_le_exp n M hq (hn.trans hpq) hMq).trans
      (Real.exp_le_exp.mpr h35)) (formalBracketMatrixHeight_le_exp n M hq (hn.trans hpq) hMq))

theorem exists_formal_geometry_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n r H : ℕ) (p : ℝ), 0 ≤ p →
      (n : ℝ) ≤ p → (r : ℝ) ≤ 5 * p → (H : ℝ) ≤ Real.exp p →
      (formalGeometryHeight n r H : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget
    (((((Polynomial.X + 2) ^ 3 + 2) ^ 9) + 2) ^ 5)
  refine ⟨C, hC, fun n r H p hp hn hr hH => ?_⟩
  let t := (p + 2) ^ 3
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_power_budget hp (by decide : 1 ≤ 3)
  have hrt : (r : ℝ) ≤ t := by
    have h : 0 ≤ p ^ 3 + 6 * p ^ 2 + 7 * p + 8 := by positivity
    dsimp [t]
    nlinarith
  have hcap : ((t + 2) ^ 9 + 2) ^ 5 ≤ (p + C) ^ C := by
    simpa [t, Polynomial.eval₂_pow] using hbound p hp
  exact (formalGeometryHeight_le_exp n r H ht (hn.trans hpt) hrt
    (hH.trans (Real.exp_le_exp.mpr hpt))).trans (Real.exp_le_exp.mpr hcap)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BracketStepBudget
namespace OAI

section

namespace Erdos3

theorem exists_bracket_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      separationBudget (bracketConstructionBudget p) + bracketCorrectionBudget p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 3 * Polynomial.X + 2
  let B : Polynomial ℕ := (Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1 +
    ((Q + 2) ^ 36 + (Q + 2) ^ 18 + Q + (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X + 1)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [B, Q, separationBudget, bracketCorrectionBudget, bracketConstructionBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScaledLatticeCovolume
namespace OAI

section

namespace Erdos3

open Module

theorem exists_lattice_basis_covolume_factor
    {E ι α β : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype α] [Fintype β] [DecidableEq β]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ)) [IsZLattice ℝ (latticeKernel Λ π)]
    (bK : Basis α ℤ (latticeKernel Λ π)) (bI : Basis β ℤ (latticeImage Λ π)) :
    ∃ b : Basis (α ⊕ β) ℤ Λ,
      (∀ i, (b (Sum.inl i) : E) = (bK i).val.val) ∧
      (∀ j, π (b (Sum.inr j) : E) = (bI j).val) ∧
      ZLattice.covolume Λ ^ 2 = ZLattice.covolume (latticeKernel Λ π) ^ 2 *
        (Matrix.gram ℝ (fun j : β => (b (Sum.inr j) : E) -
          (LinearMap.ker π).starProjection (b (Sum.inr j) : E))).det := by
  classical
  obtain ⟨b, hbK, hbI⟩ := exists_lattice_split_basis Λ π bK bI
  refine ⟨b, hbK, hbI, ?_⟩
  let bR := b.ofZLatticeBasis ℝ Λ
  let bKR := bK.ofZLatticeBasis ℝ (latticeKernel Λ π)
  have hval (i : α) : bR (Sum.inl i) = (bKR i : E) := by
    simpa only [bR, bKR, Basis.ofZLatticeBasis_apply] using hbK i
  have hspan : Submodule.span ℝ (Set.range (fun i : α => bR (Sum.inl i))) =
      LinearMap.ker π := by
    rw [show (fun i : α => bR (Sum.inl i)) = (fun i : α => (bKR i : E)) from funext hval]
    change Submodule.span ℝ (Set.range ((LinearMap.ker π).subtype ∘ bKR)) = _
    rw [Set.range_comp, ← Submodule.map_span, bKR.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hkernelGram : (Matrix.gram ℝ (fun i : α => bR (Sum.inl i))).det =
      ZLattice.covolume (latticeKernel Λ π) ^ 2 := by
    have he : Matrix.gram ℝ (fun i : α => bR (Sum.inl i)) = Matrix.gram ℝ bKR := by
      ext i j
      simp only [Matrix.gram_apply, hval]
      rfl
    rw [he]
    exact (lattice_covolume_sq_eq_gram (latticeKernel Λ π) bK).symm
  have hblock := gram_det_orthogonal_block bR
  dsimp only at hblock
  rw [hspan, hkernelGram] at hblock
  rw [lattice_covolume_sq_eq_gram Λ b]
  simpa only [bR, Basis.ofZLatticeBasis_apply] using hblock

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.EuclideanDerivativeProjection
namespace OAI

section

namespace Erdos3

theorem euclideanDerivativeLattice_shortSpan_projection
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
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T
      (fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne') scale hscale Y A l hl
    (shortVectorSpan Λ ρ).map ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp
      productEuclideanEquiv.symm.toLinearMap) = ⊤ := by
  let hT0 : ∀ i, 0 < T i := fun i => lt_of_lt_of_le zero_lt_one (hT i)
  let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T (fun i => (hT0 i).ne') scale hscale Y A l hl
  let π₀ := (LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap
  let e := coordinateScaleEquiv T (fun i => (hT0 i).ne')
  let π := e.toLinearMap.comp π₀
  have hspan := integer_points_span_eq_top_of_density H T R δ hT hR
    (fun h hh => derivativeGridPoint_shift_bound T hT0 scale Y _ h (r h) R (hnorm h hh))
    hdense hlarge
  have hmap : (shortVectorSpan Λ ρ).map π = ⊤ := by
    apply shortVectorSpan_map_eq_top_of_spanning_integer_images Λ π H ρ hspan
    intro h hh
    let v := derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)
    refine ⟨productEuclideanEquiv v, ?_, ?_, ?_⟩
    · apply (productEuclideanEquiv_mem_derivativeLattice T
        (fun i => (hT0 i).ne') scale hscale Y A l hl v).mpr
      rw [← SetLike.mem_coe, derivativeLattice_carrier]
      exact derivativeGridPoint_mem T scale Y _ l h (r h) (hr h hh)
    · exact (productEuclideanEquiv_norm_le v).trans
        (mul_le_mul_of_nonneg_left (hnorm h hh) (Nat.cast_nonneg _))
    · change e (LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)
        (productEuclideanEquiv.symm (productEuclideanEquiv v))) = _
      rw [LinearEquiv.symm_apply_apply]
      funext i
      exact mul_div_cancel₀ (h i : ℝ) (hT0 i).ne'
  have hmap' : ((shortVectorSpan Λ ρ).map π₀).map e.toLinearMap = ⊤ := by
    simpa only [← Submodule.map_comp] using hmap
  exact (Submodule.map_eq_top_iff (e := e)).mp hmap'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DerivativeLatticeDivision
namespace OAI

section

namespace Erdos3

theorem divided_derivative_lattice_coordinates
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hs : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (I : ℕ) (hI : 0 < I) (y : σ → ℝ)
    (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hv : v ∈ euclideanDerivativeLattice T hT scale hs Y A l hl)
    (hshift : euclideanDerivativeShiftMap T hT v = (I : ℝ) • y) :
    ∃ r : κ → ℝ, r ∈ realDenominatorGrid (l * I) ∧
      ∀ j, ((I : ℝ)⁻¹ • v) (Sum.inr j) = scale j * (Y y j - A r j) := by
  have hIr : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  have hv' := (euclideanDerivativeLattice_mem_iff T hT scale hs Y A l hl v).mp hv
  rw [← SetLike.mem_coe, derivativeLattice_carrier] at hv'
  obtain ⟨h, r, hr, he⟩ := hv'
  have hleft (i) : v (Sum.inl i) = (h i : ℝ) / T i :=
    congrArg (fun x : (σ → ℝ) × (κ → ℝ) => x.1 i) he
  have hright (j) : v (Sum.inr j) =
      scale j * (Y (fun i => (h i : ℝ)) j - A r j) := by
    have hc := congrArg (fun x : (σ → ℝ) × (κ → ℝ) => x.2 j) he
    change (productEuclideanEquiv.symm v).2 j = _
    simpa only [derivativeGridPoint, LinearMap.toMatrix'_mulVec,
      LinearEquiv.coe_coe, Pi.sub_apply] using hc
  have hh : (fun i => (h i : ℝ)) = (I : ℝ) • y := by
    funext i
    have hi := congrFun hshift i
    change T i * v (Sum.inl i) = (I : ℝ) * y i at hi
    rw [hleft, mul_div_cancel₀ _ (hT i)] at hi
    exact hi
  refine ⟨(I : ℝ)⁻¹ • r, realDenominatorGrid_div_nat l I hI r hr, ?_⟩
  intro j
  change (I : ℝ)⁻¹ * v (Sum.inr j) = _
  rw [hright, hh, map_smul, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeIndexBounds
namespace OAI

section

namespace Erdos3

theorem exists_weighted_minor_lower_bound {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ) (hA : LinearIndependent ℝ A.col)
    (l : ℕ) (hl : 0 < l) (hgrid : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l)
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1)
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧
      1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤
        |(Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).det| := by
  obtain ⟨p, hp, hdet, hpreserve⟩ := exists_preserved_nonzero_row_minor A hA
  have hsubgrid : ∀ j, (fun i => (A.submatrix p id) i j) ∈ realDenominatorGrid l := by
    intro j
    obtain ⟨z, hz⟩ := hgrid j
    exact ⟨fun i => z (p i), funext (fun i => congrFun hz (p i))⟩
  have hminor := one_div_pow_le_abs_grid_det (A.submatrix p id) l hl hsubgrid hdet
  simp only [Fintype.card_fin] at hminor
  refine ⟨p, hp, ?_⟩
  rw [weighted_row_minor_det, hpreserve M hM hdiag, abs_mul,
    abs_of_pos (Finset.prod_pos (fun i _ => hw (p i)))]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right hminor (Finset.prod_nonneg (fun i _ => (hw (p i)).le))

theorem weighted_isometric_lattice_covolume_lower {ι E : Type*} [Fintype ι] {m k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : Fin m → ι) (he : Function.Injective e)
    (A : Matrix (Fin m) (Fin k) ℝ) (hA : LinearIndependent ℝ A.col)
    (l : ℕ) (hl : 0 < l) (hgrid : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l)
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1)
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (hcoord : ∀ j i, f (b j).val (e i) = w i * (M * A) i j) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧
      1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤ ZLattice.covolume Λ := by
  obtain ⟨p, hp, hlower⟩ := exists_weighted_minor_lower_bound A hA l hl hgrid M hM hdiag w hw
  refine ⟨p, hp, hlower.trans ?_⟩
  have hupper := abs_isometric_lattice_basis_det_le_covolume Λ b f (e ∘ p) (he.comp hp)
  have hmatrix : Matrix.of (fun i j => f (b i).val ((e ∘ p) j)) =
      (Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).transpose := by
    ext i j
    exact hcoord i (p j)
  simpa only [hmatrix, Matrix.det_transpose] using hupper

end Erdos3

end

section

namespace Erdos3

theorem weighted_isometric_lattice_minor_data {ι E : Type*} [Fintype ι] {m k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : Fin m → ι) (he : Function.Injective e)
    (A : Matrix (Fin m) (Fin k) ℝ) (hA : LinearIndependent ℝ A.col)
    (l : ℕ) (hl : 0 < l) (hgrid : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l)
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1)
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (hcoord : ∀ j i, f (b j).val (e i) = w i * (M * A) i j) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧ (A.submatrix p id).det ≠ 0 ∧
      1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤ ZLattice.covolume Λ := by
  obtain ⟨p, hp, hdet, hpreserve⟩ := exists_preserved_nonzero_row_minor A hA
  have hsubgrid : ∀ j, (fun i => (A.submatrix p id) i j) ∈ realDenominatorGrid l := by
    intro j
    obtain ⟨z, hz⟩ := hgrid j
    exact ⟨fun i => z (p i), funext (fun i => congrFun hz (p i))⟩
  have hminor := one_div_pow_le_abs_grid_det (A.submatrix p id) l hl hsubgrid hdet
  simp only [Fintype.card_fin] at hminor
  have hlower : 1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤
      |(Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).det| := by
    rw [weighted_row_minor_det, hpreserve M hM hdiag, abs_mul,
      abs_of_pos (Finset.prod_pos (fun i _ => hw (p i)))]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hminor (Finset.prod_nonneg (fun i _ => (hw (p i)).le))
  refine ⟨p, hp, hdet, hlower.trans ?_⟩
  have hupper := abs_isometric_lattice_basis_det_le_covolume Λ b f (e ∘ p) (he.comp hp)
  have hmatrix : Matrix.of (fun i j => f (b i).val ((e ∘ p) j)) =
      (Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).transpose := by
    ext i j
    exact hcoord i (p j)
  simpa only [hmatrix, Matrix.det_transpose] using hupper

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.GridNormalizationDenominator
namespace OAI

section

namespace Erdos3

theorem exists_bounded_rational_row_normalization {ι : Type*} {k : ℕ}
    (H : Matrix ι (Fin k) ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, H.col j ∈ realDenominatorGrid l)
    (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0)
    (C : ℝ) (hminor : ∀ q : Fin k → ι, |(H.submatrix q id).det| ≤ C) :
    ∃ Q : Matrix ι (Fin k) ℚ,
      Q.map (Rat.castHom ℝ) = H * (H.submatrix p id)⁻¹ ∧
      (∀ i j, RationalHeightLE (Q i j) (Nat.ceil (C * (l : ℝ) ^ k))) ∧
      Q.submatrix p id = 1 := by
  obtain ⟨Z, hZ⟩ := exists_integer_scaled_grid_matrix H l hgrid
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hZp : (Z.submatrix p id).det ≠ 0 := by
    intro hz
    have hf := scaled_integer_minor_eq Z H (l : ℝ) hZ p
    rw [hz, Int.cast_zero] at hf
    exact (mul_ne_zero (pow_ne_zero _ hlr.ne') hp) hf.symm
  let W := Z.map (Int.castRingHom ℚ)
  let Q := W * (W.submatrix p id)⁻¹
  have hWp : (W.submatrix p id).det ≠ 0 := by
    have he : (W.submatrix p id).det = ((Z.submatrix p id).det : ℚ) := by
      change ((Z.submatrix p id).map (Int.castRingHom ℚ)).det = _
      exact ((Int.castRingHom ℚ).map_det _).symm
    rw [he]
    exact_mod_cast hZp
  refine ⟨Q, ?_, ?_, row_normalization_submatrix W p hWp⟩
  · exact scaled_integer_row_normalization_cast Z H (l : ℝ) hlr.ne' hZ p hp hZp
  · intro i j
    exact integer_row_normalization_height Z p hZp _
      (scaled_integer_minor_natAbs_bound Z H (l : ℝ) C hlr hZ hminor) i j

end Erdos3

end

section

namespace Erdos3

theorem exists_grid_row_normalization {ι : Type*} {k : ℕ}
    (B : Matrix ι (Fin k) ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, B.col j ∈ realDenominatorGrid l)
    (p : Fin k → ι) (hp : (B.submatrix p id).det ≠ 0)
    (C : ℝ) (hminor : |(B.submatrix p id).det| ≤ C) :
    ∃ D : ℕ, 0 < D ∧ D ≤ Nat.ceil (C * (l : ℝ) ^ k) ∧
      ∃ Q : Matrix ι (Fin k) ℚ,
        (∀ j, Q.col j ∈ denominatorGrid D) ∧
        Q.map (Rat.castHom ℝ) = B * (B.submatrix p id)⁻¹ ∧
        Q.submatrix p id = 1 := by
  obtain ⟨Z, hZ⟩ := exists_integer_scaled_grid_matrix B l hgrid
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hZp : (Z.submatrix p id).det ≠ 0 := by
    intro hz
    have hf := scaled_integer_minor_eq Z B (l : ℝ) hZ p
    rw [hz, Int.cast_zero] at hf
    exact (mul_ne_zero (pow_ne_zero _ hlr.ne') hp) hf.symm
  have hbound : (Z.submatrix p id).det.natAbs ≤ Nat.ceil (C * (l : ℝ) ^ k) := by
    have h : |((Z.submatrix p id).det : ℝ)| ≤ C * (l : ℝ) ^ k := by
      rw [scaled_integer_minor_eq Z B (l : ℝ) hZ, abs_mul,
        abs_of_pos (pow_pos hlr _)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hminor (pow_pos hlr k).le
    have hc := h.trans (Nat.le_ceil (C * (l : ℝ) ^ k))
    apply (Nat.cast_le (α := ℝ)).mp
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
  let W := Z.map (Int.castRingHom ℚ)
  have hWp : (W.submatrix p id).det ≠ 0 := by
    have he : (W.submatrix p id).det = ((Z.submatrix p id).det : ℚ) := by
      change ((Z.submatrix p id).map (Int.castRingHom ℚ)).det = _
      exact ((Int.castRingHom ℚ).map_det _).symm
    rw [he]
    exact_mod_cast hZp
  refine ⟨_, Int.natAbs_pos.mpr hZp, hbound, W * (W.submatrix p id)⁻¹,
    integer_row_normalization_grid Z p hZp, ?_, row_normalization_submatrix W p hWp⟩
  exact scaled_integer_row_normalization_cast Z B (l : ℝ) hlr.ne' hZ p hp hZp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartiallyBoundedNormalization
namespace OAI

section

namespace Erdos3

theorem exists_partially_bounded_grid_normalization {ι κ : Type*} {k : ℕ}
    (B : Matrix ι (Fin k) ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, B.col j ∈ realDenominatorGrid l)
    (e : κ → ι) (p : Fin k → κ)
    (hp : (B.submatrix (e ∘ p) id).det ≠ 0)
    (C : ℝ) (hminor : ∀ q : Fin k → κ, |(B.submatrix (e ∘ q) id).det| ≤ C) :
    ∃ D : ℕ, 0 < D ∧ D ≤ Nat.ceil (C * (l : ℝ) ^ k) ∧
      ∃ Q : Matrix ι (Fin k) ℚ,
        (∀ j, Q.col j ∈ denominatorGrid D) ∧
        Q.map (Rat.castHom ℝ) = B * (B.submatrix (e ∘ p) id)⁻¹ ∧
        Q.submatrix (e ∘ p) id = 1 ∧
        (∀ i j, RationalHeightLE (Q (e i) j) (Nat.ceil (C * (l : ℝ) ^ k))) := by
  obtain ⟨D, hD, hDle, Q, hQgrid, hQ, hQid⟩ :=
    exists_grid_row_normalization B l hl hgrid (e ∘ p) hp C (hminor p)
  let H := B.submatrix e id
  have hHgrid (j) : H.col j ∈ realDenominatorGrid l := by
    obtain ⟨z, hz⟩ := hgrid j
    refine ⟨fun i => z (e i), ?_⟩
    funext i
    exact congrFun hz (e i)
  obtain ⟨QH, hQH, hheight, _⟩ :=
    exists_bounded_rational_row_normalization H l hl hHgrid p hp C hminor
  have heq : Q.submatrix e id = QH := by
    ext i j
    apply Rat.cast_injective (α := ℝ)
    change (Q (e i) j : ℝ) = (QH i j : ℝ)
    calc
      _ = (B * (B.submatrix (e ∘ p) id)⁻¹) (e i) j :=
        congrArg (fun M : Matrix ι (Fin k) ℝ => M (e i) j) hQ
      _ = (H * (H.submatrix p id)⁻¹) i j := rfl
      _ = _ := (congrArg (fun M : Matrix κ (Fin k) ℝ => M i j) hQH).symm
  refine ⟨D, hD, hDle, Q, hQgrid, hQ, hQid, ?_⟩
  intro i j
  have h := congrArg (fun M : Matrix κ (Fin k) ℚ => M i j) heq
  change Q (e i) j = QH i j at h
  rw [h]
  exact hheight i j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

open scoped NNReal

namespace Erdos3

theorem exists_productNiltestBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → productNiltestBudget p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, X, Polynomial.eval₂_pow, productNiltestBudget, productObservableLipBudget] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SquarefreeModelBudget
namespace OAI

section

namespace Erdos3

theorem squarefreeStructureHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (squarefreeStructureHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 8) := by
  have hprod : ((rationalSolveHeight n H * squarefreeBracketHeight n H : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 6) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 5) * Real.exp ((p + 2) ^ 5) :=
        mul_le_mul (rationalSolveHeight_le_budget n H hp hn hH)
          (squarefreeBracketHeight_le_exp n H hp hn hH) (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * (p + 2) ^ 5) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (p + 2) * (p + 2) ^ 5 := by gcongr; linarith
          _ = _ := by ring
  exact rational_sum_cost_le_exp n _ hp 6 1 hprod (by simpa only [pow_one] using hn.trans (by linarith))

end Erdos3

end

section

namespace Erdos3

theorem squarefreeStructureHeight_ceil_exp (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) :
    (squarefreeStructureHeight n ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 8) := by
  have h := squarefreeStructureHeight_le_exp n ⌈Real.exp p⌉₊
    (p := p + 1) (by linarith) (by linarith) (ceil_exp_le_exp_add_one hp)
  have heq : p + 1 + 2 = p + 3 := by ring
  simpa only [heq] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FormalStageBudget
namespace OAI

section

namespace Erdos3

theorem exists_formal_stage_budget (D E : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let d := (p + D) ^ D
      let u := bracketTransitionBudget (p + d)
      let q := u + bracketConstructionBudget u
      d + (q + E) ^ E + 1 ≤ (p + C) ^ C := by
  let Pd : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D
  let Pt : Polynomial ℕ := Polynomial.X + Pd
  let Pu : Polynomial ℕ := 4 * Pt + (Pt + 2) ^ 8 + (Pt + 2) ^ 9 + 1
  let Pq : Polynomial ℕ := Pu + ((Pu + 2) ^ 3 + 3 * Pu + 2)
  let P : Polynomial ℕ := Pd + (Pq + Polynomial.C E) ^ E + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Pd, Pt, Pu, Pq, bracketTransitionBudget, bracketConstructionBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UniformFormalInductionIteration
namespace OAI

section

namespace Erdos3

noncomputable def formalIterationPolynomial (C : ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | n + 1 => (formalIterationPolynomial C n + Polynomial.C C) ^ C

theorem formalIterationPolynomial_eval (C n : ℕ) (p : ℝ) :
    (formalIterationPolynomial C n).eval₂ (Nat.castRingHom ℝ) p = formalIterationBudget C p n := by
  induction n with
  | zero => simp [formalIterationPolynomial]
  | succ n ih => simp [formalIterationPolynomial, Polynomial.eval₂_pow, ih]

theorem exists_formal_iteration_uniform_budget (C n : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (n + 1 : ℝ) * formalIterationBudget C p n ≤ (p + D) ^ D := by
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_eval_budget
    (Polynomial.C (n + 1) * formalIterationPolynomial C n)
  refine ⟨D, hD, fun p hp => ?_⟩
  have h := hbound p hp
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, formalIterationPolynomial_eval] at h
  change ((n + 1 : ℕ) : ℝ) * formalIterationBudget C p n ≤ (p + D) ^ D at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSelectedCorrelators
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem cross_correlations_force_additive_quadruples
    (f₀ f₁ : G → ℂ) (g : G → G → ℂ)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) :
    (𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) ^ 4 ≤
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
  let C (a : G) := 𝔼 h, ‖𝔼 x, multiplicativeDerivative f₀ a x *
    (star (g h x) * g (h - a) (x + a))‖
  have hfirst : (𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) ^ 2 ≤
      𝔼 a, C a := by
    have hcs := shifted_test_cauchy_schwarz f₀ (fun x => star (f₁ x))
      (fun h x => star (g h x)) (M := 1) (by simpa only [norm_star] using hf₁)
    have hreindex : (𝔼 h, 𝔼 k, ‖𝔼 x, f₀ x * star (f₀ (x + h - k)) *
        star (g h x) * g k (x + h - k)‖) = 𝔼 a, C a := by
      calc
        _ = 𝔼 h, 𝔼 a, ‖𝔼 x, multiplicativeDerivative f₀ a x *
            (star (g h x) * g (h - a) (x + a))‖ := by
          apply Finset.expect_congr rfl
          intro h _
          apply Fintype.expect_equiv (Equiv.subLeft h)
          intro k
          simp only [Equiv.subLeft_apply, sub_sub_cancel, multiplicativeDerivative,
            ← add_sub_assoc, mul_assoc]
        _ = _ := Finset.expect_comm _ _ _
    rw [← hreindex]
    simpa only [one_pow, one_mul, star_star, mul_assoc] using hcs
  have hsecond (a : G) : C a ^ 2 ≤
      𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    have hcs := finite_absolute_cauchy_schwarz (multiplicativeDerivative f₀ a)
      (fun h x => star (g h x) * g (h - a) (x + a))
      (multiplicativeDerivative_norm_le_one f₀ hf₀ a)
    simpa only [one_pow, one_mul, C, additiveQuadrupleCorrelation, star_mul,
      star_star, mul_assoc, mul_comm, mul_left_comm] using hcs
  calc
    _ = ((𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) ^ 2) ^ 2 := by ring
    _ ≤ (𝔼 a, C a) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ ≤ 𝔼 a, C a ^ 2 := expect_square_le C
    _ ≤ _ := Finset.expect_le_expect (fun a _ => hsecond a)

theorem exists_many_cross_correlated_quadruples
    (f₀ f₁ : G → ℂ) (g : G → G → ℂ) (H : Finset G)
    (hf₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hf₁ : ∀ x, ‖f₁ x‖ ≤ 1) (hg : ∀ h x, ‖g h x‖ ≤ 1)
    (hzero : ∀ h, h ∉ H → ∀ x, g h x = 0)
    {alpha delta : ℝ} (halpha : 0 < alpha) (hdelta : 0 < delta)
    (hdense : alpha * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, delta ≤ ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖) :
    ∃ Q : Finset (G × G × G), Q.Nonempty ∧
      (alpha * delta) ^ 4 / 2 * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧
        t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
        (alpha * delta) ^ 4 / 2 ≤ additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
  classical
  have hcardG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hindicator : (𝔼 h : G, if h ∈ H then delta else 0) =
      (H.card : ℝ) * delta / Fintype.card G := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : alpha * delta ≤
      𝔼 h, ‖𝔼 x, (f₀ x * star (f₁ (x + h))) * star (g h x)‖ := by
    calc
      _ ≤ (H.card : ℝ) * delta / Fintype.card G := by
        apply (le_div_iff₀ hcardG).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense hdelta.le]
      _ = _ := hindicator.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact hcorr h hh
        · exact norm_nonneg _
  have hsplit : (𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2) =
      𝔼 a, 𝔼 h, 𝔼 k, additiveQuadrupleCorrelation g a h k := by
    simp only [← Finset.univ_product_univ, Finset.expect_product]
  have hquad : (alpha * delta) ^ 4 ≤
      𝔼 t : G × G × G, additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
    rw [hsplit]
    exact (pow_le_pow_left₀ (mul_pos halpha hdelta).le hmean 4).trans
      (cross_correlations_force_additive_quadruples f₀ f₁ g hf₀ hf₁)
  obtain ⟨Q, hQcard, hQ⟩ := exists_dense_level_set
    (fun t : G × G × G => additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2)
    (by positivity : 0 ≤ (alpha * delta) ^ 4)
    (fun t => additiveQuadrupleCorrelation_le_one g hg t.1 t.2.1 t.2.2) hquad
  have hcards : (Fintype.card (G × G × G) : ℝ) = (Fintype.card G : ℝ) ^ 3 := by
    simp only [Fintype.card_prod, Nat.cast_mul]
    ring
  rw [hcards] at hQcard
  have hQnonempty : Q.Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℝ) < (Q.card : ℝ) := lt_of_lt_of_le (by positivity) hQcard
    exact_mod_cast this
  refine ⟨Q, hQnonempty, hQcard, fun t ht => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := additiveQuadrupleCorrelation_support g H hzero
    (lt_of_lt_of_le (by positivity) (hQ t ht))
  exact ⟨h₁, h₂, h₃, h₄, hQ t ht⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ScaledPairBasisHeight
namespace OAI

section

namespace Erdos3

open Module

theorem exists_scaledPair_basis_height {ι α β L : Type*} [Fintype α] [Fintype β]
    [AddCommGroup L] [Module ℚ L] (e : Basis ι ℚ L)
    (P Q : Submodule ℚ L) (hQP : Q ≤ P) (a : Basis α ℚ Q) (b : Basis β ℚ P)
    (q : ℚ) {H K : ℕ} (hH : 1 ≤ H) (hK : 1 ≤ K) (hq : RationalHeightLE q K)
    (ha : ∀ j k, RationalHeightLE (e.repr (a j : L) k) H)
    (hb : ∀ j k, RationalHeightLE (e.repr (b j : L) k) H) :
    ∃ c : Basis (Fin (finrank ℚ (scaledPairLayer P Q q))) ℚ (scaledPairLayer P Q q),
      ∀ j k, RationalHeightLE (e.repr (c j).val.1 k) (H * K) ∧
        RationalHeightLE (e.repr (c j).val.2 k) (H * K) := by
  classical
  let c := (a.prod b).map (scaledPairLayerEquiv P Q hQP q)
  have hHK : H ≤ H * K := Nat.le_mul_of_pos_right H (by omega)
  have hz (k : ι) : RationalHeightLE (e.repr 0 k) (H * K) := by
    simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero (hH.trans hHK)
  have hc (j : α ⊕ β) (k : ι) :
      RationalHeightLE (e.repr (c j).val.1 k) (H * K) ∧
        RationalHeightLE (e.repr (c j).val.2 k) (H * K) := by
    rcases j with j | j
    · simpa [c, Basis.prod_apply, scaledPairLayerEquiv, scaledPairAssemble] using
        (show RationalHeightLE (e.repr (a j : L) k) (H * K) ∧
          RationalHeightLE (e.repr 0 k) (H * K) from ⟨(ha j k).mono hHK, hz k⟩)
    · have hmul : RationalHeightLE (q * e.repr (b j : L) k) (H * K) := by
        simpa only [Nat.mul_comm K H] using hq.mul (hb j k)
      simpa [c, Basis.prod_apply, scaledPairLayerEquiv, scaledPairAssemble, smul_eq_mul] using
        (show RationalHeightLE (q * e.repr (b j : L) k) (H * K) ∧
          RationalHeightLE (e.repr (b j : L) k) (H * K) from ⟨hmul, (hb j k).mono hHK⟩)
  let c' := c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)
  exact ⟨c', fun j k => by simpa only [c', Basis.reindex_apply] using hc _ k⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3

noncomputable def positivePolynomialDenominatorBudget (t : ℕ) (p : ℝ) : ℝ :=
  positivePolynomialInputBudget t p + (positivePolynomialInputBudget t p + 2) ^ 4

theorem positivePolynomialInputBudget_nonneg (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ positivePolynomialInputBudget t p :=
  add_nonneg (by linarith) (squarefreeInputBudget_nonneg t hp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeTernaryCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ I : Type*} [DecidableEq σ]

theorem coordinateTranslationExpansion_unit [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hunit : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (l : List σ) (x : Option σ → ℤ) :
    ∑ a : BinaryTensorIndex I l.length, ‖coordinateTranslationExpansion f l a x‖ ^ 2 = 1 := by
  induction l generalizing x with
  | nil => exact hunit _
  | cons i l ih =>
    change (∑ a : BinaryTensorIndex I l.length × BinaryTensorIndex I l.length,
      ‖coordinateTranslationExpansion f l a.1 x *
        coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x)‖ ^ 2) = 1
    simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, ih, mul_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
namespace OAI

section

namespace Erdos3

variable {σ I : Type*} [DecidableEq σ]

theorem coordinateTranslationExpansion_factor (f : I → (σ → ℤ) → ℂ)
    (l : List σ) (a : BinaryTensorIndex I l.length) (x : Option σ → ℤ) :
    coordinateTranslationExpansion f l a x =
      f (firstTranslationCoordinate l a) (fun j => x (some j)) *
        translationExpansionRemainder f l a x := by
  induction l generalizing x with
  | nil => exact (mul_one _).symm
  | cons i l ih =>
    change coordinateTranslationExpansion f l a.1 x *
      coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x) = _
    rw [ih]
    exact mul_assoc _ _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCommonFamily
namespace OAI

section

namespace Erdos3

theorem exists_synchronizedSquare_budget (r a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + (p + r) ^ r + a) ^ a ≤ (p + C) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + Polynomial.C r) ^ r + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem map_correlationInput {A B : Type*} (g : A → B) (h n : A) :
    (fun i => g (correlationInput h n i)) = correlationInput (g h) (g n) := by
  funext i
  fin_cases i <;> rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3

theorem le_mixedErrorPairBudget {p : ℝ} (hp : 0 ≤ p) : p ≤ mixedErrorPairBudget p := by
  have h := productNiltestBudget_geometry hp
  unfold mixedErrorPairBudget
  nlinarith only [hp, h, sq_nonneg (p + 2)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
namespace OAI

section

namespace Erdos3

theorem exists_common_rank_relation_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → p + (p + c) ^ c ≤ (p + C) ^ C := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C c) ^ c)
  exact ⟨C, hC, fun p hp => by simpa [Polynomial.eval₂_pow] using hbudget p hp⟩

theorem exists_native_common_rank_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := p + (p + a) ^ a + 2
      q ≤ (p + C) ^ C ∧ (q + c) ^ c ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + Polynomial.C a) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Y + (Y + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p hp q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpow : 0 ≤ (q + c) ^ c := by positivity
  have hsum : q + (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Y, q, Polynomial.eval₂_pow] using hbudget p hp
  constructor <;> linarith only [hq, hpow, hsum]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedSwapSample {s : ℕ} (π : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  fun k => π (mixedExchangeCoordinate (s + 1) k)

end Erdos3

end

end OAI
end


