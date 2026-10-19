-- Prove2me | Definitions.Def_OAIE3v2B081
-- name    : OAIE3v2B081
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:19:54.026301+00:00
-- url     : https://prove2.me/theorems/592c4deb-2c2a-4cde-a96c-c246fe23da2a
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 82 of 311
-- statement:
--   Definitions bundle 82 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B041`, `OAIE3v2B042`, `OAIE3v2B045`, `OAIE3v2B047`, `OAIE3v2B048`, `OAIE3v2B049`, `OAIE3v2B051`, `OAIE3v2B055`, `OAIE3v2B056`, `OAIE3v2B060` of this split.
--
--   Modules: `Dynamics/LieSubalgebraRepresentativeBudget.lean`, `Dynamics/MarkedRefilteredModelBudget.lean`, `Dynamics/NativeMarkedQuotientHeightBudget.lean`, `Dynamics/NativeOptionProductBudget.lean`, `Estimates/CopiedLayerSpace.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/DenseProgressionInnerFamily.lean`, `Estimates/EmptyLayerDetectionGeometry.lean`, `Estimates/McShaneEnvelope.lean`, `Estimates/NativeIteratedDifferencing.lean`, `Estimates/NestedProgressionReindex.lean`, `Estimates/OptionComplementCover.lean`, `Estimates/UniformControlledNativeExternalNetsOfRecovery.lean`, `Geometry/AuxiliaryBoxPartition.lean`, `Geometry/EmptyLayerChartBounds.lean`, `Geometry/NestedBoxReindex.lean`, `Geometry/PhysicalBoxPartition.lean`, `Lattices/AffineWindowGoodKernelBound.lean`, `Lattices/AllocatedSupportedSlicedResidue.lean`, `Lattices/CoefficientLatticeCompact.lean`, `Lattices/EuclideanShortLatticeBasis.lean`, `Lattices/LatticeSheetHaar.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/ResidueSliceNormalizedCell.lean`, `Lattices/ScalarResidueInteriorCell.lean`, `Linear/BasisAxisNormalization.lean`, `Linear/NormalizedBasisBounds.lean`, `Linear/OrthogonalBasisChart.lean`, `Probability/AuxiliaryBoxLaws.lean`, `Sampling/FrozenPartitionScore.lean`.
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
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B045
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049
import Definitions.Def_OAIE3v2B051
import Definitions.Def_OAIE3v2B055
import Definitions.Def_OAIE3v2B056
import Definitions.Def_OAIE3v2B060

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem gowersMoment_re_nonneg (j : ℕ) (f : H → ℂ) :
    0 ≤ (gowersMoment (j + 1) f).re := by
  induction j generalizing f with
  | zero =>
    rw [gowersMoment_one]
    change 0 ≤ ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).re
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  | succ j ih =>
    rw [gowersMoment, expect_re]
    exact Finset.expect_nonneg (fun h _ ↦ ih (multiplicativeDerivative f h))

theorem gowersNorm_nonneg (j : ℕ) (f : H → ℂ) : 0 ≤ gowersNorm (j + 1) f :=
  Real.rpow_nonneg (gowersMoment_re_nonneg j f) _

theorem gowersNorm_pow (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 1) f ^ (2 ^ (j + 1)) = (gowersMoment (j + 1) f).re := by
  exact Real.rpow_inv_natCast_pow (n := 2 ^ (j + 1)) (gowersMoment_re_nonneg j f)
    (pow_ne_zero _ (by norm_num))

theorem gowersNorm_one (f : H → ℂ) : gowersNorm 1 f = ‖𝔼 x, f x‖ := by
  have hmoment : (gowersMoment 1 f).re = ‖𝔼 x, f x‖ ^ 2 := by
    rw [gowersMoment_one]
    change ((𝔼 x, f x) * starRingEnd ℂ (𝔼 x, f x)).re = _
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  unfold gowersNorm
  rw [hmoment]
  norm_num only [pow_one, Nat.cast_ofNat]
  simpa using Real.pow_rpow_inv_natCast (norm_nonneg (𝔼 x : H, f x))
    (by norm_num : (2 : ℕ) ≠ 0)

theorem gowersNorm_derivative (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 2) f ^ (2 ^ (j + 2)) =
      𝔼 h, gowersNorm (j + 1) (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  simp only [gowersNorm_pow]
  exact expect_re _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FrozenPartitionScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_good_partition_score {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (cell : Ω → I) (good : I → Prop) [DecidablePred good] (g : Ω → ℝ) {B τ ρ S : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hg : ∀ x, g x ≤ B)
    (hbad : (𝔼 x, if good (cell x) then (0 : ℝ) else 1) ≤ ρ)
    (hscore : S ≤ 𝔼 x, g x) (hbudget : τ + B * ρ < S) :
    ∃ i, good i ∧ τ < 𝔼 x ∈ partitionCell cell i, g x := by
  classical
  by_contra! hnone
  let b : Ω → ℝ := fun x => if good (cell x) then 0 else 1
  have hcell (i : I) : (∑ x ∈ partitionCell cell i, g x) ≤
      τ * (partitionCell cell i).card + B * ∑ x ∈ partitionCell cell i, b x := by
    by_cases hi : good i
    · have hb : (∑ x ∈ partitionCell cell i, b x) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [b, (mem_partitionCell _ _ _).mp hx, hi, ite_true]
      rw [hb, mul_zero, add_zero]
      have h := mul_le_mul_of_nonneg_left (hnone i hi)
        (Nat.cast_nonneg (partitionCell cell i).card : (0 : ℝ) ≤ _)
      rw [Finset.card_mul_expect] at h
      simpa only [mul_comm] using h
    · have hb : (∑ x ∈ partitionCell cell i, b x) = (partitionCell cell i).card := by
        calc
          _ = ∑ _x ∈ partitionCell cell i, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [b, (mem_partitionCell _ _ _).mp hx, hi, ite_false]
          _ = _ := by simp
      rw [hb]
      have hs : (∑ x ∈ partitionCell cell i, g x) ≤ B * (partitionCell cell i).card := by
        calc
          _ ≤ ∑ _x ∈ partitionCell cell i, B := Finset.sum_le_sum (fun x _ => hg x)
          _ = _ := by simp [mul_comm]
      exact hs.trans (le_add_of_nonneg_left (mul_nonneg hτ (Nat.cast_nonneg _)))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hcell i)
  rw [sum_partitionCell, Finset.sum_add_distrib, ← Finset.mul_sum, card_partitionCell_sum,
    ← Finset.mul_sum, sum_partitionCell] at hsum
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hupper : (𝔼 x, g x) ≤ τ + B * (𝔼 x, b x) := by
    rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
    apply (div_le_iff₀ hN).mpr
    convert hsum using 1
    field_simp
  have hb : (𝔼 x, b x) ≤ ρ := hbad
  have hfinal := hupper.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hB))
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_good_frozen_partition_score {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    (cell : Ω → I) (good : I → Prop) [DecidablePred good]
    (a W : Ω → ℝ) (V : I → Ω → ℝ) {B τ ρ ε S : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (ha : ∀ x, |a x| ≤ 1) (hW : ∀ x, a x * W x ≤ B)
    (hbad : (𝔼 x, if good (cell x) then (0 : ℝ) else 1) ≤ ρ)
    (hclose : ∀ x, dist (W x) (V (cell x) x) ≤ ε)
    (hscore : S ≤ 𝔼 x, a x * W x) (hbudget : τ + ε + B * ρ < S) :
    ∃ i, good i ∧ τ < 𝔼 x ∈ partitionCell cell i, a x * V i x := by
  obtain ⟨i, hi, hs⟩ := exists_good_partition_score cell good (fun x => a x * W x)
    hB (add_nonneg hτ hε) hW hbad hscore hbudget
  have hne : (partitionCell cell i).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [hz, Finset.expect_empty] at hs
    linarith
  have herr : (𝔼 x ∈ partitionCell cell i, a x * W x) ≤
      (𝔼 x ∈ partitionCell cell i, a x * V i x) + ε := by
    calc
      _ ≤ 𝔼 x ∈ partitionCell cell i, (a x * V i x + ε) := by
        apply Finset.expect_le_expect
        intro x hx
        apply unit_weight_score_error (ha x)
        simpa only [(mem_partitionCell _ _ _).mp hx] using hclose x
      _ = _ := by rw [Finset.expect_add_distrib, Finset.expect_const hne]
  exact ⟨i, hi, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {ι : Type*} {N : ι → ℕ} {q : ℕ}

noncomputable def center (A : ResidueBoxSlice N q) : ι → ℝ :=
  fun i => (A.start i : ℝ) / N i

noncomputable abbrev ofBlocks (H : ι → ℕ) (hq : 0 < q) (hH : ∀ i, 0 < H i)
    (a : ∀ i, (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).Label) :
    ResidueBoxSlice N q where
  start i := (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).start (a i)
  length i := (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).length (a i)
  inside i _j hj := (FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)).point_lt (a i) hj

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LieSubalgebraRepresentativeBudget
namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [LieRing L] [LieAlgebra ℚ L]

theorem lieSubalgebraRepresentativeHeight_le_exp (d r H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (lieSubalgebraRepresentativeHeight d r H : ℝ) ≤ Real.exp ((p + 2) ^ 11) :=
  rationalLieStructureHeight_inverse_budget d r H hp hd hr hH

theorem lieSubalgebraRepresentativeHeight_le_exp_parameter (d r H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (lieSubalgebraRepresentativeHeight d r H : ℝ) ≤
      Real.exp (lieSubalgebraRepresentativeParameter p) := by
  apply (lieSubalgebraRepresentativeHeight_le_exp d r H hp hd hr hH).trans
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 11 ≤ 12)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MarkedRefilteredModelBudget
namespace OAI

section

namespace Erdos3

theorem exists_markedRefilteredModelInput_budget (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      markedRefilteredModelInput A p ≤ (p + C) ^ C ∧
      ((markedRefilteredModelInput A p + 2) ^ 4 + markedRefilteredModelInput A p + 4) ^ 8 ≤
        (p + C) ^ C := by
  let Q : Polynomial ℕ := Polynomial.X +
    (Polynomial.X + (Polynomial.X + 4) ^ 5 + (Polynomial.X + 2) ^ 4 + 2) ^ 4 + 1
  let T : Polynomial ℕ := Q + (Q + 2) ^ 4
  let R : Polynomial ℕ := Polynomial.X + T + (T + Polynomial.C A) ^ A + 1
  let P : Polynomial ℕ := R + ((R + 2) ^ 4 + R + 4) ^ 8
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  have hr := (markedRefilteredModelInput_bounds A hp).2.2.2.2.2.2.1
  have hcost : 0 ≤
      ((markedRefilteredModelInput A p + 2) ^ 4 + markedRefilteredModelInput A p + 4) ^ 8 := by
    positivity
  have hsum : markedRefilteredModelInput A p +
      ((markedRefilteredModelInput A p + 2) ^ 4 + markedRefilteredModelInput A p + 4) ^ 8 ≤
      (p + C) ^ C := by
    simpa [P, R, T, Q, markedRefilteredModelInput, markedRefilteredMapInput,
      markedRefilteredBasisInput, adaptedMarkedMapHeightBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  exact ⟨(le_add_of_nonneg_right hcost).trans hsum, (le_add_of_nonneg_left hr).trans hsum⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.McShaneEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

theorem mcShaneEnvelope_le_add (f g : X → ℝ) (hf : ∀ x, 0 ≤ f x) {δ : ℝ}
    (hfg : ∀ x, f x ≤ g x + δ) (y : Y) :
    mcShaneEnvelope φ L f y ≤ mcShaneEnvelope φ L g y + δ := by
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro x
  have h := mcShaneEnvelope_le φ L f hf y x
  linarith [hfg x]

theorem mcShaneEnvelope_abs_sub_le (f g : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) {δ : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ δ) (y : Y) :
    |mcShaneEnvelope φ L f y - mcShaneEnvelope φ L g y| ≤ δ := by
  apply abs_le.mpr
  constructor
  · have h := mcShaneEnvelope_le_add φ L g f hg
      (fun x => by have hx := (abs_le.mp (hfg x)).1; linarith) y
    linarith
  · have h := mcShaneEnvelope_le_add φ L f g hf
      (fun x => by have hx := (abs_le.mp (hfg x)).2; linarith) y
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineWindowGoodKernelBound
namespace OAI

section

namespace Erdos3

theorem mem_integerProgressionSupport_iff (c : ℤ) (m H : ℕ) (hm : 0 < m) (x : ℤ) :
    x ∈ integerProgressionSupport c (m : ℤ) H ↔
      c ≤ x ∧ x < c + (m * H : ℕ) ∧ (x : ZMod m) = (c : ZMod m) := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  rw [integerProgressionSupport, mem_translateSupport, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, he⟩
    have hy' := Finset.mem_Ico.mp hy
    change (m : ℤ) * y = x - c at he
    have hx : x = c + (m : ℤ) * y := by omega
    constructor
    · nlinarith
    constructor
    · push_cast
      nlinarith
    · rw [hx]
      simp
  · rintro ⟨hlo, hhi, hr⟩
    have hz : ((x - c : ℤ) : ZMod m) = 0 := by simp [hr]
    obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - c) m).mp hz
    have hy0 : 0 ≤ y := by nlinarith
    have hyH : y < H := by push_cast at hhi; nlinarith
    exact ⟨y, Finset.mem_Ico.mpr ⟨hy0, hyH⟩, hy.symm⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

section

namespace Erdos3

theorem integerProgressionSupport_point (c : ℤ) (m H : ℕ) (hm : 0 < m) (j : ℕ) (hj : j < H) :
    c + (m : ℤ) * j ∈ integerProgressionSupport c (m : ℤ) H := by
  apply (mem_integerProgressionSupport_iff c m H hm _).mpr
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hj' : (j : ℤ) < H := by exact_mod_cast hj
  refine ⟨?_, ?_, ?_⟩
  · have := mul_nonneg hm'.le (Int.natCast_nonneg j)
    omega
  · push_cast
    nlinarith
  · simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NestedProgressionReindex
namespace OAI

section

namespace Erdos3

theorem exists_nested_progression_affine (c b : ℤ) {m d H L : ℕ}
    (hm : 0 < m) (hd : 0 < d) (hL : 0 < L)
    (hsub : integerProgressionSupport b d L ⊆ integerProgressionSupport c m H) :
    ∃ a s : ℤ, ∀ x : ℤ, 0 ≤ x → x < L →
      0 ≤ a + s * x ∧ a + s * x < H ∧ b + (d : ℤ) * x = c + m * (a + s * x) := by
  have hb := hsub (integerProgressionSupport_point b d L hd 0 hL)
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  obtain ⟨a, ha0, haH, hba⟩ := (mem_integerProgressionSupport_iff_parameter c m b H).mp hb
  by_cases hsingle : L = 1
  · refine ⟨a, 0, fun x hx0 hxL => ?_⟩
    have hx : x = 0 := by rw [hsingle] at hxL; omega
    simpa only [hx, mul_zero, add_zero] using And.intro ha0 (And.intro haH hba)
  · have hb1 := hsub (integerProgressionSupport_point b d L hd 1 (by omega))
    simp only [Nat.cast_one, mul_one] at hb1
    obtain ⟨a₁, _, _, hba₁⟩ := (mem_integerProgressionSupport_iff_parameter c m (b + d) H).mp hb1
    let s := a₁ - a
    have hs : (d : ℤ) = m * s := by dsimp [s]; nlinarith [hba, hba₁]
    refine ⟨a, s, fun x hx0 hxL => ?_⟩
    have hinner : b + (d : ℤ) * x ∈ integerProgressionSupport b d L :=
      (mem_integerProgressionSupport_iff_parameter b d _ L).mpr ⟨x, hx0, hxL, rfl⟩
    obtain ⟨j, hj0, hjH, hj⟩ := (mem_integerProgressionSupport_iff_parameter c m _ H).mp (hsub hinner)
    have hpoint : b + (d : ℤ) * x = c + m * (a + s * x) := by rw [hba, hs]; ring
    have hj' : j = a + s * x :=
      mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0) (add_left_cancel (hj.symm.trans hpoint))
    exact ⟨hj' ▸ hj0, hj' ▸ hjH, hpoint⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NestedBoxReindex
namespace OAI

section

namespace Erdos3

theorem exists_nested_box_affine {I : Type*} [Fintype I] [DecidableEq I]
    (c b : I → ℤ) {m d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (H L : I → ℕ) (hL : ∀ i, 0 < L i)
    (hsub : commonStrideBox b d L ⊆ commonStrideBox c m H) :
    ∃ (A : I → I → ℤ) (a : I → ℤ), ∀ x ∈ integerBox L,
      integerAffineMap A a x ∈ integerBox H ∧
      commonStridePoint b d x = commonStridePoint c m (integerAffineMap A a x) := by
  have haxis (i : I) : (integerProgressionSupport (b i) d (L i)).Nonempty :=
    Finset.card_pos.mp (by simpa only [card_integerProgressionSupport _ _ _ hd] using hL i)
  have hcoord (i : I) := piFinset_axis_subset _ _ haxis hsub i
  choose a s ha using fun i => exists_nested_progression_affine (c i) (b i) hm hd (hL i) (hcoord i)
  refine ⟨(fun i j => if i = j then s i else 0), a, fun x hx => ?_⟩
  rw [integerAffineMap_diagonal]
  have hb (i : I) := ha i (x i) ((mem_integerBox L x).mp hx i).1 ((mem_integerBox L x).mp hx i).2
  refine ⟨(mem_integerBox H _).mpr (fun i => ⟨(hb i).1, (hb i).2.1⟩), ?_⟩
  funext i
  exact (hb i).2.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisAxisNormalization
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalizedAxisBasis_apply (b : Basis I ℝ E) (i : I) :
    normalizedAxisBasis b i = (basisAxisScale b i : ℝ) • b i := by
  simp only [normalizedAxisBasis, Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]

theorem normalizedAxisBasis_norm (b : Basis I ℝ E) (i : I) :
    ‖normalizedAxisBasis b i‖ = (basisAxisScale b i : ℝ) * ‖b i‖ := by
  rw [normalizedAxisBasis_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]

theorem normalizedAxisBasis_norm_bounds (b : Basis I ℝ E) {B : ℝ}
    (hb : ∀ i, ‖b i‖ ≤ B) (i : I) :
    1 ≤ ‖normalizedAxisBasis b i‖ ∧ ‖normalizedAxisBasis b i‖ ≤ B + 1 := by
  rw [normalizedAxisBasis_norm]
  refine ⟨(basisAxisScale_mul_norm b i).1, ?_⟩
  have h := (basisAxisScale_mul_norm b i).2
  have hi := hb i
  linarith

variable [Fintype I]

theorem normalizedAxisBasis_norm_product (b : Basis I ℝ E) :
    (∏ i, ‖normalizedAxisBasis b i‖) = (∏ i, (basisAxisScale b i : ℝ)) * ∏ i, ‖b i‖ := by
  simp only [normalizedAxisBasis_norm, Finset.prod_mul_distrib]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NormalizedBasisBounds
namespace OAI

section

namespace Erdos3

open Module MeasureTheory
open scoped BigOperators

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem covolume_basis_le_norm_bound (o : OrthonormalBasis I ℝ E) (b : Basis I ℝ E)
    {H : ℝ} (hb : ∀ i, ‖b i‖ ≤ H) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ≤
      (Fintype.card I).factorial * H ^ Fintype.card I := by
  classical
  rw [covolume_basis_eq_orthonormal_det o b, Basis.det_apply]
  apply matrix_det_abs_le_uniform_bound
  intro i j
  exact (orthonormal_basis_coordinate_abs_le o (b j) i).trans (hb j)

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem normalizedAxisBasis_covolume (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) :
    ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) =
      (∏ i, (basisAxisScale b i : ℝ)) * ZLattice.covolume (span ℤ (Set.range b)) :=
  covolume_basis_scale o b (normalizedAxisBasis b) (fun i => (basisAxisScale b i : ℝ))
    (fun _ => Nat.cast_nonneg _) (normalizedAxisBasis_apply b)

theorem normalizedAxisBasis_covolume_lower (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {D : ℝ} (hD : 0 < D)
    (hb : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b))) :
    1 / D ≤ ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) := by
  have hprod : 1 ≤ ∏ i, ‖normalizedAxisBasis b i‖ := by
    apply Finset.one_le_prod
    intro i _
    rw [normalizedAxisBasis_norm]
    exact (basisAxisScale_mul_norm b i).1
  have hupper : (∏ i, ‖normalizedAxisBasis b i‖) ≤
      D * ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) := by
    rw [normalizedAxisBasis_norm_product, normalizedAxisBasis_covolume o b]
    calc
      _ ≤ (∏ i, (basisAxisScale b i : ℝ)) *
          (D * ZLattice.covolume (span ℤ (Set.range b))) :=
        mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
      _ = _ := by ring
  apply (div_le_iff₀ hD).mpr
  simpa only [mul_comm] using hprod.trans hupper

theorem normalizedAxisBasis_covolume_upper (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {B : ℝ} (hb : ∀ i, ‖b i‖ ≤ B) :
    ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) ≤
      (n.factorial : ℝ) * (B + 1) ^ n := by
  simpa only [Fintype.card_fin] using covolume_basis_le_norm_bound o (normalizedAxisBasis b)
    (fun i => (normalizedAxisBasis_norm_bounds b hb i).2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem normalizedAxisBasis_synthesis_bound (b : Basis (Fin n) ℝ E) {B : ℝ}
    (hb : ∀ i, ‖b i‖ ≤ B) (x : Fin n → ℝ) :
    ‖(normalizedAxisBasis b).equivFun.symm x‖ ≤ (n : ℝ) * (B + 1) * ‖x‖ :=
  basis_synthesis_norm_le (normalizedAxisBasis b)
    (fun i => (normalizedAxisBasis_norm_bounds b hb i).2) x

theorem normalizedAxisBasis_reciprocal_covolume (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {q : ℝ}
    (hq : q * ZLattice.covolume (span ℤ (Set.range b)) = 1) :
    q / (∏ i, (basisAxisScale b i : ℝ)) =
      1 / ZLattice.covolume (span ℤ (Set.range (normalizedAxisBasis b))) := by
  have hc := (ZLattice.covolume_pos (span ℤ (Set.range b)) volume).ne'
  have hp : (∏ i, (basisAxisScale b i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (basisAxisScale_pos b i))).ne'
  have heq : q = 1 / ZLattice.covolume (span ℤ (Set.range b)) := (eq_div_iff hc).mpr hq
  rw [heq, normalizedAxisBasis_covolume o b]
  field_simp [hp, hc]

theorem normalizedAxisBasis_covolume_ratio_bounds (o : OrthonormalBasis (Fin n) ℝ E)
    (b : Basis (Fin n) ℝ E) {B D q : ℝ} (hD : 0 < D)
    (hb : ∀ i, ‖b i‖ ≤ B)
    (hprod : (∏ i, ‖b i‖) ≤ D * ZLattice.covolume (span ℤ (Set.range b)))
    (hq : q * ZLattice.covolume (span ℤ (Set.range b)) = 1) :
    1 / ((n.factorial : ℝ) * (B + 1) ^ n) ≤ q / (∏ i, (basisAxisScale b i : ℝ)) ∧
      q / (∏ i, (basisAxisScale b i : ℝ)) ≤ D := by
  rw [normalizedAxisBasis_reciprocal_covolume o b hq]
  have hpos := ZLattice.covolume_pos (span ℤ (Set.range (normalizedAxisBasis b))) volume
  refine ⟨div_le_div_of_nonneg_left zero_le_one hpos
    (normalizedAxisBasis_covolume_upper o b hb), ?_⟩
  apply (div_le_iff₀ hpos).mpr
  have h := (div_le_iff₀ hD).mp (normalizedAxisBasis_covolume_lower o b hD hprod)
  simpa only [mul_comm] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrthogonalBasisChart
namespace OAI

section

namespace Erdos3

open Module

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem orthogonalBasisChart_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖b.equivFun x‖ ≤ C * ‖x‖) (x : E) :
    ‖orthogonalBasisChart W b x‖ ≤ (1 + C) * ‖x‖ := by
  rw [orthogonalBasisChart_apply, Prod.norm_def]
  apply max_le
  · have h := W.norm_orthogonalProjectionOnto_apply_le x
    nlinarith [norm_nonneg x]
  · calc
      _ ≤ C * ‖Wᗮ.orthogonalProjectionOnto x‖ := hb _
      _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_left (Wᗮ.norm_orthogonalProjectionOnto_apply_le x) hC
      _ ≤ _ := by nlinarith [norm_nonneg x]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmptyLayerChartBounds
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem normalizedOrthogonalChart_symm_norm_le (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, ‖b i‖ ≤ B) (p : W × (Fin n → ℝ)) :
    ‖(normalizedOrthogonalChart W b).symm p‖ ≤ (1 + (n : ℝ) * (B + 1)) * ‖p‖ := by
  apply orthogonalBasisChart_symm_norm_le W (normalizedAxisBasis b) (by positivity)
  exact normalizedAxisBasis_synthesis_bound b hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Submodule _root_.Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem orthogonalLatticeImage_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E)
    [IsZLattice ℝ (latticeSection (euclideanDualLattice Λ) W)] :
    DiscreteTopology (orthogonalLatticeImage Λ W) := by
  have hdis : DiscreteTopology (euclideanDualLattice (latticeSection (euclideanDualLattice Λ) W)) :=
    euclideanDualLattice_discrete _
  have hd : IsDiscrete (euclideanDualLattice (latticeSection (euclideanDualLattice Λ) W) : Set W) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr hdis
  exact isDiscrete_iff_discreteTopology.mp (hd.mono (orthogonalLatticeImage_le_dual_section Λ W))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeSheetHaar
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem orthogonalLattice_covolume_sq (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E)
    [IsZLattice ℝ (latticeSection Λ Wᗮ)]
    [DiscreteTopology (orthogonalLatticeImage Λ W)] [IsZLattice ℝ (orthogonalLatticeImage Λ W)] :
    ZLattice.covolume Λ ^ 2 = ZLattice.covolume (latticeSection Λ Wᗮ) ^ 2 *
      ZLattice.covolume (orthogonalLatticeImage Λ W) ^ 2 := by
  classical
  let bK := Free.chooseBasis ℤ (latticeSection Λ Wᗮ)
  let bP := Free.chooseBasis ℤ (orthogonalLatticeImage Λ W)
  obtain ⟨b, hbK, hbP⟩ := exists_orthogonal_lattice_split_basis Λ W bK bP
  let B := b.ofZLatticeBasis ℝ Λ
  let K := bK.ofZLatticeBasis ℝ (latticeSection Λ Wᗮ)
  let P := bP.ofZLatticeBasis ℝ (orthogonalLatticeImage Λ W)
  have hleft (i) : B (Sum.inl i) = (K i : E) := by
    simpa only [B, K, Basis.ofZLatticeBasis_apply] using hbK i
  have hspan : span ℝ (Set.range (fun i => B (Sum.inl i))) = Wᗮ := by
    rw [show (fun i => B (Sum.inl i)) = (fun i => (K i : E)) from funext hleft]
    change span ℝ (Set.range (Wᗮ.subtype ∘ K)) = Wᗮ
    rw [Set.range_comp, ← Submodule.map_span, K.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hright (j) : B (Sum.inr j) - Wᗮ.starProjection (B (Sum.inr j)) = (P j : E) := by
    have hp : W.starProjection (B (Sum.inr j)) = (P j : E) := by
      simpa only [B, P, Basis.ofZLatticeBasis_apply, Submodule.coe_orthogonalProjectionOnto_apply]
        using congrArg Subtype.val (hbP j)
    have hsum := W.starProjection_add_starProjection_orthogonal (B (Sum.inr j))
    rw [hp] at hsum
    exact (eq_sub_iff_add_eq.mpr hsum).symm
  have hKGram : (Matrix.gram ℝ (fun i => B (Sum.inl i))).det =
      ZLattice.covolume (latticeSection Λ Wᗮ) ^ 2 := by
    have hg : Matrix.gram ℝ (fun i => B (Sum.inl i)) = Matrix.gram ℝ K := by
      ext i j
      simp only [Matrix.gram_apply, hleft]
      rfl
    rw [hg]
    exact (lattice_covolume_sq_eq_gram (latticeSection Λ Wᗮ) bK).symm
  have hPGram : (Matrix.gram ℝ (fun j => B (Sum.inr j) -
      Wᗮ.starProjection (B (Sum.inr j)))).det =
      ZLattice.covolume (orthogonalLatticeImage Λ W) ^ 2 := by
    have hg : Matrix.gram ℝ (fun j => B (Sum.inr j) - Wᗮ.starProjection (B (Sum.inr j))) =
        Matrix.gram ℝ P := by
      ext i j
      simp only [Matrix.gram_apply, hright]
      rfl
    rw [hg]
    exact (lattice_covolume_sq_eq_gram (orthogonalLatticeImage Λ W) bP).symm
  have hblock := gram_det_orthogonal_block B
  dsimp only at hblock
  rw [hspan, hKGram, hPGram] at hblock
  rw [lattice_covolume_sq_eq_gram Λ b]
  exact hblock

theorem orthogonalLattice_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (W : Submodule ℝ E)
    [IsZLattice ℝ (latticeSection Λ Wᗮ)]
    [DiscreteTopology (orthogonalLatticeImage Λ W)] [IsZLattice ℝ (orthogonalLatticeImage Λ W)] :
    ZLattice.covolume Λ = ZLattice.covolume (latticeSection Λ Wᗮ) *
      ZLattice.covolume (orthogonalLatticeImage Λ W) := by
  apply (sq_eq_sq₀ (ZLattice.covolume_pos Λ volume).le
    (mul_nonneg (ZLattice.covolume_pos (latticeSection Λ Wᗮ) volume).le
      (ZLattice.covolume_pos (orthogonalLatticeImage Λ W) volume).le)).mp
  simpa only [mul_pow] using orthogonalLattice_covolume_sq Λ W

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanShortLatticeBasis
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory BohrLattice.MinkowskiSecondBox
open scoped BigOperators

theorem exists_short_euclidean_lattice_basis {E A : Type*} {n : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (o : OrthonormalBasis (Fin n) ℝ E) (v : A → E) {R : ℝ}
    (hspan : span ℝ (Set.range v) = ⊤) (hmem : ∀ a, v a ∈ Λ)
    (hnorm : ∀ a, ‖v a‖ ≤ R) :
    ∃ b : Basis (Fin n) ℝ E,
      span ℤ (Set.range b) = Λ ∧
      (∏ i, ‖b i‖) ≤ (n : ℝ) ^ n * minkowskiSecondConstant n * ZLattice.covolume Λ ∧
      ∀ i, ‖b i‖ ≤ (n : ℝ) * n.factorial * minkowskiSecondConstant n * R := by
  classical
  let e := orthonormalChart o
  let L := orthonormalCoordinateLattice Λ o
  let B := IsZLattice.basis L
  let b₀ := B.ofZLatticeBasis ℝ L
  let u := fun a => e.symm (v a)
  have huSpan : span ℝ (Set.range u) = ⊤ := by
    change span ℝ (Set.range (e.symm.toLinearMap ∘ v)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, hspan, Submodule.map_top]
    exact e.symm.toLinearEquiv.range
  have huMem : ∀ a, u a ∈ span ℤ (Set.range b₀) := by
    intro a
    rw [show span ℤ (Set.range b₀) = L from B.ofZLatticeBasis_span ℝ L]
    change e (e.symm (v a)) ∈ Λ
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hmem a
  have huNorm : ∀ a, ‖u a‖ ≤ R := fun a =>
    (orthonormalChart_symm_norm_le o (v a)).trans (hnorm a)
  obtain ⟨c, hcSpan, hcProd, hcNorm⟩ := exists_short_same_lattice_basis b₀ u huSpan huMem huNorm
  let b := c.map e.toLinearEquiv
  have hb (i) : b i = e (c i) := by simp [b]
  have hmap : L.map (e.toLinearMap.restrictScalars ℤ) = Λ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e (e.symm y) ∈ Λ
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy
  have hbSpan : span ℤ (Set.range b) = Λ := by
    calc
      _ = (span ℤ (Set.range c)).map (e.toLinearMap.restrictScalars ℤ) := by
        rw [Submodule.map_span, ← Set.range_comp]
        congr 2
      _ = L.map (e.toLinearMap.restrictScalars ℤ) := by
        rw [hcSpan, show span ℤ (Set.range b₀) = L from B.ofZLatticeBasis_span ℝ L]
      _ = Λ := hmap
  have hdet : |(Matrix.of c).det| = ZLattice.covolume Λ := by
    calc
      _ = |(Matrix.of b₀).det| := abs_det_eq_of_same_integer_span c b₀ hcSpan
      _ = ZLattice.covolume L := by
        have hb₀ : (b₀ : Fin n → Fin n → ℝ) = fun i => (B i : Fin n → ℝ) :=
          funext (fun i => Basis.ofZLatticeBasis_apply ℝ L B i)
        rw [hb₀]
        exact (ZLattice.covolume_eq_det L B).symm
      _ = ZLattice.covolume Λ := orthonormalCoordinateLattice_covolume Λ o
    rfl
  have hbNorm (i) : ‖b i‖ ≤ (n : ℝ) * ‖c i‖ := by
    rw [hb]
    simpa only [Fintype.card_fin] using orthonormalChart_norm_le o (c i)
  refine ⟨b, hbSpan, ?_, ?_⟩
  · calc
      _ ≤ ∏ i, (n : ℝ) * ‖c i‖ :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hbNorm i)
      _ = (n : ℝ) ^ n * ∏ i, ‖c i‖ := by simp [Finset.prod_mul_distrib]
      _ ≤ (n : ℝ) ^ n * (minkowskiSecondConstant n * ZLattice.covolume Λ) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
        simpa only [hdet] using hcProd
      _ = _ := by ring
  · intro i
    calc
      _ ≤ (n : ℝ) * ‖c i‖ := hbNorm i
      _ ≤ (n : ℝ) * ((n.factorial : ℝ) * minkowskiSecondConstant n * R) :=
        mul_le_mul_of_nonneg_left (hcNorm i) (Nat.cast_nonneg _)
      _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmptyLayerDetectionGeometry
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedDensityCovolumeRatio_pos
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)] :
    0 < mixedDensityCovolumeRatio W b :=
  div_pos (ZLattice.covolume_pos _ volume)
    (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (basisAxisScale_pos b i)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def comparableBoxPartitions {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) : ∀ i, FiniteProgressionPartition (N i) :=
  fun i => FiniteProgressionPartition.mergedIntervals (N i) (H i) (hH i) (hHN i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def scalarCubeResidueCutoffBudget (I : Type*) [Fintype I] [DecidableEq I]
    (A r : ℝ≥0) (L M : ℕ) : ℝ :=
  scalarCubeBoundaryConstant I * r +
    (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) +
      scalarCubeCutoffLipschitzConstant I A r) * ((M : ℝ) / L)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

theorem positiveImageExtension_nonexpansive (f g : X → ℂ)
    (hf : ∀ x, 0 ≤ (f x).re) (hg : ∀ x, 0 ≤ (g x).re)
    {δ : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ δ) (y : Y) :
    ‖positiveImageExtension φ L f y - positiveImageExtension φ L g y‖ ≤ δ := by
  have henv := mcShaneEnvelope_abs_sub_le φ L (fun x => (f x).re) (fun x => (g x).re)
    hf hg (fun x => (Complex.abs_re_le_norm (f x - g x)).trans (hfg x)) y
  have hclip := positiveClip_lipschitz.dist_le_mul
    (mcShaneEnvelope φ L (fun x => (f x).re) y : ℂ)
    (mcShaneEnvelope φ L (fun x => (g x).re) y : ℂ)
  have hbound : ‖positiveImageExtension φ L f y - positiveImageExtension φ L g y‖ ≤
      |mcShaneEnvelope φ L (fun x => (f x).re) y - mcShaneEnvelope φ L (fun x => (g x).re) y| := by
    simpa only [positiveImageExtension, NNReal.coe_one, one_mul, dist_eq_norm,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hclip
  exact hbound.trans henv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeMarkedQuotientHeightBudget
namespace OAI

section

namespace Erdos3

theorem exists_nativeMarkedQuotientHeightBudget (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + A) ^ A ≤ (p + C) ^ C ∧
      quotientInducedMapHeightBudget ((p + A) ^ A) ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  let R : Polynomial ℕ := Q + (Q + 3) ^ 7 + 1
  let B : Polynomial ℕ := ((R + 2) ^ 4 + R + 2) ^ 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (Q + B)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hsum : (p + A) ^ A + quotientInducedMapHeightBudget ((p + A) ^ A) ≤
      (p + C) ^ C := by
    simpa [Q, R, B, quotientInducedMapHeightBudget, Polynomial.eval₂_pow] using hbound p hp
  have hq : 0 ≤ (p + A) ^ A := pow_nonneg (add_nonneg hp (Nat.cast_nonneg A)) A
  have hb : 0 ≤ quotientInducedMapHeightBudget ((p + A) ^ A) := by
    unfold quotientInducedMapHeightBudget
    positivity
  exact ⟨(le_add_of_nonneg_right hb).trans hsum,
    (le_add_of_nonneg_left hq).trans hsum⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeOptionProductBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped NNReal

theorem exists_optionProductMetric_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (d : Option ι → ℕ) {p : ℝ},
      0 ≤ p → (Fintype.card (Option ι) : ℝ) ≤ p → (∀ i, (d i : ℝ) ≤ p) →
      (((1 + productMetricBound (fun i => d (some i))) * productMetricBound d : ℝ≥0) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let T := 2 * X * (X ^ 2 + X + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((1 + T) * T)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ d p hp hι hd
  have hι' : (Fintype.card ι : ℝ) ≤ p := by
    simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one] at hι
    linarith
  have hfull := productMetricBound_le d hp hι hd
  have hrest := productMetricBound_le (fun i => d (some i)) hp hι' (fun i => hd (some i))
  have hpoly : (1 + 2 * p * (p ^ 2 + p + 1)) * (2 * p * (p ^ 2 + p + 1)) ≤
      (p + C) ^ C := by
    simpa [T, X, Polynomial.eval₂_pow] using hbudget p hp
  calc
    _ ≤ (1 + 2 * p * (p ^ 2 + p + 1)) * (2 * p * (p ^ 2 + p + 1)) := by
      push_cast
      gcongr
    _ ≤ (p + C) ^ C := hpoly
    _ ≤ Real.exp ((p + C) ^ C) := by linarith [Real.add_one_le_exp ((p + C) ^ C)]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CopiedLayerSpace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

theorem copiedLayerMatrix_height {J K C : Type*} (B : Matrix J C ℚ) (e : K → ℚ)
    {H He : ℕ} (hH : 1 ≤ H) (hB : ∀ j c, RationalHeightLE (B j c) H)
    (he : ∀ k, RationalHeightLE (e k) He) :
    ∀ j c, RationalHeightLE (copiedLayerMatrix B e j c) (max H He) := by
  intro j c
  cases j <;> cases c
  · exact rationalHeightLE_zero (hH.trans (le_max_left _ _))
  · exact (hB _ _).mono (le_max_left _ _)
  · exact (he _).mono (le_max_right _ _)
  · exact rationalHeightLE_zero (hH.trans (le_max_left _ _))

theorem copiedLayerRows_height {J K V : Type*} (A : Matrix V J ℚ)
    {R : ℕ} (hR : 1 ≤ R) (hA : ∀ r j, RationalHeightLE (A r j) R) :
    ∀ r j, RationalHeightLE (copiedLayerRows (K := K) A r j) R := by
  intro r j
  cases j with
  | inl j => exact hA r j
  | inr _ => exact rationalHeightLE_zero hR

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AuxiliaryBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def boxAuxiliaryCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d : I → ℕ) (hd : ∀ i, 0 < d i)
    (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (x : IntegerResidueBox a (fun i => a i + N i) r b) : AuxiliaryBoxLabels P M d u :=
  fun i => intervalAuxiliaryCell (a i) (P i) (M i) (d i) (hd i) (u i) (r i) (b i) (hbase i) (x i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AuxiliaryBoxLaws
namespace OAI

section

namespace Erdos3

noncomputable def baseAuxiliaryBoxCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d : I → ℕ) (hd : ∀ i, 0 < d i)
    (u : I → ℤ) :
    IntegerResidueBox a (fun i => a i + N i) (fun i => (M i : ℤ)) u → AuxiliaryBoxLabels P M d u :=
  boxAuxiliaryCell a N P M d hd u (fun i => (M i : ℤ)) u (fun _ _ hx => hx)

noncomputable def refinedAuxiliaryBoxCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (M d J : I → ℕ) (hd : ∀ i, 0 < d i)
    (u w : I → ℤ) (hw : ∀ i, w i ≡ u i [ZMOD (M i : ℤ)]) :
    IntegerResidueBox a (fun i => a i + N i) (fun i => (M i * J i : ℕ)) w → AuxiliaryBoxLabels P M d u :=
  boxAuxiliaryCell a N P M d hd u (fun i => (M i * J i : ℕ)) w
    (fun i => refinedResidue_implies_base (M i) (J i) (u i) (w i) (hw i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionComplementCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s d : ℕ}

theorem productMetricBound_singleton (d : ℕ) :
    productMetricBound (fun _ : Unit => d) = coordinateLipschitzBound d d 1 := by
  simp [productMetricBound, Fintype.card_sigma]

theorem productMetricBound_singleton_le_exp {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (productMetricBound (fun _ : Unit => d) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
  rw [productMetricBound_singleton]
  exact coordinateLipschitzBound_le_exp d d 1 hp hd hd
    (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeIteratedDifferencing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mean_row_correlation_sq_le_product_derivatives {H G : Type*}
    [Fintype H] [Nonempty H] [AddCommGroup G] [Fintype G]
    (f u v : H → G → ℂ) (U V : G → H → G → ℂ) {B ε δ : ℝ}
    (hf : ∀ h n, ‖f h n‖ ≤ 1) (hv : ∀ h n, ‖v h n‖ ≤ 1) (hB : 0 ≤ B)
    (hU : ∀ k h n, ‖U k h n‖ ≤ B)
    (huerr : ∀ k h, (𝔼 n, ‖multiplicativeDerivative (u h) k n - U k h n‖) ≤ ε)
    (hverr : ∀ k h, (𝔼 n, ‖multiplicativeDerivative (v h) k n - V k h n‖) ≤ δ) :
    (𝔼 h, ‖𝔼 n, f h n * star (u h n * v h n)‖) ^ 2 ≤
      (𝔼 k, 𝔼 h, ‖𝔼 n, multiplicativeDerivative (f h) k n * star (U k h n * V k h n)‖) +
        (ε + B * δ) := by
  apply mean_row_correlation_sq_le_approximated_derivatives f
    (fun h n => u h n * v h n) (fun k h n => U k h n * V k h n) hf
  intro k h
  have heq : multiplicativeDerivative (fun n => u h n * v h n) k =
      fun n => multiplicativeDerivative (u h) k n * multiplicativeDerivative (v h) k n := by
    funext n
    simp only [multiplicativeDerivative, star_mul]
    ring
  rw [heq]
  apply mean_mul_error_le_separate _ _ _ _ hB _ (hU k h) (huerr k h) (hverr k h)
  intro n
  simp only [multiplicativeDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hv h n)).trans (hv h (n + k))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerProgressionSupport_subset_iff_fin (L H step : ℕ) (start : ℤ) :
    integerProgressionSupport start (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ) ↔
      ∀ t : Fin H, 0 ≤ start + (step : ℤ) * t.val ∧
        start + (step : ℤ) * t.val < L := by
  constructor
  · intro hs t
    apply Finset.mem_Ico.mp
    apply hs
    rw [integerProgressionSupport, mem_translateSupport]
    apply Finset.mem_image.mpr
    refine ⟨(t.val : ℤ), Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast t.isLt⟩, ?_⟩
    change (step : ℤ) * t.val = _
    ring
  · intro hi z hz
    rw [integerProgressionSupport, mem_translateSupport] at hz
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hz
    have hv' := Finset.mem_Ico.mp hv
    let t : Fin H := ⟨v.toNat, by omega⟩
    have ht : (t.val : ℤ) = v := Int.toNat_of_nonneg hv'.1
    have hi' := hi t
    rw [ht] at hi'
    change (step : ℤ) * v = _ at he
    apply Finset.mem_Ico.mpr
    constructor <;> omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoefficientLatticeCompact
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

theorem coefficientTorus_compact_of_lattice {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] :
    CompactSpace (CoefficientTorus (K := K) U) := by
  classical
  let Λ := fun j => latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))
  let : ∀ j, Module.Finite ℤ (Λ j) := fun j => ZLattice.module_finite ℝ (Λ j)
  let b := fun j => Module.Free.chooseBasis ℤ (Λ j)
  let e := fun j => (euclideanSubspaceArrayEquiv (U j)).toLinearEquiv.trans
    (LinearEquiv.piUnique ℝ (fun _ : Unit => U j))
  apply coefficientTorus_compact_of_basis U
    (fun j => ((b j).ofZLatticeBasis ℝ (Λ j)).map (e j))
  intro j i a
  have hi := (euclideanSubspaceArrayEquiv_mem_lattice (U j)
    ((b j i : Λ j) : euclideanSubspace (U j))).mpr (b j i).property
  simpa only [Basis.map_apply, Basis.ofZLatticeBasis_apply, e,
    LinearEquiv.trans_apply, LinearEquiv.piUnique_apply, Equiv.piUnique,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] using hi default a

end Erdos3.VectorPolynomial

end

end OAI
end


