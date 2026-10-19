-- Prove2me | Definitions.Def_OAIE3v2B093
-- name    : OAIE3v2B093
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:24:00.881466+00:00
-- url     : https://prove2.me/theorems/84198feb-a162-4a78-ac53-6f84b58b5f58
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 94 of 311
-- statement:
--   Definitions bundle 94 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B068`, `OAIE3v2B069`, `OAIE3v2B071`, `OAIE3v2B073`, `OAIE3v2B074`, `OAIE3v2B075` of this split.
--
--   Modules: `Dynamics/ArbitraryStepPrescribedBudget.lean`, `Dynamics/ConstructLayerResetScales.lean`, `Dynamics/ScalarCubePrimitiveBudget.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/CoveredMixedArrayImage.lean`, `Estimates/DenseCommonStrideCardRatio.lean`, `Estimates/DilationPairFiltration.lean`, `Estimates/MultidegreeDilationPair.lean`, `Estimates/QuotientInducedMark.lean`, `Estimates/SquarefreeSplitCount.lean`, `Geometry/MultidegreeCoordinateFreezing.lean`, `Geometry/MultidegreeCoordinateSplit.lean`, `Geometry/MultidegreeOrbitTransport.lean`, `Geometry/RealSquarefreeCoordinates.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/LatticeOrderedGenerators.lean`, `Nilpotent/BCHConjugationLinear.lean`, `Nilpotent/BCHLatticeImageGap.lean`, `Nilpotent/BCHOrderedReduction.lean`, `Nilpotent/BCHSubgroupGridExistence.lean`, `Nilpotent/VectorPolynomialSupportBracket.lean`, `Polynomial/BlockMonomialWeight.lean`, `Polynomial/ExtendedPolynomialValues.lean`, `Polynomial/MultidegreeDilationDegree.lean`, `Polynomial/PolynomialCoordinatePartition.lean`, `Polynomial/SchmidtShortDualVector.lean`, `Polynomial/WeightedPolynomialRestriction.lean`, `Probability/RelativeSliceFiniteLaw.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B068
import Definitions.Def_OAIE3v2B069
import Definitions.Def_OAIE3v2B071
import Definitions.Def_OAIE3v2B073
import Definitions.Def_OAIE3v2B074
import Definitions.Def_OAIE3v2B075

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*}

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem integralVector_denominator_mulVec (A : Matrix ι κ ℚ) (x : κ → ℚ)
    (hx : IntegralVector x) :
    IntegralVector ((matrixDenominator A : ℚ) • (A *ᵥ x)) := by
  obtain ⟨z, hz⟩ := hx
  have hx_eq : x = fun i => (z i : ℚ) := funext hz
  refine ⟨(clearedMatrix A) *ᵥ z, fun i => ?_⟩
  rw [← Matrix.smul_mulVec, ← clearedMatrix_cast, hx_eq]
  exact ((Int.castRingHom ℚ).map_mulVec (clearedMatrix A) z i).symm

theorem rational_embedding_grid_bounds (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ)
    (hCB : C * B = 1) :
    scaledIntegerGrid (matrixDenominator B * matrixDenominator C) ⊆
      {x | IntegralVector (B *ᵥ x)} ∧
    {x | IntegralVector (B *ᵥ x)} ⊆
      denominatorGrid (matrixDenominator B * matrixDenominator C) := by
  constructor
  · rintro x ⟨z, rfl⟩
    have hz : IntegralVector (fun i => (z i : ℚ)) := ⟨z, fun _ => rfl⟩
    have h := (integralVector_denominator_mulVec B _ hz).nat_smul (matrixDenominator C)
    simpa only [Set.mem_ofPred_eq, Matrix.mulVec_smul, smul_smul, Nat.cast_mul, mul_comm] using h
  · intro x hx
    have h := (integralVector_denominator_mulVec C (B *ᵥ x) hx).nat_smul (matrixDenominator B)
    rw [Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec] at h
    simpa only [denominatorGrid, Set.mem_ofPred_eq, smul_smul, Nat.cast_mul] using h

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem rational_preimage_grid_transport (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ)
    (hCB : C * B = 1) (l : ℕ) (Γ : Set (ι → ℚ))
    (hinner : scaledIntegerGrid l ⊆ Γ) (houter : Γ ⊆ denominatorGrid l) :
    scaledIntegerGrid (l * (matrixDenominator B * matrixDenominator C)) ⊆ B.mulVec ⁻¹' Γ ∧
      B.mulVec ⁻¹' Γ ⊆ denominatorGrid (l * (matrixDenominator B * matrixDenominator C)) := by
  constructor
  · rintro x ⟨z, rfl⟩
    apply hinner
    have hz : ((matrixDenominator B * matrixDenominator C : ℕ) : ℚ) •
        (fun i => (z i : ℚ)) ∈ scaledIntegerGrid (matrixDenominator B * matrixDenominator C) :=
      ⟨z, rfl⟩
    have h := scaled_grid_mulVec B l _ ((rational_embedding_grid_bounds B C hCB).1 hz)
    simpa only [smul_smul, Nat.cast_mul] using h
  · intro x hx
    have h := (integralVector_denominator_mulVec C ((l : ℚ) • (B *ᵥ x)) (houter hx)).nat_smul
      (matrixDenominator B)
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec] at h
    simpa only [denominatorGrid, Set.mem_ofPred_eq, smul_smul, Nat.cast_mul,
      mul_assoc, mul_left_comm, mul_comm] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem weighted_monomial_dilation (w : σ → ℕ) (r : R) (x : σ → R) (α : σ →₀ ℕ) :
    α.prod (fun i n => (r ^ w i * x i) ^ n) =
      r ^ Finsupp.weight w α * α.prod (fun i n => x i ^ n) := by
  classical
  simp only [Finsupp.prod, mul_pow, ← pow_mul, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
namespace OAI

section

namespace Erdos3

variable {ι σ : Type*} [Fintype ι]

omit [Fintype ι] in
theorem SquarefreeIndex.support_subset_of_add (a b c : SquarefreeIndex ι)
    (h : a.val + b.val = c.val) : a.val.support ⊆ c.val.support := by
  intro i hi
  apply Finsupp.mem_support_iff.mpr
  have ha := Finsupp.mem_support_iff.mp hi
  have hs := congrArg (fun u : ι →₀ ℕ => u i) h
  simp only [Finsupp.add_apply] at hs
  omega

abbrev SquarefreeSplit (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ) :=
  {p : SquarefreeIndex ι × SquarefreeIndex ι //
    p.1.val + p.2.val = c.val ∧ blockDegree π p.1.val = a ∧ blockDegree π p.2.val = b}

theorem squarefreeSplit_ext (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ)
    (p q : SquarefreeSplit π c a b) (h : p.val.1 = q.val.1) : p = q := by
  apply Subtype.ext
  apply Prod.ext h
  apply Subtype.ext
  have hs := p.property.1.trans q.property.1.symm
  rw [h] at hs
  exact add_left_cancel hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

theorem integerScalarCubeReference_mass (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    (integerScalarCubeReference I L hL).mass (integerScalarCubeSet I L) =
      ((integerScalarCubeSet I L).card : ℝ) / Fintype.card (IntegerScalarCubeBox I L) := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  unfold integerScalarCubeReference
  exact FiniteProbabilityWeights.uniform_mass _

theorem integerScalarCubeReference_mass_pos (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    0 < (integerScalarCubeReference I L hL).mass (integerScalarCubeSet I L) := by
  rw [integerScalarCubeReference_mass, integerScalarCubeBox_card]
  exact div_pos (by exact_mod_cast (integerScalarCubeSet_nonempty I L hL).card_pos)
    (by positivity)

noncomputable def integerScalarCubeWeights (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    FiniteProbabilityWeights (IntegerScalarCubeBox I L) := by
  classical
  exact (integerScalarCubeReference I L hL).condition (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL)


open scoped BigOperators Classical

end Erdos3


namespace Erdos3

theorem scalarCubeResidueReference_mass_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    (scalarCubeResidueDensityCap I M)⁻¹ ≤
      (integerScalarCubeReference I L hL).mass
        ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) := by
  let n := Fintype.card I + 1
  let H := L / (n * M)
  have hn : 0 < n := by dsimp [n]; omega
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hH : 0 < H := Nat.div_pos hsize (Nat.mul_pos hn hM)
  have hHL : n * (M * H) ≤ L := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_div_le L (n * M)
  have hc := scalarCubeResidueSet_card_lower I L M H m r hm hmM hH hHL
  have hfloor : (L : ℝ) ≤ 2 * ((n : ℝ) * M) * (H : ℝ) := by
    exact_mod_cast nat_div_half_lower (Nat.mul_pos hn hM) hsize
  have hratio : 1 / (4 * (n : ℝ) * M) ≤ (H : ℝ) / (2 * (L : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  calc
    _ = (1 / (4 * (n : ℝ) * M)) ^ n := by
      simp only [scalarCubeResidueDensityCap, n, one_div, inv_pow]
    _ ≤ ((H : ℝ) / (2 * (L : ℝ))) ^ n := pow_le_pow_left₀ (by positivity) hratio n
    _ = (H : ℝ) ^ n / (2 * (L : ℝ)) ^ n := div_pow _ _ _
    _ ≤ _ := by
      unfold integerScalarCubeReference
      rw [FiniteProbabilityWeights.uniform_mass, integerScalarCubeBox_card]
      push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc

theorem scalarCubeResidue_mass_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    (scalarCubeResidueDensityCap I M)⁻¹ ≤
      (integerScalarCubeWeights I L hL).mass (scalarCubeResidueSet I L m r) := by
  exact (scalarCubeResidueReference_mass_lower I L M hL m r hm hmM hsize).trans
    (FiniteProbabilityWeights.mass_inter_le_condition_mass _ _ _ _)

theorem scalarCubeResidue_mass_pos (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    0 < (integerScalarCubeWeights I L hL).mass (scalarCubeResidueSet I L m r) :=
  (inv_pos.mpr (scalarCubeResidueDensityCap_pos I M ((hm none).trans_le (hmM none)))).trans_le
    (scalarCubeResidue_mass_lower I L M hL m r hm hmM hsize)


open scoped BigOperators

noncomputable def scalarCubeResidueWeights (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    FiniteProbabilityWeights (IntegerScalarCubeBox I L) := by
  classical
  exact (integerScalarCubeWeights I L hL).condition (scalarCubeResidueSet I L m r)
    (scalarCubeResidue_mass_pos I L M hL m r hm hmM hsize)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ArbitraryStepPrescribedBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem arbitraryStep_prescribed_product_le (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) {step : ℕ} (hstep : 0 < step) :
    (∏ p : Pr, p.val ^ padicValNat p.val step) ≤ step :=
  Nat.le_of_dvd hstep (arbitraryStep_prescribed_product_dvd Pr hprime step)

theorem arbitraryStep_prescribed_product_cast_le (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) {step : ℕ} (hstep : 0 < step) :
    ((∏ p : Pr, p.val ^ padicValNat p.val step : ℕ) : ℝ) ≤ step := by
  exact_mod_cast arbitraryStep_prescribed_product_le Pr hprime hstep

theorem arbitraryStep_prescribed_product_exp_le (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) {step : ℕ} (hstep : 0 < step)
    {cost : ℝ} (hcost : (step : ℝ) ≤ 2 * Real.exp cost) :
    ((∏ p : Pr, p.val ^ padicValNat p.val step : ℕ) : ℝ) ≤
      Real.exp (cost + 1) := by
  calc
    _ ≤ (step : ℝ) := arbitraryStep_prescribed_product_cast_le Pr hprime hstep
    _ ≤ 2 * Real.exp cost := hcost
    _ ≤ Real.exp 1 * Real.exp cost :=
      mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ Real.exp 1)
        (Real.exp_pos cost).le
    _ = Real.exp (cost + 1) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include hnil

theorem lieBCH_sub_add_mem (I : LieIdeal ℚ L) (a b : L) (hab : ⁅a, b⁆ ∈ I) :
    lieBCH s a b - (a + b) ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  have hbracket : ⁅lieQuotientMap I a, lieQuotientMap I b⁆ = 0 := by
    rw [← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hab
  rw [map_sub, map_add, map_lieBCH,
    lieBCH_eq_add_of_lie_eq_zero (lie_quotient_lowerCentralSeries_eq_bot hnil I) hbracket, sub_self]

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem coord_zpow (g : NilpotentLieBCHGroup L s hnil) (n : ℤ) :
    (g ^ n).coord = n • g.coord := by
  cases n with
  | ofNat n =>
    change (g ^ (n : ℤ)).coord = (n : ℤ) • g.coord
    simpa only [zpow_natCast, natCast_zsmul] using coord_pow g n
  | negSucc n =>
    simp only [zpow_negSucc, coord_inv, coord_pow, negSucc_zsmul]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DilationPairFiltration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem dilationPairLayer_top_relation (q : ℚ) {x : L × L}
    (hx : x ∈ F.dilationPairLayer q s) : x.1 = q ^ s • x.2 := by
  have h : x.1 - q ^ s • x.2 ∈ F.layer (s + 1) := hx.2.2
  rw [F.terminal, Submodule.mem_bot, sub_eq_zero] at h
  exact h

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

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def strictUpperLayer (a : σ → ℕ) : LieIdeal ℚ L :=
  ⨆ i : σ, F.layerIdeal (a + Pi.single i 1)

theorem successor_le_strictUpperLayer (a : σ → ℕ) (i : σ) :
    F.layerIdeal (a + Pi.single i 1) ≤ F.strictUpperLayer a :=
  le_iSup (fun j => F.layerIdeal (a + Pi.single j 1)) i

theorem strictUpperLayer_le_layer (a : σ → ℕ) :
    F.strictUpperLayer a ≤ F.layerIdeal a := by
  apply iSup_le
  intro i
  exact F.antitone (fun j => Nat.le_add_right (a j) _)

theorem strictUpperLayer_antitone : Antitone F.strictUpperLayer := by
  intro a b hab
  apply iSup_le
  intro i
  exact (F.antitone (fun j => Nat.add_le_add_right (hab j) _)).trans
    (F.successor_le_strictUpperLayer a i)

theorem layer_le_strictUpperLayer {a b : σ → ℕ} (hab : a < b) :
    F.layerIdeal b ≤ F.strictUpperLayer a := by
  obtain ⟨i, hi⟩ := not_forall.mp hab.not_ge
  have hstep : a + Pi.single i 1 ≤ b := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Pi.add_apply, Pi.single_eq_same] using Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)
    · simpa only [Pi.add_apply, Pi.single_eq_of_ne hji, add_zero] using hab.le j
  exact (F.antitone hstep).trans (F.successor_le_strictUpperLayer a i)

theorem strictUpperLayer_le_ordinary (a : σ → ℕ) :
    (F.strictUpperLayer a).toSubmodule ≤ F.ordinary.layer ((∑ i, a i) + 1) := by
  rw [strictUpperLayer, LieSubmodule.iSup_toSubmodule]
  apply iSup_le
  intro i
  change F.layer (a + Pi.single i 1) ≤ _
  have hsum : (∑ j, (a + Pi.single i 1 : σ → ℕ) j) = (∑ j, a j) + 1 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    congr 1
    simp
  rw [← hsum]
  exact F.layer_le_ordinary (a + Pi.single i 1)

theorem strictUpperLayer_top : F.strictUpperLayer bound = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro i
  have hnot : ¬bound + Pi.single i 1 ≤ bound := by
    intro h
    have hh := h i
    simp only [Pi.add_apply, Pi.single_eq_same] at hh
    omega
  intro x hx
  change x = 0
  have h : x ∈ F.layer (bound + Pi.single i 1) := hx
  simpa only [F.terminal _ hnot, Submodule.mem_bot] using h

theorem strictUpper_lie_layer {a b : σ → ℕ} {x y : L}
    (hx : x ∈ F.strictUpperLayer a) (hy : y ∈ F.layer b) :
    ⁅x, y⁆ ∈ F.strictUpperLayer (a + b) := by
  change x ∈ ⨆ i : σ, F.layerIdeal (a + Pi.single i 1) at hx
  refine LieSubmodule.iSup_induction _ hx
    (motive := fun z => ⁅z, y⁆ ∈ F.strictUpperLayer (a + b)) ?_ ?_ ?_
  · intro i u hu
    apply F.successor_le_strictUpperLayer (a + b) i
    change ⁅u, y⁆ ∈ F.layer (a + b + Pi.single i 1)
    simpa only [add_right_comm a (Pi.single i 1) b] using F.lie_mem hu hy
  · simpa only [zero_lie] using (F.strictUpperLayer (a + b)).zero_mem
  · intro u v hu hv
    rw [LieRing.add_lie]
    exact (F.strictUpperLayer (a + b)).add_mem hu hv

theorem layer_lie_strictUpper {a b : σ → ℕ} {x y : L}
    (hx : x ∈ F.layer a) (hy : y ∈ F.strictUpperLayer b) :
    ⁅x, y⁆ ∈ F.strictUpperLayer (a + b) := by
  have h := (F.strictUpperLayer (b + a)).neg_mem (F.strictUpper_lie_layer hy hx)
  change ⁅x, y⁆ ∈ (F.strictUpperLayer (a + b)).toSubmodule
  simpa only [lie_skew, add_comm b a] using h

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {bound : σ → ℕ}

def piLayerEquiv (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound) (a : σ → ℕ) :
    (∀ i, (F i).layer a) ≃ₗ[ℚ] (pi F).layer a where
  toFun x := ⟨fun i => x i, (mem_pi_layer F a _).mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, (mem_pi_layer F a _).mp x.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def dilationPairLayer (q : ℚ) (a : σ → ℕ) : Submodule ℚ (L × L) :=
  scaledPairLayer (F.layer a) (F.strictUpperLayer a).toSubmodule (q ^ ∑ i, a i)

theorem mem_dilationPairLayer (q : ℚ) (a : σ → ℕ) (x : L × L) :
    x ∈ F.dilationPairLayer q a ↔ x.1 ∈ F.layer a ∧ x.2 ∈ F.layer a ∧
      x.1 - q ^ (∑ i, a i) • x.2 ∈ F.strictUpperLayer a := Iff.rfl

theorem dilationPairLayer_antitone (q : ℚ) : Antitone (F.dilationPairLayer q) := by
  intro a b hab x hx
  by_cases heq : a = b
  · subst b
    exact hx
  have hlt : a < b := lt_iff_le_not_ge.mpr ⟨hab, fun hba => heq (le_antisymm hab hba)⟩
  refine ⟨F.antitone hab hx.1, F.antitone hab hx.2.1, ?_⟩
  change x.1 - q ^ (∑ i, a i) • x.2 ∈ F.strictUpperLayer a
  have hdiff : x.1 - q ^ (∑ i, a i) • x.2 =
      (x.1 - q ^ (∑ i, b i) • x.2) + (q ^ (∑ i, b i) - q ^ (∑ i, a i)) • x.2 := by
    rw [sub_smul]
    abel
  rw [hdiff]
  exact (F.strictUpperLayer a).add_mem (F.strictUpperLayer_antitone hab hx.2.2)
    ((F.strictUpperLayer a).smul_mem _ (F.layer_le_strictUpperLayer hlt hx.2.1))

theorem dilationPairLayer_lie_mem (q : ℚ) {a b : σ → ℕ} {x y : L × L}
    (hx : x ∈ F.dilationPairLayer q a) (hy : y ∈ F.dilationPairLayer q b) :
    ⁅x, y⁆ ∈ F.dilationPairLayer q (a + b) := by
  refine ⟨F.lie_mem hx.1 hy.1, F.lie_mem hx.2.1 hy.2.1, ?_⟩
  change ⁅x.1, y.1⁆ - q ^ (∑ i, (a + b) i) • ⁅x.2, y.2⁆ ∈ F.strictUpperLayer (a + b)
  have hdiff : ⁅x.1, y.1⁆ - q ^ (∑ i, (a + b) i) • ⁅x.2, y.2⁆ =
      ⁅x.1 - q ^ (∑ i, a i) • x.2, y.1⁆ +
        q ^ (∑ i, a i) • ⁅x.2, y.1 - q ^ (∑ i, b i) • y.2⁆ := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, sub_lie, lie_sub,
      smul_lie, lie_smul, smul_sub, smul_smul, pow_add]
    abel
  rw [hdiff]
  have h₁ := F.strictUpper_lie_layer hx.2.2 hy.1
  have h₂ := F.layer_lie_strictUpper hx.2.1 hy.2.2
  rw [scaledPairDifference_apply] at h₁ h₂
  exact (F.strictUpperLayer (a + b)).add_mem h₁ ((F.strictUpperLayer (a + b)).smul_mem _ h₂)

theorem dilationPairLayer_le_ordinary (q : ℚ) (a : σ → ℕ) :
    F.dilationPairLayer q a ≤ F.ordinary.dilationPairLayer q (∑ i, a i) := by
  intro x hx
  exact ⟨F.layer_le_ordinary a hx.1, F.layer_le_ordinary a hx.2.1,
    F.strictUpperLayer_le_ordinary a hx.2.2⟩

theorem dilationPairLayer_le_subalgebra (q : ℚ) (a : σ → ℕ) (ha : 1 ≤ ∑ i, a i) :
    F.dilationPairLayer q a ≤ (F.ordinary.dilationPairSubalgebra q).toSubmodule :=
  (F.dilationPairLayer_le_ordinary q a).trans (F.ordinary.dilationPairLayer_antitone q ha)

theorem dilationPairLayer_terminal (q : ℚ) (a : σ → ℕ) (ha : ¬a ≤ bound) :
    F.dilationPairLayer q a = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Prod.ext
  · exact (Submodule.mem_bot ℚ).mp (F.terminal a ha ▸ hx.1)
  · exact (Submodule.mem_bot ℚ).mp (F.terminal a ha ▸ hx.2.1)

theorem dilationPairLayer_top_relation (q : ℚ) {x : L × L}
    (hx : x ∈ F.dilationPairLayer q bound) : x.1 = q ^ (∑ i, bound i) • x.2 := by
  have h : x.1 - q ^ (∑ i, bound i) • x.2 ∈ F.strictUpperLayer bound := hx.2.2
  rw [F.strictUpperLayer_top, LieSubmodule.mem_bot, sub_eq_zero] at h
  exact h

theorem dilationPairLayer_diagonal (q : ℚ) (a : σ → ℕ) {x : L} (hx : x ∈ F.layer a) :
    (q ^ (∑ i, a i) • x, x) ∈ F.dilationPairLayer q a :=
  ⟨(F.layer a).smul_mem _ hx, hx, by simp⟩

theorem dilationPairLayer_of_strictUpper (q : ℚ) (a : σ → ℕ) {x y : L}
    (hx : x ∈ F.strictUpperLayer a) (hy : y ∈ F.strictUpperLayer a) :
    (x, y) ∈ F.dilationPairLayer q a :=
  ⟨F.strictUpperLayer_le_layer a hx, F.strictUpperLayer_le_layer a hy,
    (F.strictUpperLayer a).sub_mem hx ((F.strictUpperLayer a).smul_mem _ hy)⟩

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L M N : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [LieRing N] [LieAlgebra ℚ N] {s t u : ℕ}
  {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
  {hN : LieModule.lowerCentralSeries ℚ N N u = ⊥}

theorem mapOfSteps_injective (φ : L →ₗ⁅ℚ⁆ M) (hφ : Function.Injective φ) :
    Function.Injective (mapOfSteps (hL := hL) (hM := hM) φ) := by
  intro g h heq
  exact ext (hφ (congrArg coord heq))

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem bchSubgroupCoordinates_comap_of_steps [DecidableEq κ]
    (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) :
    bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.mapOfSteps (hL := hM) φ)) =
      (LinearMap.toMatrix b e φ.toLinearMap).mulVec ⁻¹' bchSubgroupCoordinates e Γ := by
  ext x
  change ((⟨φ (b.equivFun.symm x)⟩ : NilpotentLieBCHGroup L s hL) ∈ Γ) ↔
    ((⟨e.equivFun.symm (LinearMap.toMatrix b e φ.toLinearMap *ᵥ x)⟩ :
      NilpotentLieBCHGroup L s hL) ∈ Γ)
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M)
  (φ : NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M s hM)

theorem homCoordinates_apply (g : NilpotentLieBCHGroup L s hnil) :
    homCoordinates e f φ (basisHomeomorph e g) = basisHomeomorph f (φ g) := by
  simp only [homCoordinates, Homeomorph.symm_apply_apply]

theorem homCoordinates_continuous (hφ : Continuous φ) : Continuous (homCoordinates e f φ) :=
  (basisHomeomorph f).continuous.comp (hφ.comp (basisHomeomorph e).symm.continuous)

theorem basisHomeomorph_zpow (g : NilpotentLieBCHGroup L s hnil) (n : ℤ) :
    basisHomeomorph e (g ^ n) = n • basisHomeomorph e g := by
  change e.equivFun (g ^ n).coord = n • e.equivFun g.coord
  rw [coord_zpow, map_zsmul]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (a : NilpotentLieBCHGroup L s hnil)

include e in
theorem continuous_conjugation : Continuous ((MulAut.conj a).toMonoidHom) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  exact (continuous_const.mul continuous_id).mul continuous_const

theorem contDiff_conjugationCoordinates (n : ℕ∞ω) :
    ContDiff ℝ n (homCoordinates e e (MulAut.conj a).toMonoidHom) := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e n
  exact ((contMDiff_basisHomeomorph e n).comp
    ((contMDiff_const.mul (contMDiff_basisHomeomorph_symm e n)).mul contMDiff_const)).contDiff

noncomputable def conjugationLinearMap : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  fderiv ℝ (homCoordinates e e (MulAut.conj a).toMonoidHom) 0

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M)
  (φ : NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M s hM)
  (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (hA : homCoordinates e f φ = A)

include hA

theorem linear_hom_basisHomeomorph (g : NilpotentLieBCHGroup L s hnil) :
    basisHomeomorph f (φ g) = A (basisHomeomorph e g) := by
  rw [← homCoordinates_apply e f φ, hA]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOrderedReduction
namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include he hnil

theorem bch_remainder_mem_tail (i : ℕ) (a : L) {b : L} (hb : b ∈ basisTail e i) :
    lieBCH s a b - (a + b) ∈ basisTail e (i + 1) :=
  lieBCH_sub_add_mem hnil (he.tailIdeal (i + 1)) a b (he.lie_mem_tail_succ i a hb)

theorem bch_low_coordinate (i : ℕ) (a : L) {b : L} (hb : b ∈ basisTail e i)
    (k : Fin d) (hk : k.val ≤ i) :
    e.repr (lieBCH s a b) k = e.repr a k + e.repr b k := by
  have h := he.bch_remainder_mem_tail hnil i a hb k (Nat.lt_succ_of_le hk)
  rw [map_sub, Finsupp.sub_apply, map_add, Finsupp.add_apply] at h
  exact sub_eq_zero.mp h

end Erdos3.IsCentralLieBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeOrderedGenerators
namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))

include he

def leadingCoordinateSubgroup (j : Fin d) : AddSubgroup ℚ where
  carrier := {q | ∃ g ∈ Γ, g.coord ∈ basisTail e j.val ∧ e.repr g.coord j = q}
  zero_mem' := ⟨1, Γ.one_mem, (basisTail e j.val).zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨g, hg, hgt, rfl⟩ ⟨h, hh, hht, rfl⟩
    refine ⟨g * h, Γ.mul_mem hg hh, ?_, ?_⟩
    · exact (NilpotentLieBCHGroup.subgroup (he.tailIdeal j.val).toLieSubalgebra).mul_mem hgt hht
    · exact he.bch_low_coordinate hnil j.val g.coord hht j le_rfl
  neg_mem' := by
    rintro a ⟨g, hg, hgt, rfl⟩
    exact ⟨g⁻¹, Γ.inv_mem hg, (basisTail e j.val).neg_mem hgt, by simp⟩

end Erdos3.IsCentralLieBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSquarefreeCoordinates
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def realSquarefreePolynomialEquiv :
    (ℝ ⊗[ℚ] SquarefreePolynomial ι L) ≃ₗ[ℝ] (SquarefreeIndex ι → ℝ ⊗[ℚ] L) := by
  classical
  exact ((squarefreePolynomialEquiv (ι := ι) (L := L)).baseChange ℚ ℝ _ _).trans
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : SquarefreeIndex ι => L))

theorem realSquarefreePolynomialEquiv_tmul (r : ℝ) (x : SquarefreePolynomial ι L)
    (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv (r ⊗ₜ[ℚ] x) c = r ⊗ₜ[ℚ] squarefreePolynomialEquiv x c := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtShortDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def polynomialExponentialSum (P : Polynomial ℝ) (N : ℕ) : ℂ :=
  ∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition
namespace OAI

section

namespace Erdos3

universe u

open Polynomial

def PolynomialCoordinatePartitionBound (k : ℕ) (K : ℝ) (p : ℕ) : Prop :=
  ∀ (ι : Type u) [Fintype ι] (P : ι → Polynomial ℝ),
    (∀ i, (P i).natDegree ≤ k) → ∀ (N H : ℕ), 0 < H →
    K * ((Fintype.card ι : ℝ) + 1) ≤ H →
    H ^ (p * (Fintype.card ι + 1) ^ (2 * k)) ≤ N →
    ∃ (Q : FiniteProgressionPartition N) (z : Q.Label → ι → ℝ) (m : Q.Label → ℕ → ι → ℤ),
      Fintype.card Q.Label * H ≤ 2 ^ k * N ∧
      ∀ i n, n < Q.length i → ∀ j,
        |(P j).eval ((Q.start i + Q.step i * n : ℕ) : ℝ) - m i n j - z i j| ≤ (k : ℝ) / H

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ τ R V : Type*} [DecidableEq σ] [CommRing R] [AddCommGroup V] [Module R V]

theorem substitute_update_add (f : σ → MvPolynomial τ R) (i : σ)
    (u v : MvPolynomial τ R) (p : VectorPolynomial σ R V)
    (hp : ∀ a, 1 < a i → coefficients p a = 0) :
    substitute (Function.update f i (u + v)) p =
      substitute (Function.update f i u) p + substitute (Function.update f i v) p -
      substitute (Function.update f i 0) p := by
  apply coefficients.injective
  ext b
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply, coefficients_substitute]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a i ≤ 1
  · rw [aeval_monomial_update_add (R := R) f i u v a ha,
      MvPolynomial.coeff_sub, MvPolynomial.coeff_add, sub_smul, add_smul]
  · simp only [hp a (Nat.lt_of_not_ge ha), smul_zero, add_zero, sub_zero]

theorem coefficients_substitute_update_sub_mem (P : Submodule R V)
    (f : σ → MvPolynomial τ R) (i : σ) (u v : MvPolynomial τ R)
    (p : VectorPolynomial σ R V) (hp : ∀ a, 0 < a i → coefficients p a ∈ P)
    (b : τ →₀ ℕ) :
    coefficients (substitute (Function.update f i u) p - substitute (Function.update f i v) p) b ∈ P := by
  classical
  simp only [map_sub, Finsupp.sub_apply, coefficients_substitute]
  rw [← Finset.sum_sub_distrib]
  apply P.sum_mem
  intro a _
  by_cases ha : a i = 0
  · rw [aeval_monomial_update_eq_of_zero (R := R) f i u v a ha, sub_self]
    exact P.zero_mem
  · exact P.sub_mem (P.smul_mem _ (hp a (Nat.pos_of_ne_zero ha)))
      (P.smul_mem _ (hp a (Nat.pos_of_ne_zero ha)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators

theorem multidegreeWeight_finsupp {σ : Type*} [Fintype σ] (c : σ → ℕ) (a : σ →₀ ℕ) :
    multidegreeWeight c (fun i => a i) = Finsupp.weight c a := by
  simp only [multidegreeWeight, Finsupp.weight_eq_sum, smul_eq_mul, mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

theorem splitCoordinatePolynomial_support (i : σ) (u : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1) (j : σ) :
    splitCoordinatePolynomial i u j ∈ weightedSupportLE (fun _ : Option σ => 1) 1 := by
  by_cases hj : j = i
  · subst j
    simpa only [splitCoordinatePolynomial, Function.update_self] using hu
  · rw [splitCoordinatePolynomial, Function.update_of_ne hj]
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : Option σ => 1) (Finsupp.single (some j) 1) (1 : ℚ)

theorem splitCoordinatePolynomial_zero_support (i j : σ) :
    splitCoordinatePolynomial i 0 j ∈
      weightedSupportLE (fun _ : Option σ => 1) (omittedCoordinateWeight i j) := by
  by_cases hj : j = i
  · subst j
    simp only [splitCoordinatePolynomial, Function.update_self, omittedCoordinateWeight, ite_true]
    exact Submodule.zero_mem _
  · simp only [splitCoordinatePolynomial, Function.update_of_ne hj, omittedCoordinateWeight, if_neg hj]
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : Option σ => 1) (Finsupp.single (some j) 1) (1 : ℚ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientInducedMark
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def quotientMultidegree (I : LieIdeal ℚ L) :
    MultidegreeLieFiltration σ (L ⧸ I) s bound where
  ordinary := F.ordinary.quotientLie I (by rw [F.ordinary.terminal]; exact bot_le)
  layer a := (F.layer a).map (lieQuotientMap I).toLinearMap
  antitone := fun _ _ hab => Submodule.map_mono (F.antitone hab)
  zero_eq_top := by
    rw [F.zero_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective I)
  lie_mem := by
    rintro a b x y ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨⁅p, q⁆, F.lie_mem hp hq, (lieQuotientMap I).map_lie p q⟩
  terminal := by
    intro a ha
    rw [F.terminal a ha, Submodule.map_bot]
  degree_eq := by
    intro n
    change (F.ordinary.layer n).map (lieQuotientMap I).toLinearMap = _
    rw [F.degree_eq]
    simp only [Submodule.map_iSup]

theorem quotientMultidegree_layer_eq_bot (I : LieIdeal ℚ L) (a : σ → ℕ)
    (ha : F.layer a ≤ I.toSubmodule) : (F.quotientMultidegree I).layer a = ⊥ := by
  apply bot_unique
  rintro x ⟨y, hy, rfl⟩
  exact (lieQuotientMap_eq_zero I y).mpr (ha hy)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeCoordinateFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

theorem freezingPolynomial_support (S : Finset σ) (b : σ → ℤ) (i : σ) :
    freezingPolynomial S b i ∈ weightedSupportLE (fun _ : S => 1) (retainedCoordinateWeight S i) := by
  by_cases hi : i ∈ S
  · simp only [freezingPolynomial, retainedCoordinateWeight, dif_pos hi, if_pos hi]
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : S => 1) (Finsupp.single (⟨i, hi⟩ : S) 1) (1 : ℚ)
  · simp only [freezingPolynomial, retainedCoordinateWeight, dif_neg hi, if_neg hi]
    exact weightedSupportLE_C _ _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeCoordinateSplit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

omit [DecidableEq σ] in
theorem adapted_coefficient_zero_of_coordinate (i : σ) (hi : bound i ≤ 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) (a : σ →₀ ℕ) (ha : 1 < a i) :
    coefficients p a = 0 := by
  have hn : ¬(fun j => a j) ≤ bound := by
    intro h
    exact (not_le_of_gt (hi.trans_lt ha)) (h i)
  have h := hp a
  simpa only [F.terminal _ hn, Submodule.mem_bot] using h

theorem adapted_coefficient_mem_coordinate (i : σ) {p : VectorPolynomial σ ℚ L}
    (hp : F.Adapted p) (a : σ →₀ ℕ) (ha : 0 < a i) :
    coefficients p a ∈ F.layer (Pi.single i 1) := by
  apply F.antitone (show Pi.single i 1 ≤ fun j => a j from ?_) (hp a)
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Pi.single_eq_same] using (Nat.succ_le_of_lt ha)
  · simp [hj]

theorem split_substitution_add (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    VectorPolynomial.substitute (splitCoordinatePolynomial i (u + v)) p =
      VectorPolynomial.substitute (splitCoordinatePolynomial i u) p +
      VectorPolynomial.substitute (splitCoordinatePolynomial i v) p -
      VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p :=
  substitute_update_add _ i u v p (F.adapted_coefficient_zero_of_coordinate i hi hp)

theorem split_substitution_sub_mem_coordinate (i : σ)
    (u v : MvPolynomial (Option σ) ℚ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p)
    (a : Option σ →₀ ℕ) :
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p -
      VectorPolynomial.substitute (splitCoordinatePolynomial i v) p) a ∈ F.layer (Pi.single i 1) :=
  coefficients_substitute_update_sub_mem (F.layer (Pi.single i 1)) _ i u v p
    (F.adapted_coefficient_mem_coordinate i hp) a

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultidegreeDilationDegree
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def dilationPairDegreeLayer (q : ℚ) (n : ℕ) : Submodule ℚ (L × L) :=
  ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), F.dilationPairLayer q a

theorem dilationPairLayer_le_degree (q : ℚ) (n : ℕ) (a : σ → ℕ) (ha : n ≤ ∑ i, a i) :
    F.dilationPairLayer q a ≤ F.dilationPairDegreeLayer q n :=
  le_iSup_of_le a (le_iSup_of_le ha le_rfl)

theorem dilationPairDegreeLayer_le_ordinary (q : ℚ) (n : ℕ) :
    F.dilationPairDegreeLayer q n ≤ F.ordinary.dilationPairLayer q n := by
  apply iSup_le
  intro a
  apply iSup_le
  intro ha
  exact (F.dilationPairLayer_le_ordinary q a).trans (F.ordinary.dilationPairLayer_antitone q ha)

theorem dilationPairDegree_higher (q : ℚ) (n : ℕ) (c d : ℚ) {x : L}
    (hx : x ∈ F.ordinary.layer (n + 1)) : (c • x, d • x) ∈ F.dilationPairDegreeLayer q n := by
  let φ : L →ₗ[ℚ] L × L := (c • LinearMap.id).prod (d • LinearMap.id)
  have hφ : F.ordinary.layer (n + 1) ≤ (F.dilationPairDegreeLayer q n).comap φ := by
    rw [F.degree_eq]
    apply iSup_le
    intro b
    apply iSup_le
    intro hb x hx
    obtain ⟨a, hab, ha⟩ := multidegree_exists_predecessor_above b n hb
    apply F.dilationPairLayer_le_degree q n a ha
    exact F.dilationPairLayer_of_strictUpper q a
      ((F.strictUpperLayer a).smul_mem c (F.layer_le_strictUpperLayer hab hx))
      ((F.strictUpperLayer a).smul_mem d (F.layer_le_strictUpperLayer hab hx))
  exact hφ hx

theorem dilationPairDegree_diagonal (q : ℚ) (n : ℕ) {x : L}
    (hx : x ∈ F.ordinary.layer n) : (q ^ n • x, x) ∈ F.dilationPairDegreeLayer q n := by
  let φ : L →ₗ[ℚ] L × L := ((q ^ n) • LinearMap.id).prod LinearMap.id
  have hφ : F.ordinary.layer n ≤ (F.dilationPairDegreeLayer q n).comap φ := by
    rw [F.degree_eq]
    apply iSup_le
    intro a
    apply iSup_le
    intro ha x hx
    change (q ^ n • x, x) ∈ F.dilationPairDegreeLayer q n
    by_cases hna : n = ∑ i, a i
    · apply F.dilationPairLayer_le_degree q n a ha
      simpa only [hna] using F.dilationPairLayer_diagonal q a hx
    · have hhigh : x ∈ F.ordinary.layer (n + 1) :=
        F.ordinary.antitone (by omega : n + 1 ≤ ∑ i, a i) (F.layer_le_ordinary a hx)
      simpa only [one_smul] using F.dilationPairDegree_higher q n (q ^ n) 1 hhigh
  exact hφ hx

theorem dilationPairDegreeLayer_eq (q : ℚ) (n : ℕ) :
    F.dilationPairDegreeLayer q n = F.ordinary.dilationPairLayer q n := by
  apply le_antisymm (F.dilationPairDegreeLayer_le_ordinary q n)
  intro x hx
  have hleft : (x.1 - q ^ n • x.2, (0 : L)) ∈ F.dilationPairDegreeLayer q n := by
    simpa only [one_smul, zero_smul, scaledPairDifference_apply] using
      F.dilationPairDegree_higher q n 1 0 hx.2.2
  have hright := F.dilationPairDegree_diagonal q n hx.2.1
  have heq : x = (x.1 - q ^ n • x.2, (0 : L)) + (q ^ n • x.2, x.2) := by
    apply Prod.ext <;> simp
  rw [heq]
  exact (F.dilationPairDegreeLayer q n).add_mem hleft hright

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

structure ScalarCubeLocalizationData (I : Type*) [Fintype I] [DecidableEq I] where
  length : ℕ
  modulusBound : ℕ
  length_pos : 0 < length
  modulus : Option I → ℕ
  residue : ∀ i, ZMod (modulus i)
  modulus_pos : ∀ i, 0 < modulus i
  modulus_le : ∀ i, modulus i ≤ modulusBound
  size : (Fintype.card I + 1) * modulusBound ≤ length
  gridSmall : scalarCubeGridBoundaryConstant I * ((modulusBound : ℝ) / length) <
    volume.real (scalarCubeDomain I)
  transitionBound : ℝ≥0
  transition_lipschitz : LipschitzWith transitionBound Real.smoothTransition
  radius : ℝ≥0
  radius_pos : 0 < radius
  weight : (Option I → ℝ) → ℝ
  weightBound : ℝ≥0
  weightLipschitz : ℝ≥0
  weightBound_pos : 0 < weightBound
  weight_range : ∀ x, 0 ≤ weight x ∧ weight x ≤ weightBound
  weight_lipschitz : LipschitzWith weightLipschitz weight
  normalized : (scalarCubeResidueWeights I length modulusBound length_pos modulus residue
    modulus_pos modulus_le size).mean (fun z => weight (fun i => (z i : ℝ) / length)) = 1
  mesh : ℝ
  mesh_pos : 0 < mesh
  mesh_le_one : mesh ≤ 1
  meshLarge : 2 * (modulusBound : ℝ) ≤ mesh * length
  margin : ((Fintype.card I : ℝ) + 1) * mesh < radius

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

structure NormalizedScalarCubeSource (I : Type*) [Fintype I] [DecidableEq I] where
  length : ℕ
  modulusBound : ℕ
  length_pos : 0 < length
  modulus : Option I → ℕ
  residue : ∀ i, ZMod (modulus i)
  modulus_pos : ∀ i, 0 < modulus i
  modulus_le : ∀ i, modulus i ≤ modulusBound
  size : (Fintype.card I + 1) * modulusBound ≤ length
  weight : (Option I → ℝ) → ℝ
  weightBound : ℝ≥0
  weightLipschitz : ℝ≥0
  weightBound_pos : 0 < weightBound
  weight_range : ∀ x, 0 ≤ weight x ∧ weight x ≤ weightBound
  weight_lipschitz : LipschitzWith weightLipschitz weight
  normalized : (scalarCubeResidueWeights I length modulusBound length_pos modulus residue
    modulus_pos modulus_le size).mean (fun z => weight (fun i => (z i : ℝ) / length)) = 1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def lengthLoss : ℝ := 2 * d.modulusBound / d.mesh

end ScalarCubeLocalizationData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubePrimitiveBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

structure ScalarCubePrimitiveBudget {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A : ℝ≥0) (U : ℝ) : Prop where
  one_le : 1 ≤ U
  dimension_le : (Fintype.card I : ℝ) + 1 ≤ U
  modulus_le : (s.modulusBound : ℝ) ≤ U
  weight_le : (s.weightBound : ℝ) ≤ U
  weightLipschitz_le : (s.weightLipschitz : ℝ) ≤ U
  boundary_le : scalarCubeBoundaryConstant I ≤ U
  grid_le : 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) ≤ U
  derivative_le : scalarCubeCutoffDerivativeNumerator I A ≤ U
  density_le : paddedResidueDensityCap I s.modulusBound ≤ U

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BlockMonomialWeight
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ R : Type*} [Fintype ι] [Fintype σ] [CommMonoid R]

theorem blockExponent_weight (π : ι → σ) (a : ι →₀ ℕ) (x : σ → R) :
    (a.prod fun j n => x (π j) ^ n) = (blockExponent π a).prod (fun i n => x i ^ n) := by
  classical
  rw [a.prod_fintype _ (fun _ => pow_zero _),
    (blockExponent π a).prod_fintype _ (fun _ => pow_zero _)]
  simp only [blockExponent_apply]
  calc
    (∏ j, x (π j) ^ a j) =
        ∏ i, ∏ j ∈ Finset.univ.filter (fun j => π j = i), x (π j) ^ a j :=
      (Finset.prod_fiberwise Finset.univ π (fun j => x (π j) ^ a j)).symm
    _ = ∏ i, x i ^ blockDegree π a i := by
      apply Finset.prod_congr rfl
      intro i _
      rw [blockDegree_apply, ← Finset.sum_filter, ← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredMixedArrayImage
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (O j)]
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

noncomputable def canonicalCoefficientJetArrays
    (x : CoefficientSamplerArrays (K := K) I n) :
    ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ) := fun j =>
  mixedArrayIntegerImage (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) (x j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.VectorPolynomialSupportBracket
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem coefficientSupport_lie {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    {S T U : Set (σ →₀ ℕ)} (hST : ∀ a ∈ S, ∀ b ∈ T, a + b ∈ U)
    {p q : VectorPolynomial σ R L}
    (hp : p ∈ coefficientSupport S) (hq : q ∈ coefficientSupport T) :
    ⁅p, q⁆ ∈ coefficientSupport U := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum]
  apply (coefficientSupport U).sum_mem
  intro a ha
  apply (coefficientSupport U).sum_mem
  intro b hb
  rw [lie_monomial]
  apply monomial_mem_coefficientSupport
  apply hST
  · by_contra h
    exact (Finsupp.mem_support_iff.mp ha) (hp a h)
  · by_contra h
    exact (Finsupp.mem_support_iff.mp hb) (hq b h)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeOrbitTransport
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {G : MultidegreeLieFiltration σ L s bound}

noncomputable def orbitEquivOfEq (h : F = G) : F.PolynomialOrbit ≃* G.PolynomialOrbit := by
  subst G
  exact MulEquiv.refl _

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSliceFiniteLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

theorem fiberIntegerPoint_mem_integerBox
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (u : ∀ k, Fin (S.length k)) : S.fiberIntegerPoint fixed u ∈ integerBox N := by
  rw [mem_integerBox]
  intro i
  by_cases hi : keep i
  · change 0 ≤ finiteSplitPoint keep _ fixed i ∧ finiteSplitPoint keep _ fixed i < (N i : ℤ)
    simp only [finiteSplitPoint, dif_pos hi]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast (S.point u ⟨i, hi⟩).isLt⟩
  · change 0 ≤ finiteSplitPoint keep _ fixed i ∧ finiteSplitPoint keep _ fixed i < (N i : ℤ)
    simpa only [finiteSplitPoint, dif_neg hi] using hfixed ⟨i, hi⟩

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ConstructLayerResetScales
namespace OAI

section

namespace Erdos3

structure LayerResetScales (s r : ℕ) (L : ℝ) where
  threshold : ℕ → ℕ
  cellScale : ℕ → ℕ
  score : ℕ → ℝ
  constant : ℕ → ℝ
  exponent : ℕ → ℕ
  score_pos : ∀ h ≤ s + 1, 0 < score h
  constant_nonneg : ∀ h ≤ s, 0 ≤ constant h
  partition : ∀ h ≤ s, PolynomialCoordinatePartitionBound.{0} h (constant h) (exponent h)
  cell_pos : ∀ h ≤ s, 0 < cellScale h
  scale_bound : ∀ h ≤ s, constant h * ((r : ℝ) + 1) ≤ cellScale h
  power_bound : ∀ h ≤ s, cellScale h ^ (exponent h * (r + 1) ^ (2 * h)) ≤ threshold h
  lift_error : ∀ h ≤ s, (2 : ℝ) ^ (h + 1) * ((h : ℝ) / cellScale h) < 1
  freeze_error : ∀ h ≤ s, (r : ℝ) * (2 * ((h : ℝ) / cellScale h)) < 1 / 12
  score_error : ∀ h ≤ s, 8 * L * r * h ≤ score h * cellScale h
  score_next : ∀ h ≤ s, score (h + 1) ≤ score h / 2
  length_bound : ∀ h ≤ s, (threshold (h + 1) : ℝ) ≤
    score h * cellScale h / (2 : ℝ) ^ (h + 3)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseCommonStrideCardRatio
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem IsDenseCommonStrideBox.card_ratio {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {p : ℝ} {A : Finset (I → ℤ)} (h : IsDenseCommonStrideBox N p A) :
    ((integerBox N).card : ℝ) / A.card ≤ Real.exp (p * Fintype.card I) := by
  obtain ⟨c, step, H, hstep, hH, _, hdense, rfl⟩ := h
  rw [commonStrideBox_card c hstep H, card_integerBox, Nat.cast_prod, Nat.cast_prod]
  apply (div_le_iff₀ (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (hH i)))).mpr
  have haxis (i) : (N i : ℝ) ≤ Real.exp p * H i := by
    calc
      _ = Real.exp p * (Real.exp (-p) * (N i : ℝ)) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdense i) (Real.exp_nonneg _)
  calc
    _ ≤ ∏ i, (Real.exp p * (H i : ℝ)) :=
      Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => haxis i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      rw [mul_comm (Fintype.card I : ℝ) p]

end Erdos3

end

end OAI
end


