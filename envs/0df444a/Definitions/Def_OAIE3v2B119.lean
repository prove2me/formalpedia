-- Prove2me | Definitions.Def_OAIE3v2B119
-- name    : OAIE3v2B119
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:50:20.603725+00:00
-- url     : https://prove2.me/theorems/e8a0159f-bf9d-4e70-8aab-a38496a1ccfc
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 121 of 311
-- statement:
--   Definitions bundle 121 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B102`, `OAIE3v2B104`, `OAIE3v2B105`, `OAIE3v2B106`, `OAIE3v2B107` of this split.
--
--   Modules: `Dynamics/NativeParameterCoverBudget.lean`, `Estimates/ControlledSurjectiveReconstruction.lean`, `Estimates/FixedObservableCorrelation.lean`, `Estimates/ImageRepresentatives.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/NativeCentralSeed.lean`, `Estimates/PolarizedCoefficientPermutation.lean`, `Estimates/RationalPowerHeight.lean`, `Estimates/RealifiedReconstruction.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/SquareGradedRelative.lean`, `Geometry/SupportedQuotientFamilyFaithful.lean`, `Lattices/ConjugatedLatticeGrids.lean`, `Lattices/FilteredLatticePowerIndex.lean`, `Lattices/SourceLatticeCover.lean`, `Linear/AdaptedBasisGeometry.lean`, `Linear/CanonicalRankCompatibility.lean`, `Linear/NativeRankBudget.lean`, `Linear/RankQuotientHeightBudget.lean`, `Linear/RealifiedCentralBasisAction.lean`, `Nilpotent/BCHDenominatorBudget.lean`, `Nilpotent/BCHQuotientLocalIsometry.lean`, `Nilpotent/BCHSmoothPartitionBudget.lean`, `Nilpotent/BCHUniformQuotientCharts.lean`, `Nilpotent/IdealInvariantNiltestBudget.lean`, `Nilpotent/NiltestComplement.lean`, `Nilpotent/RationalBCHProducts.lean`, `Polynomial/PolynomialGridValues.lean`, `Polynomial/ScaledPolynomialDualBounds.lean`, `Polynomial/SquarefreeTopDegree.lean`, `Polynomial/UniformPolynomialPeriodBudget.lean`, `Sampling/NativeGridRightDictionary.lean`.
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHDenominatorBudget
namespace OAI

section

namespace Erdos3

open Module

theorem exists_bchCoordinateDenominator_exp_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (bchCoordinateDenominator e s : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨c, _, hc⟩ := exists_bchCoordinateHeight_exp_budget s
  let R : Polynomial ℕ :=
    (2 * Polynomial.X + (Polynomial.X + Polynomial.C c) ^ c + Polynomial.C (s + 3)) ^ (s + 3)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hp hd hH hstructure
  let q : ℝ := 2 * p + (p + c) ^ c
  have hpower : 0 ≤ (p + c) ^ c := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hheight := hc (Fintype.card ι) H p hp hd hH
  have hcoeff : ∀ i α, (((bchCoordinatePolynomial (lieStructureConstants e) s i).coeff α).den : ℝ) ≤
      Real.exp q := by
    intro i α
    exact (Nat.cast_le.mpr (bchCoordinatePolynomial_height (lieStructureConstants e) hstructure s i α).2).trans
      (hheight.trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith)))
  have hinputs : (Fintype.card (Fin 2 × ι) : ℝ) ≤ q := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [q]
    linarith
  have hD := polynomialFamilyDenominator_degree_budget (bchCoordinatePolynomial (lieStructureConstants e) s)
    s (bchCoordinatePolynomial_totalDegree _ s) hq (hd.trans hpq) hinputs hcoeff
  have hpoly : (q + (s + 3)) ^ (s + 3) ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  exact hD.trans (Real.exp_le_exp.mpr hpoly)

theorem exists_bch_rational_closure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ q ∣ m ∧
        ∀ a b : L, e.equivFun a ∈ denominatorGrid q → e.equivFun b ∈ denominatorGrid q →
          e.equivFun (lieBCH s a b) ∈ denominatorGrid m := by
  obtain ⟨K, _, hK⟩ := exists_bchCoordinateDenominator_exp_budget s
  refine ⟨K + s + 5, by omega, ?_⟩
  intro ι L _ _ _ e H p hp hd hH hstructure q hq hqp
  let D := bchCoordinateDenominator e s
  let m := q * D * q ^ s
  have hD : 0 < D := bchCoordinateDenominator_pos e s
  have hqm : q ∣ m := ⟨D * q ^ s, Nat.mul_assoc q D (q ^ s)⟩
  have hDm : D * q ^ s ∣ m := ⟨q,
    (Nat.mul_assoc q D (q ^ s)).trans (Nat.mul_comm q (D * q ^ s))⟩
  refine ⟨m, Nat.mul_pos (Nat.mul_pos hq hD) (pow_pos hq _), ?_, hqm, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using conjugation_grid_allowance_le_exp K s q D q hp hqp
      (hK e H p hp hd hH hstructure) hqp
  · intro a b ha hb
    exact denominatorGrid_subset_of_dvd hDm (lieBCH_mem_denominatorGrid e s q a b ha hb)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

theorem lipschitz_mapReal_of_rational_height (A : κ → ι → ℚ) (H : ℕ)
    (hA : ∀ k i, f.repr (φ (e i)) k = (A k i : ℝ))
    (hH : ∀ k i, RationalHeightLE (A k i) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H)
      (mapReal (hnil := hnil) (hM := hM) φ) := by
  apply lipschitz_mapReal_of_entry_bound e f φ H
  intro k i
  rw [hA]
  exact (hH k i).abs_real_le

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

section Map

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem basisQuotientDist_mapReal_le (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ⁅ℝ⁆ M) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (hΛ : IsClosed (Λ : Set (NilpotentLieBCHGroup M s hM)))
    (hmap : Γ ≤ Λ.comap (mapReal φ)) (B : ℝ≥0) (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B)
    (x y : _ ⧸ Γ) :
    basisQuotientDist f Λ hΛ (cosetMap Γ Λ (mapReal φ) hmap x) (cosetMap Γ Λ (mapReal φ) hmap y) ≤
      coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B * basisQuotientDist e Γ hΓ x y := by
  let := quotientMetricSpace e Γ hΓ
  let := quotientMetricSpace f Λ hΛ
  exact (lipschitz_quotient_mapReal_of_entry_bound e f φ Γ Λ hΓ hΛ hmap B hφ).dist_le_mul x y

end Map

section BasisChange

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem basisQuotientDist_change_le (e : Basis ι ℝ L) (f : Basis κ ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (B : ℝ≥0) (hB : ∀ k i, |f.repr (e i) k| ≤ B) (x y : _ ⧸ Γ) :
    basisQuotientDist f Γ hΓ x y ≤
      coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B * basisQuotientDist e Γ hΓ x y := by
  have hmap : Γ ≤ Γ.comap (mapReal (LieHom.id : L →ₗ⁅ℝ⁆ L)) := by
    intro g hg
    simpa only [Subgroup.mem_comap, mapReal_id] using hg
  have heq : cosetMap Γ Γ (mapReal (LieHom.id : L →ₗ⁅ℝ⁆ L)) hmap = id := by
    funext z
    induction z using Quotient.inductionOn with
    | h z => rfl
  simpa only [heq, id_eq] using
    basisQuotientDist_mapReal_le e f LieHom.id Γ Γ hΓ hΓ hmap B hB x y

end BasisChange

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct NNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)

theorem lipschitz_realificationMap (H : ℕ)
    (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H)
      (realificationMap (hnil := hnil) (hM := hM) φ) :=
  lipschitz_mapReal_of_rational_height (e.baseChange ℝ) (f.baseChange ℝ) (realificationLieHom φ)
    (fun k i => f.repr (φ (e i)) k) H (realificationLieHom_basis e f φ) hH

theorem exists_realificationMap_lipschitz_exp_bound (H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
    ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
      LipschitzWith C (realificationMap (hnil := hnil) (hM := hM) φ) :=
  ⟨coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H,
    coordinateLipschitzBound_pos _ _ _, coordinateLipschitzBound_le_exp _ _ H hp hκ hι hHp,
    lipschitz_realificationMap e f φ H hH⟩

variable (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (Λ : Subgroup (NilpotentLieBCHGroup M t hM)) (hφ : Γ ≤ Λ.comap (mapOfSteps φ))

theorem exists_realificationMap_quotient_lipschitz_exp_bound
    (l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := realificationQuotientMetricSpace e Γ l hl hΓ
    letI := realificationQuotientMetricSpace f Λ m hm hΛ
    ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
      LipschitzWith C (cosetMap (Γ.map realificationHom) (Λ.map realificationHom)
        (realificationMap (hnil := hnil) (hM := hM) φ) (realificationMap_subgroup φ Γ Λ hφ)) :=
  ⟨coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H,
    coordinateLipschitzBound_pos _ _ _, coordinateLipschitzBound_le_exp _ _ H hp hκ hι hHp,
    lipschitz_realificationMap_quotient e f φ Γ Λ hφ l m hl hm hΓ hΛ H hH⟩

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)

include hstructure hc

theorem dist_le_bchBoxMetricConstant (B : ℝ≥0) (hB : 1 ≤ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (x y : NilpotentLieBCHGroup L s hnil)
    (hx : ∀ i, |e.repr x.coord i| ≤ B) (hy : ∀ i, |e.repr y.coord i| ≤ B)
    (hxy : ∀ i, |e.repr x.coord i - e.repr y.coord i| ≤ δ) :
    letI := rightMetricSpace (hnil := hnil) e
    dist x y ≤ bchBoxMetricConstant s (Fintype.card ι) H B * δ := by
  let := rightMetricSpace (hnil := hnil) e
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hcoord (i : ι) : |basisHomeomorph e (x * y⁻¹) i| ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ :=
    lieBCH_sub_coordinates_bound e c hstructure hc hnil x.coord y.coord hBr hδ hx hy hxy i
  calc
    _ ≤ coordinateL2Norm (basisHomeomorph e (x * y⁻¹)) := dist_le_coordinateL2Norm_mul_inv e x y
    _ ≤ (Fintype.card ι + 1) * (bchBoxCoordinateBound s (Fintype.card ι) H B * δ) :=
      coordinateL2Norm_le_card_bound _
        (mul_nonneg (bchBoxCoordinateBound_nonneg s _ H B.coe_nonneg) hδ) hcoord
    _ = _ := by change _ = ((Fintype.card ι + 1) * bchBoxCoordinateBound s (Fintype.card ι) H B) * δ; ring

theorem lipschitzOn_basisHomeomorph_symm_box (B : ℝ≥0) (hB : 1 ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    LipschitzOnWith (bchBoxMetricConstant s (Fintype.card ι) H B)
      (basisHomeomorph (hnil := hnil) e).symm {v | ∀ i, |v i| ≤ B} := by
  let := rightMetricSpace (hnil := hnil) e
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  apply dist_le_bchBoxMetricConstant e c hstructure hc B hB dist_nonneg
  · intro i
    change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm v) i| ≤ _
    simpa only [Homeomorph.apply_symm_apply] using hv i
  · intro i
    change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm w) i| ≤ _
    simpa only [Homeomorph.apply_symm_apply] using hw i
  · intro i
    change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm v) i -
      basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm w) i| ≤ _
    simpa only [Homeomorph.apply_symm_apply, Real.dist_eq] using dist_le_pi_dist v w i

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem dist_linear_lift_le (e : Basis ι ℝ L) (f : Basis κ ℝ M) (σ : M →ₗ[ℝ] L)
    (B : ℝ≥0) (hσB : ∀ i j, |e.repr (σ (f j)) i| ≤ B)
    (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = f.repr ⁅f i, f j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    let C := bchLogMetricConstant t (Fintype.card κ) H 1
    let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B *
      ((Fintype.card κ : ℝ≥0) + 1) * C
    ∀ g : NilpotentLieBCHGroup M t hM, dist 1 g < (C⁻¹ : ℝ≥0) →
      dist 1 (⟨σ g.coord⟩ : NilpotentLieBCHGroup L s hnil) ≤ K * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  let C := bchLogMetricConstant t (Fintype.card κ) H 1
  let A := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B
  change ∀ g : NilpotentLieBCHGroup M t hM, dist 1 g < (C⁻¹ : ℝ≥0) →
    dist 1 (⟨σ g.coord⟩ : NilpotentLieBCHGroup L s hnil) ≤
      (A * ((Fintype.card κ : ℝ≥0) + 1) * C : ℝ≥0) * dist 1 g
  intro g hg
  have hC : (0 : ℝ) < C := bchLogMetricConstant_pos t (Fintype.card κ) H 1
  have hnear : (C : ℝ) * dist 1 g < (1 : ℝ≥0) := by
    rw [NNReal.coe_inv] at hg
    change (C : ℝ) * dist 1 g < 1
    have hh := mul_lt_mul_of_pos_left hg hC
    simpa only [mul_inv_cancel₀ hC.ne'] using hh
  have hnorm := norm_coordinates_le_of_near_one f c hstructure hc 1 le_rfl g hnear
  let h : NilpotentLieBCHGroup L s hnil := ⟨σ g.coord⟩
  have hcoord : basisHomeomorph e h = basisCoordinateMap f e σ (basisHomeomorph f g) := by
    change e.equivFun (σ g.coord) = e.equivFun (σ (f.equivFun.symm (f.equivFun g.coord)))
    rw [LinearEquiv.symm_apply_apply]
  calc
    dist 1 h ≤ coordinateL2Norm (basisHomeomorph e h) := dist_one_le_coordinateL2Norm e h
    _ ≤ (A : ℝ) * coordinateL2Norm (basisHomeomorph f g) := by
      rw [hcoord]
      exact basisCoordinateMap_L2_bound f e σ B B.coe_nonneg hσB _
    _ ≤ A * (((Fintype.card κ : ℝ) + 1) * ‖basisHomeomorph f g‖) := by
      apply mul_le_mul_of_nonneg_left _ A.coe_nonneg
      exact coordinateL2Norm_le_card_bound _ (norm_nonneg _) (fun j => by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (basisHomeomorph f g) j)
    _ ≤ A * (((Fintype.card κ : ℝ) + 1) * ((C : ℝ) * dist 1 g)) := by
      gcongr
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]; ring

theorem exists_local_metric_lifts_of_section (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ⁅ℝ⁆ M) (σ : M →ₗ[ℝ] L) (hσ : Function.RightInverse σ φ)
    (B : ℝ≥0) (hσB : ∀ i j, |e.repr (σ (f j)) i| ≤ B)
    (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = f.repr ⁅f i, f j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    let C := bchLogMetricConstant t (Fintype.card κ) H 1
    let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B *
      ((Fintype.card κ : ℝ≥0) + 1) * C
    ∀ g : NilpotentLieBCHGroup M t hM, dist 1 g < (C⁻¹ : ℝ≥0) →
      ∃ h : NilpotentLieBCHGroup L s hnil,
        mapReal φ h = g ∧ dist 1 h ≤ K * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  dsimp only
  intro g hg
  exact ⟨⟨σ g.coord⟩, ext (hσ g.coord), dist_linear_lift_le e f σ B hσB c hstructure hc g hg⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

theorem exists_coordinateBox_metric_cover {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
    {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (B : ℝ≥0) (hB : 1 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    let K := bchBoxMetricConstant s (Fintype.card ι) H B
    let N := boxCoverMeshCount B K ε
    ∃ centers : (ι → Fin (N + 1)) → coordinateBox (hnil := hnil) e B,
      letI := rightMetricSpace (hnil := hnil) e
      ∀ x : coordinateBox (hnil := hnil) e B, ∃ j, dist x (centers j) ≤ ε := by
  let K := bchBoxMetricConstant s (Fintype.card ι) H B
  let N := boxCoverMeshCount B K ε
  have hN : 0 < N := boxCoverMeshCount_pos _ _ _
  let centers : (ι → Fin (N + 1)) → coordinateBox (hnil := hnil) e B := fun k =>
    ⟨(basisHomeomorph (hnil := hnil) e).symm (uniformBoxGrid B N k), by
      intro i
      change |basisHomeomorph (hnil := hnil) e
        ((basisHomeomorph (hnil := hnil) e).symm (uniformBoxGrid B N k)) i| ≤ B
      rw [Homeomorph.apply_symm_apply]
      exact uniformBoxGrid_mem B.coe_nonneg hN k i⟩
  refine ⟨centers, ?_⟩
  let := rightMetricSpace (hnil := hnil) e
  intro x
  obtain ⟨j, hj⟩ := exists_uniformBoxGrid_approx (lt_of_lt_of_le zero_lt_one hB) hN
    (basisHomeomorph (hnil := hnil) e x.val) x.property
  refine ⟨j, ?_⟩
  have h := (lipschitzOn_basisHomeomorph_symm_box (hnil := hnil) e c hstructure hc B hB).dist_le_mul
    (basisHomeomorph (hnil := hnil) e x.val) x.property
    (uniformBoxGrid B N j) (uniformBoxGrid_mem B.coe_nonneg hN j)
  have hdist := h.trans ((mul_le_mul_of_nonneg_left hj K.coe_nonneg).trans (boxCoverMeshCount_error K hε))
  simpa only [centers, Subtype.dist_eq, Homeomorph.symm_apply_apply] using hdist

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeParameterCoverBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_bchBoxCover_count_budget (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (B : ℝ≥0) {p ε : ℝ},
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ r) → 0 < ε → 1 / ε ≤ Real.exp p →
      (((boxCoverMeshCount B (bchBoxMetricConstant s d H B) ε + 1) ^ d : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  obtain ⟨A, _, hmetric⟩ := exists_bchBoxMetricConstant_exp_bound s r
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ r + (X + Polynomial.C A) ^ A
  let P := R * (3 * R + 4)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro d H B p ε hp hd hH hB hε hεinv
  let q := p + (p + 2) ^ r + (p + A) ^ A
  have hr : 0 ≤ (p + 2) ^ r := pow_nonneg (by linarith) _
  have hA : 0 ≤ (p + A) ^ A := pow_nonneg (add_nonneg hp (Nat.cast_nonneg A)) _
  have hpq : p ≤ q := (le_add_of_nonneg_right hr).trans (le_add_of_nonneg_right hA)
  have hrq : (p + 2) ^ r ≤ q := (le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right hA)
  have hAq : (p + A) ^ A ≤ q := le_add_of_nonneg_left (add_nonneg hp hr)
  have hsize := boxCoverCount_dimension_bound d (bchBoxMetricConstant s d H B) B.coe_nonneg hε
    (hp.trans hpq) (hd.trans hpq) (hB.trans (Real.exp_le_exp.mpr hrq))
    ((hmetric d H B p hp hd hH hB).trans (Real.exp_le_exp.mpr hAq))
    (hεinv.trans (Real.exp_le_exp.mpr hpq))
  have hfinal : q * (3 * q + 4) ≤ (p + C) ^ C := by
    simpa [P, R, X, q, Polynomial.eval₂_pow] using hbudget p hp
  exact hsize.trans (Real.exp_le_exp.mpr hfinal)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedReconstruction
namespace OAI

section

namespace Erdos3

open Module
open scoped NNReal TensorProduct

variable {ι κ L M E : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

open NilpotentLieBCHGroup

theorem realificationMap_lattice_cover (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M t hM))
    (hcover : Λ ≤ Γ.map (mapOfSteps φ)) :
    Λ.map realificationHom ≤ (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ) := by
  rintro g ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ := hcover hy
  refine ⟨realificationHom x, ⟨x, hx, rfl⟩, ?_⟩
  rw [realificationMap_realificationHom_ofSteps, hxy]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] [NormedAddCommGroup E]

theorem exists_lipschitz_realification_reconstruction
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : Function.Surjective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M t hM))
    (hcover : Λ ≤ Γ.map (mapOfSteps φ))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (hstructure : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H)
    (u : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL) ⧸
      Γ.map realificationHom) → E)
    (hker : ∀ k ∈ (realificationMap (hnil := hL) (hM := hM) φ).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x))
    (ℓ B : ℝ≥0)
    (hu : letI := realificationQuotientMetricSpace e Γ l hl hΓ; LipschitzWith ℓ u)
    (hub : ∀ x, ‖u x‖ ≤ B) :
    letI := realificationQuotientMetricSpace f Λ m hm hΛ
    ∃ v : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM) ⧸
      Λ.map realificationHom) → E,
      (∀ x, v (QuotientGroup.mk (realificationMap (hnil := hL) (hM := hM) φ x)) = u (QuotientGroup.mk x)) ∧
      LipschitzWith (rationalReconstructionLipschitzBound t (Fintype.card ι) (Fintype.card κ) H ℓ B) v ∧
      ∀ y, ‖v y‖ ≤ B := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (f.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hL) (e.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
  obtain ⟨σ, hσ, hσB⟩ := exists_bounded_realified_linear_section e f φ.toLinearMap hφ hH hentries
  have hsurj : Function.Surjective (realificationMap (hnil := hL) (hM := hM) φ) := by
    intro g
    exact ⟨⟨σ g.coord⟩, ext (hσ g.coord)⟩
  let C := bchLogMetricConstant t (Fintype.card κ) H 1
  let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ)
    (rationalSolveHeight (Fintype.card κ) H) * ((Fintype.card κ : ℝ≥0) + 1) * C
  have hC : 0 < C := bchLogMetricConstant_pos t (Fintype.card κ) H 1
  have hlift := exists_local_metric_lifts_of_section
    (hnil := realification_lowerCentralSeries_eq_bot hL) (hM := realification_lowerCentralSeries_eq_bot hM)
    (e.baseChange ℝ) (f.baseChange ℝ) (realificationLieHom φ) σ hσ
    (rationalSolveHeight (Fintype.card κ) H) hσB (lieStructureConstants f)
    (fun i j k => (realLieBasis_structure f i j k).symm) hstructure
  exact exists_lipschitz_observable_reconstruction (realificationMap (hnil := hL) (hM := hM) φ) hsurj
    (Γ.map realificationHom) (Λ.map realificationHom)
    (realification_subgroup_closed_discrete e Γ l hl hΓ).1
    (realification_subgroup_closed_discrete f Λ m hm hΛ).1
    (realificationMap_lattice_cover φ Γ Λ hcover) u hker ℓ K B C⁻¹ (inv_pos.mpr hC) hu hub hlift

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FilteredLatticePowerIndex
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem subgroupPowerCover_index_le (e : Basis ι ℚ L) (Γ : Subgroup F.Group)
    (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (m : ℕ) (hm : 0 < m) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).FiniteIndex ∧
      (subgroupPowerCover Γ m).relIndex Γ ≤ m ^ Fintype.card ι := by
  let : FiniteDimensional ℚ L := Module.Finite.of_basis e
  obtain ⟨b, hb⟩ := F.exists_central_basis
  obtain ⟨N, hN, hgrid⟩ := exists_bchSubgroup_outer_grid_change_basis e b Γ l hl houter
  simpa only [finrank_eq_card_basis e] using
    hb.subgroupPowerCover_index_le F.lowerCentralSeries_eq_bot Γ N hN hgrid m hm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledSurjectiveReconstruction
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem exists_sharp_normal_cover (e : Basis ι ℚ L) (Γ Λ₀ : Subgroup F.Group)
    (l m₀ : ℕ) (hl : 0 < l) (hm₀ : 0 < m₀)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (htarget : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀) :
    ∃ Λ : Subgroup F.Group,
      Λ ≤ Λ₀ ∧ Λ ≤ Γ ∧ (Λ.subgroupOf Γ).Characteristic ∧ (Λ.subgroupOf Γ).Normal ∧
      (Λ.subgroupOf Γ).FiniteIndex ∧ Λ.relIndex Γ ≤ (l * m₀) ^ Fintype.card ι ∧
      scaledIntegerGrid ((l * m₀) * l) ⊆ bchSubgroupCoordinates e Λ ∧
      bchSubgroupCoordinates e Λ ⊆ denominatorGrid ((l * m₀) * l) := by
  let m := l * m₀
  obtain ⟨hfinite, hindex⟩ := F.subgroupPowerCover_index_le e Γ l hl houter m
    (Nat.mul_pos hl hm₀)
  exact ⟨subgroupPowerCover Γ m,
    subgroupPowerCover_le_of_grid e Γ Λ₀ l m₀ m houter htarget dvd_rfl,
    subgroupPowerCover_le Γ m, inferInstance, inferInstance, hfinite, hindex,
    subgroupPowerCover_grid e Γ l m hinner houter⟩

theorem exists_normal_cover_exp_quadratic (e : Basis ι ℚ L) (Γ Λ₀ : Subgroup F.Group)
    (l m₀ : ℕ) (hl : 0 < l) (hm₀ : 0 < m₀)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (htarget : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hlb : (l : ℝ) ≤ Real.exp p) (hm₀b : (m₀ : ℝ) ≤ Real.exp p) :
    ∃ Λ : Subgroup F.Group,
      Λ ≤ Λ₀ ∧ Λ ≤ Γ ∧ (Λ.subgroupOf Γ).Characteristic ∧ (Λ.subgroupOf Γ).Normal ∧
      (Λ.subgroupOf Γ).FiniteIndex ∧ (Λ.relIndex Γ : ℝ) ≤ Real.exp (2 * p ^ 2) ∧
      ∃ ℓ : ℕ, 0 < ℓ ∧ (ℓ : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
        scaledIntegerGrid ℓ ⊆ bchSubgroupCoordinates e Λ ∧
        bchSubgroupCoordinates e Λ ⊆ denominatorGrid ℓ := by
  obtain ⟨Λ, hΛ₀, hΛ, hchar, hnormal, hfinite, hindex, hin, hout⟩ :=
    F.exists_sharp_normal_cover e Γ Λ₀ l m₀ hl hm₀ hinner houter htarget
  refine ⟨Λ, hΛ₀, hΛ, hchar, hnormal, hfinite, ?_, (l * m₀) * l,
    Nat.mul_pos (Nat.mul_pos hl hm₀) hl, powerCover_grid_allowance_le_exp l m₀ hp hlb hm₀b,
    hin, hout⟩
  exact (Nat.cast_le.mpr hindex).trans (powerCover_index_allowance_le_exp l m₀ _ hp hlb hm₀b hd)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))

theorem centralBCHCircleAction_act_coe (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ)
    (r : ℝ) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    (centralBCHCircleAction e Γ hΓ v hv hperiod).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := hnil) v r • x := by
  let := quotientMetricSpace e Γ hΓ
  dsimp only [centralBCHCircleAction, CircleFourier.isometricCircleActionOfFlow]
  exact CircleFourier.periodicFlowAct_coe _ _ r x

theorem centralBCHCircleAction_displacement (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ)
    (t : CircleFourier.Circle) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    dist ((centralBCHCircleAction e Γ hΓ v hv hperiod).act t x) x ≤
      coordinateL2Norm (e.equivFun v) * ‖t‖ := by
  let := quotientMetricSpace e Γ hΓ
  dsimp only [centralBCHCircleAction, CircleFourier.isometricCircleActionOfFlow]
  exact CircleFourier.periodicFlowAct_displacement _ _
    ⟨coordinateL2Norm (e.equivFun v), coordinateL2Norm_nonneg _⟩
    (centralBCHFlow_displacement e Γ hΓ v) t x

theorem centralBCHCircleAction_commutes (v w : L)
    (hv : ∀ z : L, ⁅v, z⁆ = 0) (hw : ∀ z : L, ⁅w, z⁆ = 0)
    (hvΓ : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ)
    (hwΓ : (⟨w⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    (centralBCHCircleAction e Γ hΓ v hv hvΓ).Commutes (centralBCHCircleAction e Γ hΓ w hw hwΓ) := by
  let := quotientMetricSpace e Γ hΓ
  intro t u x
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective u
  simp only [centralBCHCircleAction_act_coe]
  rw [← mul_smul, ← mul_smul, (realBCHLine_commute v hv r (realBCHLine (hnil := hnil) w q)).eq]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageRepresentatives
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

theorem exists_bounded_realification_layer_reduction (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) (n : ℕ) :
    ∃ K : Set G, IsCompact K ∧
      (∀ r ∈ K, ∀ i, |(e.baseChange ℝ).repr r.coord i| ≤
        layerRoundingBound (Fintype.card ι) H l n) ∧
      ∀ g : G, g.coord ∈ LieModule.lowerCentralSeries ℚ E E n →
        ∃ r ∈ K, ∃ w ∈ Γ.map NilpotentLieBCHGroup.realificationHom,
          (r⁻¹ * g * w⁻¹).coord ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
  obtain ⟨r, hr, v, hspan, hv⟩ := exists_bounded_layer_spanning e hc n
  let B := lieCoordinateHeight (Fintype.card ι) H n
  let m := rationalSpanGridStep e v l
  have hB : 1 ≤ B := lieCoordinateHeight_pos _ _ _
  have hm : m ≤ l * B ^ (Fintype.card ι * Fintype.card ι) := by
    apply (rationalSpanGridStep_le e v l (fun i j => hv j i)).trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right hB
    simpa only [Fintype.card_fin] using Nat.mul_le_mul_left (Fintype.card ι) hr
  have hsize : r * m * B ≤ layerRoundingBound (Fintype.card ι) H l n := by
    calc
      _ ≤ Fintype.card ι * (l * B ^ (Fintype.card ι * Fintype.card ι)) * B :=
        Nat.mul_le_mul_right B (Nat.mul_le_mul hr hm)
      _ = _ := by simp [layerRoundingBound, pow_succ, mul_assoc, B]
  refine ⟨(fun x : E => (⟨x⟩ : G)) ''
    boundedSpanCell (fun j => rationalLieInclusion (v j)) (m : ℝ),
    (isCompact_boundedSpanCell _ _).image NilpotentLieBCHGroup.continuous_mk, ?_,
    realification_layer_reduction_in_cell e Γ l hl hinner n v hspan⟩
  rintro _ ⟨x, hx, rfl⟩ i
  have hcoord : ∀ j k, |(e.baseChange ℝ).repr (rationalLieInclusion (v j)) k| ≤ (B : ℝ) := by
    intro j k
    rw [rationalLieInclusion_coordinates]
    exact (hv j k).abs_real_le
  have hb := boundedSpanCell_coordinate_bound (e.baseChange ℝ) _
    (Nat.cast_nonneg m) hcoord hx i
  apply hb.trans
  simpa only [Fintype.card_fin, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hsize

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

theorem exists_bounded_realification_factors (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∀ g : G, ∃ rs : List G, rs.length = s ∧
      (∀ r ∈ rs, ∀ i, |(e.baseChange ℝ).repr r.coord i| ≤
        layerRoundingBound (Fintype.card ι) H l s) ∧
      ∃ γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom, g = rs.prod * γ := by
  let J : ℕ → Subgroup G := fun n => NilpotentLieBCHGroup.subgroup
    (show LieIdeal ℚ E from LieModule.lowerCentralSeries ℚ E E n).toLieSubalgebra
  have hzero : J 0 = ⊤ := by
    ext g
    change (g.coord ∈ LieModule.lowerCentralSeries ℚ E E 0) ↔ g ∈ (⊤ : Subgroup G)
    simp
  have hterminal : J s = ⊥ := by
    ext g
    change (g.coord ∈ LieModule.lowerCentralSeries ℚ E E s) ↔ g = 1
    rw [realification_lowerCentralSeries_eq_bot hnil, LieSubmodule.mem_bot]
    exact ⟨fun h => NilpotentLieBCHGroup.ext h, fun h => congrArg NilpotentLieBCHGroup.coord h⟩
  apply exists_representative_factors_of_reductions
    (Γ.map NilpotentLieBCHGroup.realificationHom) J s _ hzero hterminal
  intro i hi g hg
  obtain ⟨K, _, hbound, hreduce⟩ := exists_bounded_realification_layer_reduction e Γ l hl hinner hc i
  obtain ⟨r, hr, w, hw, hrem⟩ := hreduce g hg
  refine ⟨r, ?_, w, hw, hrem⟩
  intro k
  exact (hbound r hr k).trans (Nat.cast_le.mpr (layerRoundingBound_mono_layer _ _ _ hi.le))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_realification_representatives_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil),
        ∃ r, (∀ i, |(e.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom, g = r * γ := by
  obtain ⟨C, hC, hprod⟩ := exists_bch_group_product_exp_bound s (3 * s + 5)
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ _ _ _ e hnil Γ l H p hl hinner hc hp hd hH hlbound g
  obtain ⟨rs, hlen, hcoords, γ, hγ, heq⟩ := exists_bounded_realification_factors e Γ l hl hinner hc g
  refine ⟨rs.prod, ?_, γ, hγ, heq⟩
  apply hprod (e.baseChange ℝ) (lieStructureConstants e) H p
    (realification_lowerCentralSeries_eq_bot hnil) rs
  · intro i j k
    exact (realLieBasis_structure e i j k).symm
  · exact hp
  · exact hd
  · exact hlen.le
  · exact hH
  · exact hc
  · intro r hr i
    exact (hcoords r hr i).trans (layerRoundingBound_le_exp _ _ _ _ hp hd hH hlbound)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CanonicalRankCompatibility
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L s)

theorem orbitEquivOfEq_eval {G : NilpotentLieFiltration L s} (h : F = G)
    {σ : Type*} (w : σ → ℕ) (g : F.PolynomialOrbit w) (x : σ → ℤ) :
    G.polynomialOrbitEval w x (F.orbitEquivOfEq h w g) = F.polynomialOrbitEval w x g := by
  subst G
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ConjugatedLatticeGrids
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem exists_uniform_conjugated_inner_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l q H : ℕ) (p : ℝ),
      0 < l → 0 < q → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (l : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ z : NilpotentLieBCHGroup L s hnil, e.equivFun z.coord ∈ denominatorGrid q →
          scaledIntegerGrid M ⊆ bchSubgroupCoordinates e (Γ.map (MulAut.conj z).toMonoidHom) := by
  obtain ⟨K, hK, hden⟩ := exists_conjugation_denominator_exp_bound s
  refine ⟨K + s + 5, by omega, ?_⟩
  intro ι L _ _ _ e hnil Γ l q H p hl hq hinner hp hd hH hc hlb hqb
  refine ⟨l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s,
    Nat.mul_pos (Nat.mul_pos hl (polynomialFamilyDenominator_pos _)) (pow_pos hq _), ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using
      conjugation_grid_allowance_le_exp K s l _ q hp hlb (hden e H p hp hd hH hc) hqb
  · intro z hz
    exact conjugated_subgroup_inner_grid e hnil Γ l q hq hinner z hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RationalBCHProducts
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_real_bch_rational_closure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ a b : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil),
          (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun b.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (a * b).coord ∈ realDenominatorGrid m) ∧
        (∀ a : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil),
          (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (a⁻¹).coord ∈ realDenominatorGrid m) := by
  obtain ⟨C, hC, hbound⟩ := exists_bch_rational_closure s
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hmul⟩ := hbound e H p hp hd hH hc l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_, ?_⟩
  · exact NilpotentLieBCHGroup.realification_grid_mul (hnil := hnil) e l m hl
      (fun a b ha hb => hmul a.coord b.coord ha hb)
  · apply NilpotentLieBCHGroup.realification_grid_inv (hnil := hnil) e l m hl
    intro a ha
    change e.equivFun (-a.coord) ∈ denominatorGrid m
    rw [map_neg]
    exact denominatorGrid_subset_of_dvd hlm (denominatorGrid_neg l ha)

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

theorem squareLattice_le_fst (Γ : Subgroup F.Group) : F.squareLattice Γ ≤ Γ.comap F.squareFstHom :=
  fun _ h => h.1

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareGradedRelative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem associatedGradedPieceMap_basis (j : ℕ) (i : ι) (hi : j ≤ ω i) (he : j = ω i) :
    F.associatedGradedPieceMap j
      ⟨b i, by rw [hlayers]; exact Submodule.subset_span ⟨i, hi, rfl⟩⟩ =
        F.associatedGradedBasis b ω hlayers i := by
  classical
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext k
  rw [F.associatedGradedPieceMap_coordinate]
  simp only [Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = k
  · subst k
    simp only [he, ite_true]
  · simp only [h, ite_false, ite_self]

theorem associatedGradedPieceMap_range (j : ℕ) :
    LinearMap.range (F.associatedGradedPieceMap j) =
      Submodule.span ℚ (F.associatedGradedBasis b ω hlayers '' {i | ω i = j}) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [basis_mem_span_image_iff]
    intro i hi
    rw [F.associatedGradedPieceMap_coordinate]
    exact if_neg (Ne.symm hi)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨⟨b i, ?_⟩, ?_⟩
    · rw [hlayers]
      exact Submodule.subset_span ⟨i, hi.symm.le, rfl⟩
    · exact F.associatedGradedPieceMap_basis b ω hlayers j i hi.symm.le hi.symm

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
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

theorem affinePolynomialOrbit_real_coord (b : L) (a : σ → L) (x : σ → ℝ) :
    (F.polynomialOrbitRealEval (fun _ => 1) x (F.affinePolynomialOrbit b a)).coord =
      b + ∑ j, x j • a j := by
  rw [polynomialOrbitRealEval_coord, affinePolynomialOrbit_log, map_add,
    eval₂_monomial, Finsupp.prod_zero_index, one_smul, eval₂_linearPolynomial]

theorem affinePolynomialOrbit_integer_coord (b : L) (a : σ → L) (x : σ → ℤ) :
    (F.polynomialOrbitEval (fun _ => 1) x (F.affinePolynomialOrbit b a)).coord =
      b + ∑ j, (x j : ℝ) • a j := by
  rw [← F.polynomialOrbitRealEval_integer]
  exact F.affinePolynomialOrbit_real_coord b a _

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreeTopDegree
namespace OAI

section

namespace Erdos3

theorem SquarefreeIndex.one_le_iff {ι : Type*} [Fintype ι] (a : SquarefreeIndex ι) :
    (fun _ => 1) ≤ (fun i => a.val i) ↔ a = full ι := by
  constructor
  · intro h
    apply Subtype.ext
    ext i
    exact le_antisymm (a.property i) (h i)
  · rintro rfl
    intro i
    exact le_rfl

theorem SquarefreeIndex.permute_full {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    permute e (full ι) = full κ := by
  apply Subtype.ext
  ext j
  rfl

theorem squarefree_top_monomial {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (x : SquarefreePolynomial ι L)
    (hx : x ∈ squarefreeSupportModule (fun a : SquarefreeIndex ι => (fun _ => 1) ≤ fun i => a.val i)) :
    x = squarefreeMonomial (SquarefreeIndex.full ι)
      (squarefreePolynomialEquiv x (SquarefreeIndex.full ι)) := by
  apply squarefreePolynomialEquiv.injective
  ext a
  by_cases ha : SquarefreeIndex.full ι = a
  · subst a
    rw [squarefreePolynomialEquiv_monomial_self]
  · rw [squarefreePolynomialEquiv_monomial_ne _ _ ha]
    exact hx a (fun h => ha ((SquarefreeIndex.one_le_iff a).mp h).symm)

namespace MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeBlockPermute_eq_self_top (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (x : F.SquarefreeAlgebra π) (hx : x ∈ F.squarefreeMultidegreeLayer π (fun _ => 1)) :
    F.squarefreeBlockPermute π e he x = x := by
  apply Subtype.ext
  change squarefreePermute e x.val = x.val
  rw [squarefree_top_monomial x.val hx, squarefreePermute_monomial, SquarefreeIndex.permute_full]

end MultidegreeLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem dilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairFiltration (q : ℚ)).Group)
    (hg : g ∈ (F.dilationPairFiltration (q : ℚ)).subgroup s) :
    (NilpotentLieBCHGroup.map (F.dilationPairFirst (q : ℚ)) g : F.Group) =
      (NilpotentLieBCHGroup.map (F.dilationPairSecond (q : ℚ)) g) ^ (q ^ s) := by
  apply NilpotentLieBCHGroup.ext
  rw [NilpotentLieBCHGroup.coord_zpow]
  change F.dilationPairFirst (q : ℚ) g.coord = (q ^ s) • F.dilationPairSecond (q : ℚ) g.coord
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow]
  exact F.dilationPairTop_relation (q : ℚ) hg

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

namespace MultidegreeStructure

variable {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem orbitToOrdinary_eval (g : M.filtration.realification.PolynomialOrbit) (x : σ → ℤ) :
    D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) x (M.orbitToOrdinary g) =
      M.filtration.realification.polynomialOrbitEval x g := by
  have h : M.filtration.realification.ordinary = D.filtration.realification := by
    change M.filtration.ordinary.realification = D.filtration.realification
    rw [M.ordinary]
  change D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) x
    (M.filtration.realification.ordinary.orbitEquivOfEq h (fun _ : σ => 1)
      (M.filtration.realification.toOrdinaryOrbit g)) = _
  rw [NilpotentLieFiltration.orbitEquivOfEq_eval,
    MultidegreeLieFiltration.toOrdinaryOrbit_eval]

end MultidegreeStructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def restrictBound (bound' : σ → ℕ)
    (hzero : ∀ a, ¬a ≤ bound' → F.layer a = ⊥) :
    MultidegreeLieFiltration σ L s bound' where
  ordinary := F.ordinary
  layer := F.layer
  antitone := F.antitone
  zero_eq_top := F.zero_eq_top
  lie_mem := F.lie_mem
  terminal := hzero
  degree_eq := F.degree_eq

noncomputable def restrictBoundRealOrbit (bound' : σ → ℕ)
    (hzero : ∀ a, ¬a ≤ bound' → F.layer a = ⊥)
    (g : F.realification.PolynomialOrbit) :
    (F.restrictBound bound' hzero).realification.PolynomialOrbit := g

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedLayer_eq_finite (c : σ → ℕ) (n : ℕ) :
    F.weightedLayer c n =
      ⨆ a : {a : ∀ i, Fin (bound i + 1) // n ≤ multidegreeWeight c (fun i => (a i).val)},
        F.layerIdeal (fun i => (a.val i).val) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro a
    by_cases ha : a.val ≤ bound
    · let b : ∀ i, Fin (bound i + 1) := fun i => ⟨a.val i, Nat.lt_succ_of_le (ha i)⟩
      exact le_iSup_of_le ⟨b, a.property⟩ le_rfl
    · intro x hx
      have h : x = 0 := by
        have hx' : x ∈ F.layer a.val := hx
        simpa only [F.terminal a.val ha, Submodule.mem_bot] using hx'
      rw [h]
      exact LieSubmodule.zero_mem _
  · apply iSup_le
    intro a
    exact F.layer_le_weightedLayer c (fun i => (a.val i).val) n a.property

end Erdos3.MultidegreeLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem weightedLayer_span (c : σ → ℕ) (n : ℕ) :
    (M.filtration.weightedLayer c n).toSubmodule = Submodule.span ℚ
      (Set.range (fun a : Σ a : {a : ∀ i, Fin (bound i + 1) //
          n ≤ multidegreeWeight c (fun i => (a i).val)},
          Fin (finrank ℚ (M.filtration.layer (fun i => (a.val i).val))) =>
        (M.basis a.1.val a.2 : L))) := by
  rw [M.filtration.weightedLayer_eq_finite]
  simp only [LieSubmodule.iSup_toSubmodule]
  apply le_antisymm
  · apply iSup_le
    intro a
    change M.filtration.layer (fun i => (a.val i).val) ≤ _
    rw [← span_submodule_basis _ (M.basis a.val)]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact Submodule.subset_span ⟨⟨a, j⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨a, j⟩, rfl⟩
    exact Submodule.mem_iSup_of_mem a (M.basis a.val j).property

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AdaptedBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L)

theorem exists_adapted_basis_and_grid {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤)
    (Γ : Subgroup F.Group) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ i j k, RationalHeightLE (e.repr (v i j : L) k) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      Monotone w ∧ IsCentralLieBasis b ∧
      (∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, RationalHeightLE (e.repr (b j) i) H) ∧
      (∀ i j, RationalHeightLE (b.repr (e i) j) (rationalSolveHeight (finrank ℚ L) H)) ∧
      (∀ i j k, ((lieStructureConstants b i j k).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧
        ((lieStructureConstants b i j k).den : ℝ) ≤ Real.exp ((p + 2) ^ 11)) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ ∧
      bchSubgroupCoordinates b Γ ⊆ denominatorGrid N := by
  obtain ⟨b, w, hw, _, hcentral, hb, hlayer⟩ := F.exists_bounded_sorted_adapted_basis e v hspan hv
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis e] using hd
  obtain ⟨N, hN, hNp, hin, hout⟩ :=
    exists_basis_change_grid_exp_bound e b Γ hH hl hb hinner houter hp hd hr hHp hlp
  have hbinv := inverse_basis_entries_height e b hH hb
  have hstructure := basis_change_structure_height e b hH hb hc
  have hbudget := rationalLieStructureHeight_inverse_budget (Fintype.card ι)
    (Fintype.card (Fin (finrank ℚ L))) H hp hd hr hHp
  refine ⟨b, w, N, hw, hcentral, hlayer, hb, ?_, ?_, hN, hNp, hin, hout⟩
  · simpa only [Fintype.card_fin] using hbinv
  · intro i j k
    exact ⟨(Nat.cast_le.mpr (hstructure i j k).1).trans hbudget,
      (Nat.cast_le.mpr (hstructure i j k).2).trans hbudget⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalPowerHeight
namespace OAI

section

namespace Erdos3

theorem mem_boundedRationalCandidates {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) :
    q ∈ boundedRationalCandidates H := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(q.num, q.den), Finset.mem_product.mpr ⟨?_, ?_⟩, Rat.num_div_den q⟩
  · apply Finset.mem_Icc.mpr
    have hn : |q.num| ≤ (H : ℤ) := by
      simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hq.1)
    exact abs_le.mp hn
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hq.2)

theorem finite_card_bounded_height_arrays {ι : Type*} [Fintype ι]
    (S : Set (ι → ℚ)) (H : ℕ) (hS : ∀ x ∈ S, ∀ i, RationalHeightLE (x i) H) :
    S.Finite ∧ S.ncard ≤ ((2 * H + 1) * (H + 1)) ^ Fintype.card ι := by
  classical
  let f : S → (ι → ↥(boundedRationalCandidates H)) :=
    fun x i => ⟨x.val i, mem_boundedRationalCandidates (hS x x.property i)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  let : Finite S := Finite.of_injective f hf
  have hc := Nat.card_le_card_of_injective f hf
  have hb := Nat.pow_le_pow_left (boundedRationalCandidates_card H) (Fintype.card ι)
  refine ⟨Set.toFinite S, ?_⟩
  have hbound : S.ncard ≤ (boundedRationalCandidates H).card ^ Fintype.card ι := by
    simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      Fintype.card_fun, Fintype.card_coe] using hc
  exact hbound.trans hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ K Ξ : Type*} [LieRing K] [LieAlgebra ℚ K] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
  (D : RationalFilteredNilmanifold K s d) {w : σ → ℕ}

noncomputable def sectionNiltest
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a))
    (a : Option Ξ) : D.Niltest w where
  orbit := g
  observable := fun z => (frozenRealSection F a z : ℂ)
  normBound := 1
  lipBound := M
  norm_le z := by
    have h := frozenRealSection_unit_interval F hF a z
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1, NNReal.coe_one] using h.2
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    cases a with
    | none =>
      change dist (0 : ℂ) 0 ≤ (M : ℝ) * dist x y
      rw [dist_self]
      positivity
    | some a =>
      change dist (F x a : ℂ) (F y a : ℂ) ≤ (M : ℝ) * dist x y
      simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using
        (hLip a).dist_le_mul x y

theorem sectionNiltest_complexityLE
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a))
    (a : Option Ξ) {p : ℝ} (hD : D.GeometryComplexityLE p)
    (hbudget : Real.log (3 + (M : ℝ)) ≤ p) :
    (D.sectionNiltest g F hF M hLip a).ComplexityLE p := by
  refine ⟨hD, ?_⟩
  change Real.log (2 + (1 : ℝ) + (M : ℝ)) ≤ p
  norm_num only [show (2 : ℝ) + 1 = 3 by norm_num]
  exact hbudget

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NativeGridRightDictionary
namespace OAI

section

namespace Erdos3

theorem finite_card_real_grid_box {ι : Type*} [Fintype ι]
    (S : Set (ι → ℝ)) (l N : ℕ) (hl : 0 < l) {B : ℝ}
    (hgrid : S ⊆ realDenominatorGrid l)
    (hbound : ∀ x ∈ S, ∀ i, |x i| ≤ B)
    (hN : (l : ℝ) * B ≤ N) :
    S.Finite ∧ S.ncard ≤ (2 * N + 1) ^ Fintype.card ι := by
  classical
  let z : S → ι → ℤ := fun x => Classical.choose (hgrid x.property)
  have hz (x : S) (i : ι) : (z x i : ℝ) = (l : ℝ) * x.val i :=
    congrFun (Classical.choose_spec (hgrid x.property)) i
  have hzi (x : S) (i : ι) : z x i ∈ Set.Icc (-(N : ℤ)) N := by
    have hb : |(z x i : ℝ)| ≤ (N : ℝ) := by
      rw [hz, abs_mul, abs_of_nonneg (Nat.cast_nonneg l)]
      exact (mul_le_mul_of_nonneg_left (hbound x x.property i) (Nat.cast_nonneg l)).trans hN
    apply abs_le.mp
    exact_mod_cast hb
  let f : S → (ι → Set.Icc (-(N : ℤ)) N) := fun x i => ⟨z x i, hzi x i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : z x i = z y i := congrArg Subtype.val (congrFun hxy i)
    apply mul_left_cancel₀ (show (l : ℝ) ≠ 0 by exact_mod_cast hl.ne')
    rw [← hz, ← hz, hi]
  let : Finite S := Finite.of_injective f hf
  have hcardI : Fintype.card (Set.Icc (-(N : ℤ)) N) = 2 * N + 1 := by
    have h := Int.card_fintype_Icc_of_le (-(N : ℤ)) N (show -(N : ℤ) ≤ N + 1 by omega)
    omega
  refine ⟨Set.toFinite S, ?_⟩
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fun, hcardI] using hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_coordinateBox_cover {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d H : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) {ε : ℝ} (hε : 0 < ε) :
    let n := (boxCoverMeshCount B (bchBoxMetricConstant s d H B) ε + 1) ^ d
    ∃ centers : Fin n → coordinateBox
        (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B,
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ)
      ∀ x : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ) B, ∃ j, dist x (centers j) ≤ ε := by
  classical
  have hcover := exists_coordinateBox_metric_cover
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ) (lieStructureConstants D.basis)
    (fun i j k => (realLieBasis_structure D.basis i j k).symm) hc B hB hε
  change ∃ centers : (Fin d → Fin (boxCoverMeshCount B
      (bchBoxMetricConstant s (Fintype.card (Fin d)) H B) ε + 1)) →
      coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B,
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      ∀ x : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B, ∃ j, dist x (centers j) ≤ ε at hcover
  rw [Fintype.card_fin] at hcover
  obtain ⟨c, hc⟩ := hcover
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let N := boxCoverMeshCount B (bchBoxMetricConstant s d H B) ε
  let I := Fin d → Fin (N + 1)
  have hcard : Fintype.card I = (N + 1) ^ d := by simp only [I, Fintype.card_fun, Fintype.card_fin]
  let e : I ≃ Fin ((N + 1) ^ d) := Fintype.equivFinOfCardEq hcard
  refine ⟨fun i => c (e.symm i), ?_⟩
  intro x
  obtain ⟨j, hj⟩ := hc x
  refine ⟨e j, ?_⟩
  simpa only [e.symm_apply_apply] using hj

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCentralSeed
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def basisFrequency {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (n : S → ℤ) : L →ₗ[ℚ] ℚ :=
  ∑ j : S, ((n j : ℚ) / (N : ℚ)) • b.coord j

theorem basisFrequency_apply {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (n : S → ℤ) (v : L) :
    basisFrequency b S N n v = ∑ j : S, ((n j : ℚ) / (N : ℚ)) * b.repr v j := by
  simp [basisFrequency, Basis.coord_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedQuotientFamilyFaithful
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {α ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

omit [Fintype ι] in
theorem realQuotientFamily_joint_injective
    (I : α → LieIdeal ℚ L) (hI : ∀ a, F.layer (t + 1) ≤ (I a).toSubmodule)
    (S : α → Set ι) (hspan : ∀ a, (I a).toSubmodule = Submodule.span ℚ (b '' S a))
    (hcover : ∀ i, ∃ a, i ∉ S a) :
    Function.Injective (fun g : F.realification.Group => fun a => F.realQuotientStepHom (I a) (hI a) g) := by
  intro g h heq
  apply NilpotentLieBCHGroup.ext
  apply (b.baseChange ℝ).repr.injective
  ext i
  obtain ⟨a, ha⟩ := hcover i
  have hc := congrArg (fun v : (F.quotientLie (I a) (hI a)).realification.Group =>
    ((supportedQuotientBasis b (I a).toSubmodule (S a) (hspan a)).baseChange ℝ).repr
      v.coord ⟨i, ha⟩) (congrFun heq a)
  change ((supportedQuotientBasis b (I a).toSubmodule (S a) (hspan a)).baseChange ℝ).repr
    ((I a).toSubmodule.mkQ.baseChange ℝ g.coord) ⟨i, ha⟩ =
    ((supportedQuotientBasis b (I a).toSubmodule (S a) (hspan a)).baseChange ℝ).repr
      ((I a).toSubmodule.mkQ.baseChange ℝ h.coord) ⟨i, ha⟩ at hc
  simpa only [realSupportedQuotientBasis_repr_mk] using hc

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SourceLatticeCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

noncomputable def withLattice {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (Λ : Subgroup D.filtration.Group)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold L s d :=
  { D with lattice := Λ, grid := N, grid_pos := hN, inner_grid := hin, outer_grid := hout }

theorem withLattice_geometry {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (Λ : Subgroup D.filtration.Group)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
    (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
    {p q : ℝ} (hD : D.GeometryComplexityLE p) (hpq : p ≤ q) (hNb : (N : ℝ) ≤ Real.exp q) :
    (D.withLattice Λ N hN hin hout).GeometryComplexityLE q :=
  ⟨hD.1.trans hpq, hNb, fun i j k => (hD.2.2.1 i j k).trans hpq,
    fun i j k => (hD.2.2.2 i j k).trans hpq⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix

theorem bchSubgroupCoordinates_comap_ofSteps
    {ι κ L M : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
    (b : Basis ι ℚ L) (e : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup M t hM)) :
    bchSubgroupCoordinates b (Γ.comap (mapOfSteps (hL := hL) φ)) =
      (LinearMap.toMatrix b e φ.toLinearMap).mulVec ⁻¹' bchSubgroupCoordinates e Γ := by
  ext x
  change ((⟨φ (b.equivFun.symm x)⟩ : NilpotentLieBCHGroup M t hM) ∈ Γ) ↔
    ((⟨e.equivFun.symm (LinearMap.toMatrix b e φ.toLinearMap *ᵥ x)⟩ :
      NilpotentLieBCHGroup M t hM) ∈ Γ)
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

abbrev RankAlphabet := Σ i : Fin (s + 1), Fin (finrank ℚ (D.filtration.layer (i.val + 1)))

def rankAlphabetWeight (a : D.RankAlphabet) : ℕ := a.1.val + 1

noncomputable def rankAlphabetVector (a : D.RankAlphabet) : L := D.layerBasis a.1 a.2

theorem rankAlphabetWeight_pos (a : D.RankAlphabet) : 0 < D.rankAlphabetWeight a := Nat.succ_pos _

theorem rankAlphabetVector_mem (a : D.RankAlphabet) :
    D.rankAlphabetVector a ∈ D.filtration.layer (D.rankAlphabetWeight a) :=
  (D.layerBasis a.1 a.2).property

theorem rankAlphabet_spans_layer (i : ℕ) (hi : 0 < i) :
    D.filtration.layer i ≤ Submodule.span ℚ
      (D.rankAlphabetVector '' {a | D.rankAlphabetWeight a = i}) := by
  by_cases his : i ≤ s + 1
  · let j : Fin (s + 1) := ⟨i - 1, by omega⟩
    have hj : j.val + 1 = i := by dsimp [j]; omega
    have heq : D.filtration.layer i = Submodule.span ℚ
        (Set.range (fun k => ((D.layerBasis j k : D.filtration.layer (j.val + 1)) : L))) := by
      rw [span_submodule_basis, hj]
    rw [heq]
    apply Submodule.span_mono
    rintro x ⟨k, rfl⟩
    exact ⟨⟨j, k⟩, hj, rfl⟩
  · have hbot : D.filtration.layer i = ⊥ := by
      apply bot_unique
      exact (D.filtration.antitone (show s + 1 ≤ i by omega)).trans D.filtration.terminal.le
    rw [hbot]
    exact bot_le

theorem rankAlphabet_span_layer (i : ℕ) (hi : 0 < i) :
    Submodule.span ℚ (D.rankAlphabetVector '' {a | D.rankAlphabetWeight a = i}) =
      D.filtration.layer i := by
  apply le_antisymm _ (D.rankAlphabet_spans_layer i hi)
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, rfl⟩
  exact ha ▸ D.rankAlphabetVector_mem a

noncomputable def finiteRankGenerators (i r : ℕ) : Finset L := by
  classical
  exact ((Finset.univ.filter (fun a : D.RankAlphabet => D.rankAlphabetWeight a = i + 1)).image
    D.rankAlphabetVector) ∪ finiteWeightedLieValues D.rankAlphabetVector D.rankAlphabetWeight i r

theorem finiteRankGenerators_span (i r : ℕ) :
    Submodule.span ℚ (D.finiteRankGenerators i r : Set L) = D.filtration.rankLayer i r := by
  classical
  rw [D.filtration.rankLayer_eq_weighted_tree_span D.rankAlphabetVector D.rankAlphabetWeight
    D.rankAlphabetWeight_pos D.rankAlphabetVector_mem D.rankAlphabet_spans_layer]
  rw [weightedLieTreeSpan_eq_finite_span _ _ D.rankAlphabetWeight_pos]
  have hleaf : Submodule.span ℚ
      (((Finset.univ.filter (fun a : D.RankAlphabet => D.rankAlphabetWeight a = i + 1)).image
        D.rankAlphabetVector : Finset L) : Set L) = D.filtration.layer (i + 1) := by
    simpa only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ,
      true_and] using D.rankAlphabet_span_layer (i + 1) (Nat.succ_pos i)
  change Submodule.span ℚ ((_ ∪ _ : Finset L) : Set L) = _
  rw [Finset.coe_union, Submodule.span_union, hleaf]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem finiteRankGenerators_height {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hb : ∀ i j k, RationalHeightLE (D.basis.repr (D.layerBasis i j) k) H)
    (i r : ℕ) (hi : i ≤ s) (x : L) (hx : x ∈ D.finiteRankGenerators i r) (k : Fin d) :
    RationalHeightLE (D.basis.repr x k) (lieTreeHeight d H s) := by
  classical
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h
    exact (hb a.1 a.2 k).mono (lieTreeHeight_ge_input d H s)
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    have h := finiteLieTrees_coordinate_height D.basis D.rankAlphabetVector hc
      (fun a j => hb a.1 a.2 j) i a (Finset.mem_filter.mp ha).1 k
    simp only [Fintype.card_fin] at h
    exact h.mono (lieTreeHeight_mono d H hi)

theorem exists_rankLayer_basis_height {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hb : ∀ i j k, RationalHeightLE (D.basis.repr (D.layerBasis i j) k) H)
    (i r : ℕ) (hi : i ≤ s) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.rankLayer i r))) ℚ (D.filtration.rankLayer i r),
      ∀ j k, RationalHeightLE (D.basis.repr (b j : L) k) (lieTreeHeight d H s) := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (D.finiteRankGenerators i r : Set L)
  rw [D.finiteRankGenerators_span] at hex
  obtain ⟨v, hv, hvspan, hli⟩ := hex
  refine ⟨(Basis.span hli).map (LinearEquiv.ofEq _ _ hvspan), ?_⟩
  intro j k
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  exact D.finiteRankGenerators_height hc hb i r hi (v j) (hv j) k

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ V : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]

theorem exists_bounded_submodule_quotient_basis (b : Basis ι ℚ V) (U : Submodule ℚ V)
    (v : κ → V) (hspan : Submodule.span ℚ (Set.range v) = U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∃ t : ℕ, t ≤ Fintype.card κ ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ f : Basis (Fin d) ℚ (V ⧸ U),
        ∀ i j, RationalHeightLE (f.repr (U.mkQ (b j)) i) (rationalKernelHeight t H) := by
  classical
  let A : Matrix ι κ ℚ := fun i j => b.repr (v j) i
  have hA : LinearMap.range A.mulVecLin = U.map b.equivFun.toLinearMap := by
    rw [Matrix.range_mulVecLin, ← hspan, Submodule.map_span, ← Set.range_comp]
    rfl
  obtain ⟨t, ht, d, hd, D, hsurj, hker, hD⟩ :=
    exists_bounded_image_equations A hH (fun i j => hv j i)
  have hkerD := hker.trans hA
  let f := submoduleQuotientCoordinateBasis b U D hkerD hsurj
  have hf : LinearMap.toMatrix b f U.mkQ = D :=
    submoduleQuotientCoordinateBasis_matrix b U D hkerD hsurj
  refine ⟨t, ht, d, hd, f, fun i j => ?_⟩
  have hij := congrFun (congrFun hf i) j
  rw [LinearMap.toMatrix_apply] at hij
  rw [hij]
  exact hD i j

theorem exists_submodule_quotient_basis_exp (b : Basis ι ℚ V) (U : Submodule ℚ V)
    (v : κ → V) (hspan : Submodule.span ℚ (Set.range v) = U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hm : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
      ∃ d : ℕ, d ≤ Fintype.card ι ∧ ∃ f : Basis (Fin d) ℚ (V ⧸ U),
        ∀ i j, RationalHeightLE (f.repr (U.mkQ (b j)) i) H' := by
  obtain ⟨t, ht, d, hd, f, hf⟩ := exists_bounded_submodule_quotient_basis b U v hspan hH hv
  exact ⟨rationalKernelHeight t H, rationalKernelHeight_pos t hH,
    rationalKernelHeight_le_budget t H hp ((Nat.cast_le.mpr ht).trans hm) hHp,
    d, hd, f, hf⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealifiedCentralBasisAction
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

variable (e : Basis ι ℚ L) (b : Basis κ ℚ L)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
  (N : ℕ) (hinner : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)

noncomputable def realifiedCentralBasisAction (j : κ) (hj : ∀ w : L, ⁅b j, w⁆ = 0) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    CircleFourier.IsometricCircleAction
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) ⧸
        Γ.map realificationHom) :=
  centralBCHCircleAction (e.baseChange ℝ) (Γ.map realificationHom)
    (realification_subgroup_closed_discrete e Γ l hl houter).1
    ((N : ℝ) • (b.baseChange ℝ) j) (scaled_real_basis_central b j hj N)
    (scaled_real_basis_mem_realification b Γ N hinner j)

theorem realifiedCentralBasisAction_act_coe (j : κ) (hj : ∀ w : L, ⁅b j, w⁆ = 0)
    (r : ℝ) (x : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hnil) ⧸ Γ.map realificationHom) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    (realifiedCentralBasisAction e b Γ l hl houter N hinner j hj).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := realification_lowerCentralSeries_eq_bot hnil)
        ((N : ℝ) • (b.baseChange ℝ) j) r • x := by
  let := realificationQuotientMetricSpace e Γ l hl houter
  exact centralBCHCircleAction_act_coe _ _ _ _ _ _ r x

theorem realifiedCentralBasisAction_displacement (j : κ) (hj : ∀ w : L, ⁅b j, w⁆ = 0)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, |(e.repr (b j) i : ℝ)| ≤ B)
    (t : CircleFourier.Circle) (x : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hnil) ⧸ Γ.map realificationHom) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    dist ((realifiedCentralBasisAction e b Γ l hl houter N hinner j hj).act t x) x ≤
      ((Fintype.card ι : ℝ) + 1) * ((N : ℝ) * B) * ‖t‖ := by
  let := realificationQuotientMetricSpace e Γ l hl houter
  apply (centralBCHCircleAction_displacement _ _ _ _ _ _ t x).trans
  exact mul_le_mul_of_nonneg_right (scaled_real_basis_coordinate_bound e b N j hB hb) (norm_nonneg t)

theorem realifiedCentralBasisAction_commutes (i j : κ)
    (hi : ∀ w : L, ⁅b i, w⁆ = 0) (hj : ∀ w : L, ⁅b j, w⁆ = 0) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    (realifiedCentralBasisAction e b Γ l hl houter N hinner i hi).Commutes
      (realifiedCentralBasisAction e b Γ l hl houter N hinner j hj) := by
  let := realificationQuotientMetricSpace e Γ l hl houter
  exact centralBCHCircleAction_commutes _ _ _ _ _ _ _ _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realificationLieHom_id_apply {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (x : ℝ ⊗[ℚ] L) : realificationLieHom (LieHom.id : L →ₗ⁅ℚ⁆ L) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialGridValues
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_slow_polynomial_metric_budget (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d n H : ℕ) (p M : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      0 ≤ M → M ≤ Real.exp ((p + 2) ^ r) →
      ∃ B : ℝ≥0, 1 ≤ B ∧
        ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * M ≤ B ∧
        (bchBoxMetricConstant s d H B : ℝ) *
          (((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * M * n * s) ≤
            Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C s * (X + 1) + (X + 2) ^ r
  obtain ⟨a, _, hP⟩ := exists_natPolynomial_eval_budget P
  obtain ⟨b, _, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s a
  let Q := (X + Polynomial.C a + Polynomial.C b) ^ b + P + X + Polynomial.C s
  obtain ⟨C, hC, hQ⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro d n H p M hp hd hn hH hM hMp
  let q : ℝ := s * (p + 1) + (p + 2) ^ r
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let B : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := Real.one_le_exp hq
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hAM : ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * M ≤ Real.exp q := by
    calc
      _ ≤ Real.exp s * (Real.exp p) ^ s * Real.exp ((p + 2) ^ r) :=
        mul_le_mul (mul_le_mul (Real.add_one_le_exp (s : ℝ))
          (pow_le_pow_left₀ (by positivity) hn1 _) (by positivity) (Real.exp_pos _).le)
          hMp hM (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [q]; ring
  have hpA : p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hBa : (B : ℝ) ≤ Real.exp (((p + a) + 2) ^ a) := by
    apply Real.exp_le_exp.mpr
    have h := hP p hp
    have h' : q ≤ (p + a) ^ a := by simpa [P, X, q, Polynomial.eval₂_pow] using h
    exact h'.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  have hBC : (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + a + b) ^ b) :=
    hbox d H B (p + a) (hp.trans hpA) (hd.trans hpA)
      (hH.trans (Real.exp_le_exp.mpr hpA)) hBa
  have hnexp : (n : ℝ) ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hsexp : (s : ℝ) ≤ Real.exp s := by linarith [Real.add_one_le_exp (s : ℝ)]
  refine ⟨B, hB, hAM, ?_⟩
  calc
    _ ≤ Real.exp ((p + a + b) ^ b) * (Real.exp q * Real.exp p * Real.exp s) := by
      apply mul_le_mul hBC
        (mul_le_mul (mul_le_mul hAM hnexp (Nat.cast_nonneg _) (Real.exp_pos _).le)
          hsexp (Nat.cast_nonneg _) (by positivity))
        (by positivity) (Real.exp_pos _).le
    _ = Real.exp (((p + a + b) ^ b) + q + p + s) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((p + C) ^ C) := by
      apply Real.exp_le_exp.mpr
      simpa [Q, P, X, q, Polynomial.eval₂_pow] using hQ p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UniformPolynomialPeriodBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

theorem exists_uniformPolynomialBCHPeriod_exp_bound (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ L : Type*} [Fintype ι] [Fintype σ]
      [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (l H q : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  obtain ⟨K, hK, hden⟩ := exists_conjugation_denominator_exp_bound s
  refine ⟨K + r + s + 10, by omega, ?_⟩
  intro ι σ L _ _ _ _ e l H q p hp hd hn hH hlb hqb hc
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    uniformPolynomialBCHPeriod_le_exp (σ := σ) e K s r l q hp hd hn hlb hqb
    (hden e H p hp hd hH hc)

theorem realPolynomialBCHMap_uniform_cosets {ι σ L : Type*} [Fintype ι] [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hP : ∀ i α, ((P i).coeff α).den ∣ q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ)
    (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℤ) ∣ x j - y j) :
    let f := fun z : σ → ℤ => realPolynomialBCHMap
      (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ) P
      (fun j => (z j : ℝ))
    ((QuotientGroup.mk (f x) : _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) =
      QuotientGroup.mk (f y)) ∧
    ((QuotientGroup.mk (f x)⁻¹ : _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) =
      QuotientGroup.mk (f y)⁻¹) := by
  dsimp only
  constructor
  · rw [realPolynomialBCHMap_integer, realPolynomialBCHMap_integer]
    exact realification_coset_eq Γ _ _
      (polynomialBCHMap_uniform_coset_eq e hnil Γ r l q P hdegree hP hinner x y hxy)
  · rw [realPolynomialBCHMap_integer, realPolynomialBCHMap_integer,
      ← map_inv, ← map_inv]
    exact realification_coset_eq Γ _ _
      (polynomialBCHMap_uniform_inverse_coset_eq e hnil Γ r l q P hdegree hP hinner x y hxy)

end Erdos3

end

end OAI
end


