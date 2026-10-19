-- Prove2me | Definitions.Def_OAIE3v2B152
-- name    : OAIE3v2B152
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:06:45.946974+00:00
-- url     : https://prove2.me/theorems/c60d99d6-88da-48d9-975c-4ae73eda095e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 154 of 311
-- statement:
--   Definitions bundle 154 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B140`, `OAIE3v2B141`, `OAIE3v2B142`, `OAIE3v2B143` of this split.
--
--   Modules: `Estimates/CommonRefilteredFactorization.lean`, `Estimates/CubicAntisymmetricTransfer.lean`, `Estimates/FormalInductionTerminal.lean`, `Estimates/NativeBinaryAssignments.lean`, `Estimates/NativeMixedReflectionBridge.lean`, `Estimates/NativeSpaceMap.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/OptionMarkedSurjective.lean`, `Estimates/SquarefreeRealAction.lean`, `Estimates/UniformControlledNativeExternalNetsOfRecovery.lean`, `Fourier/BohrNiltestBudget.lean`, `Geometry/MixedEvaluationCoordinates.lean`, `Geometry/MixedReplicatedCoordinates.lean`, `Geometry/NativeMixedCoordinateSlices.lean`, `Geometry/SquarefreeActionMetric.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/NativeRankQuotientOrbit.lean`, `Nilpotent/ComparisonLayerBracket.lean`, `Nilpotent/FreeDegreeRankNilmanifold.lean`, `Nilpotent/LocalMajorDenseSliceNiltest.lean`, `Nilpotent/NiltestComplement.lean`, `Polynomial/FreeDegreeRankAdaptedBounds.lean`, `Polynomial/NativePolynomialOrbit.lean`, `Polynomial/OptionMarkedPolynomialProjection.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`, `Polynomial/PolynomialShiftStructure.lean`, `Polynomial/PositivePolynomialLayerBases.lean`, `Polynomial/RaisedDegreeRank.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B140
import Definitions.Def_OAIE3v2B141
import Definitions.Def_OAIE3v2B142
import Definitions.Def_OAIE3v2B143

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalInductionTerminal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}

structure FormalInductionRun (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L)
    (w : μ → ℕ) (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (eK : Basis κ ℚ K) (T : σ → ℝ)
    (original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) (r : ℕ) (q : ℝ) where
  state : F.FormalInductionState b w U V K eK T (2 + r) q
  left : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
  right : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp ((r + 1 : ℝ) * q)
  state_denominator_dvd : state.denominator ∣ denominator
  left_length : left.length = 2 * r
  right_length : right.length = 2 * r
  left_good : ∀ g ∈ left, F.FormalCorrectionProperty b w U g
  right_good : ∀ g ∈ right, F.FormalCorrectionProperty b w U g
  left_bound : ∀ g ∈ left, CoefficientBound (b.baseChange ℝ) T (Real.exp q) g.coord
  right_grid : ∀ g ∈ right, CoefficientGrid (b.baseChange ℝ) denominator g.coord
  factorization : left.prod * state.P * right.prod = original

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ}

noncomputable def FormalInductionRun.extend
    {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot} {r : ℕ} {q q' : ℝ}
    (W : F.FormalInductionRun b w U V K eK T original r q)
    (hq : q ≤ q') (hT : ∀ i, 0 < T i)
    (Y : F.FormalInductionState b w U V K eK T (2 + (r + 1)) q')
    (A₁ A₂ B₁ B₂ : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hfactor : (A₁ * A₂) * Y.P * (B₂ * B₁) = W.state.P)
    (hA₁ : F.FormalCorrectionProperty b w U A₁)
    (hA₂ : F.FormalCorrectionProperty b w U A₂)
    (hB₁ : F.FormalCorrectionProperty b w U B₁)
    (hB₂ : F.FormalCorrectionProperty b w U B₂)
    (hA₁bound : CoefficientBound (b.baseChange ℝ) T (Real.exp q') A₁.coord)
    (hA₂bound : CoefficientBound (b.baseChange ℝ) T (Real.exp q') A₂.coord)
    (hB₁grid : CoefficientGrid (b.baseChange ℝ) Y.denominator B₁.coord)
    (hB₂grid : CoefficientGrid (b.baseChange ℝ) Y.denominator B₂.coord) :
    F.FormalInductionRun b w U V K eK T original (r + 1) q' := by
  refine {
    state := Y
    left := W.left ++ [A₁, A₂]
    right := [B₂, B₁] ++ W.right
    denominator := W.denominator * Y.denominator
    denominator_pos := Nat.mul_pos W.denominator_pos Y.denominator_pos
    denominator_bound := ?_
    state_denominator_dvd := dvd_mul_left _ _
    left_length := ?_
    right_length := ?_
    left_good := ?_
    right_good := ?_
    left_bound := ?_
    right_grid := ?_
    factorization := ?_ }
  · have hmul : (r + 1 : ℝ) * q ≤ (r + 1 : ℝ) * q' :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    calc
      ((W.denominator * Y.denominator : ℕ) : ℝ) =
          (W.denominator : ℝ) * (Y.denominator : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp ((r + 1 : ℝ) * q') * Real.exp q' :=
        mul_le_mul (W.denominator_bound.trans (Real.exp_le_exp.mpr hmul))
          Y.denominator_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((r + 1 + 1 : ℝ) * q') := by rw [← Real.exp_add]; congr 1; ring
      _ = Real.exp (((r + 1 : ℕ) + 1 : ℝ) * q') := by push_cast; rfl
  · simp only [List.length_append, List.length_cons, List.length_nil, W.left_length]
    omega
  · simp only [List.length_append, List.length_cons, List.length_nil, W.right_length]
    omega
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact W.left_good g hg
    · exact hA₁
    · exact hA₂
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (rfl | rfl) | hg
    · exact hB₂
    · exact hB₁
    · exact W.right_good g hg
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact (W.left_bound g hg).mono _ T hT (Real.exp_le_exp.mpr hq)
    · exact hA₁bound
    · exact hA₂bound
  · intro g hg α
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (rfl | rfl) | hg
    · exact realDenominatorGrid_subset_of_dvd Y.denominator_pos
        (dvd_mul_left _ _) (hB₂grid α)
    · exact realDenominatorGrid_subset_of_dvd Y.denominator_pos
        (dvd_mul_left _ _) (hB₁grid α)
    · exact realDenominatorGrid_subset_of_dvd W.denominator_pos
        (dvd_mul_right _ _) (W.right_grid g hg α)
  · have h : W.left.prod * ((A₁ * A₂) * Y.P * (B₂ * B₁)) * W.right.prod = original := by
      rw [hfactor]
      exact W.factorization
    simpa only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FreeDegreeRankAdaptedBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_free_degree_rank_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (r : ℕ) (w : X → ℕ)
      (hw : ∀ x, 0 < w x) (p : ℝ), 0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ
          (FreeDegreeRankLieAlgebra X s r w hw),
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) i) ≤ (p + C) ^ C) ∧
        ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
          (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
          (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
          ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s)))
              (Fin (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw))) ℚ,
            LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap * S = 1 ∧
            ∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hmodel⟩ := exists_bounded_free_weighted_model s
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let V₀ : Polynomial ℕ := (Polynomial.C (s + 1) * (Polynomial.X + 2) ^ (3 ^ s) + 2) ^ (3 ^ s)
  let T₀ := B₀ + V₀ + (B₀ + 3) ^ (6 * s + 2) + 2
  let W₀ := T₀ + (T₀ + 3) ^ 51
  let R₀ := (W₀ + 2) ^ 4 + W₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R₀ + (R₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro X _ r w hw p hp hX
  classical
  let B := (p + a) ^ a
  let V := (((s + 1 : ℕ) : ℝ) * (p + 2) ^ (3 ^ s) + 2) ^ (3 ^ s)
  let E := (B + 3) ^ (6 * s + 2)
  let T := B + V + E + 2
  let W := T + (T + 3) ^ 51
  let R := (W + 2) ^ 4 + W
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hBT : B ≤ T := (le_add_of_nonneg_right hV).trans
    ((le_add_of_nonneg_right hE).trans (le_add_of_nonneg_right (by norm_num)))
  have hVT : V ≤ T := (le_add_of_nonneg_left hB).trans
    ((le_add_of_nonneg_right hE).trans (le_add_of_nonneg_right (by norm_num)))
  have hET : E ≤ T := (le_add_of_nonneg_left (add_nonneg hB hV)).trans
    (le_add_of_nonneg_right (by norm_num))
  have hT : 0 ≤ T := hB.trans hBT
  have hTW : T ≤ W := le_add_of_nonneg_right (by positivity)
  have hW : 0 ≤ W := hT.trans hTW
  have hWR : W ≤ R := le_add_of_nonneg_left (by positivity)
  have hR : 0 ≤ R := hW.trans hWR
  have hprojR : (W + 2) ^ 4 ≤ R := le_add_of_nonneg_right hW
  have hsmall (k : ℕ) (hk : k ≤ 51) : (T + 1 + 2) ^ k ≤ W := by
    rw [show T + 1 + 2 = T + 3 from
      (add_assoc T 1 2).trans (congrArg (fun z : ℝ => T + z) (by norm_num))]
    exact (pow_le_pow_right₀ (by linarith only [hT]) hk).trans (le_add_of_nonneg_left hT)
  have hsum : R + (R + 3) ^ 5 ≤ (p + C) ^ C := by
    simpa [B₀, V₀, T₀, W₀, R₀, B, V, E, T, W, R, Polynomial.eval₂_pow] using hbudget p hp
  have hRC : R ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (R + 3) ^ 5)).trans hsum
  have hSC : (R + 3) ^ 5 ≤ (p + C) ^ C := (le_add_of_nonneg_left hR).trans hsum
  have hBC : B ≤ (p + C) ^ C := hBT.trans (hTW.trans (hWR.trans hRC))
  obtain ⟨hdim, e, _, _, _, _, _, hc, hgen, e₀, he₀, hdim₀, _⟩ := hmodel X w hw p hp hX
  let A := FreeWeightedNilpotentLieAlgebra.topRankGenerators X s w (r + 1)
  let I := (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)
  let v : A → FreeWeightedNilpotentLieAlgebra X s w := Subtype.val
  have hrange : Set.range v = (A : Set (FreeWeightedNilpotentLieAlgebra X s w)) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule := by
    rw [hrange]
    exact FreeWeightedNilpotentLieAlgebra.topRankGenerators_span X s w hw (r + 1)
  have hcount : (Fintype.card A : ℝ) ≤ V := by
    have hcard := FreeWeightedNilpotentLieAlgebra.topRankGenerators_card_le X s w (r + 1)
    have hbase := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Fintype.card X + 2)
      (add_le_add hX (le_refl (2 : ℝ))) (3 ^ s)
    calc
      _ ≤ (((s + 1 : ℕ) : ℝ) * ((Fintype.card X : ℝ) + 2) ^ (3 ^ s) + 2) ^ (3 ^ s) := by
        simpa only [A, Fintype.card_coe, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          using (Nat.cast_le.mpr hcard : ((FreeWeightedNilpotentLieAlgebra.topRankGenerators X s w (r + 1)).card : ℝ) ≤ _)
      _ ≤ V := pow_le_pow_left₀ (by positivity)
        (add_le_add (mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg (s + 1))) (le_refl (2 : ℝ))) _
  have hv (i) (j : A) : rationalLogHeight (e.repr (v j) i) ≤ T :=
    (FreeWeightedNilpotentLieAlgebra.topRankGenerators_logHeight X s w e hB
      (by simpa only [Fintype.card_fin] using hdim) hc hgen (r + 1) j.val j.property i).trans hET
  obtain ⟨d, hd, b, D, _, hmatrix, _, hD, _, hbracket⟩ :=
    exists_lie_quotient_basis_exp_height e I v hspan (one_le_ceil_exp T)
      (fun i j => rationalHeightLE_ceil_exp (hv i j))
      (fun i j k => rationalHeightLE_ceil_exp ((hc i j k).trans hBT))
      (hT.trans (le_add_of_nonneg_right zero_le_one))
      (by simpa only [Fintype.card_fin] using hdim.trans (hBT.trans (le_add_of_nonneg_right zero_le_one)))
      (hcount.trans (hVT.trans (le_add_of_nonneg_right zero_le_one)))
      (ceil_exp_le_exp_add_one hT)
  change Basis (Fin d) ℚ (FreeDegreeRankLieAlgebra X s r w hw) at b
  change LinearMap.toMatrix e b (FreeDegreeRankLieAlgebra.mk X s r w hw).toLinearMap = D at hmatrix
  have hfin : finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) = d := by
    simpa only [Fintype.card_fin] using finrank_eq_card_basis b
  subst d
  have hdimq : (finrank ℚ (FreeDegreeRankLieAlgebra X s r w hw) : ℝ) ≤ B :=
    (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using hd)).trans hdim
  have hD' (i j) : rationalLogHeight (D i j) ≤ W :=
    ((rationalLogHeight_le_iff _ _).mpr (hD i j)).trans (hsmall 7 (by omega))
  have htree (x : FreeNilpotentLieAlgebra X s)
      (hx : x ∈ FreeNilpotentLieAlgebra.treeGenerators X s) (j) :
      rationalLogHeight (b.repr (FreeDegreeRankLieAlgebra.projection X s r w hw x) j) ≤ R := by
    apply le_trans _ hprojR
    apply linearMap_coordinate_logHeight e b (FreeDegreeRankLieAlgebra.mk X s r w hw).toLinearMap hW
      (by simpa only [Fintype.card_fin] using hdim.trans (hBT.trans hTW)) ?_
      (FreeWeightedNilpotentLieAlgebra.mk X s w x) (fun i => (hgen x hx i).trans (hBT.trans hTW)) j
    intro i j
    have h := hD' j i
    rw [← hmatrix, LinearMap.toMatrix_apply] at h
    exact h
  let M := LinearMap.toMatrix e₀ b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
  have hM (i j) : rationalLogHeight (M i j) ≤ R := by
    dsimp only [M]
    rw [LinearMap.toMatrix_apply]
    exact htree (e₀ j) (he₀ j) i
  obtain ⟨S, hMS, hS⟩ := exists_rational_section_exp_height M
    (basisMatrix_surjective e₀ b (FreeDegreeRankLieAlgebra.projection X s r w hw).toLinearMap
      (FreeDegreeRankLieAlgebra.projection_surjective X s r w hw))
    (one_le_ceil_exp R) (fun i j => rationalHeightLE_ceil_exp (hM i j))
    (hR.trans (le_add_of_nonneg_right zero_le_one))
    (by simpa only [Fintype.card_fin] using (hdimq.trans
      (hBT.trans (hTW.trans (hWR.trans (le_add_of_nonneg_right zero_le_one))))))
    (ceil_exp_le_exp_add_one hR)
  refine ⟨hdimq.trans hBC, b, ?_, fun x hx i => (htree x hx i).trans hRC,
    e₀, he₀, hdim₀.trans hBC, S, hMS, ?_⟩
  · intro i j k
    exact ((rationalLogHeight_le_iff _ _).mpr (hbracket i j k)).trans
      ((hsmall 51 (by omega)).trans (hWR.trans hRC))
  · intro i j
    apply le_trans ((rationalLogHeight_le_iff _ _).mpr (hS i j))
    simpa only [show R + 1 + 2 = R + 3 from
      (add_assoc R 1 2).trans (congrArg (fun z : ℝ => R + z) (by norm_num))] using hSC

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeRealAction
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparisonGraph_mem_layer (n : ℕ) (a : σ → ℕ) (ha : a ≠ 0)
    (hn : n ≤ ∑ i, a i) (x : F.layer a) :
    F.comparisonGraph π a ha x ∈ F.comparisonLayer π n :=
  (le_sup_right : F.comparisonGraphLayer π n ≤ F.comparisonLayer π n)
    (F.comparisonGraph_mem_graphLayer π n a ha hn x)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open Module
open scoped BigOperators

namespace MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparisonLayer_le_of_generators (n : ℕ) (P : Submodule ℚ (L × F.SquarefreeAlgebra π))
    (hfirst : ∀ x ∈ F.ordinary.layer (n + 1), (x, 0) ∈ P)
    (hsecond : ∀ y ∈ F.squarefreeDegreeLayer π (n + 1), (0, y) ∈ P)
    (hgraph : ∀ (a : σ → ℕ) (ha : a ≠ 0), a ≤ bound → n ≤ ∑ i, a i →
      ∀ x : F.layer a, F.comparisonGraph π a ha x ∈ P) :
    F.comparisonLayer π n ≤ P := by
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
  apply P.add_mem
  · simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      P.add_mem (hfirst u.1 hu.1) (hsecond u.2 hu.2)
  · refine F.comparisonGraphLayer_induction π n (P := fun v => v ∈ P) hv ?_ P.zero_mem ?_
    · intro a ha hn x
      by_cases hab : a ≤ bound
      · exact hgraph a ha hab hn x
      · have hx : x = 0 := by
          apply Subtype.ext
          exact (Submodule.mem_bot ℚ).mp (F.terminal a hab ▸ x.property)
        rw [hx, map_zero]
        exact P.zero_mem
    · exact fun x y hx hy => P.add_mem hx hy

end MultidegreeLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.ComparisonLayerBracket
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparisonGraphLayer_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonGraphLayer π i) (hy : y ∈ F.comparisonGraphLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonGraphLayer π (i + j) := by
  refine F.comparisonGraphLayer_induction π i
    (P := fun z => ⁅z, y⁆ ∈ F.comparisonGraphLayer π (i + j)) hx ?_ ?_ ?_
  · intro a ha hia u
    refine F.comparisonGraphLayer_induction π j
      (P := fun z => ⁅F.comparisonGraph π a ha u, z⁆ ∈ F.comparisonGraphLayer π (i + j)) hy ?_ ?_ ?_
    · intro b hb hjb v
      have hab : a + b ≠ 0 := by
        intro h
        apply ha
        funext k
        change a k = 0
        have hk : a k + b k = 0 := congrFun h k
        omega
      rw [F.comparisonGraph_lie π a b ha hb hab u v]
      apply F.comparisonGraph_mem_graphLayer π (i + j) (a + b) hab
      simpa only [Pi.add_apply, Finset.sum_add_distrib] using Nat.add_le_add hia hjb
    · rw [lie_zero]
      exact Submodule.zero_mem _
    · intro v w hv hw
      rw [lie_add]
      exact Submodule.add_mem _ hv hw
  · rw [zero_lie]
    exact Submodule.zero_mem _
  · intro u v hu hv
    rw [add_lie]
    exact Submodule.add_mem _ hu hv

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparison_lie_deep_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonLayer π i) (hy : y ∈ F.comparisonProductLayer π (j + 1)) :
    ⁅x, y⁆ ∈ F.comparisonLayer π (i + j) := by
  apply (le_sup_left : F.comparisonProductLayer π (i + j + 1) ≤ F.comparisonLayer π (i + j))
  simpa only [Nat.add_assoc] using
    F.comparisonProductLayer_lie_mem π (F.comparisonLayer_le_product π i hx) hy

theorem comparisonLayer_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonLayer π i) (hy : y ∈ F.comparisonLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonLayer π (i + j) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  rw [add_lie]
  apply Submodule.add_mem _ (F.comparison_deep_lie_mem π hu hy)
  obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  rw [lie_add]
  apply Submodule.add_mem _
    (F.comparison_lie_deep_mem π
      ((le_sup_right : F.comparisonGraphLayer π i ≤ F.comparisonLayer π i) hv) hz)
  exact (le_sup_right : F.comparisonGraphLayer π (i + j) ≤ F.comparisonLayer π (i + j))
    (F.comparisonGraphLayer_lie_mem π hv hw)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquarefreeActionMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem nativeMap_dist_le
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {s t d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hlattice : D.lattice ≤ E.lattice.comap (mapOfSteps
      (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hφ : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p)
    (u v : D.RealGroup) :
    letI := D.metricSpace
    letI := E.metricSpace
    dist (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ u) : E.Space)
      (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ v)) ≤
          Real.exp ((p + 3) ^ 2) * dist (QuotientGroup.mk u : D.Space) (QuotientGroup.mk v) := by
  let := D.metricSpace
  let := E.metricSpace
  let := realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid
  let := realificationQuotientMetricSpace E.basis E.lattice E.grid E.grid_pos E.outer_grid
  obtain ⟨K, _, hK, hLip⟩ := exists_realificationMap_quotient_lipschitz_exp_bound
    D.basis E.basis φ D.lattice E.lattice hlattice
    D.grid E.grid D.grid_pos E.grid_pos D.outer_grid E.outer_grid ⌈Real.exp p⌉₊
    (by linarith : 0 ≤ p + 1)
    (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
    (by simpa only [Fintype.card_fin] using hE.1.trans (by linarith : p ≤ p + 1))
    (ceil_exp_le_exp_add_one hp) (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  have hd := hLip.dist_le_mul (QuotientGroup.mk u) (QuotientGroup.mk v)
  change dist (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ u) : E.Space)
    (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ v)) ≤
        (K : ℝ) * dist (QuotientGroup.mk u : D.Space) (QuotientGroup.mk v) at hd
  apply hd.trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  simpa only [show p + 1 + 2 = p + 3 by ring] using hK

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSpaceMap
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

noncomputable def nativeSpaceMap : D.Space → E.Space :=
  cosetMap D.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
    (realificationMap_subgroup φ D.lattice E.lattice hφ)

theorem nativeSpaceMap_smul (z : D.RealGroup) (x : D.Space) :
    D.nativeSpaceMap E φ hφ (z • x) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ z • D.nativeSpaceMap E φ hφ x :=
  cosetMap_smul _ _ _ _ z x

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

theorem nativeSpaceMap_lipschitz {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hentries : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) :
    letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩ (D.nativeSpaceMap E φ hφ) := by
  let := D.metricSpace
  let := E.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  exact D.nativeMap_dist_le E φ hφ hp hD hE hentries u v

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalTorus

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct NNReal

abbrev BottomQuotient (d : ℕ) := Algebra d ⧸ (⊥ : LieIdeal ℚ (Algebra d))

end Erdos3.RationalTorus

end

section

namespace Erdos3.CircleFourier

theorem real_phase_map_lipschitz {ι : Type*} [Fintype ι] :
    LipschitzWith 1 (fun v : ι → ℝ => fun i => (v i : Circle)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg dist_nonneg).mpr
  intro i
  change ‖(v i : Circle) - (w i : Circle)‖ ≤ dist v w
  calc
    _ = ‖((v i - w i : ℝ) : Circle)‖ := rfl
    _ ≤ ‖v i - w i‖ := QuotientAddGroup.norm_mk_le_norm
    _ = dist (v i) (w i) := rfl
    _ ≤ dist v w := dist_le_pi_dist v w i

end Erdos3.CircleFourier

end

section

namespace Erdos3

open scoped TensorProduct NNReal

namespace RationalTorus

variable {ι : Type*} [Fintype ι] {d : ℕ} (e : ι ≃ Fin d)
  (Ψ : (ι → CircleFourier.Circle) → ℝ)

noncomputable def reindexedRealObservable : (Fin d → CircleFourier.Circle) → ℂ :=
  fun v => (Ψ (fun i => v (e i)) : ℂ)

end RationalTorus
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
namespace OAI

section

namespace Erdos3.RationalTorus

instance zeroAlgebraSubsingleton : Subsingleton (Algebra 0) :=
  inferInstanceAs (Subsingleton (Fin 0 → ℚ))

def trivialFiltration (s : ℕ) : NilpotentLieFiltration (Algebra 0) s where
  layer _ := ⊤
  antitone _ _ _ := le_rfl
  one_eq_top := rfl
  lie_mem _ _ := Submodule.mem_top
  terminal := by
    apply le_antisymm _ bot_le
    intro x _
    simpa only [Submodule.mem_bot] using (Subsingleton.elim x 0)

theorem trivialFiltration_basis_layers (s j : ℕ) :
    (trivialFiltration s).layer j = Submodule.span ℚ ((basis 0) '' {_i : Fin 0 | j ≤ (0 : ℕ)}) := by
  ext x
  rw [Subsingleton.elim x 0]
  simp only [Submodule.zero_mem]

theorem trivial_lattice_inner_grid (s : ℕ) :
    scaledIntegerGrid 1 ⊆ bchSubgroupCoordinates (basis 0) (⊤ : Subgroup (trivialFiltration s).Group) := by
  intro x _
  trivial

theorem trivial_lattice_outer_grid (s : ℕ) :
    bchSubgroupCoordinates (basis 0) (⊤ : Subgroup (trivialFiltration s).Group) ⊆ denominatorGrid 1 := by
  intro x _
  exact ⟨0, fun i => Fin.elim0 i⟩

noncomputable def trivialNilmanifold (s : ℕ) : RationalFilteredNilmanifold (Algebra 0) s 0 :=
  (trivialFiltration s).ofAdaptedBasis (basis 0) (fun _ => 0) (trivialFiltration_basis_layers s)
    ⊤ 1 (by omega) (trivial_lattice_inner_grid s) (trivial_lattice_outer_grid s)

theorem trivialNilmanifold_geometry (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (trivialNilmanifold s).GeometryComplexityLE p := by
  apply (trivialFiltration s).ofAdaptedBasis_geometry (basis 0) (fun _ => 0)
    (trivialFiltration_basis_layers s) ⊤ 1 (by omega)
    (trivial_lattice_inner_grid s) (trivial_lattice_outer_grid s) hp (by simpa using hp)
  · simpa only [Nat.cast_one] using Real.one_le_exp hp
  · intro i
    exact Fin.elim0 i

theorem trivialNilmanifold_const_one_complexity (s : ℕ) {σ : Type*} (w : σ → ℕ) {p : ℝ}
    (hp : 2 ≤ p) :
    (RationalFilteredNilmanifold.Niltest.const (trivialNilmanifold s) w 1).ComplexityLE p := by
  refine ⟨trivialNilmanifold_geometry s (by linarith), ?_⟩
  change Real.log (2 + (‖(1 : ℂ)‖₊ : ℝ) + (0 : ℝ)) ≤ p
  simp only [nnnorm_one, NNReal.coe_one, add_zero]
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  norm_num at *
  linarith

end Erdos3.RationalTorus

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

noncomputable local instance phaseBasisFintype (s : ℕ) :
    Fintype (WeightedBasisIndex weight s) := by
  let := weightedBasisIndex_finite weight s weight_pos
  exact Fintype.ofFinite _

noncomputable def budget (s : ℕ) : ℝ :=
  max ((0 + (0 + 1)^s + s.factorial + 2*s + 1 : ℕ) : ℝ)
    (Real.log (3 + (2 * bufferedTranslationTermLip weight s
      (localTentKernel 0 8 (by decide)) 0 : ℝ≥0)))

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_change_left (T : D.Niltest w) (a a₀ : D.RealGroup) (x : D.Space) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖T.observable (a • x) - T.observable (a₀ • x)‖ ≤ (T.lipBound : ℝ) * dist a a₀ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  have hpoint : dist (a • x) (a₀ • x) ≤ dist a a₀ := by
    have hLip : LipschitzWith 1 (fun a : D.RealGroup => a • x) :=
      quotientMetricSpace_lipschitz_orbit (D.basis.baseChange ℝ) D.realLattice
        D.realLattice_closed_discrete.1 x
    simpa only [NNReal.coe_one, one_mul] using hLip.dist_le_mul a a₀
  calc
    _ ≤ (T.lipBound : ℝ) * dist (a • x) (a₀ • x) := by
      simpa only [dist_eq_norm] using T.lipschitz.dist_le_mul (a • x) (a₀ • x)
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoint T.lipBound.coe_nonneg

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization
namespace OAI

section

namespace Erdos3

open Module

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_weighted_layer_basis (c : σ → ℕ) (n : ℕ) {H : ℕ}
    (hM : ∀ a i k, RationalHeightLE (D.basis.repr (M.basis a i : L) k) H) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.weightedLayer c n))) ℚ
        (M.filtration.weightedLayer c n),
      ∀ i k, RationalHeightLE (D.basis.repr (b i : L) k) H := by
  apply exists_bounded_submodule_basis_from_spanning D.basis
    (M.filtration.weightedLayer c n).toSubmodule
    (fun a : Σ a : {a : ∀ i, Fin (bound i + 1) //
        n ≤ multidegreeWeight c (fun i => (a i).val)},
        Fin (finrank ℚ (M.filtration.layer (fun i => (a.val i).val))) =>
      (M.basis a.1.val a.2 : L)) (M.weightedLayer_span c n).symm
  exact fun a k => hM a.1.val a.2 k

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionMarkedSurjective
namespace OAI

section

universe u v

namespace Erdos3

open scoped TensorProduct

variable {ι : Type v} {L₀ M₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

theorem realification_optionMarkedLieMap_none (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) :
    realificationLieHom (liePiEval none) (realificationLieHom (optionMarkedLieMap φ) x) =
      realificationLieHom φ (realificationLieHom (liePiEval none) x) := by
  rw [optionMarkedLieMap, realification_liePiEval_liePiMap]
  induction x using TensorProduct.induction_on with
  | zero =>
    first
      | (simp; done)
      | (simp only [map_zero]; done)
      | (simp only [map_zero]; exact (map_zero (realificationLieHom φ)).symm)
  | tmul r x => rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (map_add (realificationLieHom φ) _ _).symm

theorem realification_optionMarkedLieMap_some (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) (i : ι) :
    realificationLieHom (liePiEval (some i))
        (realificationLieHom (optionMarkedLieMap φ) x) =
      realificationLieHom (liePiEval (some i)) x := by
  rw [optionMarkedLieMap, realification_liePiEval_liePiMap]
  rfl

open NilpotentLieFiltration

variable [Fintype ι] [DecidableEq ι]

theorem realBCHPiEquiv_optionMarkedLieMap_none
    (F₀ : NilpotentLieFiltration L₀ s) (G₀ : NilpotentLieFiltration M₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (g : (pi (optionFiltrations F₀ F)).realification.Group) :
    realBCHPiEquiv (optionFiltrations G₀ F)
        (NilpotentLieBCHGroup.realificationMap
          (hnil := (pi (optionFiltrations F₀ F)).lowerCentralSeries_eq_bot)
          (hM := (pi (optionFiltrations G₀ F)).lowerCentralSeries_eq_bot)
          (optionMarkedLieMap φ) g) none =
      NilpotentLieBCHGroup.realificationMap
        (hnil := F₀.lowerCentralSeries_eq_bot) (hM := G₀.lowerCentralSeries_eq_bot)
        φ (realBCHPiEquiv (optionFiltrations F₀ F) g none) := by
  apply NilpotentLieBCHGroup.ext
  exact realification_optionMarkedLieMap_none φ g.coord

theorem realBCHPiEquiv_optionMarkedLieMap_some
    (F₀ : NilpotentLieFiltration L₀ s) (G₀ : NilpotentLieFiltration M₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (g : (pi (optionFiltrations F₀ F)).realification.Group) (i : ι) :
    realBCHPiEquiv (optionFiltrations G₀ F)
        (NilpotentLieBCHGroup.realificationMap
          (hnil := (pi (optionFiltrations F₀ F)).lowerCentralSeries_eq_bot)
          (hM := (pi (optionFiltrations G₀ F)).lowerCentralSeries_eq_bot)
          (optionMarkedLieMap φ) g) (some i) =
      realBCHPiEquiv (optionFiltrations F₀ F) g (some i) := by
  apply NilpotentLieBCHGroup.ext
  exact realification_optionMarkedLieMap_some φ g.coord i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeIntegerModelFamily.lie NativeIntegerModelFamily.algebra
  NativeIntegerModelFamily.topology NativeIntegerModelFamily.topologicalAdd
  NativeIntegerModelFamily.continuousSMul NativeIntegerModelFamily.hausdorff

namespace NativeIntegerExpansion

variable {σ : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ} {f : (σ → ℤ) → ℂ}

noncomputable def mono (E : NativeIntegerExpansion w s p f) (hpq : p ≤ q) :
    NativeIntegerExpansion w s q f :=
  { E with
    count_bound := E.count_bound.trans (Real.exp_le_exp.mpr hpq)
    complexity := fun i => (E.complexity i).mono hpq
    cost := E.cost.trans (Real.exp_le_exp.mpr hpq) }

end NativeIntegerExpansion

end Erdos3

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def ofFamily {I : Type*} [Fintype I] {L : I → Type}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {σ : Type*} {w : σ → ℕ} {s : ℕ} {d : I → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (T : ∀ i, (D i).Niltest w) (c : I → ℂ)
    {p : ℝ} {f : (σ → ℤ) → ℂ} (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hT : ∀ i, (T i).ComplexityLE p) (hc : (∑ i, ‖c i‖) ≤ Real.exp p)
    (hf : ∀ x, f x = ∑ i, c i * (T i).eval x) :
    NativeIntegerExpansion w s p f := by
  let e := (Fintype.equivFin I).symm
  exact {
    count := Fintype.card I
    count_bound := hcard
    L := fun i => L (e i)
    dim := fun i => d (e i)
    model := fun i => D (e i)
    test := fun i => T (e i)
    complexity := fun i => hT (e i)
    coefficient := fun i => c (e i)
    cost := (e.sum_comp (fun i => ‖c i‖)).le.trans hc
    eval := fun x => (hf x).trans (e.sum_comp
      (fun i => c i * (T i).eval x)).symm
  }

noncomputable def weightedSum {I : Type*} [Fintype I] {σ : Type*} {w : σ → ℕ} {s : ℕ}
    {p q : ℝ} {f : I → (σ → ℤ) → ℂ} (E : ∀ i, NativeIntegerExpansion w s p (f i))
    (c : I → ℂ) (hq : 0 ≤ q) (hcard : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp q) :
    NativeIntegerExpansion w s (p + q) (fun x => ∑ i, c i * f i x) := by
  classical
  let A := Σ i, Fin (E i).count
  refine ofFamily (I := A) (fun a => (E a.1).model a.2)
    (fun a => (E a.1).test a.2) (fun a => c a.1 * (E a.1).coefficient a.2) ?_
    (fun a => ((E a.1).complexity a.2).mono (by linarith)) ?_ ?_
  · change (Fintype.card (Σ i, Fin (E i).count) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _ : I, Real.exp p := Finset.sum_le_sum (fun i _ => by
        simpa only [Fintype.card_fin] using (E i).count_bound)
      _ = (Fintype.card I : ℝ) * Real.exp p := by simp
      _ ≤ Real.exp q * Real.exp p := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (p + q) := by rw [← Real.exp_add, add_comm]
  · exact (sum_pair_coefficient_norms_le c (fun i => (E i).coefficient)
      (Real.exp_nonneg p) hc (fun i => (E i).cost)).trans_eq
      (by rw [← Real.exp_add, add_comm])
  · intro x
    change (∑ i, c i * f i x) = ∑ a : Sigma (fun i => Fin (E i).count), _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [(E i).eval x, Finset.mul_sum]
    simp only [mul_assoc]

end Erdos3.NativeIntegerExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold

open Module
open scoped NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)

theorem raiseStepProjection_mk (x : (D.raiseStep hst).RealGroup) :
    D.raiseStepProjection hst (QuotientGroup.mk x) =
      QuotientGroup.mk (NilpotentLieBCHGroup.realificationMap
        (hnil := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x) := rfl

theorem raiseStepProjection_orbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    D.raiseStepProjection hst (QuotientGroup.mk
      ((D.raiseStep hst).filtration.realification.polynomialOrbitEval w x
        (D.raiseStepRealOrbit hst g))) =
      QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g) := by
  rw [D.raiseStepProjection_mk]
  apply congrArg (QuotientGroup.mk : D.RealGroup → D.Space)
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (LieHom.id : L →ₗ⁅ℚ⁆ L)
    (VectorPolynomial.eval (fun i => (x i : ℚ)) g.log) =
      VectorPolynomial.eval (fun i => (x i : ℚ)) g.log
  exact realificationLieHom_id_apply _

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem raiseStep_eval (T : D.Niltest w) (hst : s ≤ t) (x : σ → ℤ) :
    (T.raiseStep hst).eval x = T.eval x := by
  change T.observable (D.raiseStepProjection hst (QuotientGroup.mk
    ((D.raiseStep hst).filtration.realification.polynomialOrbitEval w x
      (D.raiseStepRealOrbit hst T.orbit)))) = T.eval x
  rw [D.raiseStepProjection_orbit]
  rfl

theorem raiseStep_evalCyclic (T : D.Niltest w) (hst : s ≤ t)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.raiseStep hst).evalCyclic N x = T.evalCyclic N x :=
  T.raiseStep_eval hst _

theorem raiseStep_complexity (T : D.Niltest w) (hst : s ≤ t) {p : ℝ}
    (hp : 0 ≤ p) (hT : T.ComplexityLE p) :
    (T.raiseStep hst).ComplexityLE (raisedNiltestBudget p) := by
  refine ⟨GeometryComplexityLE.mono (D.raiseStep hst)
    (D.raiseStep_geometry hst hT.1) (le_raisedNiltestBudget p), ?_⟩
  have hraw := T.observable_budget hT
  have hn : (T.normBound : ℝ) ≤ Real.exp p := by linarith [T.lipBound.coe_nonneg]
  have hl : (T.lipBound : ℝ) ≤ Real.exp p := by linarith [T.normBound.coe_nonneg]
  have hK := coordinateLipschitzBound_le_exp d d 1 hp hT.1.1 hT.1.1
    (by simpa using Real.one_le_exp_iff.mpr hp)
  have hn' : (T.normBound : ℝ) ≤ Real.exp (p + (p + 2) ^ 2) :=
    hn.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (p + 2)]))
  have hl' : (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ) ≤
      Real.exp (p + (p + 2) ^ 2) := by
    rw [Real.exp_add]
    exact mul_le_mul hl hK (by positivity) (Real.exp_nonneg _)
  have hone : 1 ≤ Real.exp (p + (p + 2) ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hsum : 2 + (T.normBound : ℝ) +
      (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ) ≤
        Real.exp (raisedNiltestBudget p) := by
    calc
      _ ≤ 4 * Real.exp (p + (p + 2) ^ 2) := by linarith
      _ ≤ Real.exp 3 * Real.exp (p + (p + 2) ^ 2) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; unfold raisedNiltestBudget; ring
  change Real.log (2 + (T.normBound : ℝ) +
    (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ)) ≤ raisedNiltestBudget p
  exact (Real.log_le_iff_le_exp (by positivity)).mpr hsum

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace PositiveCyclicNiltest

universe u

theorem unit_interval {degree N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f) (x : ZMod N) :
    0 ≤ f x ∧ f x ≤ 1 := by
  rcases hf with ⟨D, hs, T, hT, hTc, heval⟩
  rw [heval]
  exact (T.unit_interval_evalCyclic hT N (fun _ => x)).2

theorem mono {degree degree' N : ℕ} [NeZero N] {p p' : ℝ} {f : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f) (hdegree : degree ≤ degree')
    (hp : p ≤ p') : PositiveCyclicNiltest.{u} degree' N p' f := by
  rcases hf with ⟨D, hs, T, hT, hTc, heval⟩
  exact .of_test D (hs.trans hdegree) T hT (hTc.mono hp) heval

end PositiveCyclicNiltest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RaisedDegreeRank
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}

namespace DegreeRankStructure

variable {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

theorem ComplexityLE.mono {p q : ℝ} (hR : R.ComplexityLE p) (hpq : p ≤ q) : R.ComplexityLE q :=
  ⟨GeometryComplexityLE.mono D hR.1 hpq, fun i j a k => (hR.2 i j a k).trans hpq⟩

end DegreeRankStructure

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OptionMarkedPolynomialProjection
namespace OAI

section

universe u v

namespace Erdos3

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

theorem optionMarkedPolynomialProjection_none
    {ι : Type v} [Fintype ι] {L₀ M₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {σ : Type*} {s : ℕ} {w : σ → ℕ}
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)))
    (φ : L₀ →ₗ⁅ℚ⁆ M₀) (F₀ : NilpotentLieFiltration M₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s)
    (g : ∀ i, (optionFiltrations F₀ F i).realification.PolynomialOrbit w)
    (h : VectorPolynomial.map
      ((realificationLieHom (optionMarkedLieMap φ)).toLinearMap.restrictScalars ℚ) p =
        (piRealOrbit (optionFiltrations F₀ F) g).log) :
    VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
      (VectorPolynomial.map
        ((realificationLieHom (liePiEval none)).toLinearMap.restrictScalars ℚ) p) =
          (g none).log := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  erw [coefficients_map, coefficients_map]
  have hα := congrArg
    (fun q : VectorPolynomial σ ℚ
        (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace M₀ L i)) =>
      realificationLieHom (liePiEval none) (coefficients q α)) h
  simp only [coefficients_map] at hα
  change realificationLieHom (liePiEval none)
    (realificationLieHom (optionMarkedLieMap φ) (coefficients p α)) = _ at hα
  rw [realification_optionMarkedLieMap_none, piRealOrbit_coefficient] at hα
  exact hα

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositivePolynomialLayerBases
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialCoefficientEquiv :
    F.positivePolynomialAlgebra ≃ₗ[ℚ] (∀ a : BoxedDegreeIndex bound, F.positiveCoefficientLayer a) where
  toFun p a := ⟨coefficients p.val (boxedDegreeMonomial a),
    (F.mem_positiveCoefficientLayer a _).mpr ⟨by
      simpa only [boxedDegreeMonomial_apply] using p.property.1 (boxedDegreeMonomial a),
      fun ha => by rw [ha]; exact p.property.2⟩⟩
  invFun f := ⟨boxedPolynomial (fun a => (f a).val), F.boxedPolynomial_positive f⟩
  left_inv p := by
    apply F.positivePolynomialCoordinates_injective
    funext a
    exact boxedPolynomial_coefficient _ a
  right_inv f := by
    funext a
    apply Subtype.ext
    exact boxedPolynomial_coefficient _ a
  map_add' p q := by ext a; simp
  map_smul' c p := by ext a; simp

theorem positivePolynomialCoefficientEquiv_apply
    (p : F.positivePolynomialAlgebra) (a : BoxedDegreeIndex bound) :
    (F.positivePolynomialCoefficientEquiv p a).val = coefficients p.val (boxedDegreeMonomial a) := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

noncomputable def positivePolynomialBasis : Basis (Σ a, κ a) ℚ F.positivePolynomialAlgebra := by
  classical
  exact (Pi.basis b).map F.positivePolynomialCoefficientEquiv.symm

theorem positivePolynomialBasis_repr (p : F.positivePolynomialAlgebra) (j : Σ a, κ a) :
    (F.positivePolynomialBasis b).repr p j =
      (b j.1).repr (F.positivePolynomialCoefficientEquiv p j.1) j.2 := by
  classical
  rfl

theorem positivePolynomialBasis_coefficient_self (a : BoxedDegreeIndex bound) (j : κ a) :
    coefficients (F.positivePolynomialBasis b ⟨a, j⟩).val (boxedDegreeMonomial a) = (b a j).val := by
  classical
  change (F.positivePolynomialCoefficientEquiv (F.positivePolynomialBasis b ⟨a, j⟩) a).val = _
  simp only [positivePolynomialBasis, Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basis_apply, Pi.single_eq_same]

theorem positivePolynomialBasis_coefficient_ne (a c : BoxedDegreeIndex bound)
    (h : a ≠ c) (j : κ a) :
    coefficients (F.positivePolynomialBasis b ⟨a, j⟩).val (boxedDegreeMonomial c) = 0 := by
  classical
  change (F.positivePolynomialCoefficientEquiv (F.positivePolynomialBasis b ⟨a, j⟩) c).val = _
  simp only [positivePolynomialBasis, Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basis_apply, Pi.single_eq_of_ne (Ne.symm h), ZeroMemClass.coe_zero]

theorem positivePolynomialBasis_monomial (j : Σ a, κ a) :
    (F.positivePolynomialBasis b j).val = monomial (boxedDegreeMonomial j.1) (b j.1 j.2).val := by
  classical
  apply coefficients.injective
  ext a
  by_cases ha : (fun i => a i) ≤ bound
  · obtain ⟨c, rfl⟩ := exists_boxedDegreeMonomial a ha
    by_cases hc : j.1 = c
    · subst c
      rw [F.positivePolynomialBasis_coefficient_self, coefficients_monomial, Finsupp.single_eq_same]
    · rw [F.positivePolynomialBasis_coefficient_ne b _ _ hc]
      simp [boxedDegreeMonomial_injective.ne hc]
  · have hp : coefficients (F.positivePolynomialBasis b j).val a = 0 := by
      simpa only [F.terminal _ ha, Submodule.mem_bot] using
        (F.positivePolynomialBasis b j).property.1 a
    have hne : boxedDegreeMonomial j.1 ≠ a := by
      intro h
      apply ha
      simpa only [h] using boxedDegreeMonomial_le j.1
    simp [hp, hne]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

theorem positivePolynomialSupport_eq_span (S : Set (σ →₀ ℕ)) :
    F.positivePolynomialSupport S =
      Submodule.span ℚ (F.positivePolynomialBasis b '' {j | boxedDegreeMonomial j.1 ∈ S}) := by
  ext p
  rw [basis_mem_span_image_iff]
  constructor
  · intro hp j hj
    have hz : F.positivePolynomialCoefficientEquiv p j.1 = 0 := Subtype.ext (hp _ hj)
    rw [F.positivePolynomialBasis_repr, hz, map_zero, Finsupp.zero_apply]
  · intro hp a ha
    change coefficients p.val a = 0
    by_cases hbox : (fun i => a i) ≤ bound
    · obtain ⟨c, rfl⟩ := exists_boxedDegreeMonomial a hbox
      have hz : F.positivePolynomialCoefficientEquiv p c = 0 := by
        apply (b c).repr.injective
        ext j
        simpa only [F.positivePolynomialBasis_repr, map_zero, Finsupp.zero_apply] using hp ⟨c, j⟩ ha
      exact congrArg Subtype.val hz
    · simpa only [F.terminal _ hbox, Submodule.mem_bot] using p.property.1 a

noncomputable def positivePolynomialSupportedBasis (S : Set (σ →₀ ℕ)) :
    Basis {j : Σ a, κ a // boxedDegreeMonomial j.1 ∈ S} ℚ (F.positivePolynomialSupport S) :=
  supportedSubmoduleBasis (F.positivePolynomialBasis b) _ _ (F.positivePolynomialSupport_eq_span b S)

theorem positivePolynomialSupportedBasis_coe (S : Set (σ →₀ ℕ))
    (j : {j : Σ a, κ a // boxedDegreeMonomial j.1 ∈ S}) :
    (F.positivePolynomialSupportedBasis b S j).val = F.positivePolynomialBasis b j.val :=
  supportedSubmoduleBasis_coe _ _ _ _ j

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial

variable {σ ν L : Type*} [Fintype σ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))
  (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
  (hb : ∀ a j k, RationalHeightLE (e.repr (b a j).val k) H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

include hH hb hc in
theorem positivePolynomialBasis_bracket_coefficient_height
    (x y : Σ a, κ a) (a : BoxedDegreeIndex bound) (k : ν) :
    RationalHeightLE (e.repr
      (F.positivePolynomialCoefficientEquiv ⁅F.positivePolynomialBasis b x,
        F.positivePolynomialBasis b y⁆ a).val k)
      (squarefreeBracketHeight (Fintype.card ν) H) := by
  classical
  rw [F.positivePolynomialCoefficientEquiv_apply]
  change RationalHeightLE (e.repr (coefficients
    ⁅(F.positivePolynomialBasis b x).val, (F.positivePolynomialBasis b y).val⁆
    (boxedDegreeMonomial a)) k) _
  rw [F.positivePolynomialBasis_monomial, F.positivePolynomialBasis_monomial, lie_monomial]
  by_cases ha : boxedDegreeMonomial x.1 + boxedDegreeMonomial y.1 = boxedDegreeMonomial a
  · rw [ha, coefficients_monomial, Finsupp.single_eq_same]
    exact lie_bracket_coordinate_height e hc _ _ (hb x.1 x.2) (hb y.1 y.2) k
  · simp only [coefficients_monomial, Finsupp.single_apply, ha, ite_false, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (squarefreeBracketHeight_pos _ hH)

include hH hb hc in
theorem positivePolynomialBasis_structure_height [∀ a, Fintype (κ a)]
    (hκ : ∀ a, Fintype.card (κ a) ≤ Fintype.card ν) (x y z : Σ a, κ a) :
    RationalHeightLE (lieStructureConstants (F.positivePolynomialBasis b) x y z)
      (squarefreeStructureHeight (Fintype.card ν) H) := by
  change RationalHeightLE ((F.positivePolynomialBasis b).repr
    ⁅F.positivePolynomialBasis b x, F.positivePolynomialBasis b y⁆ z) _
  rw [F.positivePolynomialBasis_repr]
  have h := submodule_basis_coordinate_height (F.positiveCoefficientLayer z.1) (b z.1) e hH
    (fun i j => hb z.1 j i)
    (F.positivePolynomialCoefficientEquiv ⁅F.positivePolynomialBasis b x,
      F.positivePolynomialBasis b y⁆ z.1)
    (fun k => F.positivePolynomialBasis_bracket_coefficient_height b e hH hb hc x y z.1 k) z.2
  apply h.mono
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_right _ (rationalSolveHeight_mono hH (hκ z.1))) _)

theorem positivePolynomialBasis_evaluation (j : Σ a, κ a) :
    F.positivePolynomialEvaluation (F.positivePolynomialBasis b j) = (b j.1 j.2).val := by
  rw [F.positivePolynomialEvaluation_apply, F.positivePolynomialBasis_monomial]
  simp [eval_monomial, Finsupp.prod]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))
  (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)

theorem positivePolynomialDownsetIdeal_eq_span :
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule =
      Submodule.span ℚ (F.positivePolynomialBasis b '' {j | boxedDegreeMonomial j.1 ∉ J}) :=
  (F.positivePolynomialDownsetIdeal_eq_support J hJ).trans
    (F.positivePolynomialSupport_eq_span b Jᶜ)

noncomputable def positivePolynomialDownsetBasis :
    Basis {j : Σ a, κ a // j ∉ {k | boxedDegreeMonomial k.1 ∉ J}} ℚ
      (F.positivePolynomialAlgebra ⧸ restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ) :=
  supportedQuotientBasis (F.positivePolynomialBasis b) _ _
    (F.positivePolynomialDownsetIdeal_eq_span b J hJ)

theorem positivePolynomialDownsetBasis_repr (x : F.positivePolynomialAlgebra) (j) :
    (F.positivePolynomialDownsetBasis b J hJ).repr
      (lieQuotientMap (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ) x) j =
        (F.positivePolynomialBasis b).repr x j.val :=
  supportedQuotientBasis_repr_mk _ _ _ _ x j

theorem positivePolynomialDownset_multidegree_span (a : σ → ℕ) :
    (F.positivePolynomialDownsetQuotient J hJ).layer a =
      Submodule.span ℚ (F.positivePolynomialDownsetBasis b J hJ ''
        {j | a ≤ fun i => boxedDegreeMonomial j.val.1 i}) := by
  change (F.positivePolynomialSupport {c : σ →₀ ℕ | a ≤ fun i => c i}).map
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule.mkQ = _
  rw [F.positivePolynomialSupport_eq_span b]
  exact supportedQuotientBasis_map_span _ _ _ _ _

theorem positivePolynomialDownset_degree_span (n : ℕ) :
    (F.positivePolynomialDownsetQuotient J hJ).ordinary.layer n =
      Submodule.span ℚ (F.positivePolynomialDownsetBasis b J hJ ''
        {j | n ≤ ∑ i, boxedDegreeMonomial j.val.1 i}) := by
  change (F.positivePolynomialSupport {c : σ →₀ ℕ | n ≤ ∑ i, c i}).map
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule.mkQ = _
  rw [F.positivePolynomialSupport_eq_span b]
  exact supportedQuotientBasis_map_span _ _ _ _ _

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {bound : σ → ℕ}
  (F : MultidegreeLieFiltration σ L s bound)
  (J : α → Set (σ →₀ ℕ)) (hJ : ∀ a, IsLowerSet (J a))

variable {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ c, Basis (κ c) ℚ (F.positiveCoefficientLayer c))

omit [Fintype α] [DecidableEq α] in
include b in
theorem positivePolynomial_quotient_family_basis_cover
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥)
    (j : Σ c, κ c) : ∃ a, boxedDegreeMonomial j.1 ∈ J a := by
  classical
  rcases j with ⟨c, j⟩
  by_contra hnone
  have hs : ∀ c, c ≠ 0 → c ∉ ⋃ a, J a → F.layer (fun i => c i) = ⊥ := by
    intro c hc hnot
    exact hcover c hc (fun a ha => hnot (Set.mem_iUnion.mpr ⟨a, ha⟩))
  have hz := F.positivePolynomial_support_of_layers (⋃ a, J a) hs
    (F.positivePolynomialBasis b ⟨c, j⟩) (boxedDegreeMonomial c)
    (fun h => hnone (Set.mem_iUnion.mp h))
  change coefficients (F.positivePolynomialBasis b ⟨c, j⟩).val (boxedDegreeMonomial c) = 0 at hz
  rw [F.positivePolynomialBasis_coefficient_self] at hz
  exact (b c).ne_zero j (Subtype.ext hz)

variable [DecidableEq σ] [∀ c, Fintype (κ c)]

omit [DecidableEq σ] [∀ c, Fintype (κ c)] in
include b in
theorem positivePolynomialQuotientProductRealMap_injective
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥) :
    Function.Injective (F.positivePolynomialQuotientProductRealMap J hJ) := by
  classical
  have hcov (j : Σ c, κ c) : ∃ a, j ∉ {k | boxedDegreeMonomial k.1 ∉ J a} := by
    simpa only [Set.mem_ofPred_eq, not_not] using F.positivePolynomial_quotient_family_basis_cover J b hcover j
  intro g h heq
  apply F.positivePolynomialMultidegree.ordinary.realQuotientFamily_joint_injective
    (t := ∑ i, bound i)
    (F.positivePolynomialBasis b)
    (fun a => restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
    (fun a => by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le)
    (fun a => {k | boxedDegreeMonomial k.1 ∉ J a})
    (fun a => F.positivePolynomialDownsetIdeal_eq_span b (J a) (hJ a)) hcov
  funext a
  simpa only [F.positivePolynomialQuotientProductRealMap_component] using
    congrArg (fun x => realBCHPiEquiv
      (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary) x a) heq

theorem positivePolynomialQuotientProduct_lattice_detect
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥)
    (Γ : Subgroup F.positivePolynomialMultidegree.ordinary.Group) (B : ℕ)
    (hgrid : bchSubgroupCoordinates (F.positivePolynomialBasis b) Γ = scaledIntegerGrid B)
    (g : F.positivePolynomialMultidegree.ordinary.realification.Group)
    (hg : F.positivePolynomialQuotientProductRealMap J hJ g ∈
      (F.positivePolynomialQuotientProductLattice J hJ Γ).map realificationHom) :
    g ∈ Γ.map realificationHom := by
  classical
  apply F.positivePolynomialMultidegree.ordinary.realQuotientFamily_lattice_detect
    (t := ∑ i, bound i)
    (F.positivePolynomialBasis b)
    (fun a => restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
    (fun a => by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le)
    (fun a => {k | boxedDegreeMonomial k.1 ∉ J a})
    (fun a => F.positivePolynomialDownsetIdeal_eq_span b (J a) (hJ a))
    (fun j => by simpa only [Set.mem_ofPred_eq, not_not] using
      F.positivePolynomial_quotient_family_basis_cover J b hcover j) Γ B hgrid g
  intro a
  have ha := (realBCHPiEquiv_mem_lattice
    (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary) _ _).mp hg a
  simpa only [F.positivePolynomialQuotientProductRealMap_component] using ha

theorem positivePolynomialQuotientProduct_lattice_cover
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥)
    (Γ : Subgroup F.positivePolynomialMultidegree.ordinary.Group) (B : ℕ)
    (hgrid : bchSubgroupCoordinates (F.positivePolynomialBasis b) Γ = scaledIntegerGrid B) :
    (F.positivePolynomialQuotientProductLattice J hJ Γ).map realificationHom ⊓
      (F.positivePolynomialQuotientProductRealMap J hJ).range ≤
        (Γ.map realificationHom).map (F.positivePolynomialQuotientProductRealMap J hJ) := by
  rintro y ⟨hy, g, rfl⟩
  exact Subgroup.mem_map.mpr ⟨g,
    F.positivePolynomialQuotientProduct_lattice_detect J hJ b hcover Γ B hgrid g hy, rfl⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))
  (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)

noncomputable def positivePolynomialDownsetMultidegreeBasis (a : σ → ℕ) :
    Basis (Fin (finrank ℚ ((F.positivePolynomialDownsetQuotient J hJ).layer a))) ℚ
      ((F.positivePolynomialDownsetQuotient J hJ).layer a) := by
  classical
  let c := supportedSubmoduleBasis (F.positivePolynomialDownsetBasis b J hJ) _ _
    (F.positivePolynomialDownset_multidegree_span b J hJ a)
  exact c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)

theorem positivePolynomialDownsetMultidegreeBasis_height (a : σ → ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialDownsetBasis b J hJ).repr
      (F.positivePolynomialDownsetMultidegreeBasis b J hJ a j).val k) 1 := by
  classical
  unfold positivePolynomialDownsetMultidegreeBasis
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one _ _ _

noncomputable def positivePolynomialDownsetDegreeBasis (n : ℕ) :
    Basis (Fin (finrank ℚ ((F.positivePolynomialDownsetQuotient J hJ).ordinary.layer n))) ℚ
      ((F.positivePolynomialDownsetQuotient J hJ).ordinary.layer n) := by
  classical
  let c := supportedSubmoduleBasis (F.positivePolynomialDownsetBasis b J hJ) _ _
    (F.positivePolynomialDownset_degree_span b J hJ n)
  exact c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)

theorem positivePolynomialDownsetDegreeBasis_height (n : ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialDownsetBasis b J hJ).repr
      (F.positivePolynomialDownsetDegreeBasis b J hJ n j).val k) 1 := by
  classical
  unfold positivePolynomialDownsetDegreeBasis
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one _ _ _

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

noncomputable def positivePolynomialSupportedFinBasis (S : Set (σ →₀ ℕ)) :
    Basis (Fin (finrank ℚ (F.positivePolynomialSupport S))) ℚ (F.positivePolynomialSupport S) := by
  classical
  exact (F.positivePolynomialSupportedBasis b S).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (F.positivePolynomialSupportedBasis b S)).symm)

theorem positivePolynomialSupportedFinBasis_height (S : Set (σ →₀ ℕ)) (j k) :
    RationalHeightLE ((F.positivePolynomialBasis b).repr
      (F.positivePolynomialSupportedFinBasis b S j).val k) 1 := by
  classical
  unfold positivePolynomialSupportedFinBasis
  rw [Basis.reindex_apply, F.positivePolynomialSupportedBasis_coe]
  exact basis_repr_height_one _ _ _

noncomputable def positivePolynomialMultidegreeBasis (a : σ → ℕ) :
    Basis (Fin (finrank ℚ (F.positivePolynomialMultidegreeLayer a))) ℚ
      (F.positivePolynomialMultidegreeLayer a) :=
  F.positivePolynomialSupportedFinBasis b {c : σ →₀ ℕ | a ≤ fun i => c i}

theorem positivePolynomialMultidegreeBasis_height (a : σ → ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialBasis b).repr
      (F.positivePolynomialMultidegreeBasis b a j).val k) 1 :=
  F.positivePolynomialSupportedFinBasis_height b _ j k

noncomputable def positivePolynomialDegreeBasis (n : ℕ) :
    Basis (Fin (finrank ℚ (F.positivePolynomialDegreeLayer n))) ℚ
      (F.positivePolynomialDegreeLayer n) :=
  F.positivePolynomialSupportedFinBasis b {c : σ →₀ ℕ | n ≤ ∑ i, c i}

theorem positivePolynomialDegreeBasis_height (n : ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialBasis b).repr
      (F.positivePolynomialDegreeBasis b n j).val k) 1 :=
  F.positivePolynomialSupportedFinBasis_height b _ j k

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedTranslationCoordinates (s : ℕ) :
    List (ReplicatedIndex (mixedCorrelationDegree s)) :=
  (Finset.univ.filter (fun j : ReplicatedIndex (mixedCorrelationDegree s) => j.1 = 1)).toList

@[simp] theorem mem_mixedTranslationCoordinates (s : ℕ) (j : ReplicatedIndex (mixedCorrelationDegree s)) :
    j ∈ mixedTranslationCoordinates s ↔ j.1 = 1 := by
  simp [mixedTranslationCoordinates]

def mixedTranslationSample (s : ℕ) (x : Fin 3 → ℤ) :
    Option (ReplicatedIndex (mixedCorrelationDegree s)) → ℤ
  | none => x 2
  | some j => correlationInput (x 0) (x 1) j.1

theorem replicatedMixed_card (s : ℕ) :
    Fintype.card (ReplicatedIndex (mixedCorrelationDegree s)) = s + 1 := by
  rw [replicatedIndex_card, Fin.sum_univ_two]
  change 1 + s = s + 1
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativePolynomialOrbit
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

variable (F : NilpotentLieFiltration L (s + 1))

noncomputable def nativeReducedPolynomialOrbit (g : F.RealAdaptedPolynomialGroup w) :
    F.quotientTop.realification.PolynomialOrbit w :=
  F.realQuotientPolynomialOrbit (F.layerIdeal (s + 1)) le_rfl (F.nativePolynomialOrbit w g)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

theorem basisOfTail_height (b : Basis (Fin d) ℚ L) (P : Submodule ℚ L) (c : ℕ)
    (hP : P = basisTail b c) (i : Fin (finrank ℚ P)) (j : Fin d) :
    RationalHeightLE (b.repr (basisOfTail b P c hP i : L) j) 1 := by
  classical
  unfold basisOfTail
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one b _ j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev CubicReplicatedIndex := ReplicatedIndex (mixedCorrelationDegree 2)

def cubicTrilinearInput (h u v : ℤ) (j : CubicReplicatedIndex) : ℤ :=
  if j.1 = 0 then h else if j.2.val = 0 then u else v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedEvaluationCoordinates
namespace OAI

section

namespace Erdos3

def mixedEvaluationEmbedding (s : ℕ) : Fin s ↪ ReplicatedIndex (mixedCorrelationDegree s) where
  toFun k := ⟨1, k⟩
  inj' := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : ReplicatedIndex (mixedCorrelationDegree s) => z.2.val) hij)

def mixedEvaluationCoordinates (s : ℕ) : Finset (ReplicatedIndex (mixedCorrelationDegree s)) :=
  Finset.univ.map (mixedEvaluationEmbedding s)

@[simp] theorem mem_mixedEvaluationCoordinates (s : ℕ) (j : ReplicatedIndex (mixedCorrelationDegree s)) :
    j ∈ mixedEvaluationCoordinates s ↔ j.1 = 1 := by
  constructor
  · intro hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hj
    rfl
  · intro hj
    rcases j with ⟨j, k⟩
    dsimp only at hj
    subst j
    exact Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩

@[simp] theorem mixedEvaluationCoordinates_card (s : ℕ) :
    (mixedEvaluationCoordinates s).card = s := by
  simp only [mixedEvaluationCoordinates, Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeDegreeRankNilmanifold
namespace OAI

section

namespace Erdos3

namespace DegreeRankLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis (Fin d) ℚ L)
  (htail : ∀ i j, ∃ c ≤ d, F.layer i j = basisTail b c)

noncomputable def tailLayerBasis (i j : ℕ) :
    Basis (Fin (finrank ℚ (F.layer i j))) ℚ (F.layer i j) :=
  basisOfTail b (F.layer i j) (Classical.choose (htail i j)) (Classical.choose_spec (htail i j)).2

theorem tailLayerBasis_height (i j : ℕ) (a : Fin (finrank ℚ (F.layer i j))) (k : Fin d) :
    RationalHeightLE (b.repr (F.tailLayerBasis b htail i j a : L) k) 1 :=
  basisOfTail_height b (F.layer i j) (Classical.choose (htail i j)) (Classical.choose_spec (htail i j)).2 a k

end DegreeRankLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (S : Fin s → Submodule ℚ L)

noncomputable def filtration (hr : r ≤ s) : DegreeRankLieFiltration (Algebra S r) s r :=
  FreeDegreeRankLieAlgebra.filtration (Alphabet S) s r (weight S) (weight_pos S) hr

variable (B : ∀ d, Basis (Fin (finrank ℚ (S d))) ℚ (S d))

variable (F : DegreeRankLieFiltration L s r)
  (hS : ∀ d, S d ≤ F.layer (d.val + 1) 0)

noncomputable def evaluation : Algebra S r →ₗ⁅ℚ⁆ L :=
  FreeDegreeRankLieAlgebra.lift F (weight S) (weight_pos S)
    (fun x => (B x.1 x.2).val) (fun x => hS x.1 (B x.1 x.2).property)

end Erdos3.SubspaceFreeLift

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedReplicatedCoordinates
namespace OAI

section

namespace Erdos3

abbrev MixedReplicatedIndex (s : ℕ) := ReplicatedIndex (mixedCorrelationDegree s)

def mixedReplicatedInput {s : ℕ} {α : Type*} (h : α) (v : Fin s → α)
    (j : MixedReplicatedIndex s) : α :=
  if hj : j.1 = 1 then v ⟨j.2.val, by
    have hs : mixedCorrelationDegree s j.1 = s := by rw [hj]; rfl
    simpa only [hs] using j.2.isLt⟩
  else h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge
namespace OAI

section

namespace Erdos3

def mixedSlotInput {n : ℕ} {α : Type*} (h t : α) (v : Fin n → α) :
    MixedReplicatedIndex (n + 1) → α := mixedReplicatedInput h (Fin.cons t v)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeMixedCoordinateSlices
namespace OAI

section

namespace Erdos3

def mixedInputCoordinate (n : ℕ) : MixedReplicatedIndex (n + 1) → Fin (n + 2) :=
  mixedSlotInput 0 1 (fun j => j.succ.succ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShiftStructure
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem pderiv_commute (i j : σ) (p : VectorPolynomial σ ℚ L) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L
        ((MvPolynomial.pderiv j).toLinearMap.rTensor L p) =
      (MvPolynomial.pderiv j).toLinearMap.rTensor L
        ((MvPolynomial.pderiv i).toLinearMap.rTensor L p) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  apply coefficients.injective
  ext α
  simp only [coefficients_pderiv, Finsupp.add_apply,
    Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne (Ne.symm hij),
    Nat.add_zero, smul_smul]
  congr 1
  · ring
  · congr 1
    abel

theorem directionalDerivative_commute [Fintype σ]
    (h k : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative h (directionalDerivative k p) =
      directionalDerivative k (directionalDerivative h p) := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pderiv_commute, mul_comm]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedShiftDerivation (h : σ → ℚ) :
    LieDerivation ℚ (F.adaptedLieSubalgebra (fun _ : σ => 1))
      (F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toLinearMap := F.adaptedDirectionalDerivative h
  leibniz' p q := by
    rw [F.adaptedDirectionalDerivative_lie, sub_eq_add_neg, ← lie_skew]
    exact add_comm _ _

@[simp] theorem adaptedShiftDerivation_coe (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (F.adaptedShiftDerivation h p : VectorPolynomial σ ℚ L) =
      directionalDerivative h p.val := rfl

noncomputable def adaptedShiftDerivationLinear :
    (σ → ℚ) →ₗ[ℚ] LieDerivation ℚ (F.adaptedLieSubalgebra (fun _ : σ => 1))
      (F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toFun := F.adaptedShiftDerivation
  map_add' h k := by
    apply LieDerivation.ext
    intro p
    apply Subtype.ext
    exact directionalDerivative_direction_add h k p.val
  map_smul' r h := by
    apply LieDerivation.ext
    intro p
    apply Subtype.ext
    exact directionalDerivative_direction_smul r h p.val

theorem adaptedShiftDerivation_commute (h k : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedShiftDerivation h (F.adaptedShiftDerivation k p) =
      F.adaptedShiftDerivation k (F.adaptedShiftDerivation h p) := by
  apply Subtype.ext
  exact directionalDerivative_commute h k p.val

omit [Fintype σ] in
noncomputable def adaptedShiftAction (d : ℕ) :
    RationalTorus.Algebra d →ₗ⁅ℚ⁆
      LieDerivation ℚ (F.adaptedLieSubalgebra (fun _ : Fin d => 1))
        (F.adaptedLieSubalgebra (fun _ : Fin d => 1)) where
  toLinearMap := F.adaptedShiftDerivationLinear
  map_lie' {h k} := by
    apply LieDerivation.ext
    intro p
    rw [RationalTorus.lie_eq_zero]
    change (F.adaptedShiftDerivationLinear (0 : Fin d → ℚ)) p = _
    rw [map_zero, LieDerivation.zero_apply, LieDerivation.lie_apply]
    exact (sub_eq_zero.mpr (F.adaptedShiftDerivation_commute h k p)).symm

omit [Fintype σ] in
@[simp] theorem adaptedShiftAction_coe (d : ℕ) (h : RationalTorus.Algebra d)
    (p : F.adaptedLieSubalgebra (fun _ : Fin d => 1)) :
    (F.adaptedShiftAction d h p : VectorPolynomial (Fin d) ℚ L) =
      directionalDerivative h p.val := rfl

omit [Fintype σ] in

abbrev PolynomialShiftAlgebra (d : ℕ) :=
  LieAlgebra.SemiDirectSum (F.adaptedLieSubalgebra (fun _ : Fin d => 1))
    (RationalTorus.Algebra d) (F.adaptedShiftAction d)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {E : Fin m → Type*} {N : ℕ}

noncomputable def resampleCoefficientDeckCoordinate {A : Type*}
    (r : CoefficientDeckResidues (K := K) E N) (j : Fin m) (i : E j)
    (slot : A → BoundedCoefficientExponent K (j.val + 1)) (c : A → ZMod N) :
    CoefficientDeckResidues (K := K) E N :=
  Function.update r j (fun e => Function.update (r j e) i
    (Function.extend slot c (fun e => r j e i) e))

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

noncomputable def factorizationInputOffset (s : ℕ) : ℕ :=
  ⌈budget s⌉₊ + 2

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardDetectorOffset (depth : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (depth + 1), OrdinaryPolynomialPhase.factorizationInputOffset r

noncomputable def preparedFiniteForwardDetectorPolynomial (depth : ℕ) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (preparedFiniteForwardDetectorOffset depth)

@[simp] theorem preparedFiniteForwardDetectorPolynomial_eval (depth : ℕ) (p : ℝ) :
    (preparedFiniteForwardDetectorPolynomial depth).eval₂ (Nat.castRingHom ℝ) p =
      p + preparedFiniteForwardDetectorOffset depth := by
  simp [preparedFiniteForwardDetectorPolynomial]

end Erdos3.VectorPolynomial

end

end OAI
end


