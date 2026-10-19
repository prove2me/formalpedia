-- Prove2me | Definitions.Def_OAIE3v2B106
-- name    : OAIE3v2B106
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:42:08.121271+00:00
-- url     : https://prove2.me/theorems/6ff7a29b-797c-4887-a453-924989f84182
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 108 of 311
-- statement:
--   Definitions bundle 108 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B089`, `OAIE3v2B090`, `OAIE3v2B092`, `OAIE3v2B093`, `OAIE3v2B298` of this split.
--
--   Modules: `Dynamics/ConjugationDenominatorBudget.lean`, `Estimates/DilationPairFiltration.lean`, `Estimates/FiniteSeriesCoefficientBounds.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/MultidegreeDilationPair.lean`, `Estimates/QuotientInducedMark.lean`, `Estimates/RealifiedDilationMultidegree.lean`, `Estimates/SquarefreeSplitCount.lean`, `Estimates/SquarefreeStructureHeight.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Geometry/ConjugationCoordinates.lean`, `Geometry/MultidegreeOrbitTransport.lean`, `Geometry/SquarefreeAlgebraCoordinates.lean`, `Geometry/SubmoduleCoordinateHeight.lean`, `Geometry/SupportedLieQuotient.lean`, `Lattices/ConjugatedLatticeGrids.lean`, `Lattices/ImageLatticeSubgroup.lean`, `Linear/AdaptedBasisGeometry.lean`, `Linear/SquarefreeBasisPermutation.lean`, `Nilpotent/BCHChartCutoffSmooth.lean`, `Nilpotent/BCHConjugationLinear.lean`, `Nilpotent/BCHDenominatorBudget.lean`, `Nilpotent/BCHLatticeImageGap.lean`, `Nilpotent/BCHOuterGridChangeBasis.lean`, `Nilpotent/BCHQuotientLocalIsometry.lean`, `Nilpotent/BCHSmoothPartitionBudget.lean`, `Nilpotent/BCHSubgroupGridExistence.lean`, `Nilpotent/BCHUniformQuotientCharts.lean`, `Nilpotent/RealPolynomialBCH.lean`, `Nilpotent/SquarefreeBracketHeight.lean`, `Polynomial/LieCoordinatePolynomials.lean`, `Polynomial/RealGradedSymbolPolynomial.lean`, `Polynomial/UniformPolynomialPeriodBudget.lean`, `Polynomial/WeightedPolynomialRestriction.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B087
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B089
import Definitions.Def_OAIE3v2B090
import Definitions.Def_OAIE3v2B092
import Definitions.Def_OAIE3v2B093
import Definitions.Def_OAIE3v2B298

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem exists_preimage_grid_exp_bound (B : Matrix ι κ ℚ)
    (hli : LinearIndependent ℚ B.col) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hB : ∀ i j, RationalHeightLE (B i j) H) (Γ : Set (ι → ℚ))
    (hinner : scaledIntegerGrid l ⊆ Γ) (houter : Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hd : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid L ⊆ B.mulVec ⁻¹' Γ ∧ B.mulVec ⁻¹' Γ ⊆ denominatorGrid L := by
  obtain ⟨C, hCB, hC⟩ := exists_bounded_rational_left_inverse B hli hHpos hB
  have hK : ((matrixDenominator B * matrixDenominator C : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 8) := by
    have hc := Nat.mul_le_mul (matrixDenominator_le B hB) (matrixDenominator_le C hC)
    exact (show ((matrixDenominator B * matrixDenominator C : ℕ) : ℝ) ≤
      ((H ^ (Fintype.card ι * Fintype.card κ) *
        rationalSolveHeight (Fintype.card κ) H ^ (Fintype.card κ * Fintype.card ι) : ℕ) : ℝ) from
      by exact_mod_cast hc).trans (rational_grid_height_le_exp _ _ _ hp hn hd hH)
  exact ⟨l * (matrixDenominator B * matrixDenominator C),
    Nat.mul_pos hlpos (Nat.mul_pos (matrixDenominator_pos B) (matrixDenominator_pos C)),
    grid_allowance_mul_le_exp hp hl hK, rational_preimage_grid_transport B C hCB l Γ hinner houter⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]

theorem rationalSpanGridStep_combination (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) (z : κ → ℤ) :
    e.equivFun (∑ j, ((z j : ℚ) * (rationalSpanGridStep e v l : ℚ)) • v j) ∈ scaledIntegerGrid l := by
  classical
  let B := spanningCoordinateMatrix e v
  have hz : IntegralVector (fun j => (z j : ℚ)) := ⟨z, fun _ => rfl⟩
  have hB : IntegralVector (B *ᵥ ((matrixDenominator B : ℚ) • (fun j => (z j : ℚ)))) := by
    rw [Matrix.mulVec_smul]
    exact integralVector_denominator_mulVec B _ hz
  have heq : (fun j => (z j : ℚ) * (rationalSpanGridStep e v l : ℚ)) =
      (l : ℚ) • ((matrixDenominator B : ℚ) • (fun j => (z j : ℚ))) := by
    ext j
    simp only [rationalSpanGridStep, Nat.cast_mul, Pi.smul_apply, smul_eq_mul, B]
    ring
  rw [spanningCoordinateMatrix_mulVec, heq]
  exact scaled_grid_mulVec B l _ hB

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

theorem bchCoordinatePolynomial_eval (e : Basis ι ℚ L) (s : ℕ) (a b : L) (k : ι) :
    aeval (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2)
        (bchCoordinatePolynomial (lieStructureConstants e) s k) = e.repr (lieBCH s a b) k := by
  rw [lieBCH_bracket_formula]
  simp only [bchCoordinatePolynomial, map_sum, map_mul, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply,
    dynkinCoordinatePolynomial_eval, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply,
    smul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHDenominatorBudget
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def bchCoordinateDenominator (e : Basis ι ℚ L) (s : ℕ) : ℕ :=
  polynomialFamilyDenominator (bchCoordinatePolynomial (lieStructureConstants e) s)

theorem bchCoordinateDenominator_pos (e : Basis ι ℚ L) (s : ℕ) :
    0 < bchCoordinateDenominator e s := polynomialFamilyDenominator_pos _

theorem lieBCH_mem_denominatorGrid (e : Basis ι ℚ L) (s q : ℕ) (a b : L)
    (ha : e.equivFun a ∈ denominatorGrid q) (hb : e.equivFun b ∈ denominatorGrid q) :
    e.equivFun (lieBCH s a b) ∈ denominatorGrid (bchCoordinateDenominator e s * q ^ s) := by
  have h := polynomial_family_rational_values_grid
    (bchCoordinatePolynomial (lieStructureConstants e) s) q s
    (bchCoordinatePolynomial_totalDegree _ s)
    (fun xi : Fin 2 × ι => (![e.equivFun a, e.equivFun b] xi.1) xi.2)
    (pairInput_mem_denominatorGrid (e.equivFun a) (e.equivFun b) q ha hb)
  have he : (fun k => MvPolynomial.eval
      (fun xi : Fin 2 × ι => (![e.equivFun a, e.equivFun b] xi.1) xi.2)
      (bchCoordinatePolynomial (lieStructureConstants e) s k)) = e.equivFun (lieBCH s a b) := by
    funext k
    have hi : (fun xi : Fin 2 × ι => (![e.equivFun a, e.equivFun b] xi.1) xi.2) =
        (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2) := by
      funext xi
      rcases xi with ⟨i, j⟩
      fin_cases i <;> rfl
    rw [hi]
    exact bchCoordinatePolynomial_eval e s a b k
  rw [he] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable [DecidableEq ι] [DecidableEq κ]

theorem exists_bchSubgroup_comap_grid_exp_bound (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hB : ∀ i j, RationalHeightLE (LinearMap.toMatrix b e φ.toLinearMap i j) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hr : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) ∧
      bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) ⊆ denominatorGrid N := by
  rw [bchSubgroupCoordinates_comap b e φ Γ]
  exact exists_preimage_grid_exp_bound (LinearMap.toMatrix b e φ.toLinearMap)
    (Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ.toLinearMap hφ))
    hHpos hlpos hB _ hinner houter hp hd hr hH hl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem subgroupPowerCover_le_of_grid (e : Basis ι ℚ L)
    (Γ Λ₀ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m₀ m : ℕ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hinner : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀)
    (hm : l * m₀ ∣ m) : subgroupPowerCover Γ m ≤ Λ₀ := by
  apply (subgroupPowerCover_le_iff Γ Λ₀ m).mpr
  intro g hg
  apply (bchSubgroupCoordinates_repr e Λ₀ (g ^ m)).mp
  rw [NilpotentLieBCHGroup.coord_pow_rat, map_smul]
  exact hinner (denominator_grid_smul_mem_scaled l m₀ m hm
    (houter ((bchSubgroupCoordinates_repr e Γ g).mpr hg)))

theorem subgroupPowerCover_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    scaledIntegerGrid (m * l) ⊆ bchSubgroupCoordinates e (subgroupPowerCover Γ m) ∧
      bchSubgroupCoordinates e (subgroupPowerCover Γ m) ⊆ denominatorGrid (m * l) := by
  refine ⟨subgroupPowerCover_inner_grid e Γ l m hinner, ?_⟩
  intro x hx
  exact denominator_grid_subset_mul l m (houter (subgroupPowerCover_le Γ m hx))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bchSubgroup_outer_grid_change_basis
    {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ N : ℕ, 0 < N ∧ bchSubgroupCoordinates b Γ ⊆ denominatorGrid N := by
  classical
  let A := LinearMap.toMatrix e b (LinearMap.id : L →ₗ[ℚ] L)
  refine ⟨matrixDenominator A * l, Nat.mul_pos (matrixDenominator_pos A) hl, ?_⟩
  intro x hx
  let g : NilpotentLieBCHGroup L s hnil := ⟨b.equivFun.symm x⟩
  have hg : g ∈ Γ := hx
  have hgrid := houter ((bchSubgroupCoordinates_repr e Γ g).mpr hg)
  have hint := integralVector_denominator_mulVec A ((l : ℚ) • e.equivFun g.coord) hgrid
  have hA : A *ᵥ e.equivFun g.coord = x := by
    dsimp only [A]
    rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
    exact b.equivFun.apply_symm_apply x
  simpa only [denominatorGrid, Set.mem_ofPred_eq, Matrix.mulVec_smul, hA,
    smul_smul, Nat.cast_mul] using hint

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSeriesCoefficientBounds
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem finiteLog_freeCoefficientBound {s D M : ℕ} {p : FreeAlgebra ℚ X}
    (hp : FreeCoefficientBound s D M p) :
    FreeCoefficientBound s (finiteSeriesDenominator s * D ^ s)
      ((s + 1) * finiteSeriesNumeratorBound s * (D + (s + 1) * M) ^ s) (finiteLog (s + 1) p) := by
  have hterm : ∀ i ∈ Finset.range (s + 1),
      FreeCoefficientBound s (finiteSeriesDenominator s * D ^ s)
        (finiteSeriesNumeratorBound s * (D + (s + 1) * M) ^ s)
        (((-1 : ℚ) ^ (i + 1) / i) • p ^ i) := by
    intro i hi
    have his : i ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    let j : Fin 2 × Fin (s + 1) := (1, ⟨i, Finset.mem_range.mp hi⟩)
    have h := ((hp.pow i).smul (finiteSeriesNumerator_cast s j)
      (finiteSeriesNumerator_le s j)).enlarge_denominator (D ^ (s - i))
    have hden : D ^ (s - i) * (finiteSeriesDenominator s * D ^ i) = finiteSeriesDenominator s * D ^ s := by
      rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel his]
    rw [hden] at h
    have hmass : D ^ (s - i) * (finiteSeriesNumeratorBound s * (((s + 1) * M) ^ i)) ≤
        finiteSeriesNumeratorBound s * (D + (s + 1) * M) ^ s := by
      calc
        _ = finiteSeriesNumeratorBound s * (D ^ (s - i) * (((s + 1) * M) ^ i)) := by ring
        _ ≤ finiteSeriesNumeratorBound s *
            ((D + (s + 1) * M) ^ (s - i) * (D + (s + 1) * M) ^ i) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)
            (Nat.pow_le_pow_left (Nat.le_add_left _ _) _)
        _ = _ := by rw [← pow_add, Nat.sub_add_cancel his]
    simpa only [j, finiteSeriesWeight, show (1 : Fin 2) ≠ 0 from by decide, ite_false] using h.mono hmass
  simpa only [finiteLog, Finset.card_range, mul_assoc] using
    FreeCoefficientBound.sum_finset (Finset.range (s + 1)) _ hterm

theorem bchProductPolynomial_coefficient_bound (s : ℕ) (xs : List X) :
    FreeCoefficientBound s (bchProductDenominator s xs.length) (bchProductNumeratorBound s xs.length)
      (bchProductPolynomial s xs) := by
  have hprod := FreeCoefficientBound.list_prod
    (xs.map (fun x => finiteExp (s + 1) (FreeAlgebra.ι ℚ x))) (by
      intro p hp
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
      exact finiteExp_freeCoefficientBound s x)
  simp only [List.length_map] at hprod
  have hone := (FreeCoefficientBound.one (X := X) s).enlarge_denominator
    (finiteSeriesDenominator s ^ xs.length)
  simp only [mul_one] at hone
  have hsub := hprod.add_same hone.neg
  rw [← sub_eq_add_neg] at hsub
  exact finiteLog_freeCoefficientBound hsub

end Erdos3

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

theorem dilationPairTop_relation (q : ℚ) {x : F.dilationPairSubalgebra q}
    (hx : x ∈ (F.dilationPairFiltration q).layer s) :
    F.dilationPairFirst q x = q ^ s • F.dilationPairSecond q x :=
  F.dilationPairLayer_top_relation q hx

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

theorem weightedLayer_zero (c : σ → ℕ) : F.weightedLayer c 0 = ⊤ := by
  apply top_unique
  intro x _
  apply F.layer_le_weightedLayer c 0 0 (Nat.zero_le _)
  change x ∈ F.layer 0
  simp only [F.zero_eq_top, Submodule.mem_top]

theorem weightedLayer_terminal (c : σ → ℕ) :
    F.weightedLayer c (multidegreeWeight c bound + 1) = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro a
  have hnot : ¬a.val ≤ bound := by
    intro ha
    have h := (multidegreeWeight_mono c ha)
    have h' := a.property
    omega
  intro x hx
  change x = 0
  have h : x ∈ F.layer a.val := hx
  simpa only [F.terminal a.val hnot, Submodule.mem_bot] using h

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

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] in

theorem realification_layer_reduction_in_cell {κ : Type*} [Fintype κ] (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) (n : ℕ) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule) :
    ∀ g : G, g.coord ∈ LieModule.lowerCentralSeries ℚ E E n →
      ∃ r ∈ (fun x : E => (⟨x⟩ : G)) ''
        boundedSpanCell (fun j => rationalLieInclusion (v j)) (rationalSpanGridStep e v l : ℝ),
      ∃ w ∈ Γ.map NilpotentLieBCHGroup.realificationHom,
        (r⁻¹ * g * w⁻¹).coord ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
  classical
  let m := rationalSpanGridStep e v l
  have hm : 0 < m := rationalSpanGridStep_pos e v l hl
  let vR : κ → E := fun j => rationalLieInclusion (v j)
  intro g hg
  have hspanreal : (LieModule.lowerCentralSeries ℚ E E n : Set E) =
      (Submodule.span ℝ (Set.range vR) : Set E) := realification_layer_eq_span n v hspan
  have hgspan : g.coord ∈ Submodule.span ℝ (Set.range vR) :=
    (Set.ext_iff.mp hspanreal g.coord).mp hg
  obtain ⟨r, hr, z, hdecomp⟩ := exists_bounded_span_remainder vR (m : ℝ)
    (by exact_mod_cast hm) g.coord hgspan
  let wQ : L := ∑ j, ((z j : ℚ) * (m : ℚ)) • v j
  have hwQ : (⟨wQ⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ := by
    have h := hinner (rationalSpanGridStep_combination e v l z)
    change (⟨e.equivFun.symm (e.equivFun wQ)⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ at h
    simpa only [LinearEquiv.symm_apply_apply] using h
  have hdecomp' : g.coord = r + rationalLieInclusion wQ := by
    change g.coord = r + rationalLieInclusion (∑ j, ((z j : ℚ) * (m : ℚ)) • v j)
    rw [rationalLieInclusion_integer_combination v z m]
    exact hdecomp
  have hrLayer : r ∈ LieModule.lowerCentralSeries ℚ E E n :=
    (Set.ext_iff.mp hspanreal r).mpr (boundedSpanCell_subset_span vR (m : ℝ) hr)
  have hwLayer : rationalLieInclusion wQ ∈ LieModule.lowerCentralSeries ℚ E E n := by
    have h := (LieModule.lowerCentralSeries ℚ E E n).sub_mem hg hrLayer
    rwa [hdecomp', add_sub_cancel_left] at h
  have hbracket : ⁅r, rationalLieInclusion wQ⁆ ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp) hwLayer
  refine ⟨⟨r⟩, ⟨r, hr, rfl⟩, NilpotentLieBCHGroup.realificationHom ⟨wQ⟩,
    Subgroup.mem_map.mpr ⟨⟨wQ⟩, hwQ, rfl⟩, ?_⟩
  have hg' : g = (⟨r + rationalLieInclusion wQ⟩ : G) := NilpotentLieBCHGroup.ext hdecomp'
  rw [hg']
  exact NilpotentLieBCHGroup.additive_remainder_mem (realification_lowerCentralSeries_eq_bot hnil)
    (LieModule.lowerCentralSeries ℚ E E (n + 1)) r (rationalLieInclusion wQ) hbracket

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem exists_bchSubgroup_comap_grid_of_steps [DecidableEq ι] [DecidableEq κ]
    (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hB : ∀ i j, RationalHeightLE (LinearMap.toMatrix b e φ.toLinearMap i j) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hr : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.mapOfSteps (hL := hM) φ)) ∧
      bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.mapOfSteps (hL := hM) φ)) ⊆ denominatorGrid N := by
  rw [bchSubgroupCoordinates_comap_of_steps b e φ Γ]
  exact exists_preimage_grid_exp_bound (LinearMap.toMatrix b e φ.toLinearMap)
    (Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ.toLinearMap hφ))
    hHpos hlpos hB _ hinner houter hp hd hr hH hl

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

theorem homCoordinates_zsmul (n : ℤ) (v : ι → ℝ) :
    homCoordinates e f φ (n • v) = n • homCoordinates e f φ v := by
  have he : (basisHomeomorph (hnil := hnil) e).symm (n • v) =
      ((basisHomeomorph e).symm v) ^ n := by
    apply (basisHomeomorph e).injective
    simp only [Homeomorph.apply_symm_apply, basisHomeomorph_zpow]
  simp only [homCoordinates, he, map_zpow, basisHomeomorph_zpow]

theorem homCoordinates_intCast_smul (n : ℤ) (v : ι → ℝ) :
    homCoordinates e f φ ((n : ℝ) • v) = (n : ℝ) • homCoordinates e f φ v := by
  simpa only [Int.cast_smul_eq_zsmul] using homCoordinates_zsmul e f φ n v

theorem homCoordinates_ratCast_smul (q : ℚ) (v : ι → ℝ) :
    homCoordinates e f φ ((q : ℝ) • v) = (q : ℝ) • homCoordinates e f φ v := by
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  apply smul_right_injective (κ → ℝ) hd
  dsimp only
  rw [← homCoordinates_natCast_smul, smul_smul, hq, homCoordinates_intCast_smul,
    smul_smul, hq]

theorem homCoordinates_smul (hφ : Continuous φ) (t : ℝ) (v : ι → ℝ) :
    homCoordinates e f φ (t • v) = t • homCoordinates e f φ v := by
  have heq : (fun t : ℝ => homCoordinates e f φ (t • v)) =
      fun t : ℝ => t • homCoordinates e f φ v :=
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).equalizer
      ((homCoordinates_continuous e f φ hφ).comp (continuous_id.smul continuous_const))
      (continuous_id.smul continuous_const)
      (funext fun q => homCoordinates_ratCast_smul e f φ q v)
  exact congrFun heq t

theorem homCoordinates_eq_fderiv (hφ : Continuous φ)
    (hd : DifferentiableAt ℝ (homCoordinates e f φ) 0) (v : ι → ℝ) :
    homCoordinates e f φ v = fderiv ℝ (homCoordinates e f φ) 0 v := by
  have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hD : HasFDerivAt (homCoordinates e f φ) (fderiv ℝ (homCoordinates e f φ) 0)
      ((0 : ℝ) • v) := by simpa using hd.hasFDerivAt
  have hcomp := hD.comp_hasDerivAt (0 : ℝ) hline
  have heq : homCoordinates e f φ ∘ (fun t : ℝ => t • v) =
      fun t : ℝ => t • homCoordinates e f φ v :=
    funext fun t => homCoordinates_smul e f φ hφ t v
  rw [heq] at hcomp
  have hlin : HasDerivAt (fun t : ℝ => t • homCoordinates e f φ v)
      (homCoordinates e f φ v) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (homCoordinates e f φ v)
  exact hlin.unique hcomp

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

theorem homCoordinates_conjugation_eq :
    homCoordinates e e (MulAut.conj a).toMonoidHom = conjugationLinearMap e a := by
  funext v
  exact homCoordinates_eq_fderiv e e (MulAut.conj a).toMonoidHom (continuous_conjugation e a)
    ((contDiff_conjugationCoordinates e a 1).differentiable one_ne_zero).differentiableAt v

theorem conjugationLinearMap_coordinates (x : NilpotentLieBCHGroup L s hnil) :
    conjugationLinearMap e a (basisHomeomorph e x) = basisHomeomorph e (a * x * a⁻¹) := by
  rw [← homCoordinates_conjugation_eq, homCoordinates_apply]
  rfl

theorem conjugationLinearMap_basis [DecidableEq ι] (i k : ι) :
    conjugationLinearMap e a (Pi.single i 1) k =
      e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k := by
  have he : basisHomeomorph (hnil := hnil) e ⟨e i⟩ = Pi.single i 1 := by
    funext j
    simpa only [basisHomeomorph_apply, Pi.single_apply, eq_comm] using e.equivFun_self i j
  rw [← he, conjugationLinearMap_coordinates]
  rfl

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

theorem contMDiff_linear_hom (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) n φ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph f).isOpenEmbedding
  have hc := A.contDiff.contMDiff.comp (contMDiff_basisHomeomorph (hnil := hnil) e n)
  have he : (basisHomeomorph f) ∘ φ = A ∘ basisHomeomorph e :=
    funext (linear_hom_basisHomeomorph e f φ A hA)
  rw [he]
  exact hc

theorem mfderiv_linear_hom_coordinates (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) φ g v = A v := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  have hm := (contMDiff_linear_hom e f φ A hA 1).mdifferentiableAt (x := g) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) g φ = A := by
    funext x
    simpa only [writtenInExtChartAt, Function.comp_apply, basis_extChartAt_apply,
      basis_extChartAt_symm_apply, homCoordinates] using congrFun hA x
  rw [hm.mfderiv, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ, ContinuousLinearMap.fderiv]
  rfl

variable [IsScalarTower ℚ ℝ L] [IsScalarTower ℚ ℝ M]

theorem rightVelocity_linear_hom (g : NilpotentLieBCHGroup L s hnil) :
    (rightVelocity f (φ g)).comp A = A.comp (rightVelocity e g) := by
  have hc : rightTranslate f (φ g⁻¹) ∘ A = A ∘ rightTranslate e g⁻¹ := by
    funext v
    have h := homCoordinates_rightTranslate e f φ g⁻¹ v
    rw [hA] at h
    exact h.symm
  have hi := (contDiff_rightTranslate e g⁻¹ 1).differentiable (by decide)
  have ho := (contDiff_rightTranslate f (φ g⁻¹) 1).differentiable (by decide)
  have hd := congrArg (fun F : (ι → ℝ) → (κ → ℝ) => fderiv ℝ F (basisHomeomorph e g)) hc
  rw [fderiv_comp _ ho.differentiableAt A.differentiableAt,
    fderiv_comp _ A.differentiableAt hi.differentiableAt,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv] at hd
  rw [← linear_hom_basisHomeomorph e f φ A hA, map_inv] at hd
  exact hd

theorem norm_mfderiv_linear_hom_le {C : ℝ}
    (hbound : ∀ w, coordinateL2Norm (A w) ≤ C * coordinateL2Norm w)
    (g : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    letI := rightRiemannianBundle (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hM) f
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) φ g v‖ ≤ C * ‖v‖ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  intro v
  have hv := mfderiv_linear_hom_coordinates e f φ A hA g v
  have hc := congrArg (fun T : (ι → ℝ) →L[ℝ] (κ → ℝ) => T v)
    (rightVelocity_linear_hom e f φ A hA g)
  have hvel := (congrArg (fun w : κ → ℝ => rightVelocity f (φ g) w) hv).trans hc
  calc
    _ = coordinateL2Norm (rightVelocity f (φ g)
        (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) φ g v)) := norm_tangent_eq_coordinateL2Norm f _ _
    _ = coordinateL2Norm (A (rightVelocity e g v)) := congrArg coordinateL2Norm hvel
    _ ≤ C * coordinateL2Norm (rightVelocity e g v) := hbound _
    _ = C * ‖v‖ := congrArg (C * ·) (norm_tangent_eq_coordinateL2Norm e g v).symm

theorem lipschitz_linear_hom {C : ℝ≥0} (hC : 0 < C)
    (hbound : ∀ w, coordinateL2Norm (A w) ≤ C * coordinateL2Norm w) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith C φ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  apply riemannianEDist_le_mul_of_mfderiv_bound hC (contMDiff_linear_hom e f φ A hA 1)
  intro g v
  have h := ENNReal.ofReal_le_ofReal (norm_mfderiv_linear_hom_le e f φ A hA hbound g v)
  simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ofReal_norm,
    ENNReal.ofReal_coe_nnreal] using h

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (a : NilpotentLieBCHGroup L s hnil)

theorem lipschitz_conjugation_of_basis_bound (B : ℝ≥0)
    (hB : ∀ i k, |e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    LipschitzWith (coordinateLipschitzBound (Fintype.card ι) (Fintype.card ι) B)
      (MulAut.conj a) := by
  classical
  apply lipschitz_linear_hom e e (MulAut.conj a).toMonoidHom (conjugationLinearMap e a)
    (homCoordinates_conjugation_eq e a) (coordinateLipschitzBound_pos _ _ _)
  intro v
  apply coordinateLinearMap_L2_bound _ B B.coe_nonneg
  intro k i
  rw [conjugationLinearMap_basis]
  exact hB i k

theorem lipschitz_mul_left_of_basis_bound (B : ℝ≥0)
    (hB : ∀ i k, |e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    LipschitzWith (coordinateLipschitzBound (Fintype.card ι) (Fintype.card ι) B)
      (fun x => a * x) := by
  let := rightMetricSpace (hnil := hnil) e
  have h := (rightMetricSpace_isometry_mul_right e a).lipschitz.comp
    (lipschitz_conjugation_of_basis_bound e a B hB)
  simpa only [one_mul, Function.comp_def, MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using h

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (v : ι → ℝ)

theorem dist_le_coordinateL2Norm_mul_inv (x y : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    dist x y ≤ coordinateL2Norm (basisHomeomorph e (x * y⁻¹)) := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  rw [← dist_mul_right x y y⁻¹, mul_inv_cancel, dist_comm]
  exact dist_one_le_coordinateL2Norm e (x * y⁻¹)

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem bchProductWordCoefficient_height (s : ℕ) (xs : List X) (w : FreeMonoid X)
    (hw : w.length ≤ s) :
    RationalHeightLE (freeWordCoefficients (bchProductPolynomial s xs) w)
      (bchProductCoefficientHeight s xs.length) := by
  exact ((bchProductPolynomial_coefficient_bound s xs).rationalHeight
    (bchProductDenominator_pos s xs.length) w hw).mono
      (max_le (bchProductDenominator_le_height s xs.length) (bchProductNumeratorBound_le_height s xs.length))

theorem bchProductBracketCoefficient_height (s : ℕ) (xs : List X) {w : FreeSemigroup X}
    (hw : w ∈ bchProductBracketSupport s xs) :
    RationalHeightLE (bchProductBracketCoefficient s xs w)
      (bchProductCoefficientHeight s xs.length * (s + 1)) := by
  have hlen := bchProductBracketSupport_length s xs hw
  have hword := bchProductWordCoefficient_height s xs w.toFreeMonoid
    (by simpa only [freeSemigroup_toFreeMonoid_length] using hlen)
  have hinv : RationalHeightLE ((w.length : ℚ)⁻¹) (s + 1) := by
    have hpos : 0 < w.length := by change 0 < w.tail.length + 1; omega
    have h := rationalHeightLE_fraction (1 : ℤ) (w.length : ℤ)
      (by exact_mod_cast hpos.ne') (H := s + 1) (by simp)
      (by simpa only [Int.natAbs_natCast] using hlen.trans (Nat.le_succ s))
    simpa only [Int.cast_one, Int.cast_natCast, one_div] using h
  rw [bchProductBracketCoefficient, bchProductWordCoefficients_eq, if_pos hlen, div_eq_mul_inv]
  exact hword.mul hinv

variable {ι : Type*} [Fintype ι]

theorem bchProductCoordinatePolynomial_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (s : ℕ) (xs : List X) (k : ι) :
    RationalPolynomialHeightLE (bchProductCoordinatePolynomial c s xs k)
      (((bchProductBracketSupport s xs).card + 1) *
        (bchProductCoefficientHeight s xs.length * (s + 1) *
          lieCoordinateHeight (Fintype.card ι) H s) ^ (bchProductBracketSupport s xs).card) := by
  apply RationalPolynomialHeightLE.sum_finset
  intro w hw
  exact RationalPolynomialHeightLE.C_mul (bchProductBracketCoefficient_height s xs hw)
    ((dynkinCoordinatePolynomial_height c hc w k).mono
      (lieCoordinateHeight_mono_length _ _ (bchProductBracketSupport_length s xs hw)))

end Erdos3

end

section

namespace Erdos3

theorem exists_bchProductCoordinatePolynomial_exp_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X ι : Type*} [Fintype X] [Fintype ι]
      (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ) (xs : List X),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (xs.length : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      ∀ k m, (((bchProductCoordinatePolynomial c s xs k).coeff m).num.natAbs : ℝ) ≤
          Real.exp ((p + C) ^ C) ∧
        (((bchProductCoordinatePolynomial c s xs k).coeff m).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  let C := bchProductCoefficientBase s + 5 * s + 10
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C, hC, ?_⟩
  intro X ι _ _ c H p xs hp hd hX hn hH hc k m
  let t : ℝ := p + C
  have ht : 2 ≤ t := by
    have h : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    linarith
  have hshift : p + 2 ≤ t := by
    have h : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    linarith
  have hs : (s : ℝ) + 1 ≤ t := by
    have h : (s : ℝ) + 1 ≤ C := by exact_mod_cast (show s + 1 ≤ C by dsimp [C]; omega)
    dsimp [t]
    linarith
  have hword : (bchProductCoefficientHeight s xs.length : ℝ) ≤ Real.exp (t ^ (3 * s + 3)) := by
    apply (bchProductCoefficientHeight_le_exp s xs.length C hp hn
      (by dsimp [C]; omega) (by dsimp [C]; omega)).trans
    exact Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by omega))
  have hsbound : ((s + 1 : ℕ) : ℝ) ≤ Real.exp (t ^ (3 * s + 3)) := by
    have h1 : t ≤ t ^ (3 * s + 3) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t)
        (show 1 ≤ 3 * s + 3 by omega)
    have h2 := Real.add_one_le_exp (t ^ (3 * s + 3))
    push_cast
    linarith
  have hlie : (lieCoordinateHeight (Fintype.card ι) H s : ℝ) ≤ Real.exp (t ^ (3 * s + 3)) := by
    apply (lieCoordinateHeight_le_exp (Fintype.card ι) H s hp hd hH).trans
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by linarith) hshift _).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  have hproduct : ((bchProductCoefficientHeight s xs.length * (s + 1) *
        lieCoordinateHeight (Fintype.card ι) H s : ℕ) : ℝ) ≤ Real.exp (t ^ (3 * s + 5)) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    calc
      _ ≤ Real.exp (t ^ (3 * s + 3)) * Real.exp (t ^ (3 * s + 3)) * Real.exp (t ^ (3 * s + 3)) :=
        mul_le_mul (mul_le_mul hword hsbound (by positivity) (by positivity)) hlie
          (by positivity) (by positivity)
      _ = Real.exp (3 * t ^ (3 * s + 3)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [show 3 * s + 5 = (3 * s + 3) + 2 by omega, pow_add t (3 * s + 3) 2]
        have hsq : 3 ≤ t ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ t ^ (3 * s + 3))]
  have hcard : ((bchProductBracketSupport s xs).card : ℝ) ≤ t ^ (s + 1) := by
    have h := (Nat.cast_le (α := ℝ)).mpr (bchProductBracketSupport_card_le s xs)
    push_cast at h
    apply h.trans
    calc
      ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s ≤ t * t ^ s :=
        mul_le_mul hs (pow_le_pow_left₀ (by positivity) (by linarith) _)
          (by positivity) (by positivity)
      _ = _ := (pow_succ' t s).symm
  have hsum := rational_sum_cost_le_exp (bchProductBracketSupport s xs).card
    (bchProductCoefficientHeight s xs.length * (s + 1) * lieCoordinateHeight (Fintype.card ι) H s)
    (p := t - 2) (by linarith) (3 * s + 5) (s + 1)
    (by simpa only [sub_add_cancel] using hproduct) (by simpa only [sub_add_cancel] using hcard)
  have hfinal : (((bchProductBracketSupport s xs).card + 1) *
      (bchProductCoefficientHeight s xs.length * (s + 1) * lieCoordinateHeight (Fintype.card ι) H s) ^
        (bchProductBracketSupport s xs).card : ℕ) ≤ Real.exp (t ^ C) := by
    apply hsum.trans
    apply Real.exp_le_exp.mpr
    rw [sub_add_cancel]
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hheight := bchProductCoordinatePolynomial_height c hc s xs k m
  exact ⟨(Nat.cast_le.mpr hheight.1).trans hfinal, (Nat.cast_le.mpr hheight.2).trans hfinal⟩

theorem exists_bch_product_coordinate_polynomials_exp_height (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X ι R L : Type*} [Fintype X] [Fintype ι]
      [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L]
      [IsScalarTower ℚ R L] (e : Module.Basis ι R L) (c : ι → ι → ι → ℚ)
      (H : ℕ) (p : ℝ) (xs : List X),
      (∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k) →
      LieModule.lowerCentralSeries ℚ L L s = ⊥ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (xs.length : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      ∃ P : ι → MvPolynomial (X × ι) ℚ,
        (∀ (f : X → L) k,
          MvPolynomial.aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (P k) =
            e.repr (lieBCHList s f xs) k) ∧
        (∀ k, (P k).totalDegree ≤ s) ∧
        (∀ k, (P k).support.card ≤ (s + 1) * (Fintype.card X * Fintype.card ι + 1) ^ s) ∧
        ∀ k m, (((P k).coeff m).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          (((P k).coeff m).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_bchProductCoordinatePolynomial_exp_budget s
  refine ⟨C, hC, ?_⟩
  intro X ι R L _ _ _ _ _ _ _ _ e c H p xs hstructure hnil hp hd hX hn hH hc
  refine ⟨bchProductCoordinatePolynomial c s xs, ?_,
    bchProductCoordinatePolynomial_totalDegree c s xs,
    bchProductCoordinatePolynomial_support_card c s xs, hbudget c H p xs hp hd hX hn hH hc⟩
  intro f k
  exact bchProductCoordinatePolynomial_eval_over e c hstructure s hnil f xs k

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial

theorem exists_bch_product_box_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X ι L : Type*} [Fintype X] [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (xs : List X) (f : X → L) (B : ℝ),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      LieModule.lowerCentralSeries ℚ L L s = ⊥ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (xs.length : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      1 ≤ B → (∀ x i, |e.repr (f x) i| ≤ B) →
      ∀ i, |e.repr (lieBCHList s f xs) i| ≤
        ((s + 1) * (Fintype.card X * Fintype.card ι + 1) ^ s : ℕ) *
          Real.exp ((p + C) ^ C) * B ^ s := by
  obtain ⟨C, hC, hpoly⟩ := exists_bch_product_coordinate_polynomials_exp_height s
  refine ⟨C, hC, ?_⟩
  intro X ι L _ _ _ _ _ _ e c H p xs f B hstructure hnil hp hd hX hn hH hc hB hf i
  obtain ⟨P, heval, hdegree, hcard, hheight⟩ :=
    hpoly e c H p xs hstructure hnil hp hd hX hn hH hc
  rw [← heval f i]
  have hbound := abs_aeval_le_box_bound (P i)
    (fun xi : X × ι => e.repr (f xi.1) xi.2)
    (Real.exp_nonneg _) hB
    (fun m => (rational_abs_real_le_numerator _).trans (hheight i m).1)
    (fun xi => hf xi.1 xi.2) (hdegree i)
  apply hbound.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard i)) (Real.exp_nonneg _))
    (pow_nonneg (by linarith) _)

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_bch_group_product_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (rs : List (NilpotentLieBCHGroup L s hnil)),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → rs.length ≤ s →
      (H : ℝ) ≤ Real.exp p → (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ r ∈ rs, ∀ i, |e.repr r.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ i, |e.repr rs.prod.coord i| ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hbox⟩ := exists_bch_product_box_bound s
  refine ⟨C + 3 * s + a + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil rs hstructure hp hd hn hH hc hrs i
  let f : Fin rs.length → L := fun j => (rs.get j).coord
  let xs := List.finRange rs.length
  have hlen : (xs.length : ℝ) ≤ p + s := by
    have hn' : (rs.length : ℝ) ≤ s := by exact_mod_cast hn
    simpa only [xs, List.length_finRange] using hn'.trans (by linarith)
  have hlabels : (Fintype.card (Fin rs.length) : ℝ) ≤ p + s := by
    simpa only [Fintype.card_fin, xs, List.length_finRange] using hlen
  have hbound := hbox e c H (p + s) xs f (Real.exp ((p + 2) ^ a)) hstructure hnil
    (by positivity) (hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) s])) hlabels hlen
    (hH.trans (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) s]))) hc
    (Real.one_le_exp (by positivity))
    (fun j k => hrs (rs.get j) (List.get_mem _ _) k) i
  have hmap : (xs.map (fun j => (⟨f j⟩ : NilpotentLieBCHGroup L s hnil))) = rs := by
    change (List.finRange rs.length).map rs.get = rs
    exact List.map_get_finRange rs
  have hcoord := lieBCHList_group_prod s hnil f xs
  rw [hmap] at hcoord
  rw [← hcoord, Fintype.card_fin] at hbound
  exact hbound.trans (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      bch_box_expression_le_exp s a C rs.length (Fintype.card ι) hC hp hn hd)

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_bch_triple_product_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (u v w : NilpotentLieBCHGroup L s hnil),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ i, |e.repr u.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      (∀ i, |e.repr v.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      (∀ i, |e.repr w.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ i, |e.repr (u * v * w).coord i| ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hbox⟩ := exists_bch_product_box_bound s
  refine ⟨C + 3 * (s + 3) + a + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil u v w hstructure hp hd hH hc hu hv hw i
  let f : Fin 3 → L := ![u.coord, v.coord, w.coord]
  let xs : List (Fin 3) := [0, 1, 2]
  have hcoords (j : Fin 3) (k : ι) : |e.repr (f j) k| ≤ Real.exp ((p + 2) ^ a) := by
    fin_cases j
    · exact hu k
    · exact hv k
    · exact hw k
  have hbound := hbox e c H (p + 3) xs f (Real.exp ((p + 2) ^ a)) hstructure hnil
    (by linarith) (hd.trans (by linarith))
    (by norm_num only [Fintype.card_fin, Nat.cast_ofNat]; linarith)
    (by simp only [xs, List.length_cons, List.length_nil]; norm_num; linarith)
    (hH.trans (Real.exp_le_exp.mpr (by linarith))) hc
    (Real.one_le_exp (by positivity)) hcoords i
  have heq : lieBCHList s f xs = (u * v * w).coord := by
    simpa [xs, f, mul_assoc] using
      (lieBCHList_group_prod s hnil f xs).symm
  rw [heq, Fintype.card_fin] at hbound
  exact hbound.trans (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      bch_triple_box_expression_le_exp s a C (Fintype.card ι) hC hp hd)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped NNReal

theorem exists_bch_conjugation_basis_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (a : NilpotentLieBCHGroup L s hnil),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ i, |e.repr a.coord i| ≤ Real.exp ((p + 2) ^ r)) →
      ∀ i k, |e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k| ≤
        Real.exp ((p + D) ^ D) := by
  classical
  obtain ⟨D, hD, hprod⟩ := exists_bch_triple_product_exp_bound s r
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil a hstructure hp hd hH hc ha i k
  apply hprod e c H p hnil a ⟨e i⟩ a⁻¹ hstructure hp hd hH hc ha
  · intro j
    change |e.repr (e i) j| ≤ _
    rw [Basis.repr_self_apply]
    split_ifs
    · simpa only [abs_one] using Real.one_le_exp (by positivity : 0 ≤ (p + 2) ^ r)
    · simpa only [abs_zero] using Real.exp_nonneg ((p + 2) ^ r)
  · intro j
    change |e.repr (-a.coord) j| ≤ _
    simpa only [map_neg, Finsupp.neg_apply, abs_neg] using ha j

namespace NilpotentLieBCHGroup

theorem exists_uniform_left_lipschitz_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      letI := rightMetricSpace (hnil := hnil) e
      ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∀ a : NilpotentLieBCHGroup L s hnil,
          (∀ i, |e.repr a.coord i| ≤ Real.exp ((p + 2) ^ r)) →
          LipschitzWith C (fun x => a * x) := by
  obtain ⟨D, hD, hbound⟩ := exists_bch_conjugation_basis_exp_bound s r
  refine ⟨(D + 2) * 2, by omega, ?_⟩
  intro ι L _ _ _ _ _ _ _ _ _ e c H p hnil hstructure hp hd hH hc
  let := rightMetricSpace (hnil := hnil) e
  let B : ℝ≥0 := ⟨Real.exp ((p + D) ^ D), Real.exp_nonneg _⟩
  refine ⟨coordinateLipschitzBound (Fintype.card ι) (Fintype.card ι) B,
    coordinateLipschitzBound_pos _ _ _,
    coordinateLipschitzBound_power_budget _ D hD B hp hd le_rfl, ?_⟩
  intro a ha
  exact lipschitz_mul_left_of_basis_bound e a B (hbound e c H p hnil a hstructure hp hd hH hc ha)

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

theorem exists_uniform_quotient_left_lipschitz_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∀ (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
          (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
          (a : NilpotentLieBCHGroup L s hnil),
          (∀ i, |e.repr a.coord i| ≤ Real.exp ((p + 2) ^ r)) →
          letI := quotientMetricSpace e Γ hΓ
          LipschitzWith C (fun x : _ ⧸ Γ => a • x) := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_left_lipschitz_exp_bound s r
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ _ _ e c H p hnil hstructure hp hd hH hc
  obtain ⟨C, hC, hCp, hLip⟩ := hbound e c H p hnil hstructure hp hd hH hc
  refine ⟨C, hC, hCp, ?_⟩
  intro Γ hΓ a ha
  exact quotientMetricSpace_lipschitz_left e Γ hΓ a (hLip a ha)

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ConjugationCoordinates
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem conjugation_preserves_inner_grid (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (q l : ℕ) (hq : 0 < q)
    (z g : NilpotentLieBCHGroup L s hnil)
    (hz : e.equivFun z.coord ∈ denominatorGrid q)
    (hg : e.equivFun g.coord ∈ scaledIntegerGrid
      (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s)) :
    e.equivFun (z * g * z⁻¹).coord ∈ scaledIntegerGrid l := by
  have hb := scaledIntegerGrid_mem_denominatorGrid _ q hg
  have hzero : (0 : ι → ℚ) ∈ denominatorGrid q := ⟨0, by simp⟩
  have h := rational_polynomial_family_eval_sub_mem_grid
    (conjugationCoordinatePolynomial e s) q s l hq (conjugationCoordinatePolynomial_degree e s)
    (conjugationInput (e.equivFun z.coord) (e.equivFun g.coord))
    (conjugationInput (e.equivFun z.coord) 0)
    (conjugationInput_mem_denominatorGrid _ _ q hz hb)
    (conjugationInput_mem_denominatorGrid _ _ q hz hzero)
    (conjugationInput_sub_mem_scaledGrid _ _ _ hg)
  simpa only [conjugationCoordinatePolynomial_eval, conjugationCoordinatePolynomial_zero,
    sub_zero, ← Basis.equivFun_apply] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ConjugationDenominatorBudget
namespace OAI

section

namespace Erdos3

open Module

theorem exists_conjugation_denominator_exp_bound (s : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) : ℝ) ≤
        Real.exp ((p + K) ^ K) := by
  obtain ⟨C, hC, hcoeff⟩ := exists_bchProductCoordinatePolynomial_exp_budget s
  let K := C + 3 * s + 10
  refine ⟨K, by dsimp [K]; omega, ?_⟩
  intro ι L _ _ _ e H p hp hd hH hc
  let t := p + K
  have hK : (s : ℝ) + 3 ≤ K := by exact_mod_cast (show s + 3 ≤ K by dsimp [K]; omega)
  have ht : 3 ≤ t := by dsimp [t]; linarith
  have hpt : p + 3 ≤ t := by dsimp [t]; linarith
  have hs : (s : ℝ) + 1 ≤ t := by dsimp [t]; linarith
  have hshift : p + 3 + C ≤ t := by
    have h : C + 3 ≤ K := by dsimp [K]; omega
    have h' : (C : ℝ) + 3 ≤ K := by exact_mod_cast h
    dsimp [t]
    linarith
  have hcoeff' : ∀ i m, (((conjugationCoordinatePolynomial e s i).coeff m).den : ℝ) ≤
      Real.exp (t ^ C) := by
    intro i m
    have h := (hcoeff (lieStructureConstants e) H (p + 3) ([0, 1, 2] : List (Fin 3))
      (by positivity) (by linarith) (by simp; linarith) (by simp; linarith)
      (hH.trans (Real.exp_le_exp.mpr (by linarith))) hc i m).2
    exact h.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) hshift C))
  have hcard : ∀ i, ((conjugationCoordinatePolynomial e s i).support.card : ℝ) ≤ t ^ (2 * s + 1) := by
    intro i
    have h := (Nat.cast_le (α := ℝ)).mpr
      (bchProductCoordinatePolynomial_support_card (lieStructureConstants e) s ([0, 1, 2] : List (Fin 3)) i)
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h
    have hb : 3 * (Fintype.card ι : ℝ) + 1 ≤ t ^ 2 := by nlinarith [sq_nonneg p]
    apply h.trans
    calc
      _ ≤ t * (t ^ 2) ^ s := mul_le_mul hs (pow_le_pow_left₀ (by positivity) hb s) (by positivity) (by linarith)
      _ = t ^ (2 * s + 1) := by rw [← pow_mul, pow_succ']
  have hD := polynomialFamilyDenominator_exp_bound (conjugationCoordinatePolynomial e s)
    (p := t - 2) (by linarith) C 1 (2 * s + 1)
    (by simpa only [sub_add_cancel] using hcoeff')
    (by simpa only [sub_add_cancel] using hcard)
    (by rw [sub_add_cancel, pow_one]; linarith)
  rw [sub_add_cancel] at hD
  apply hD.trans
  exact Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by dsimp [K]; omega))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquarefreeAlgebraCoordinates
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeAlgebraEquiv_apply (x : F.SquarefreeAlgebra π) (a : SquarefreeIndex ι) :
    (F.squarefreeAlgebraEquiv π x a).val = squarefreePolynomialEquiv x.val a := rfl

instance squarefreeAlgebraFiniteDimensional [FiniteDimensional ℚ L] :
    FiniteDimensional ℚ (F.SquarefreeAlgebra π) :=
  FiniteDimensional.of_injective (F.squarefreeAlgebraEquiv π).toLinearMap
    (F.squarefreeAlgebraEquiv π).injective

theorem squarefreeAlgebra_finrank [FiniteDimensional ℚ L] :
    Module.finrank ℚ (F.SquarefreeAlgebra π) =
      ∑ a : SquarefreeIndex ι, Module.finrank ℚ (F.squarefreeCoefficientLayer π a) := by
  rw [(F.squarefreeAlgebraEquiv π).finrank_eq, Module.finrank_pi_fintype]

theorem squarefreeAlgebra_finrank_le [FiniteDimensional ℚ L] :
    Module.finrank ℚ (F.SquarefreeAlgebra π) ≤
      2 ^ Fintype.card ι * Module.finrank ℚ L := by
  rw [F.squarefreeAlgebra_finrank π]
  calc
    _ ≤ ∑ _a : SquarefreeIndex ι, Module.finrank ℚ L :=
      Finset.sum_le_sum fun a _ => (F.squarefreeCoefficientLayer π a).finrank_le
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_squarefreeIndex, Nat.cast_id]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ]

theorem blockExponent_permute (π : ι → σ) (e : Equiv.Perm ι)
    (he : ∀ i, π (e i) = π i) (a : SquarefreeIndex ι) :
    blockExponent π (SquarefreeIndex.permute e a).val = blockExponent π a.val := by
  ext i
  simp only [blockExponent_apply, SquarefreeIndex.permute_blockDegree π e he a]

end Erdos3

end

section

namespace Erdos3

theorem SquarefreeIndex.permute_weight {ι κ : Type*} (e : ι ≃ κ)
    (a : SquarefreeIndex ι) (x : ι → ℚ) :
    ((permute e a).val.prod fun j n => x (e.symm j) ^ n) =
      a.val.prod (fun i n => x i ^ n) := by
  change (Finsupp.equivMapDomain e a.val).prod _ = _
  rw [Finsupp.prod_equivMapDomain]
  simp only [Equiv.symm_apply_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquarefreeBasisPermutation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))

theorem squarefreeSupportedBasis_coe (P : SquarefreeIndex ι → Prop)
    (j : {j : Σ a, κ a // P j.1}) :
    (F.squarefreeSupportedBasis π b P j).val = F.squarefreeBasis π b j.val :=
  supportedSubmoduleBasis_coe _ _ _ _ j

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight
namespace OAI

section

namespace Erdos3

open Module

namespace MultidegreeLieFiltration

variable {ι σ ν L : Type*} [Fintype ι] [Fintype σ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))
  (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
  (hb : ∀ a j k, RationalHeightLE (e.repr (b a j).val k) H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

include hH hb hc

theorem squarefreeBasis_bracket_coefficient_height (x y : Σ a, κ a) (a : SquarefreeIndex ι) (k : ν) :
    RationalHeightLE (e.repr
      (F.squarefreeAlgebraEquiv π ⁅F.squarefreeBasis π b x, F.squarefreeBasis π b y⁆ a).val k)
      (squarefreeBracketHeight (Fintype.card ν) H) := by
  rw [F.squarefreeAlgebraEquiv_apply]
  change RationalHeightLE (e.repr (squarefreePolynomialEquiv
    ⁅(F.squarefreeBasis π b x).val, (F.squarefreeBasis π b y).val⁆ a) k) _
  rw [F.squarefreeBasis_monomial, F.squarefreeBasis_monomial]
  by_cases hxy : Disjoint x.1.val.support y.1.val.support
  · rw [squarefreeMonomial_lie_disjoint x.1 y.1 hxy]
    by_cases ha : x.1.disjointAdd y.1 hxy = a
    · subst a
      rw [squarefreePolynomialEquiv_monomial_self]
      exact lie_bracket_coordinate_height e hc _ _ (hb x.1 x.2) (hb y.1 y.2) k
    · rw [squarefreePolynomialEquiv_monomial_ne _ _ ha, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero (squarefreeBracketHeight_pos _ hH)
  · rw [squarefreeMonomial_lie_overlap _ _ hxy, map_zero, Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (squarefreeBracketHeight_pos _ hH)

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

theorem toOrdinaryOrbit_eval (p : F.PolynomialOrbit) (x : σ → ℤ) :
    F.ordinary.polynomialOrbitEval (fun _ => 1) x (F.toOrdinaryOrbit p) = F.polynomialOrbitEval x p := rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientInducedMark
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
  (hI : F.layer (t + 1) ≤ I.toSubmodule)

theorem realQuotientStepHom_surjective : Function.Surjective (F.realQuotientStepHom I hI) := by
  intro g
  obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ (lieQuotientMap_surjective I) g.coord
  exact ⟨⟨x⟩, NilpotentLieBCHGroup.ext hx⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem omitted_weighted_top (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s) :
    F.weightedLayer (omittedCoordinateWeight i) s = ⊥ := by
  have h := omittedCoordinateWeight_total i bound
  rw [hi, hs] at h
  simpa only [h] using F.weightedLayer_terminal (omittedCoordinateWeight i)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem top_commutes (g : F.Group) (hg : g ∈ F.subgroup s) (h : F.Group) : Commute g h :=
  commute_of_lie_eq_zero g h (F.top_layer_central hg h.coord)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedDilationMultidegree
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realPairEquiv_mem_dilationPairLayer (q : ℚ) (n : ℕ)
    (x : ℝ ⊗[ℚ] (L × L)) :
    realPairEquiv x ∈ F.realification.dilationPairLayer q n ↔
      x ∈ (F.dilationPairLayer q n).baseChange ℝ :=
  realPairEquiv_mem_scaledPairLayer (F.layer n) (F.layer (n + 1)) (q ^ n) x

noncomputable def realifiedDilationPairLayerEquiv (q : ℚ) (n : ℕ) :
    ((F.dilationPairLayer q n).baseChange ℝ) ≃ₗ[ℚ]
      F.realification.dilationPairLayer q n :=
  realifiedScaledPairLayerEquiv (F.layer n) (F.layer (n + 1)) (q ^ n)

noncomputable def realifiedDilationPairEquiv (q : ℚ) :
    (ℝ ⊗[ℚ] F.dilationPairSubalgebra q) ≃ₗ[ℚ]
      F.realification.dilationPairSubalgebra q :=
  ((realificationSubmoduleEquiv (F.dilationPairLayer q 1)).restrictScalars ℚ).trans
    (F.realifiedDilationPairLayerEquiv q 1)

theorem realifiedDilationPairEquiv_coe (q : ℚ)
    (x : ℝ ⊗[ℚ] F.dilationPairSubalgebra q) :
    (F.realifiedDilationPairEquiv q x : (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) =
      realPairEquiv (realificationLieHom (F.dilationPairSubalgebra q).incl x) := rfl

theorem realifiedDilationPairEquiv_mem_layer (q : ℚ) (n : ℕ)
    (x : ℝ ⊗[ℚ] F.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairFiltration q).realification.layer n ↔
      F.realifiedDilationPairEquiv q x ∈ (F.realification.dilationPairFiltration q).layer n := by
  change x ∈ ((F.dilationPairLayer q n).comap
    (F.dilationPairSubalgebra q).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change realificationLieHom (F.dilationPairSubalgebra q).incl x ∈
    (F.dilationPairLayer q n).baseChange ℝ ↔
      (F.realifiedDilationPairEquiv q x : (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) ∈
        F.realification.dilationPairLayer q n
  rw [F.realifiedDilationPairEquiv_coe, F.realPairEquiv_mem_dilationPairLayer]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SubmoduleCoordinateHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem submodule_basis_coordinate_height {ν κ L : Type*} [Fintype ν] [Fintype κ]
    [AddCommGroup L] [Module ℚ L] (U : Submodule ℚ L)
    (b : Basis κ ℚ U) (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
    (hB : ∀ i j, RationalHeightLE (e.repr (b j).val i) H)
    (x : U) {K : ℕ} (hx : ∀ i, RationalHeightLE (e.repr x.val i) K) (j : κ) :
    RationalHeightLE (b.repr x j)
      ((Fintype.card ν + 1) * (rationalSolveHeight (Fintype.card κ) H * K) ^ Fintype.card ν) := by
  classical
  let B := LinearMap.toMatrix b e U.subtype
  have hBmul (w : κ → ℚ) : B *ᵥ w = e.equivFun (b.equivFun.symm w).val := by
    have h := LinearMap.toMatrix_mulVec_repr b e U.subtype (b.equivFun.symm w)
    simp only [← b.equivFun_apply, LinearEquiv.apply_symm_apply, ← e.equivFun_apply] at h
    exact h
  have hBi : Function.Injective B.mulVec := by
    intro u v huv
    rw [hBmul, hBmul] at huv
    exact b.equivFun.symm.injective (Subtype.ext (e.equivFun.injective huv))
  obtain ⟨P, hPB, hP⟩ := exists_bounded_rational_left_inverse B
    (Matrix.mulVec_injective_iff.mp hBi) hH
    (by
      intro i j
      dsimp only [B]
      rw [LinearMap.toMatrix_apply]
      exact hB i j)
  have hretract : P *ᵥ e.repr x.val = b.repr x := by
    have hrepr : B *ᵥ b.repr x = e.repr x.val :=
      LinearMap.toMatrix_mulVec_repr b e U.subtype x
    rw [← hrepr, Matrix.mulVec_mulVec, hPB, Matrix.one_mulVec]
  rw [← congrFun hretract j]
  exact rationalHeightLE_sum (fun i => P j i * e.repr x.val i)
    (fun i => (hP j i).mul (hx i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeStructureHeight
namespace OAI

section

namespace Erdos3

open Module

namespace MultidegreeLieFiltration

variable {ι σ ν L : Type*} [Fintype ι] [Fintype σ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))
  (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
  (hb : ∀ a j k, RationalHeightLE (e.repr (b a j).val k) H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

include hH hb hc

theorem squarefreeBasis_structure_height
    (hκ : ∀ a, Fintype.card (κ a) ≤ Fintype.card ν) (x y z : Σ a, κ a) :
    RationalHeightLE (lieStructureConstants (F.squarefreeBasis π b) x y z)
      (squarefreeStructureHeight (Fintype.card ν) H) := by
  change RationalHeightLE ((F.squarefreeBasis π b).repr
    ⁅F.squarefreeBasis π b x, F.squarefreeBasis π b y⁆ z) _
  rw [F.squarefreeBasis_repr]
  have h := submodule_basis_coordinate_height (F.squarefreeCoefficientLayer π z.1) (b z.1) e hH
    (fun i j => hb z.1 j i)
    (F.squarefreeAlgebraEquiv π ⁅F.squarefreeBasis π b x, F.squarefreeBasis π b y⁆ z.1)
    (fun k => F.squarefreeBasis_bracket_coefficient_height π b e hH hb hc x y z.1 k) z.2
  apply h.mono
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_right _ (rationalSolveHeight_mono hH (hκ z.1))) _)

end MultidegreeLieFiltration

end Erdos3

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

theorem conjugated_subgroup_inner_grid (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l q : ℕ) (hq : 0 < q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (z : NilpotentLieBCHGroup L s hnil) (hz : e.equivFun z.coord ∈ denominatorGrid q) :
    scaledIntegerGrid (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s) ⊆
      bchSubgroupCoordinates e (Γ.map (MulAut.conj z).toMonoidHom) := by
  intro x hx
  let g : NilpotentLieBCHGroup L s hnil := ⟨e.equivFun.symm x⟩
  have hg : e.equivFun g.coord ∈ scaledIntegerGrid
      (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s) := by
    simpa only [g, LinearEquiv.apply_symm_apply] using hx
  have hzinv : e.equivFun (z⁻¹).coord ∈ denominatorGrid q := by
    simpa only [NilpotentLieBCHGroup.coord_inv, map_neg] using denominatorGrid_neg q hz
  have hconj := conjugation_preserves_inner_grid e hnil q l hq z⁻¹ g hzinv hg
  have hmem : z⁻¹ * g * z ∈ Γ := by
    apply (bchSubgroupCoordinates_repr e Γ _).mp
    apply hinner
    simpa only [inv_inv] using hconj
  change g ∈ Γ.map (MulAut.conj z).toMonoidHom
  refine Subgroup.mem_map.mpr ⟨z⁻¹ * g * z, hmem, ?_⟩
  change z * (z⁻¹ * g * z) * z⁻¹ = g
  group

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (v : σ → ℕ)

theorem symbolSlowBound_mono (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M N : ℝ} (hMN : M ≤ N)
    (g : F.RealPolynomialSymbolGroup v) (hg : F.SymbolSlowBound b w hlayers v T M g) :
    F.SymbolSlowBound b w hlayers v T N g := by
  intro z
  exact (hg z).trans (div_le_div_of_nonneg_right hMN (le_of_lt (monomialScale_pos T hT z.val.1)))

end Erdos3.NilpotentLieFiltration

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

theorem orbitEquivOfEq_eval (h : F = G) (p : F.PolynomialOrbit) (x : σ → ℤ) :
    G.polynomialOrbitEval x (F.orbitEquivOfEq h p) = F.polynomialOrbitEval x p := by
  subst G
  rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ImageLatticeSubgroup
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct

theorem matrix_mulVec_fine_grid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℚ) (l : ℕ) :
    scaledIntegerGrid (l * matrixDenominator S) ⊆ S.mulVec ⁻¹' scaledIntegerGrid l := by
  classical
  rintro y ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := integralVector_denominator_mulVec S (fun j => (z j : ℚ)) ⟨z, fun _ => rfl⟩
  refine ⟨w, ?_⟩
  rw [Matrix.mulVec_smul]
  ext i
  have hi := hw i
  change (matrixDenominator S : ℚ) * (S *ᵥ fun j => (z j : ℚ)) i = (w i : ℚ) at hi
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
  rw [mul_assoc, hi]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedLieQuotient
namespace OAI

section

namespace Erdos3

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem supportedQuotientBasis_projection_height (b : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (S : Set ι) (hI : I.toSubmodule = Submodule.span ℚ (b '' S))
    (i : ι) (j : {i // i ∉ S}) :
    RationalHeightLE ((supportedQuotientBasis b I.toSubmodule S hI).repr
      (lieQuotientMap I (b i)) j) 1 := by
  change RationalHeightLE ((supportedQuotientBasis b I.toSubmodule S hI).repr
    (I.toSubmodule.mkQ (b i)) j) 1
  rw [supportedQuotientBasis_repr_mk]
  exact basis_repr_height_one b i j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AdaptedBasisGeometry
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

theorem exists_basis_change_grid_exp_bound (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hb : ∀ j i, RationalHeightLE (e.repr (b j) i) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hr : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ ∧
      bchSubgroupCoordinates b Γ ⊆ denominatorGrid N := by
  classical
  have hid : NilpotentLieBCHGroup.map (hnil := hnil) (hM := hnil)
      (LieHom.id : L →ₗ⁅ℚ⁆ L) = MonoidHom.id _ := by
    ext g
    rfl
  simpa only [hid, Subgroup.comap_id] using exists_bchSubgroup_comap_grid_exp_bound
    (hM := hnil) b e (LieHom.id : L →ₗ⁅ℚ⁆ L) Function.injective_id Γ hH hl
      (by intro i j; rw [LinearMap.toMatrix_apply]; exact hb j i)
      hinner houter hp hd hr hHp hlp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealPolynomialBCH
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem bch_coset_eq_of_coordinate_congruence (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (q l : ℕ) (hq : 0 < q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (a b : NilpotentLieBCHGroup L s hnil)
    (ha : e.equivFun a.coord ∈ denominatorGrid q) (hb : e.equivFun b.coord ∈ denominatorGrid q)
    (hba : e.equivFun b.coord - e.equivFun a.coord ∈ scaledIntegerGrid
      (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * q ^ s)) :
    (QuotientGroup.mk a : _ ⧸ Γ) = QuotientGroup.mk b := by
  apply QuotientGroup.eq.mpr
  apply (bchSubgroupCoordinates_repr e Γ _).mp
  apply hinner
  have h := rational_polynomial_family_eval_sub_mem_grid
    (conjugationCoordinatePolynomial e s) q s l hq (conjugationCoordinatePolynomial_degree e s)
    (differenceInput (e.equivFun a.coord) (e.equivFun b.coord))
    (differenceInput (e.equivFun a.coord) (e.equivFun a.coord))
    (differenceInput_mem_denominatorGrid _ _ q ha hb)
    (differenceInput_mem_denominatorGrid _ _ q ha ha)
    (differenceInput_sub_mem_scaledGrid _ _ _ hba)
  simp only [differenceCoordinate_same] at h
  simpa only [differenceCoordinate_eval, sub_zero,
    ← Basis.equivFun_apply] using h

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem polynomialBCHMap_coset_eq (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l r : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ) (hxy : ∀ j, (polynomialBCHPeriod e s l P : ℤ) ∣ x j - y j) :
    (QuotientGroup.mk (polynomialBCHMap e hnil P x) : _ ⧸ Γ) =
      QuotientGroup.mk (polynomialBCHMap e hnil P y) := by
  apply Eq.symm
  apply bch_coset_eq_of_coordinate_congruence e hnil Γ (polynomialFamilyDenominator P) l
    (polynomialFamilyDenominator_pos _) hinner
  · simpa only [polynomialBCHMap_coordinates] using polynomial_family_integer_values_grid P y
  · simpa only [polynomialBCHMap_coordinates] using polynomial_family_integer_values_grid P x
  · simp only [polynomialBCHMap_coordinates]
    exact polynomial_family_integer_congruence P r _ hdegree x y hxy

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealGradedSymbolPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

theorem eval_realificationLieEquiv_tmul {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (r : ℝ) (p : VectorPolynomial σ ℚ L) (x : σ → ℚ) :
    eval x (realificationLieEquiv (r ⊗ₜ[ℚ] p)) = r ⊗ₜ[ℚ] eval x p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
    rw [realificationLieEquiv_tmul_tmul, eval_tmul, eval_tmul, TensorProduct.tmul_smul]
  | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UniformPolynomialPeriodBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem polynomialBCHMap_uniform_coset_eq (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ) (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℤ) ∣ x j - y j) :
    (QuotientGroup.mk (polynomialBCHMap e hnil P x) : _ ⧸ Γ) =
      QuotientGroup.mk (polynomialBCHMap e hnil P y) := by
  apply polynomialBCHMap_coset_eq e hnil Γ l r P hdegree hinner x y
  intro j
  exact (Int.natCast_dvd_natCast.mpr (polynomialBCHPeriod_dvd_uniform e s r l q P hdegree hden)).trans (hxy j)

theorem polynomialBCHMap_uniform_inverse_coset_eq (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ) (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℤ) ∣ x j - y j) :
    (QuotientGroup.mk (polynomialBCHMap e hnil P x)⁻¹ : _ ⧸ Γ) =
      QuotientGroup.mk (polynomialBCHMap e hnil P y)⁻¹ := by
  have hinv (z : σ → ℤ) : polynomialBCHMap e hnil (fun i => -(P i)) z =
      (polynomialBCHMap e hnil P z)⁻¹ := by
    apply NilpotentLieBCHGroup.ext
    change e.equivFun.symm (fun i => eval (fun j => (z j : ℚ)) (-(P i))) =
      -(e.equivFun.symm (fun i => eval (fun j => (z j : ℚ)) (P i)))
    simp only [map_neg, ← Pi.neg_def]
  have h := polynomialBCHMap_uniform_coset_eq e hnil Γ r l q (fun i => -(P i))
    (fun i => by simpa only [totalDegree_neg] using hdegree i)
    (fun i α => by simpa only [coeff_neg, Rat.neg_den] using hden i α)
    hinner x y hxy
  simpa only [hinv] using h

end Erdos3

end

end OAI
end


