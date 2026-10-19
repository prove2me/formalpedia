-- Prove2me | Definitions.Def_OAIE3v2B170
-- name    : OAIE3v2B170
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:35:49.591611+00:00
-- url     : https://prove2.me/theorems/4e77003f-1f72-46bf-a8f1-563e5f0ca77a
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 172 of 311
-- statement:
--   Definitions bundle 172 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152`, `OAIE3v2B156`, `OAIE3v2B157` of this split.
--
--   Modules: `Estimates/CommonRefilteredFactorization.lean`, `Estimates/ComparisonAmbient.lean`, `Estimates/ControlledComparisonModel.lean`, `Estimates/NativeBinaryAssignments.lean`, `Estimates/NativeDilationDescent.lean`, `Estimates/NativeGlobalErrorSplitting.lean`, `Estimates/NativeMultilinearityCorrelation.lean`, `Estimates/NativeResidualMultiplier.lean`, `Estimates/PrescribedInvariantUnit.lean`, `Estimates/SourceUnitCover.lean`, `Estimates/SquarefreeRealAction.lean`, `Estimates/TensorSquarePairComparison.lean`, `Estimates/TwoDownsetPrecision.lean`, `Geometry/MixedEvaluationCoordinates.lean`, `Geometry/MixedShiftCoordinate.lean`, `Geometry/NativeEquivalenceCoordinateMaps.lean`, `Geometry/NativeTripleObservableMetric.lean`, `Geometry/SquarefreeActionMetric.lean`, `Lattices/MixedTranslationAffineInput.lean`, `Linear/NativeDilationPairProjections.lean`, `Linear/NativeTripleProjections.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152
import Definitions.Def_OAIE3v2B156
import Definitions.Def_OAIE3v2B157

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeRealAction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_comparison_layer_basis_height {p : ℝ} (hM : M.ComplexityLE p) (n : ℕ) :
    ∃ b : Basis (Fin (finrank ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n))) ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n),
      ∀ j k, RationalHeightLE
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (b j).val k)
        (comparisonBasisHeight bound p) := by
  classical
  let π := fun i : ReplicatedIndex bound => i.1
  let A := M.filtration.SquarefreeAlgebra π
  let e := D.basis.prod (M.squarefreeFinBasis p)
  let U := M.filtration.comparisonLayer π n
  let S : Set (L × A) := {z | z ∈ U ∧ ∀ k,
    RationalHeightLE (e.repr z k) (comparisonBasisHeight bound p)}
  have hpos := comparisonBasisHeight_pos bound p
  have hspan : Submodule.span ℚ S = U := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (fun z hz => hz.1)
    · apply M.filtration.comparisonLayer_le_of_generators π n
      · intro x hx
        obtain ⟨b, hb⟩ : ∃ b : Basis
            (Fin (finrank ℚ (M.filtration.ordinary.layer (n + 1)))) ℚ
            (M.filtration.ordinary.layer (n + 1)),
            ∀ j k, rationalLogHeight (D.basis.repr (b j).val k) ≤ p := by
          rw [M.ordinary]
          exact D.exists_positive_layer_basis (n + 1) (by omega) hM.1
        let f := (LinearMap.inl ℚ L A).comp (M.filtration.ordinary.layer (n + 1)).subtype
        apply map_mem_submodule_of_basis b f (Submodule.span ℚ S) _ ⟨x, hx⟩
        intro j
        apply Submodule.subset_span
        refine ⟨?_, ?_⟩
        · exact (le_sup_left : M.filtration.comparisonProductLayer π (n + 1) ≤ U)
            ⟨(b j).property, Submodule.zero_mem _⟩
        · intro k
          cases k with
          | inl k =>
              exact (rationalHeightLE_ceil_exp (hb j k)).mono
                (comparisonBasisHeight_ge_ceil bound p)
          | inr k =>
              change RationalHeightLE ((M.squarefreeFinBasis p).repr 0 k) _
              simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hpos
      · intro y hy
        let b := M.filtration.squarefreeDegreeBasis π (M.squarefreeCoefficientBasis p) (n + 1)
        let f := (LinearMap.inr ℚ L A).comp (M.filtration.squarefreeDegreeLayer π (n + 1)).subtype
        apply map_mem_submodule_of_basis b f (Submodule.span ℚ S) _ ⟨y, hy⟩
        intro j
        apply Submodule.subset_span
        refine ⟨?_, ?_⟩
        · exact (le_sup_left : M.filtration.comparisonProductLayer π (n + 1) ≤ U)
            ⟨Submodule.zero_mem _, (b j).property⟩
        · intro k
          cases k with
          | inl k =>
              change RationalHeightLE (D.basis.repr 0 k) _
              simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hpos
          | inr k =>
              exact (M.squarefreeFinBasis_degree_height p (n + 1) j k).mono hpos
      · intro a ha hab hn x
        apply map_mem_submodule_of_basis (M.comparisonLayerBasis p a)
          (M.filtration.comparisonGraph π a ha) (Submodule.span ℚ S) _ x
        intro j
        exact Submodule.subset_span
          ⟨M.filtration.comparisonGraph_mem_layer π n a ha hn _,
            M.comparisonGraph_chosen_height hM a ha hab j⟩
  have hrange : Set.range (Subtype.val : S → L × A) = S := by
    ext z
    simp only [Subtype.range_coe_subtype, Set.mem_ofPred_eq]
  exact exists_bounded_submodule_basis_from_spanning e U
    (Subtype.val : S → L × A) (by rw [hrange]; exact hspan) (fun z => z.property.2)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquarefreeActionMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

variable (p : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]

theorem squarefreeSpacePermute_lipschitz {q : ℝ} (hq : 0 ≤ q)
    (hE : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q)
    (e : ReplicatedPermutation bound) :
    letI := (M.squarefreeModel p B hB hstable).metricSpace
    LipschitzWith ⟨Real.exp ((q + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.squarefreeSpacePermute p B hB hstable e) := by
  let := (M.squarefreeModel p B hB hstable).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le (M.squarefreeModel p B hB hstable) (M.squarefreeModel p B hB hstable)
        (M.filtration.replicatedLiePermute e).toLieHom
        (fun g hg => (M.squarefreeLattice_permute p B hstable (replicatedPermutation bound e)
          (replicatedPermutation_block bound e) g).mpr hg)
        hq hE hE (M.squarefreePermute_coordinate_height p e hq) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComparisonAmbient
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonAmbient (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :=
  optionProduct (D.raiseStep (Nat.le_max_left s (Fintype.card (ReplicatedIndex bound))))
    (fun _ : PUnit.{1} => (M.squarefreeModel p B hB hstable).raiseStep
      (Nat.le_max_right s (Fintype.card (ReplicatedIndex bound))))

theorem comparisonAmbient_geometry {p q : ℝ} (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) (hD : D.GeometryComplexityLE p)
    (hE : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q) :
    (M.comparisonAmbient p B hB hstable).GeometryComplexityLE ((p + q + 4) ^ 2) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hE.1
  have h := optionProduct_geometry
    (D.raiseStep (Nat.le_max_left s (Fintype.card (ReplicatedIndex bound))))
    (fun _ : PUnit.{1} => (M.squarefreeModel p B hB hstable).raiseStep
      (Nat.le_max_right s (Fintype.card (ReplicatedIndex bound))))
    (p := p + q + 1) (by linarith)
    (by simpa only [Fintype.card_punit, Nat.cast_one] using
      (show (1 : ℝ) ≤ p + q + 1 by linarith))
    ((D.raiseStep_geometry _ hD).mono _ (by linarith))
    (fun _ => ((M.squarefreeModel p B hB hstable).raiseStep_geometry _ hE).mono _ (by linarith))
  simpa only [comparisonAmbient, show p + q + 1 + 3 = p + q + 4 by ring] using h

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledComparisonModel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L K : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
  {s t d r : ℕ} (D : RationalFilteredNilmanifold L s d)

theorem exists_model_of_bounded_embedding (F : NilpotentLieFiltration K t)
    (b : Basis (Fin r) ℚ K) (φ : K →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ j k, RationalHeightLE (D.basis.repr (φ (b j)) k) H)
    (hlayers : ∀ n : Fin (t + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, RationalHeightLE (D.basis.repr (φ (a j : K)) k) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hgrid : (D.grid : ℝ) ≤ Real.exp p) :
    ∃ E : RationalFilteredNilmanifold K t r,
      E.filtration = F ∧ E.basis = b ∧
      E.lattice = D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps φ) ∧
      E.GeometryComplexityLE ((p + 2) ^ 11) := by
  classical
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hd
  have hr' : (Fintype.card (Fin r) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hr
  have hmatrix : ∀ i j, RationalHeightLE (LinearMap.toMatrix b D.basis φ.toLinearMap i j) H := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact hb j i
  obtain ⟨N, hN, hNb, hin, hout⟩ := exists_bchSubgroup_comap_grid_of_steps
    (hM := F.lowerCentralSeries_eq_bot) b D.basis φ hφ D.lattice hH D.grid_pos
    hmatrix D.inner_grid D.outer_grid hp hd' hr' hHp hgrid
  obtain ⟨_, _, _, hbracket⟩ := exists_bounded_lie_embedding_retraction b D.basis φ hφ hH hc hmatrix
  have hbracketBudget := rationalLieStructureHeight_inverse_budget d r H hp hd hr hHp
  choose a ha using hlayers
  have hLayer (n : Fin (t + 1)) (j) (k) :
      rationalLogHeight (b.repr (a n j : K) k) ≤ (p + 2) ^ 8 := by
    apply rationalLogHeight_le_of_height
      (embedding_basis_coordinate_height b D.basis φ.toLinearMap hφ hH
        (fun i j => hb j i) (a n j : K) (ha n j) k)
    simpa only [Fintype.card_fin] using
      embedding_coordinate_height_budget d r H H hp hd hr hHp hHp
  let E : RationalFilteredNilmanifold K t r :=
    { filtration := F
      basis := b
      layerBasis := a
      lattice := D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps φ)
      grid := N
      grid_pos := hN
      inner_grid := hin
      outer_grid := hout }
  have hp1 : 1 ≤ p + 2 := by linarith
  have h9 : (p + 2) ^ 9 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have h8 : (p + 2) ^ 8 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  refine ⟨E, rfl, rfl, rfl, hr.trans (le_power_budget hp (by decide)),
    hNb.trans (Real.exp_le_exp.mpr h9), ?_, ?_⟩
  · intro i j k
    apply rationalLogHeight_le_of_height (hbracket i j k)
    simpa only [Fintype.card_fin] using hbracketBudget
  · exact fun n j k => (hLayer n j k).trans h8

theorem exists_model_of_embedding_logHeight (F : NilpotentLieFiltration K t)
    (b : Basis (Fin r) ℚ K) (φ : K →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    {p : ℝ} (hD : D.GeometryComplexityLE p)
    (hb : ∀ j k, rationalLogHeight (D.basis.repr (φ (b j)) k) ≤ p)
    (hlayers : ∀ n : Fin (t + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight (D.basis.repr (φ (a j : K)) k) ≤ p) :
    ∃ E : RationalFilteredNilmanifold K t r,
      E.filtration = F ∧ E.basis = b ∧
      E.lattice = D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps φ) ∧
      E.GeometryComplexityLE ((p + 3) ^ 11) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  have hr : (r : ℝ) ≤ p := (Nat.cast_le.mpr (D.embedding_basis_card_le b φ hφ)).trans hD.1
  have hLayer : ∀ n : Fin (t + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, RationalHeightLE (D.basis.repr (φ (a j : K)) k) ⌈Real.exp p⌉₊ := by
    intro n
    obtain ⟨a, ha⟩ := hlayers n
    exact ⟨a, fun j k => rationalHeightLE_ceil_exp (ha j k)⟩
  obtain ⟨E, hEF, hEb, hEL, hE⟩ := D.exists_model_of_bounded_embedding F b φ hφ
    (one_le_ceil_exp p) (fun j k => rationalHeightLE_ceil_exp (hb j k)) hLayer
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (by linarith : 0 ≤ p + 1) (hD.1.trans (by linarith)) (hr.trans (by linarith))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  refine ⟨E, hEF, hEb, hEL, ?_⟩
  convert hE using 1
  ring

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_dilationPair_layer_basis (q : ℚ) (n : ℕ) (hn : 1 ≤ n)
    {p : ℝ} (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.dilationPairLayer q n))) ℚ
        (D.filtration.dilationPairLayer q n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j).val.1 k) ≤ (n + 1 : ℝ) * (p + 1) ∧
        rationalLogHeight (D.basis.repr (b j).val.2 k) ≤ (n + 1 : ℝ) * (p + 1) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  obtain ⟨a, ha⟩ := D.exists_positive_layer_basis (n + 1) (by omega) hD
  obtain ⟨b, hb⟩ := D.exists_positive_layer_basis n hn hD
  obtain ⟨c, hc⟩ := exists_scaledPair_basis_height D.basis
    (D.filtration.layer n) (D.filtration.layer (n + 1)) (D.filtration.antitone (Nat.le_succ n))
    a b (q ^ n) hH (one_le_pow₀ hH) ((rationalHeightLE_ceil_exp hq).pow n)
    (fun j k => rationalHeightLE_ceil_exp (ha j k))
    (fun j k => rationalHeightLE_ceil_exp (hb j k))
  have hbound : ((H * H ^ n : ℕ) : ℝ) ≤ Real.exp ((n + 1 : ℝ) * (p + 1)) := by
    rw [← pow_succ']
    simpa only [Nat.cast_add, Nat.cast_one] using ceil_exp_power_le_exp hp (n + 1)
  exact ⟨c, fun j k => ⟨rationalLogHeight_le_of_height (hc j k).1 hbound,
    rationalLogHeight_le_of_height (hc j k).2 hbound⟩⟩

theorem exists_dilationPair_filtration_basis (q : ℚ) (n : ℕ) (hn : 1 ≤ n)
    {p : ℝ} (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ ((D.filtration.dilationPairFiltration q).layer n))) ℚ
        ((D.filtration.dilationPairFiltration q).layer n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j).val.val.1 k) ≤ (n + 1 : ℝ) * (p + 1) ∧
        rationalLogHeight (D.basis.repr (b j).val.val.2 k) ≤ (n + 1 : ℝ) * (p + 1) := by
  obtain ⟨b, hb⟩ := D.exists_dilationPair_layer_basis q n hn hD hq
  let e := D.filtration.dilationPairFiltrationLayerEquiv q n hn
  let c := (b.map e.symm).reindex (finCongr e.finrank_eq.symm)
  have hval (j) :
      ((c j : D.filtration.dilationPairSubalgebra q) : L × L) =
        (b ((finCongr e.finrank_eq.symm).symm j)).val := by
    simp only [c, Basis.reindex_apply, Basis.map_apply, e,
      NilpotentLieFiltration.dilationPairFiltrationLayerEquiv]
    rfl
  refine ⟨c, fun j k => ?_⟩
  rw [hval]
  exact hb _ k

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem pairToPi_injective : Function.Injective (pairToPi (L := L)) := by
  intro x y h
  exact Prod.ext (congrFun h 0) (congrFun h 1)

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dilationPairToPi_injective (q : ℚ) : Function.Injective (F.dilationPairToPi q) :=
  fun _ _ h => Subtype.ext (pairToPi_injective h)

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {s d : ℕ} (D : RationalFilteredNilmanifold L s d)

theorem pair_product_basis_logHeight (x : L × L) {p : ℝ}
    (hx : ∀ k, rationalLogHeight (D.basis.repr x.1 k) ≤ p ∧
      rationalLogHeight (D.basis.repr x.2 k) ≤ p)
    (k : Fin (Fintype.card (Σ _ : Fin 2, Fin d))) :
    rationalLogHeight ((pi (fun _ : Fin 2 => D)).basis.repr (pairToPi x) k) ≤ p := by
  have h (j : Fin 2) (l : Fin d) : rationalLogHeight (D.basis.repr (pairToPi x j) l) ≤ p := by
    fin_cases j
    · exact (hx l).1
    · exact (hx l).2
  rw [productFinBasis_repr]
  exact h _ _

end RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

noncomputable def dilationPairLattice (q : ℚ) : Subgroup (D.filtration.dilationPairFiltration q).Group :=
  (pi (fun _ : Fin 2 => D)).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps (D.filtration.dilationPairToPi q))

theorem dilationPairLattice_mem (q : ℚ) (x : (D.filtration.dilationPairFiltration q).Group) :
    x ∈ D.dilationPairLattice q ↔
      (⟨x.coord.val.1⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨x.coord.val.2⟩ : D.filtration.Group) ∈ D.lattice := by
  change (NilpotentLieBCHGroup.mapOfSteps (D.filtration.dilationPairToPi q) x) ∈
    piBCHSubgroup (fun _ : Fin 2 => D.filtration) (fun _ : Fin 2 => D.lattice) ↔ _
  rw [mem_piBCHSubgroup]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · intro h i
    fin_cases i
    · exact h.1
    · exact h.2

theorem exists_dilationPair_model (q : ℚ) {p : ℝ}
    (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ E : RationalFilteredNilmanifold (D.filtration.dilationPairSubalgebra q) s
        (finrank ℚ (D.filtration.dilationPairSubalgebra q)),
      E.filtration = D.filtration.dilationPairFiltration q ∧
      E.lattice = D.dilationPairLattice q ∧
      E.GeometryComplexityLE (dilationPairGeometryBudget s p) ∧
      finrank ℚ (D.filtration.dilationPairSubalgebra q) ≤ 2 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ 2 * (p + 1) ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2 k) ≤ 2 * (p + 1) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  let P := pi (fun _ : Fin 2 => D)
  let K := D.filtration.dilationPairSubalgebra q
  let F := D.filtration.dilationPairFiltration q
  let φ := D.filtration.dilationPairToPi q
  let C : ℝ := (s + 2) * (p + 1)
  let R : ℝ := (p + 4) ^ 2 + C + 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCR : C ≤ R := by dsimp [R]; nlinarith only [sq_nonneg (p + 4)]
  have hP : P.GeometryComplexityLE R := by
    have hh := pi_geometry (fun _ : Fin 2 => D) (by linarith : 0 ≤ p + 2)
      (by simpa using (show (2 : ℝ) ≤ p + 2 by linarith))
      (fun _ => hD.mono D (by linarith : p ≤ p + 2))
    have hgeom : P.GeometryComplexityLE ((p + 4) ^ 2) := by
      simpa only [show p + 2 + 2 = p + 4 by ring] using hh
    exact hgeom.mono P (by dsimp [R]; linarith)
  obtain ⟨b, hb⟩ := D.exists_dilationPair_layer_basis q 1 (by decide) hD hq
  let bK : Basis (Fin (finrank ℚ K)) ℚ K := b
  have hbase : 2 * (p + 1) ≤ C := by
    apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ p + 1)
    exact le_add_of_nonneg_left (Nat.cast_nonneg s)
  have hbK (j) (k) : rationalLogHeight (P.basis.repr (φ (bK j)) k) ≤ R := by
    apply D.pair_product_basis_logHeight
    intro l
    have hh := hb j l
    norm_num only [Nat.cast_one, one_add_one_eq_two] at hh
    exact ⟨hh.1.trans (hbase.trans hCR), hh.2.trans (hbase.trans hCR)⟩
  have hlayers (n : Fin (s + 1)) :
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight (P.basis.repr (φ (a j)) k) ≤ R := by
    obtain ⟨a, ha⟩ := D.exists_dilationPair_filtration_basis q (n.val + 1) (by omega) hD hq
    refine ⟨a, fun j k => ?_⟩
    have hn : ((n.val + 1 : ℕ) + 1 : ℝ) ≤ (s + 2 : ℝ) := by
      exact_mod_cast (show n.val + 1 + 1 ≤ s + 2 by omega)
    have hbound := mul_le_mul_of_nonneg_right hn (show 0 ≤ p + 1 by linarith)
    apply D.pair_product_basis_logHeight
    intro l
    exact ⟨(ha j l).1.trans (hbound.trans hCR), (ha j l).2.trans (hbound.trans hCR)⟩
  have hφ := D.filtration.dilationPairToPi_injective q
  obtain ⟨E, hEF, hEb, hEL, hE⟩ := P.exists_model_of_embedding_logHeight F bK φ hφ hP hbK hlayers
  have hdim : finrank ℚ K ≤ 2 * d := by
    have hh := P.embedding_basis_card_le bK φ hφ
    simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] using hh
  refine ⟨E, hEF, hEL, ?_, hdim, ?_⟩
  · simpa only [R, C, dilationPairGeometryBudget, add_assoc,
      show (3 : ℝ) + 3 = 6 by norm_num] using hE
  · intro j k
    rw [hEb]
    have hh := hb j k
    norm_num only [Nat.cast_one, one_add_one_eq_two] at hh
    exact hh

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_dilationPair_model_of_eq (F : NilpotentLieFiltration L s)
    (hF : F = D.filtration) (q : ℚ) {p : ℝ}
    (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ E : RationalFilteredNilmanifold (F.dilationPairSubalgebra q) s
        (finrank ℚ (F.dilationPairSubalgebra q)),
      E.filtration = F.dilationPairFiltration q ∧
      E.lattice = (pi (fun _ : Fin 2 => D)).lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps (F.dilationPairToPi q)) ∧
      E.GeometryComplexityLE (dilationPairGeometryBudget s p) ∧
      finrank ℚ (F.dilationPairSubalgebra q) ≤ 2 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ 2 * (p + 1) ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2 k) ≤ 2 * (p + 1) := by
  subst F
  exact D.exists_dilationPair_model q hD hq

namespace MultidegreeStructure

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ}
  {D : RationalFilteredNilmanifold L s d} (M : D.MultidegreeStructure bound)

noncomputable def dilationPairLattice (q : ℚ) :
    Subgroup (M.filtration.ordinary.dilationPairFiltration q).Group :=
  (pi (fun _ : Fin 2 => D)).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps (M.filtration.ordinary.dilationPairToPi q))

theorem dilationPairLattice_mem (q : ℚ)
    (x : (M.filtration.ordinary.dilationPairFiltration q).Group) :
    x ∈ M.dilationPairLattice q ↔
      (⟨x.coord.val.1⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨x.coord.val.2⟩ : D.filtration.Group) ∈ D.lattice := by
  change (NilpotentLieBCHGroup.mapOfSteps (M.filtration.ordinary.dilationPairToPi q) x) ∈
    piBCHSubgroup (fun _ : Fin 2 => D.filtration) (fun _ : Fin 2 => D.lattice) ↔ _
  rw [mem_piBCHSubgroup]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2

theorem exists_dilationPair_model (q : ℚ) {p : ℝ}
    (hM : M.ComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s
        (finrank ℚ (M.filtration.ordinary.dilationPairSubalgebra q)),
      E.filtration = M.filtration.ordinary.dilationPairFiltration q ∧
      E.lattice = M.dilationPairLattice q ∧
      E.GeometryComplexityLE (dilationPairGeometryBudget s p) ∧
      finrank ℚ (M.filtration.ordinary.dilationPairSubalgebra q) ≤ 2 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ 2 * (p + 1) ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2 k) ≤ 2 * (p + 1) :=
  D.exists_dilationPair_model_of_eq M.filtration.ordinary M.ordinary q hM.1 hq

end MultidegreeStructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_comparison_layer_basis {p : ℝ} (hM : M.ComplexityLE p) (n : ℕ) :
    ∃ b : Basis (Fin (finrank ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n))) ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n),
      ∀ j k, rationalLogHeight
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (b j).val k) ≤
        comparisonBasisBudget (∑ i, bound i) p := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  obtain ⟨b, hb⟩ := M.exists_comparison_layer_basis_height hM n
  exact ⟨b, fun j k => rationalLogHeight_le_of_height (hb j k)
    (comparisonBasisHeight_le_exp bound hp)⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_coordinate_active_basis (i : σ) (hi : 1 ≤ bound i)
    (n : Fin (s + 1)) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.coordinateActiveLayer i (n.val + 1)))) ℚ
        (M.filtration.coordinateActiveLayer i (n.val + 1)),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 2 := by
  have hsingle : Pi.single i 1 ≤ bound := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Pi.single_eq_same] using hi
    · simpa only [Pi.single_eq_of_ne hji] using Nat.zero_le (bound j)
  obtain ⟨a, ha⟩ := M.exists_layer_basis (Pi.single i 1) hsingle hM
  obtain ⟨b, hb⟩ := M.exists_ordinary_layer_basis n hM
  exact exists_binary_intersection_basis_logHeight D.basis
    (M.filtration.layerIdeal (Pi.single i 1)).toLieSubalgebra
    (M.filtration.ordinary.layerIdeal (n.val + 1)).toLieSubalgebra a b
    ((Nat.cast_nonneg d).trans hM.1.1)
    (by simpa only [Fintype.card_fin] using hM.1.1) ha hb

theorem exists_additiveTriple_layer_basis_logHeight (i : σ) (hi : 1 ≤ bound i)
    (c : σ → ℕ) (n : Fin (s + 1)) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ q : Basis (Fin (finrank ℚ (M.filtration.additiveTripleLayer i c (n.val + 1)))) ℚ
        (M.filtration.additiveTripleLayer i c (n.val + 1)),
      ∀ j k, rationalLogHeight (D.basis.repr (q j).val.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (q j).val.2.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (q j).val.2.2 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let P := ((p + 4) ^ 2 + 2) ^ 63 + 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpP : p + 1 ≤ P := add_le_add (le_triple_basis_budget hp) (by norm_num)
  obtain ⟨a, ha⟩ := M.exists_weighted_layer_basis c (n.val + 1)
    (fun a j k => rationalHeightLE_ceil_exp (hM.2 a j k))
  obtain ⟨b, hb⟩ := M.exists_coordinate_active_basis i hi n hM
  have ha' (j) (k) : RationalHeightLE (D.basis.repr (a j : L) k) ⌈Real.exp P⌉₊ :=
    rationalHeightLE_ceil_exp
      ((rationalLogHeight_le_of_height (ha j k) (ceil_exp_le_exp_add_one hp)).trans hpP)
  obtain ⟨q, hq⟩ := M.filtration.exists_additiveTriple_layer_basis D.basis i c (n.val + 1)
    a b (one_le_ceil_exp P) ha' (fun j k => rationalHeightLE_ceil_exp (hb j k))
  refine ⟨q, fun j k => ?_⟩
  have hceil : (⌈Real.exp P⌉₊ : ℝ) ≤ Real.exp (((p + 4) ^ 2 + 2) ^ 63 + 3) := by
    simpa only [P, add_assoc, show (2 : ℝ) + 1 = 3 by norm_num] using ceil_exp_le_exp_add_one hP
  exact ⟨rationalLogHeight_le_of_height (hq j k).1 hceil,
    rationalLogHeight_le_of_height (hq j k).2.1 hceil,
    rationalLogHeight_le_of_height (hq j k).2.2 hceil⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def additiveTripleLattice (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    Subgroup (M.filtration.additiveTripleFiltration i hi c hc).Group :=
  (pi (fun _ : Fin 3 => D)).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps (M.filtration.additiveTripleToPi i hi c hc))

theorem additiveTripleLattice_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (x : (M.filtration.additiveTripleFiltration i hi c hc).Group) :
    x ∈ M.additiveTripleLattice i hi c hc ↔
      (⟨x.coord.val.1⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨x.coord.val.2.1⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨x.coord.val.2.2⟩ : D.filtration.Group) ∈ D.lattice := by
  change (NilpotentLieBCHGroup.mapOfSteps (M.filtration.additiveTripleToPi i hi c hc) x) ∈
    piBCHSubgroup (fun _ : Fin 3 => D.filtration) (fun _ : Fin 3 => D.lattice) ↔ _
  rw [mem_piBCHSubgroup]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2.1
    · exact h.2.2

theorem exists_additiveTriple_filtration_basis_logHeight (i : σ) (hi : bound i = 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : Fin (s + 1))
    {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ a : Basis (Fin (finrank ℚ
        ((M.filtration.additiveTripleFiltration i hi.le c hc).layer (n.val + 1)))) ℚ
        ((M.filtration.additiveTripleFiltration i hi.le c hc).layer (n.val + 1)),
      ∀ j k, rationalLogHeight ((pi (fun _ : Fin 3 => D)).basis.repr
        (M.filtration.additiveTripleToPi i hi.le c hc (a j)) k) ≤
          ((p + 4) ^ 2 + 2) ^ 63 + 3 := by
  obtain ⟨q, hq⟩ := M.exists_additiveTriple_layer_basis_logHeight i hi.ge c n hM
  let e := M.filtration.additiveTripleFiltrationLayerEquiv i hi.le c hc
    (n.val + 1) (Nat.le_add_left 1 _)
  let a := (q.map e.symm).reindex (finCongr e.finrank_eq.symm)
  have hval (j) : ((a j : M.filtration.additiveTripleSubalgebra i hi.le c hc) : L × L × L) =
      (q ((finCongr e.finrank_eq.symm).symm j)).val := by
    simp only [a, Basis.reindex_apply, Basis.map_apply, e,
      MultidegreeLieFiltration.additiveTripleFiltrationLayerEquiv]
    rfl
  refine ⟨a, fun j k => ?_⟩
  change rationalLogHeight ((pi (fun _ : Fin 3 => D)).basis.repr
    (tripleToPi ((a j : M.filtration.additiveTripleSubalgebra i hi.le c hc) : L × L × L)) k) ≤ _
  rw [hval]
  exact D.triple_product_basis_logHeight _ (hq _) k

theorem exists_additiveTriple_model (i : σ) (hi : bound i = 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le c hc) s
        (finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le c hc)),
      E.filtration = M.filtration.additiveTripleFiltration i hi.le c hc ∧
      E.lattice = M.additiveTripleLattice i hi.le c hc ∧
      E.GeometryComplexityLE (additiveTripleGeometryBudget p) ∧
      finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le c hc) ≤ 3 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2.1 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2.2 k) ≤ ((p + 4) ^ 2 + 2) ^ 63 + 3 := by
  let P := pi (fun _ : Fin 3 => D)
  let K := M.filtration.additiveTripleSubalgebra i hi.le c hc
  let F := M.filtration.additiveTripleFiltration i hi.le c hc
  let φ := M.filtration.additiveTripleToPi i hi.le c hc
  let C := ((p + 4) ^ 2 + 2) ^ 63
  let q := (p + 6) ^ 2 + C + 3
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCq : C + 3 ≤ q := by
    have h : C + 3 ≤ (p + 6) ^ 2 + (C + 3) := le_add_of_nonneg_left (sq_nonneg (p + 6))
    simpa only [q, add_assoc] using h
  have hP : P.GeometryComplexityLE q := by
    have hh := pi_geometry (fun _ : Fin 3 => D) (by linarith : 0 ≤ p + 3)
      (by simpa using (show (3 : ℝ) ≤ p + 3 by linarith))
      (fun _ => hM.1.mono D (by linarith : p ≤ p + 3))
    apply hh.mono P
    have hsq : (p + 3 + 2) ^ 2 ≤ (p + 6) ^ 2 := by nlinarith only [hp]
    exact hsq.trans ((le_add_of_nonneg_right hC).trans (le_add_of_nonneg_right (by norm_num)))
  obtain ⟨b, hb⟩ := M.exists_additiveTriple_layer_basis_logHeight i hi.ge c
    (⟨0, Nat.succ_pos s⟩ : Fin (s + 1)) hM
  let bK : Basis (Fin (finrank ℚ K)) ℚ K := b
  have hb' (j) (k) : rationalLogHeight (P.basis.repr (φ (bK j)) k) ≤ q :=
    (D.triple_product_basis_logHeight _ (hb j) k).trans hCq
  have hlayers (n : Fin (s + 1)) :
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight (P.basis.repr (φ (a j)) k) ≤ q := by
    obtain ⟨a, ha⟩ := M.exists_additiveTriple_filtration_basis_logHeight i hi c hc n hM
    exact ⟨a, fun j k => (ha j k).trans hCq⟩
  have hφ := M.filtration.additiveTripleToPi_injective i hi.le c hc
  obtain ⟨E, hEF, hEb, hEL, hE⟩ := P.exists_model_of_embedding_logHeight F bK φ hφ hP hb' hlayers
  have hdim : finrank ℚ K ≤ 3 * d := by
    have hh := P.embedding_basis_card_le bK φ hφ
    simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] using hh
  refine ⟨E, hEF, hEL, ?_, hdim, ?_⟩
  · simpa only [q, C, additiveTripleGeometryBudget, add_assoc, show (3 : ℝ) + 3 = 6 by norm_num] using hE
  · intro j k
    rw [hEb]
    exact hb j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SourceUnitCover
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators NNReal TensorProduct

namespace RationalFilteredNilmanifold.UnitVerticalObservable

variable {Γ I L : Type*} [Group Γ] [Fintype Γ] [Fintype I]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  [MulAction Γ D.Space]

theorem exists_invariant (V : D.UnitVerticalObservable T I p) (hp : 0 ≤ p)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp p) (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp p)
    (hact : letI := D.metricSpace; ∀ a : Γ, LipschitzWith A (fun x : D.Space => a • x))
    (hcomm : ∀ (a : Γ) (z : D.RealGroup), z ∈ T → ∀ x : D.Space,
      a • (z • x) = z • (a • x)) :
    ∃ W : D.UnitVerticalObservable T (SymmetricEvaluationIndex (Fintype.card Γ) I)
        (invariantVerticalBudget (Fintype.card Γ) p),
      W.frequency = Fintype.card Γ • V.frequency ∧
      (∀ (a : Γ) k x, W.observable k (a • x) = W.observable k x) ∧
      (Fintype.card (SymmetricEvaluationIndex (Fintype.card Γ) I) : ℝ) ≤
        Real.exp (invariantVerticalBudget (Fintype.card Γ) p) := by
  let := D.metricSpace
  let m := Fintype.card Γ
  have hp2 : 0 ≤ 2 * p := by positivity
  have hbudget : 0 ≤ symmetricUnitBudget m (2 * p) := by
    unfold symmetricUnitBudget
    positivity
  have hbase : symmetricUnitBudget m (2 * p) ≤ invariantVerticalBudget m p := by
    unfold invariantVerticalBudget
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hfreq : p + m + 1 ≤ invariantVerticalBudget m p := by
    unfold invariantVerticalBudget
    linarith
  have hIA : (Fintype.card I : ℝ) ≤ Real.exp (2 * p) :=
    hI.trans (Real.exp_le_exp.mpr (by linarith))
  have hKA : ((V.lipBound * A : ℝ≥0) : ℝ) ≤ Real.exp (2 * p) := by
    simpa only [NNReal.coe_mul, ← Real.exp_add, two_mul] using
      mul_le_mul V.lip_bound hA A.coe_nonneg (Real.exp_pos _).le
  obtain ⟨hcard, hLip⟩ := symmetricUnitBudget_bounds m (Fintype.card I) (V.lipBound * A) hp2 hIA hKA
  obtain ⟨g, hgunit, hgnorm, hglip, hginv, hgphase⟩ :=
    exists_invariant_unit_family (Γ := Γ) V.observable V.lipschitz V.unit hact
  refine ⟨{
    observable := g
    unit := hgunit
    norm := hgnorm
    lipBound := symmetricUnitFamilyLip m (Fintype.card I) (V.lipBound * A)
    lip_bound := hLip.trans (Real.exp_le_exp.mpr hbase)
    lipschitz := hglip
    frequency := m • V.frequency
    height := ?_
    vertical := ?_
    integral := ?_
  }, rfl, hginv, ?_⟩
  · intro i
    exact (show rationalLogHeight ((m • V.frequency) (D.basis i)) ≤ p + m + 1 by
      simpa only [LinearMap.smul_apply, nsmul_eq_mul] using
        rationalLogHeight_nat_mul m (V.height i)).trans hfreq
  · intro k z hz x
    have h := hgphase (z • x) x
      (character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle))
      (norm_character _) (fun a j => by rw [hcomm a z hz, V.vertical j z hz]) k
    simpa only [realifyFunctional_nsmul, AddCircle.coe_nsmul, character_nsmul] using h
  · intro z hz hL
    obtain ⟨n, hn⟩ := V.integral z hz hL
    refine ⟨(m : ℤ) * n, ?_⟩
    rw [realifyFunctional_nsmul, hn]
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  · rw [symmetricEvaluationIndex_card]
    exact hcard.trans (Real.exp_le_exp.mpr hbase)

end RationalFilteredNilmanifold.UnitVerticalObservable

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
  (E : NativeIntegerVectorEquivalence s p chi eta)

theorem expansionIndex_card_bound {a b : ℝ}
    (hJ : (Fintype.card J : ℝ) ≤ Real.exp a)
    (hK : (Fintype.card K : ℝ) ≤ Real.exp b) :
    (Fintype.card E.ExpansionIndex : ℝ) ≤ Real.exp (a + b + p) := by
  classical
  simp only [ExpansionIndex, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
  calc
    (∑ j : J, ∑ k : K, ((E.selectedExpansion j k).count : ℝ)) ≤
        ∑ _j : J, ∑ _k : K, Real.exp p :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
        (E.selectedExpansion j k).count_bound
    _ = (Fintype.card J : ℝ) * ((Fintype.card K : ℝ) * Real.exp p) := by simp
    _ ≤ Real.exp a * (Real.exp b * Real.exp p) :=
      mul_le_mul hJ (mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _))
        (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (a + b + p) := by rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeDilationPairProjections
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem dilationPairProjection_lattice (q : ℚ) (j : Fin 2) :
    M.dilationPairLattice q ≤ D.lattice.comap
      (mapOfSteps (M.filtration.ordinary.dilationPairProjection q j)) := by
  intro x hx
  have h := (M.dilationPairLattice_mem q x).mp hx
  fin_cases j
  · exact h.1
  · exact h.2

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedInvariantUnit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_prescribed_scalar (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ f : D.Space → ℂ, (letI := D.metricSpace; LipschitzWith K f) ∧
        (∀ x, ‖f x‖ ≤ 2) ∧
        (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
          f (z • x) = logCharacter (realifyFunctional η) z * f x) ∧
        f (QuotientGroup.mk (1 : D.RealGroup)) = 1 := by
  obtain ⟨C, hC, hseed⟩ := exists_native_central_seed s
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  obtain ⟨K, hK, f, hf, hb, hcentral⟩ := hseed D hp hD η hη hint
  obtain ⟨g, hg, hgb, hvertical, hone⟩ :=
    D.exists_native_prescribed_projection hp hD η f hf hb hcentral
  exact ⟨K, hK, g, hg, hgb, hvertical, hone⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeEquivalenceCoordinateMaps
namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem of_coordinate_maps {σ I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    {s : ℕ} {p r : ℝ} {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g)
    (f' : K → (σ → ℤ) → ℂ) (g' : L → (σ → ℤ) → ℂ)
    (a : K → I) (b : L → J)
    (hf : ∀ k x, f' k x = f (a k) x) (hg : ∀ l x, g' l x = g (b l) x)
    (hK : (Fintype.card K : ℝ) ≤ Real.exp r) (hL : (Fintype.card L : ℝ) ≤ Real.exp r)
    (hpr : p ≤ r) : NativeIntegerVectorEquivalence s r f' g' := by
  refine ⟨hK, hL, fun k l => ?_⟩
  obtain ⟨R⟩ := E.expansion (a k) (b l)
  have heq : (fun x => f (a k) x * star (g (b l) x)) =
      (fun x => f' k x * star (g' l x)) := by
    funext x
    rw [hf, hg]
  exact ⟨heq ▸ R.mono hpr⟩

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def positivePolynomialBasis (p : ℝ) :
    Basis M.PositivePolynomialBasisIndex ℚ M.filtration.positivePolynomialAlgebra :=
  M.filtration.positivePolynomialBasis (M.positiveCoefficientBasis p)

theorem positivePolynomialBasisIndex_card_le (p : ℝ) :
    Fintype.card M.PositivePolynomialBasisIndex ≤ 2 ^ (∑ i, bound i) * d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  rw [← finrank_eq_card_basis (M.positivePolynomialBasis p)]
  simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
    M.filtration.positivePolynomial_finrank_le_total

omit [DecidableEq σ] in
theorem positivePolynomialBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p)
    (i j k : M.PositivePolynomialBasisIndex) :
    RationalHeightLE (lieStructureConstants (M.positivePolynomialBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  have h := M.filtration.positivePolynomialBasis_structure_height
    (M.positiveCoefficientBasis p) D.basis (one_le_ceil_exp p)
    (M.positiveCoefficientBasis_height hM)
    (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
    (fun a => by simpa only [Fintype.card_fin] using M.positiveCoefficientBasis_card_le a) i j k
  simpa only [positivePolynomialBasis, Fintype.card_fin] using h

omit [DecidableEq σ] in
theorem positivePolynomialBasis_evaluation_height {p : ℝ} (hM : M.ComplexityLE p)
    (i : M.PositivePolynomialBasisIndex) (k : Fin d) :
    RationalHeightLE (D.basis.repr
      (M.filtration.positivePolynomialEvaluation (M.positivePolynomialBasis p i)) k) ⌈Real.exp p⌉₊ := by
  change RationalHeightLE (D.basis.repr
    (M.filtration.positivePolynomialEvaluation
      (M.filtration.positivePolynomialBasis (M.positiveCoefficientBasis p) i)) k) _
  rw [M.filtration.positivePolynomialBasis_evaluation]
  exact M.positiveCoefficientBasis_height hM i.1 i.2 k

noncomputable def positivePolynomialFinBasis (p : ℝ) :
    Basis (Fin (Fintype.card M.PositivePolynomialBasisIndex)) ℚ M.filtration.positivePolynomialAlgebra :=
  (M.positivePolynomialBasis p).reindex (Fintype.equivFin M.PositivePolynomialBasisIndex)

theorem positivePolynomialFinBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p) (i j k) :
    RationalHeightLE (lieStructureConstants (M.positivePolynomialFinBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  rw [positivePolynomialFinBasis, lieStructureConstants_reindex]
  exact M.positivePolynomialBasis_structure_height hM _ _ _

theorem positivePolynomialFinBasis_multidegree_height (p : ℝ) (a : σ → ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialFinBasis p).repr
      (M.filtration.positivePolynomialMultidegreeBasis (M.positiveCoefficientBasis p) a j).val k) 1 := by
  rw [positivePolynomialFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialMultidegreeBasis_height (M.positiveCoefficientBasis p) a j _

theorem positivePolynomialFinBasis_degree_height (p : ℝ) (n : ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialFinBasis p).repr
      (M.filtration.positivePolynomialDegreeBasis (M.positiveCoefficientBasis p) n j).val k) 1 := by
  rw [positivePolynomialFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialDegreeBasis_height (M.positiveCoefficientBasis p) n j _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

noncomputable def positivePolynomialDownsetBasis (p : ℝ) :
    Basis (M.PositivePolynomialDownsetIndex J) ℚ
      (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ) :=
  M.filtration.positivePolynomialDownsetBasis (M.positiveCoefficientBasis p) J hJ

noncomputable def positivePolynomialDownsetFinBasis (p : ℝ) :
    Basis (Fin (Fintype.card (M.PositivePolynomialDownsetIndex J))) ℚ
      (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ) :=
  (M.positivePolynomialDownsetBasis J hJ p).reindex (Fintype.equivFin _)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

def PositivePolynomialGridStable (p : ℝ) (B : ℕ) : Prop :=
  ∀ x ∈ coordinateGridModule (M.positivePolynomialBasis p) B,
    ∀ y ∈ coordinateGridModule (M.positivePolynomialBasis p) B,
      lieBCH (∑ i, bound i) x y ∈ coordinateGridModule (M.positivePolynomialBasis p) B

noncomputable def positivePolynomialLattice (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    Subgroup M.filtration.positivePolynomialMultidegree.ordinary.Group :=
  coordinateGridBCHSubgroup (M.positivePolynomialBasis p) B
    M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot hstable

theorem positivePolynomialLattice_coordinates (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    bchSubgroupCoordinates (M.positivePolynomialBasis p) (M.positivePolynomialLattice p B hstable) =
      scaledIntegerGrid B := coordinateGridBCHSubgroup_coordinates _ _ _ hstable

noncomputable def positivePolynomialEvaluationDenominator (p : ℝ) : ℕ :=
  D.grid * matrixDenominator (LinearMap.toMatrix (M.positivePolynomialBasis p) D.basis
    M.filtration.positivePolynomialEvaluation.toLinearMap)

theorem positivePolynomialEvaluationDenominator_pos (p : ℝ) :
    0 < M.positivePolynomialEvaluationDenominator p :=
  Nat.mul_pos D.grid_pos (matrixDenominator_pos _)

theorem positivePolynomialLattice_maps (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B)
    (hdiv : M.positivePolynomialEvaluationDenominator p ∣ B) :
    M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) := by
  classical
  intro g hg
  apply (bchSubgroupCoordinates_repr (M.positivePolynomialBasis p)
    (D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) g).mp
  rw [bchSubgroupCoordinates_comap_of_steps (M.positivePolynomialBasis p) D.basis]
  apply D.inner_grid
  apply matrix_mulVec_fine_grid
  apply scaledIntegerGrid_subset_of_dvd hdiv
  rw [← M.positivePolynomialLattice_coordinates p B hstable]
  exact (bchSubgroupCoordinates_repr (M.positivePolynomialBasis p)
    (M.positivePolynomialLattice p B hstable) g).mpr hg

theorem exists_positivePolynomial_stable_grid {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ B : ℕ, 0 < B ∧ M.positivePolynomialEvaluationDenominator p ∣ B ∧
      B ≤ bchIntegralDenominatorBound (∑ i, bound i) *
        squarefreeStructureHeight d ⌈Real.exp p⌉₊ ^ (Fintype.card M.PositivePolynomialBasisIndex ^ 3) *
        M.positivePolynomialEvaluationDenominator p ∧ M.PositivePolynomialGridStable p B :=
  exists_bch_stable_integral_grid (M.positivePolynomialBasis p)
    M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot
    (M.positivePolynomialEvaluationDenominator p) (M.positivePolynomialEvaluationDenominator_pos p)
    (M.positivePolynomialBasis_structure_height hM)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def positivePolynomialModel (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    RationalFilteredNilmanifold M.filtration.positivePolynomialAlgebra
      (∑ i, bound i) (Fintype.card M.PositivePolynomialBasisIndex) where
  filtration := M.filtration.positivePolynomialMultidegree.ordinary
  basis := M.positivePolynomialFinBasis p
  layerBasis i := M.filtration.positivePolynomialDegreeBasis (M.positiveCoefficientBasis p) (i.val + 1)
  lattice := M.positivePolynomialLattice p B hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    apply bchSubgroup_inner_grid_reindex
    rw [M.positivePolynomialLattice_coordinates]
  outer_grid := by
    apply bchSubgroup_outer_grid_reindex
    rw [M.positivePolynomialLattice_coordinates]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx

noncomputable def positivePolynomialModelMultidegree (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    (M.positivePolynomialModel p B hB hstable).MultidegreeStructure bound where
  filtration := M.filtration.positivePolynomialMultidegree
  ordinary := rfl
  basis a := M.filtration.positivePolynomialMultidegreeBasis (M.positiveCoefficientBasis p)
    (fun i => (a i).val)

theorem positivePolynomialModel_complexity {p q : ℝ} (hM : M.ComplexityLE p)
    (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
    (hq : 0 ≤ q) (hd : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤ q)
    (hBq : (B : ℝ) ≤ Real.exp q)
    (hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q) :
    (M.positivePolynomialModelMultidegree p B hB hstable).ComplexityLE q := by
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_one]
    exact Real.one_le_exp hq
  refine ⟨⟨hd, hBq, ?_, ?_⟩, ?_⟩
  · intro i j k
    exact rationalLogHeight_le_of_height (M.positivePolynomialFinBasis_structure_height hM i j k) hHq
  · intro i j k
    exact rationalLogHeight_le_of_height (M.positivePolynomialFinBasis_degree_height p (i.val + 1) j k) hone
  · intro a j k
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialFinBasis_multidegree_height p (fun i => (a i).val) j k) hone

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped BigOperators
open NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem positivePolynomialEvaluationDenominator_le_exp {p : ℝ} (hM : M.ComplexityLE p) :
    (M.positivePolynomialEvaluationDenominator p : ℝ) ≤
      Real.exp (positivePolynomialDenominatorBudget (∑ i, bound i) p) := by
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let t := ∑ i, bound i
  have hSQ := squarefreeInputBudget_le_positive t hp
  have hpQ : p ≤ positivePolynomialInputBudget t p :=
    (le_squarefreeInputBudget t hp).trans hSQ
  have hp1Q : p + 1 ≤ positivePolynomialInputBudget t p :=
    le_add_of_nonneg_right (squarefreeInputBudget_nonneg t hp)
  have hQ := positivePolynomialInputBudget_nonneg t hp
  have hNQ : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤
      positivePolynomialInputBudget t p := by
    apply le_trans _ hSQ
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast M.positivePolynomialBasisIndex_card_le p
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hM.1.1 (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have hA : ∀ i j, RationalHeightLE
      (LinearMap.toMatrix (M.positivePolynomialBasis p) D.basis
        M.filtration.positivePolynomialEvaluation.toLinearMap i j) ⌈Real.exp p⌉₊ := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact M.positivePolynomialBasis_evaluation_height hM j i
  have hden := matrixDenominator_allowance_le_exp _ D.grid ⌈Real.exp p⌉₊ hA hQ
    (by simpa only [Fintype.card_fin] using hM.1.1.trans hpQ) hNQ
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1Q))
    (hM.1.2.1.trans (Real.exp_le_exp.mpr hpQ))
  exact hden.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hQ))

theorem exists_controlled_positivePolynomial_model {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (M.positivePolynomialModelMultidegree p B hB hstable).ComplexityLE
        (positivePolynomialModelBudget (∑ i, bound i) p) ∧
      M.positivePolynomialLattice p B hstable ≤
        D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let t := ∑ i, bound i
  have hSR := (squarefreeInputBudget_le_positive t hp).trans
    (positivePolynomialInputBudget_le_denominator t p)
  have hR := (positivePolynomialInputBudget_nonneg t hp).trans
    (positivePolynomialInputBudget_le_denominator t p)
  have hRT := positivePolynomialDenominatorBudget_le_model t hp
  have hNR : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤
      positivePolynomialDenominatorBudget t p := by
    apply le_trans _ hSR
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast M.positivePolynomialBasisIndex_card_le p
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hM.1.1 (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have hHR : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (positivePolynomialDenominatorBudget t p) :=
    (squarefreeStructureHeight_ceil_exp d hp hM.1.1).trans
      (Real.exp_le_exp.mpr ((le_add_of_nonneg_left (mul_nonneg (by positivity) hp)).trans hSR))
  obtain ⟨B, hB, hdiv, hraw, hstable⟩ := M.exists_positivePolynomial_stable_grid hM
  refine ⟨B, hB, hstable, ?_, M.positivePolynomialLattice_maps p B hstable hdiv⟩
  apply M.positivePolynomialModel_complexity hM B hB hstable (hR.trans hRT) (hNR.trans hRT)
  · apply (Nat.cast_le.mpr hraw).trans
    exact (integral_grid_allowance_le_exp (bchIntegralDenominatorBound t)
      (Fintype.card M.PositivePolynomialBasisIndex) _ _ hR hNR hHR
      (M.positivePolynomialEvaluationDenominator_le_exp hM)).trans
        (Real.exp_le_exp.mpr (le_add_of_nonneg_left hR))
  · exact hHR.trans (Real.exp_le_exp.mpr hRT)

theorem exists_positivePolynomial_model_uniform (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
      {bound : σ → ℕ} (M : D.MultidegreeStructure bound) {p : ℝ},
      (∑ i, bound i) = t → M.ComplexityLE p →
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
        (M.positivePolynomialModelMultidegree p B hB hstable).ComplexityLE ((p + C) ^ C) ∧
        M.positivePolynomialLattice p B hstable ≤
          D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) := by
  obtain ⟨C, hC, hbudget⟩ := exists_positivePolynomialModel_budget t
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ s d D bound M p ht hM
  obtain ⟨B, hB, hstable, hmodel, hmap⟩ := M.exists_controlled_positivePolynomial_model hM
  refine ⟨B, hB, hstable, hmodel.mono _ ?_, hmap⟩
  rw [ht]
  exact hbudget p ((Nat.cast_nonneg d).trans hM.1.1)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

noncomputable def positivePolynomialDownsetLattice (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    Subgroup (M.filtration.positivePolynomialDownsetQuotient J hJ).ordinary.Group :=
  (M.positivePolynomialLattice p B hstable).map
    (M.filtration.positivePolynomialMultidegree.ordinary.quotientStepHom
      (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ)
      (by rw [M.filtration.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le))

theorem positivePolynomialDownsetLattice_coordinates (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    bchSubgroupCoordinates (M.positivePolynomialDownsetBasis J hJ p)
      (M.positivePolynomialDownsetLattice J hJ p B hstable) = scaledIntegerGrid B := by
  exact M.filtration.positivePolynomialMultidegree.ordinary.quotientStep_exact_grid_supported
    (M.positivePolynomialBasis p)
    (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ) _
    {j | boxedDegreeMonomial j.1 ∉ J}
    (M.filtration.positivePolynomialDownsetIdeal_eq_span (M.positiveCoefficientBasis p) J hJ)
    (M.positivePolynomialLattice p B hstable) B (M.positivePolynomialLattice_coordinates p B hstable)

noncomputable def positivePolynomialDownsetModel (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    RationalFilteredNilmanifold
      (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ)
      (∑ i, bound i) (Fintype.card (M.PositivePolynomialDownsetIndex J)) where
  filtration := (M.filtration.positivePolynomialDownsetQuotient J hJ).ordinary
  basis := M.positivePolynomialDownsetFinBasis J hJ p
  layerBasis i := M.filtration.positivePolynomialDownsetDegreeBasis
    (M.positiveCoefficientBasis p) J hJ (i.val + 1)
  lattice := M.positivePolynomialDownsetLattice J hJ p B hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    apply bchSubgroup_inner_grid_reindex
    rw [M.positivePolynomialDownsetLattice_coordinates]
  outer_grid := by
    apply bchSubgroup_outer_grid_reindex
    rw [M.positivePolynomialDownsetLattice_coordinates]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx

noncomputable def positivePolynomialDownsetModelMultidegree (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    (M.positivePolynomialDownsetModel J hJ p B hB hstable).MultidegreeStructure bound where
  filtration := M.filtration.positivePolynomialDownsetQuotient J hJ
  ordinary := rfl
  basis a := M.filtration.positivePolynomialDownsetMultidegreeBasis
    (M.positiveCoefficientBasis p) J hJ (fun i => (a i).val)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TwoDownsetPrecision
namespace OAI


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

def DownsetSplittingStatement (s t a C : ℕ) : Prop :=
    ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (Fintype.card α : ℝ) ≤ p + 2 →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      letI : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => moduleTopology ℝ _
      letI : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => IsModuleTopology.topologicalAddGroup ℝ _
      letI : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
      ∃ r : ℝ, p ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable r B),
        (∀ i, (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        (∀ i, Fintype.card (M.PositivePolynomialDownsetIndex (J i)) ≤ 2 ^ t * d) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∃ n : α → ℕ, (∀ i, 0 < n i) ∧
            (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            ∃ T : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) r B hB hstable).Niltest (fun _ : σ => 1),
              (∀ i j, (T i j).normBound = 1) ∧ (∀ i j, (T i j).UnitIntervalValued) ∧
              (∀ i j, (T i j).ComplexityLE ((p + C) ^ C)) ∧
              (∀ i j, (T i j).orbit =
                (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r B hB hstable).orbitToOrdinary
                  (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h)) ∧
              ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
                (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
                (∀ k x, ‖u k x‖ ≤ 1) →
                ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                  (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp ((p + C) ^ C)) ∧
                  ∀ x, ‖(WithLp.toLp 2 (fun k => u k
                      (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
                    ∑ j, (∏ i, (T i (j i)).eval x) • c j‖ ≤ epsilon

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct NNReal

def TwoDownsetSplittingStatement (s t a C : ℕ) : Prop :=
    ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : Bool → Set (σ →₀ ℕ))
      [∀ b, DecidablePred (· ∈ J b)] (hJ : ∀ b, IsLowerSet (J b))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (∀ c, c ≠ 0 → c ∉ J false ∪ J true → M.filtration.layer (fun i => c i) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun _ => moduleTopology ℝ _
      letI : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun _ => IsModuleTopology.topologicalAddGroup ℝ _
      letI : ∀ b, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun b => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J b) (hJ b) p)
      ∃ r : ℝ, p ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable r B),
        let E := fun b => M.positivePolynomialDownsetModel (J b) (hJ b) r B hB hstable
        (∀ b, (M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        (∀ b, Fintype.card (M.PositivePolynomialDownsetIndex (J b)) ≤ 2 ^ t * d) ∧
        (∀ b c, c ∉ J b →
          (M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable).filtration.layer (fun i => c i) = ⊥) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∀ (u : D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
            (letI := D.metricSpace; LipschitzWith ell u) → (∀ x, ‖u x‖ ≤ 1) →
            ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∃ (A : Fin N → (E false).Niltest (fun _ : σ => 1))
                (B' : Fin N → (E true).Niltest (fun _ : σ => 1)),
                (∀ j, (A j).normBound ≤ 1) ∧ (∀ j, (B' j).normBound ≤ 1) ∧
                (∀ j, (A j).ComplexityLE ((p + C) ^ C)) ∧
                (∀ j, (B' j).ComplexityLE ((p + C) ^ C)) ∧
                (∀ j, (A j).orbit =
                  (M.positivePolynomialDownsetModelMultidegree (J false) (hJ false) r B hB hstable).orbitToOrdinary
                    (M.filtration.positivePolynomialDownsetOrbit (J false) (hJ false) h)) ∧
                (∀ j, (B' j).orbit =
                  (M.positivePolynomialDownsetModelMultidegree (J true) (hJ true) r B hB hstable).orbitToOrdinary
                    (M.filtration.positivePolynomialDownsetOrbit (J true) (hJ true) h)) ∧
                ∀ x, ‖u (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) -
                  ∑ j, (A j).eval x * (B' j).eval x‖ ≤ epsilon

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGlobalErrorSplitting
namespace OAI

section

namespace Erdos3.NativeTwoVariableSplit

open scoped TensorProduct BigOperators

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem exists_fixed_correlating_term {G X : Type*} [Fintype X] [Nonempty X]
    {s d : ℕ} {p epsilon rho : ℝ} {u : (Fin 2 → ℤ) → ℂ}
    (R : NativeTwoVariableSplit s d p epsilon u) (H : Finset G) (hH : H.Nonempty)
    (sample : G → X → Fin 2 → ℤ) (f : G → X → ℂ)
    (hrho : 0 < rho) (hepsilon : epsilon ≤ rho / 2)
    (hf : ∀ h ∈ H, ∀ x, ‖f h x‖ ≤ 1)
    (hcorr : ∀ h ∈ H, rho ≤ ‖𝔼 x, f h x * star (u (sample h x))‖) :
    ∃ (j : Fin R.count) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-p) * (H.card : ℝ) ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, rho / (2 * Real.exp p) ≤
        ‖𝔼 x, f h x * star ((R.test false j).eval (sample h x) *
          (R.test true j).eval (sample h x))‖ := by
  classical
  let rel (h : G) (_ : Unit) (j : Fin R.count) : Prop :=
    rho / (2 * Real.exp p) ≤
      ‖𝔼 x, f h x * star ((R.test false j).eval (sample h x) *
        (R.test true j).eval (sample h x))‖
  have hcount : (Fintype.card (Fin R.count) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using R.count_bound
  have hchoice : ∀ h ∈ H, ∀ i, ∃ j, rel h i j := by
    intro h hh _
    apply exists_correlating_summand (J := Fin R.count) Finset.univ_nonempty
      (f h) (fun x => u (sample h x))
      (fun j x => (R.test false j).eval (sample h x) * (R.test true j).eval (sample h x))
      hrho (Real.exp_pos p) hcount (fun x _ => hf h hh x) _ (hcorr h hh)
    intro x _
    rw [norm_sub_rev]
    exact (R.approximation (sample h x)).trans hepsilon
  obtain ⟨j, S, hsub, hS, hsize, hfixed⟩ :=
    exists_large_fixed_choices H hH rel hchoice hcount
  refine ⟨j (), S, hsub, hS, ?_, fun h hh => hfixed h hh ()⟩
  simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize

end Erdos3.NativeTwoVariableSplit

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeTripleProjections
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem additiveTripleProjection_lattice (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) :
    M.additiveTripleLattice i hi c hc ≤ D.lattice.comap
      (mapOfSteps (M.filtration.additiveTripleProjection i hi c hc j)) := by
  intro x hx
  have h := (M.additiveTripleLattice_mem i hi c hc x).mp hx
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2

noncomputable def tripleSpaceProjection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hE : E.lattice = M.additiveTripleLattice i hi c hc) (j : Fin 3) : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice (M.filtration.realAdditiveTripleProjection i hi c hc j)
    (realificationMap_subgroup (M.filtration.additiveTripleProjection i hi c hc j) _ _
      (by rw [hE]; exact M.additiveTripleProjection_lattice i hi c hc j))

theorem tripleSpaceProjection_smul (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hE : E.lattice = M.additiveTripleLattice i hi c hc) (j : Fin 3)
    (g : E.RealGroup) (x : E.Space) :
    M.tripleSpaceProjection i hi c hc E hE j (g • x) =
      M.filtration.realAdditiveTripleProjection i hi c hc j g •
        M.tripleSpaceProjection i hi c hc E hE j x := cosetMap_smul _ _ _ _ _ _

theorem tripleSpaceProjection_lipschitz (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi c hc) (j : Fin 3)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ a k, rationalLogHeight
      (D.basis.repr (M.filtration.additiveTripleProjection i hi c hc j (E.basis a)) k) ≤ p) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.tripleSpaceProjection i hi c hc E hEL j) := by
  let := E.metricSpace
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E D (M.filtration.additiveTripleProjection i hi c hc j)
        (by rw [hEL]; exact M.additiveTripleProjection_lattice i hi c hc j)
        hp hE hD (fun k a => hheight a k) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationDescent
namespace OAI

section

namespace Erdos3

namespace RationalFilteredNilmanifold.MultidegreeStructure

open CircleFourier
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)
  (i : σ) (hi : bound i ≤ 1) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
  (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
  (hEL : E.lattice = M.additiveTripleLattice i hi c hc)

noncomputable def tripleObservable (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (x : E.Space) : ℂ :=
  u 0 (ε • M.tripleSpaceProjection i hi c hc E hEL 0 x) *
    star (u 1 (ε • M.tripleSpaceProjection i hi c hc E hEL 1 x)) *
    star (u 2 (ε • M.tripleSpaceProjection i hi c hc E hEL 2 x))

theorem tripleObservable_mk (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (g : E.RealGroup) :
    M.tripleObservable i hi c hc E hEL ε u (QuotientGroup.mk g) =
      u 0 (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi c hc 0 g)) *
        star (u 1 (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi c hc 1 g))) *
        star (u 2 (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi c hc 2 g))) := rfl

theorem tripleObservable_norm_le (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ)
    (hu : ∀ j x, ‖u j x‖ ≤ 1) (x : E.Space) :
    ‖M.tripleObservable i hi c hc E hEL ε u x‖ ≤ 1 := by
  simp only [tripleObservable, norm_mul, norm_star]
  have h01 : ‖u 0 (ε • M.tripleSpaceProjection i hi c hc E hEL 0 x)‖ *
      ‖u 1 (ε • M.tripleSpaceProjection i hi c hc E hEL 1 x)‖ ≤ 1 := by
    simpa only [mul_one] using mul_le_mul (hu 0 _) (hu 1 _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [mul_one] using mul_le_mul h01 (hu 2 _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem tripleSpaceProjection_top_smul (ε : D.RealGroup) (j : Fin 3) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi c hc).realification.subgroup s)
    (x : E.Space) :
    ε • M.tripleSpaceProjection i hi c hc E hEL j (k • x) =
      M.filtration.realAdditiveTripleProjection i hi c hc j k •
        (ε • M.tripleSpaceProjection i hi c hc E hEL j x) := by
  have hz := M.filtration.realAdditiveTripleProjection_mem i hi c hc j hk
  rw [M.tripleSpaceProjection_smul, ← mul_smul, ← mul_smul,
    (M.filtration.realification.ordinary.top_commutes _ hz ε).eq]

theorem tripleObservable_component_top (ε : D.RealGroup) (u : D.Space → ℂ)
    (χ : D.RealGroup → CircleFourier.Circle)
    (hu : ∀ z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u (z • x) = character (χ z) * u x)
    (j : Fin 3) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi c hc).realification.subgroup s)
    (x : E.Space) :
    u (ε • M.tripleSpaceProjection i hi c hc E hEL j (k • x)) =
      character (χ (M.filtration.realAdditiveTripleProjection i hi c hc j k)) *
        u (ε • M.tripleSpaceProjection i hi c hc E hEL j x) := by
  rw [M.tripleSpaceProjection_top_smul i hi c hc E hEL ε j k hk x]
  exact hu _ (M.filtration.realAdditiveTripleProjection_mem i hi c hc j hk) _

theorem tripleObservable_top_invariant
    (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (χ : D.RealGroup → CircleFourier.Circle)
    (hu : ∀ j z, z ∈ M.filtration.realification.ordinary.subgroup s →
      ∀ x, u j (z • x) = character (χ z) * u j x)
    (k : E.RealGroup)
    (hk : k ∈ (M.filtration.additiveTripleFiltration i hi c hc).realification.subgroup s)
    (hphase : χ (M.filtration.realAdditiveTripleProjection i hi c hc 0 k) =
      χ (M.filtration.realAdditiveTripleProjection i hi c hc 1 k) +
        χ (M.filtration.realAdditiveTripleProjection i hi c hc 2 k))
    (x : E.Space) :
    M.tripleObservable i hi c hc E hEL ε u (k • x) =
      M.tripleObservable i hi c hc E hEL ε u x := by
  have hvalue (j : Fin 3) := M.tripleObservable_component_top i hi c hc E hEL ε (u j) χ (hu j) j k hk x
  have hprod := congrArg₂ (fun a b : ℂ => a * b)
    (congrArg₂ (fun a b : ℂ => a * star b) (hvalue 0) (hvalue 1))
    (congrArg star (hvalue 2))
  exact hprod.trans (triple_phase_cancellation
    (fun j => u j (ε • M.tripleSpaceProjection i hi c hc E hEL j x))
    (fun j => χ (M.filtration.realAdditiveTripleProjection i hi c hc j k)) hphase)

end RationalFilteredNilmanifold.MultidegreeStructure
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem tripleObservable_of_addition_values (i : σ) (hi : bound i ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi
      (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
    (g : M.filtration.realification.PolynomialOrbit) (ε : D.RealGroup)
    (q : E.filtration.realification.PolynomialOrbit (fun _ : Option σ => 1))
    (hvalues : ∀ (x : Option σ → ℤ) (j : Fin 3),
      (QuotientGroup.mk (ε * M.filtration.realAdditiveTripleProjection i hi
        (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i) j
        (E.filtration.realification.polynomialOrbitEval _ x q)) : D.Space) =
        QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x j) g))
    (u : Fin 3 → D.Space → ℂ) (x : Option σ → ℤ) :
    M.tripleObservable i hi _ (omittedCoordinateWeight_le_one i) E hEL ε u
      (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x q)) =
        u 0 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x 0) g)) *
        star (u 1 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x 1) g))) *
        star (u 2 (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (coordinateAdditionInputs i x 2) g))) := by
  rw [M.tripleObservable_mk, hvalues x 0, hvalues x 1, hvalues x 2]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

omit [DecidableEq σ] in
theorem unitVertical_top_action (hs : ∑ j, bound j = s)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (a : I) (z : D.RealGroup) (hz : z ∈ M.filtration.realification.ordinary.subgroup s)
    (x : D.Space) : V.observable a (z • x) =
      character (realifyFunctional V.frequency z.coord : CircleFourier.Circle) * V.observable a x := by
  have htop : M.realSubgroup bound = M.filtration.realification.ordinary.subgroup s := by
    rw [M.realSubgroup_top, hs]
    change D.filtration.realification.subgroup s = M.filtration.ordinary.realification.subgroup s
    rw [M.ordinary]
  exact V.vertical a z (htop.symm ▸ hz) x

end RationalFilteredNilmanifold.MultidegreeStructure
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeTripleObservableMetric
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound)

theorem tripleObservable_lipschitz (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi c hc) s r)
    (hEL : E.lattice = M.additiveTripleLattice i hi c hc)
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi c hc)]
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hheight : ∀ j a k, rationalLogHeight
      (D.basis.repr (M.filtration.additiveTripleProjection i hi c hc j (E.basis a)) k) ≤ p)
    (ε : D.RealGroup) (u : Fin 3 → D.Space → ℂ) (K A : ℝ≥0)
    (hu : ∀ j x, ‖u j x‖ ≤ 1)
    (hLip : letI := D.metricSpace; ∀ j, LipschitzWith K (u j))
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) :
    letI := E.metricSpace
    LipschitzWith (3 * (K * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩)))
      (M.tripleObservable i hi c hc E hEL ε u) := by
  let := E.metricSpace
  let := D.metricSpace
  apply lipschitz_three_conjugates_of_bounds
    (fun j x => u j (ε • M.tripleSpaceProjection i hi c hc E hEL j x))
  · intro j
    exact (hLip j).comp (hε.comp
      (M.tripleSpaceProjection_lipschitz i hi c hc E hEL j hp hD hE (hheight j)))
  · exact fun j x => hu j _

end RationalFilteredNilmanifold.MultidegreeStructure
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultilinearityCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_controlled_addition_model (i : σ) (hi : bound i = 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
        c hc) s
        (finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le
          c hc)),
      E.filtration = M.filtration.additiveTripleFiltration i hi.le
        c hc ∧
      E.lattice = M.additiveTripleLattice i hi.le
        c hc ∧
      E.GeometryComplexityLE (MultilinearityBudget.ambient p) ∧
      (∀ j a k, rationalLogHeight (D.basis.repr (M.filtration.additiveTripleProjection i hi.le
        c hc j (E.basis a)) k) ≤
          MultilinearityBudget.ambient p) ∧
      finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le c hc) ≤ 3 * d := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  obtain ⟨E, hEF, hEL, hE, hdim, he⟩ :=
    M.exists_additiveTriple_model i hi c hc hM
  have hR := MultilinearityBudget.ambient_bounds hp
  have hE' := hE.mono E hR.2.2.1
  have he' (j : Fin 3) (a) (k) :
      rationalLogHeight (D.basis.repr (M.filtration.additiveTripleProjection i hi.le
        c hc j (E.basis a)) k) ≤
          MultilinearityBudget.ambient p := by
    fin_cases j
    · exact (he a k).1.trans hR.2.2.2
    · exact (he a k).2.1.trans hR.2.2.2
    · exact (he a k).2.2.trans hR.2.2.2
  exact ⟨E, hEF, hEL, hE', he', hdim⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedTranslationSampleHom (s : ℕ) (j : Option (ReplicatedIndex (mixedCorrelationDegree s))) :
    ((Fin 3 → ℤ) →+ ℤ) where
  toFun x := mixedTranslationSample s x j
  map_zero' := by
    rcases j with _ | ⟨j, k⟩
    · rfl
    · fin_cases j <;> rfl
  map_add' x y := by
    rcases j with _ | ⟨j, k⟩
    · rfl
    · fin_cases j <;> rfl

theorem mixedTranslationSample_translated (s : ℕ) (x : Fin 3 → ℤ) :
    coordinateTranslatedInput (mixedTranslationCoordinates s) (mixedTranslationSample s x) =
      fun j => correlationInput (x 0) (x 1 + x 2) j.1 := by
  funext ⟨j, k⟩
  fin_cases j <;> simp [coordinateTranslatedInput, mixedTranslationSample, correlationInput]
  rfl

theorem replicatedMixed_nonempty (s : ℕ) : Nonempty (ReplicatedIndex (mixedCorrelationDegree s)) :=
  ⟨⟨0, ⟨0, by change 0 < 1; omega⟩⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TensorSquarePairComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def rationalDilation (r : ℚ) : NativeMultidegreeNilcharacter bound p :=
  { W with orbit := W.multi.filtration.realification.rationalDilationOrbit r W.orbit }

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedEvaluationCoordinates
namespace OAI

section

namespace Erdos3

theorem mixedEvaluationCoordinates_erase_card (s : ℕ)
    (i : ReplicatedIndex (mixedCorrelationDegree s)) (hi : i.1 = 1) :
    ((mixedEvaluationCoordinates s).erase i).card = s - 1 := by
  rw [Finset.card_erase_of_mem ((mem_mixedEvaluationCoordinates s i).mpr hi),
    mixedEvaluationCoordinates_card]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedShiftCoordinate
namespace OAI

section

namespace Erdos3

def mixedShiftCoordinate (s : ℕ) : ReplicatedIndex (mixedCorrelationDegree s) :=
  ⟨0, ⟨0, by change 0 < 1; omega⟩⟩

theorem mixedShiftCoordinate_unique (s : ℕ) (j : ReplicatedIndex (mixedCorrelationDegree s))
    (hj : j.1 = 0) : j = mixedShiftCoordinate s := by
  rcases j with ⟨j, k⟩
  dsimp only at hj
  subst j
  dsimp only [mixedShiftCoordinate]
  apply congrArg (fun t : Fin (mixedCorrelationDegree s 0) =>
    (⟨0, t⟩ : ReplicatedIndex (mixedCorrelationDegree s)))
  apply Fin.ext
  have hk := k.isLt
  change k.val < 1 at hk
  change k.val = 0
  omega

theorem mixed_input_eq_coordinateConstant (s : ℕ) (h n : ℤ) :
    (fun j : ReplicatedIndex (mixedCorrelationDegree s) => correlationInput h n j.1) =
      coordinateConstantInput (mixedShiftCoordinate s) h n := by
  funext j
  by_cases hj : j = mixedShiftCoordinate s
  · subst j
    simp [coordinateConstantInput, mixedShiftCoordinate, correlationInput]
  · have hj₀ : j.1 ≠ 0 := fun h => hj (mixedShiftCoordinate_unique s j h)
    have hj₁ : j.1 = 1 := by
      apply Fin.ext
      have hlt := j.1.isLt
      have hne : j.1.val ≠ 0 := fun h => hj₀ (Fin.ext h)
      change j.1.val = 1
      omega
    rw [hj₁, coordinateConstantInput, Function.update_of_ne hj]
    rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedTranslationAffineInput
namespace OAI

section

namespace Erdos3

def mixedTranslationSlope (s : ℕ) : Option (ReplicatedIndex (mixedCorrelationDegree s)) → ℤ
  | none => 0
  | some j => if j.1 = 1 then 1 else 0

def mixedTranslationIntercept (s : ℕ) (h δ : ℤ) :
    Option (ReplicatedIndex (mixedCorrelationDegree s)) → ℤ
  | none => δ
  | some j => if j.1 = 1 then 0 else h

theorem mixedTranslationSample_affine (s : ℕ) (h n δ : ℤ) :
    (fun j => mixedTranslationIntercept s h δ j + mixedTranslationSlope s j * n) =
      mixedTranslationSample s ![h, n, δ] := by
  funext j
  rcases j with _ | ⟨j, k⟩
  · simp [mixedTranslationIntercept, mixedTranslationSlope, mixedTranslationSample]
  · fin_cases j <;> simp [mixedTranslationIntercept, mixedTranslationSlope,
      mixedTranslationSample, correlationInput]
    rfl

theorem mixedTranslationSlope_replaced_none (s : ℕ) (i : ReplicatedIndex (mixedCorrelationDegree s)) :
    mixedTranslationSlope s (coordinateReplaceIndex i none) = 0 := by
  simp [coordinateReplaceIndex, mixedTranslationSlope]

theorem mixedTranslationSlope_replaced_vanishes (s : ℕ)
    (i j : ReplicatedIndex (mixedCorrelationDegree s))
    (hj : j ∉ (mixedEvaluationCoordinates s).erase i) :
    mixedTranslationSlope s (coordinateReplaceIndex i (some j)) = 0 := by
  by_cases hji : j = i
  · simp [coordinateReplaceIndex, hji, mixedTranslationSlope]
  · have hj₁ : j.1 ≠ 1 := by
      intro h
      exact hj (Finset.mem_erase.mpr ⟨hji, (mem_mixedEvaluationCoordinates s j).mpr h⟩)
    simp [coordinateReplaceIndex, hji, mixedTranslationSlope, hj₁]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

theorem budget_le_factorizationInputOffset (s : ℕ) :
    budget s ≤ (factorizationInputOffset s : ℝ) := by
  apply (Nat.le_ceil _).trans
  exact_mod_cast (Nat.le_add_right ⌈budget s⌉₊ 2)

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end


