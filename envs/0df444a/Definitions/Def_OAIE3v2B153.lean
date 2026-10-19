-- Prove2me | Definitions.Def_OAIE3v2B153
-- name    : OAIE3v2B153
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:16:47.410172+00:00
-- url     : https://prove2.me/theorems/ff5f7f83-7af9-4984-9968-ad8e4897863b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 155 of 311
-- statement:
--   Definitions bundle 155 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B140`, `OAIE3v2B141`, `OAIE3v2B142`, `OAIE3v2B143`, `OAIE3v2B144` of this split.
--
--   Modules: `Dynamics/ComparisonEquivalenceBudget.lean`, `Estimates/CommonNativeSquareFactors.lean`, `Estimates/FirstCoefficientDerivativeBounds.lean`, `Estimates/NativeSquareOrbit.lean`, `Estimates/NormalizedCommonFamily.lean`, `Estimates/RealFirstCoefficientHorizontal.lean`, `Estimates/ReducedNativeFactorization.lean`, `Estimates/ReducedRelativeCoefficientBounds.lean`, `Estimates/ReducedSquareSymbol.lean`, `Estimates/SymbolFastMembership.lean`, `Estimates/UniformControlledNativeExternalNetsOfRecovery.lean`, `Fourier/BohrNiltestBudget.lean`, `Geometry/CoordinateQuotientModel.lean`, `Geometry/NativeIntervalCoordinate.lean`, `Linear/RealFirstCoefficientBasis.lean`, `Linear/SquareBasisGeometry.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Nilpotent/NativeResidueNiltests.lean`, `Nilpotent/NiltestComplement.lean`, `Nilpotent/RankBracketFactorizationMonotone.lean`, `Polynomial/NativePolynomialOrbit.lean`, `Polynomial/PolynomialGridValues.lean`, `Polynomial/RaisedDegreeRank.lean`, `Polynomial/RealCoefficientPolynomialProjection.lean`, `Polynomial/RealReducedSquarePolynomial.lean`, `Polynomial/RealSquarePolynomialFactors.lean`, `Sampling/RealAdaptedCoefficientGrid.lean`.
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
import Definitions.Def_OAIE3v2B144

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace RationalFilteredNilmanifold

theorem piNiltest_unit_interval {ι σ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}
    (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hunit : ∀ i, (T i).UnitIntervalValued) :
    (piNiltest D T hp hι hT).UnitIntervalValued := by
  intro z
  exact complex_prod_unit_interval (fun i => (T i).observable (productProjection D i z))
    (fun i => hunit i _)

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolFastMembership
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_symbol_composition (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ControlledSymbolCompositionSpec s C := by
  obtain ⟨a, _, hslow⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨b, _, hgrid⟩ := exists_symbol_rational_product_bound s 2
  let P : Polynomial ℕ := Polynomial.X + (2 * Polynomial.X + Polynomial.C a) ^ a +
    (2 * Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hc T hT η l hl hlp A X R hA hR hX
  have hpa : 0 ≤ (2 * p + a) ^ a := by positivity
  have hpb : 0 ≤ (2 * p + b) ^ b := by positivity
  have hbound : p + (2 * p + a) ^ a + (2 * p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hfinal p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have haC : (2 * p + a) ^ a ≤ (p + C) ^ C := by linarith
  have hbC : (2 * p + b) ^ b ≤ (p + C) ^ C := by linarith
  have h2p : 0 ≤ 2 * p := by positivity
  have hp2 : p ≤ 2 * p := by linarith
  have he2 := Real.exp_le_exp.mpr hp2
  have he : Real.exp p ≤ Real.exp ((2 * p + 2) ^ 1) := Real.exp_le_exp.mpr (by rw [pow_one]; linarith)
  obtain ⟨m, E, Q, B, Z, v, hm, hmp, hprod, hE, hB, hv, hZ, hh, hη, hQ⟩ := hX
  have hleft := hslow F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H (2 * p) hH h2p (hι.trans hp2) (hσ.trans hp2) (hHp.trans he2) hc T hT [A, E] (by simp) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact F.symbolSlowBound_mono e ω hF (fun _ => 1) T hT he _ hA
      · exact F.symbolSlowBound_mono e ω hF (fun _ => 1) T hT he _ hE)
  have hleft' : F.SymbolSlowBound e ω hF (fun _ => 1) T (Real.exp ((2 * p + a) ^ a)) (A * E) := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hleft
  have hdenom : ((l * m : ℕ) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨n, hn, hnp, _, hproducts⟩ := hgrid F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H (2 * p) hH h2p (hι.trans hp2) (hσ.trans hp2) (hHp.trans he2) hc (l * m) (Nat.mul_pos hl hm) hdenom
  have hright := hproducts [B, R] (by simp) (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact F.symbolRationalGrid_mono e ω hF (fun _ => 1) hm (dvd_mul_left m l) _ hB
    · exact F.symbolRationalGrid_mono e ω hF (fun _ => 1) hl (dvd_mul_right l m) _ hR)
  have hright' : F.SymbolRationalGrid e ω hF (fun _ => 1) n (B * R) := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hright
  refine ⟨n, A * E, Q, B * R, Z, v, hn, hnp.trans (Real.exp_le_exp.mpr hbC), ?_,
    F.symbolSlowBound_mono e ω hF (fun _ => 1) T hT (Real.exp_le_exp.mpr haC) (A * E) hleft',
    hright', hv, hZ, (fun i j => (hh i j).trans hpC), hη, hQ⟩
  calc
    (A * E) * Q * (B * R) = A * (E * Q * B) * R := by group
    _ = A * X * R := by rw [hprod]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedSquareSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

theorem reducedSquareGradedDiagonalPiece_eq_zero_iff (j : ℕ) (hj : j ≤ s) (x : F.layer j) :
    F.reducedSquareGradedDiagonalPiece j x = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  change F.squareFiltration.quotientTopGradedMap
    (F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j x)) = 0 ↔ _
  rw [F.squareFiltration.quotientTopGradedMap_piece_eq_zero_iff j hj]
  exact (F.squareFiltration.associatedGradedPieceMap_eq_zero_iff j _).symm.trans
    (F.squareGradedDiagonalPiece_eq_zero_iff j x)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def reducedSquareSymbolBasis :
    Basis (ReducedSquareSymbolIndex s w ω) ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  F.squareFiltration.quotientTop.polynomialSymbolBasis (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

theorem realAdaptedLogDerivative_tensor
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.realAdaptedPolynomialTensor (fun _ => 1) (F.realAdaptedLogDerivative h x) =
      F.realification.adaptedLogDerivative h (F.realAdaptedPolynomialTensor (fun _ => 1) x) := by
  let φ := F.realAdaptedPolynomialTensor (fun _ : σ => 1)
  apply dualLinearLift_logDerivative_eq
    (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).lowerCentralSeries_eq_bot
    (⊤ : LieIdeal ℚ (ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))) φ φ.toLinearMap
    (fun u v _ => φ.map_lie u v) (F.realAdaptedPolynomialJet h x) (by trivial)
    (F.realification.adaptedPolynomialJet h (φ x))
  rw [dualLinearLift_apply, F.realAdaptedPolynomialJet_base, F.realAdaptedPolynomialJet_tangent]
  change dualConstantLie (φ x) + dualInfinitesimal (φ (F.realAdaptedDirectionalDerivative h x)) =
    dualConstantLie (φ x) + dualInfinitesimal (F.realification.adaptedDirectionalDerivative h (φ x))
  rw [F.realAdaptedDirectionalDerivative_tensor]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realFirstCoefficientDirectionMap_rat [Fintype σ]
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1)) (h : σ → ℚ) :
    F.realFirstCoefficientDirectionMap x (fun i => (h i : ℝ)) =
      F.realFirstCoefficientMap (fun _ => 1)
        ⟨F.realAdaptedLogDerivative h x, F.realAdaptedLogDerivative_mem_first h x⟩ := by
  apply congrArg (F.realFirstCoefficientMap (fun _ => 1))
  apply Subtype.ext
  exact F.realLogDerivativeDirectionMap_rat x h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem firstCoefficientRealEquiv_map (x : ℝ ⊗[ℚ] (F.shiftedPolynomialIdeal w 1)) :
    F.firstCoefficientRealEquiv w ((F.firstCoefficientMap w).baseChange ℝ x) =
      F.realFirstCoefficientMap w (realificationSubmoduleEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule x) :=
  realSubquotientEquiv_project _ _ x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealAdaptedCoefficientGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedCoefficientGrid_polynomial_iff (l : ℕ) (g : F.RealAdaptedPolynomialGroup w) :
    F.RealAdaptedCoefficientGrid b ω hF w l g.coord ↔
      F.PolynomialRationalGrid b w l (F.realAdaptedPolynomialGroupHom w g) :=
  (F.polynomialRationalGrid_groupHom_iff b w ω hF l g).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateQuotientModel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

theorem coordinateQuotientModel_geometry (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hNp : (N : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) :
    (F.coordinateQuotientModel b w hlayers I hI S hspan Γ N hN hin hout).GeometryComplexityLE p := by
  apply (F.quotientLie I hI).ofAdaptedBasis_geometry _ _ _ _ _ _ _ _ hp
  · exact (Nat.cast_le.mpr (Fintype.card_subtype_le (fun i => i ∉ S))).trans hd
  · exact hNp
  · intro i j k
    simp only [quotientFinBasis, lieStructureConstants_reindex, supportedQuotientBasis_lieStructure]
    exact hc _ _ _

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalTorus

open Module

theorem nilmanifold_geometry (d : ℕ) {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (nilmanifold d).GeometryComplexityLE p := by
  apply (filtration d).ofAdaptedBasis_geometry (basis d) (fun _ => 1) (basis_layers d)
    (lattice d) 1 (by decide) (lattice_inner_grid d) (lattice_outer_grid d) hp hd
  · simpa only [Nat.cast_one] using Real.one_le_exp hp
  · intro i j k
    simpa [lieStructureConstants, lie_eq_zero, rationalLogHeight] using hp

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open scoped BigOperators TensorProduct NNReal

variable {σ : Type*} [Fintype σ] (d : ℕ)

noncomputable def affineOrbit (b : Fin d → ℝ) (a : σ → Fin d → ℝ) :
    (nilmanifold d).filtration.realification.PolynomialOrbit (fun _ : σ => 1) :=
  (nilmanifold d).filtration.realification.affinePolynomialOrbit
    (((basis d).baseChange ℝ).equivFun.symm b)
    (fun j => ((basis d).baseChange ℝ).equivFun.symm (a j))

theorem affineOrbit_coordinates (b : Fin d → ℝ) (a : σ → Fin d → ℝ) (x : σ → ℤ) :
    ((basis d).baseChange ℝ).equivFun
        ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
          (affineOrbit d b a)).coord =
      b + ∑ j, (x j : ℝ) • a j := by
  unfold affineOrbit
  rw [NilpotentLieFiltration.affinePolynomialOrbit_integer_coord, map_add, map_sum]
  simp only [map_smul, LinearEquiv.apply_symm_apply]

theorem affineOrbit_phases (b : Fin d → ℝ) (a : σ → Fin d → ℝ) (x : σ → ℤ) :
    phaseCoordinates d
        ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
          (affineOrbit d b a)) =
      fun i => ((b + ∑ j, (x j : ℝ) • a j) i : CircleFourier.Circle) := by
  change (fun i => (((basis d).baseChange ℝ).equivFun
    ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
      (affineOrbit d b a)).coord i : CircleFourier.Circle)) = _
  rw [affineOrbit_coordinates]

end Erdos3.RationalTorus

end

section

namespace Erdos3

open scoped TensorProduct NNReal

theorem torus_reindex_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι → κ) :
    LipschitzWith 1 (fun v : κ → CircleFourier.Circle => fun i => v (e i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg dist_nonneg).mpr
  intro i
  change ‖v (e i) - w (e i)‖ ≤ dist v w
  rw [← dist_eq_norm]
  exact dist_le_pi_dist v w (e i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

theorem frozen_observable_change_left (S : D.Space → ℂ) {ℓ : ℝ≥0}
    (hS : letI := D.metricSpace; LipschitzWith ℓ S) (a a' b r : D.RealGroup) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
    ‖S (QuotientGroup.mk (a * b * r)) - S (QuotientGroup.mk (a' * b * r))‖ ≤
      (ℓ : ℝ) * dist a a' := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := D.metricSpace
  let x : D.Space := QuotientGroup.mk (b * r)
  have hLip : LipschitzWith 1 (fun a : D.RealGroup => a • x) :=
    quotientMetricSpace_lipschitz_orbit (D.basis.baseChange ℝ) D.realLattice
      D.realLattice_closed_discrete.1 x
  have hpoint : dist (a • x) (a' • x) ≤ dist a a' := by
    simpa only [NNReal.coe_one, one_mul] using hLip.dist_le_mul a a'
  have h := (hS.dist_le_mul (a • x) (a' • x)).trans
    (mul_le_mul_of_nonneg_left hpoint ℓ.coe_nonneg)
  simpa only [x, MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc, dist_eq_norm] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

namespace RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem raiseStep_unit_interval (T : D.Niltest w) (hst : s ≤ t) (hT : T.UnitIntervalValued) :
    (T.raiseStep hst).UnitIntervalValued := fun z => hT (D.raiseStepProjection hst z)

end RationalFilteredNilmanifold.Niltest
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

theorem real_associated : R.filtration.realification.associatedDegree = D.filtration.realification := by
  rw [R.filtration.realification_associatedDegree, R.associated]

theorem realSubgroup_le_degree (i j : ℕ) : R.realSubgroup i j ≤ D.filtration.realification.subgroup i := by
  intro x hx
  have h := R.filtration.realification.subgroup_le_associatedDegree i j hx
  change x.coord ∈ R.filtration.realification.associatedDegree.layer i at h
  change x.coord ∈ D.filtration.realification.layer i
  rwa [R.real_associated] at h

end DegreeRankStructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

namespace RationalFilteredNilmanifold.DegreeRankStructure

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r t d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

noncomputable def withRank (R : D.DegreeRankStructure r) (ht : t ≤ s)
    (hterminal : R.filtration.layer s (t + 1) = ⊥) : D.DegreeRankStructure t where
  filtration := R.filtration.withRank ht hterminal
  associated := R.associated
  basis := R.basis

theorem withRank_complexity (R : D.DegreeRankStructure r) (ht : t ≤ s)
    (hterminal : R.filtration.layer s (t + 1) = ⊥) {p : ℝ} (hR : R.ComplexityLE p) :
    (R.withRank ht hterminal).ComplexityLE p := hR

end RationalFilteredNilmanifold.DegreeRankStructure

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_native_degree_rank_structure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ R : D.DegreeRankStructure s, R.filtration = D.filtration.canonicalDegreeRank ∧
        R.ComplexityLE ((p + C) ^ C) := by
  obtain ⟨a, _, hbasis⟩ := exists_canonical_rank_basis_budget s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hcost : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hex : ∀ i j : Fin (s + 1),
      ∃ b : Basis (Fin (finrank ℚ (D.filtration.rankLayer i.val j.val))) ℚ
          (D.filtration.rankLayer i.val j.val),
        ∀ k l, rationalLogHeight (D.basis.repr (b k : L) l) ≤ (p + a) ^ a := by
    intro i j
    obtain ⟨b, _, hb⟩ := hbasis D hp hD i.val j.val (Nat.le_of_lt_succ i.isLt)
    exact ⟨b, hb⟩
  choose b hb using hex
  let R : D.DegreeRankStructure s := {
    filtration := D.filtration.canonicalDegreeRank
    associated := D.filtration.canonicalDegreeRank_associatedDegree_eq
    basis := b }
  refine ⟨R, rfl, hD.mono D (by linarith), ?_⟩
  intro i j k l
  exact (hb i j k l).trans (by linarith)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t r d : ℕ}

theorem raiseStep_rankSubgroup_eq_bot (D : RationalFilteredNilmanifold L t d)
    (hts : t < s) (R : (D.raiseStep hts.le).DegreeRankStructure r) (j : ℕ) :
    R.realSubgroup s j = ⊥ := by
  apply bot_unique
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply NilpotentLieBCHGroup.ext
  change x.coord = 0
  have hm := R.realSubgroup_le_degree s j hx
  change x.coord ∈ D.filtration.realification.layer s at hm
  simpa only [D.filtration.realification.layer_eq_bot_above_step hts, Submodule.mem_bot] using hm

theorem exists_raised_degree_rank_structure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {t r d : ℕ}
      (D : RationalFilteredNilmanifold L t d) (hts : t < s), r ≤ s →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∃ R : (D.raiseStep hts.le).DegreeRankStructure r,
        R.ComplexityLE ((p + C) ^ C) ∧ R.realSubgroup s r = ⊥ := by
  obtain ⟨C, hC, hcanonical⟩ := exists_native_degree_rank_structure s
  refine ⟨C, hC, ?_⟩
  intro L _ _ t r d D hts hrs p hp hD
  obtain ⟨A, _, hA⟩ := hcanonical (D.raiseStep hts.le) hp (D.raiseStep_geometry hts.le hD)
  have hzero (j : ℕ) : A.filtration.layer s j = ⊥ := by
    apply bot_unique
    have h := A.filtration.layer_le_associatedDegree s j
    rw [A.associated] at h
    exact h.trans (D.filtration.layer_eq_bot_above_step hts).le
  let R := A.withRank hrs (hzero (r + 1))
  exact ⟨R, A.withRank_complexity hrs (hzero (r + 1)) hA,
    D.raiseStep_rankSubgroup_eq_bot hts R r⟩

namespace Niltest

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {σ : Type*} {w : σ → ℕ} {D : RationalFilteredNilmanifold L t d}

theorem raiseStep_rank_vertical (T : D.Niltest w) (hts : t < s)
    (R : (D.raiseStep hts.le).DegreeRankStructure r)
    (z : (D.raiseStep hts.le).RealGroup) (hz : z ∈ R.realSubgroup s r)
    (x : (D.raiseStep hts.le).Space) :
    (T.raiseStep hts.le).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
          (T.raiseStep hts.le).observable x := by
  rw [D.raiseStep_rankSubgroup_eq_bot hts R r] at hz
  have hz' : z = 1 := Subgroup.mem_bot.mp hz
  subst z
  simp

end Niltest

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialGridValues
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem adaptedPolynomial_coordinate_totalDegree (hw : ∀ i, 0 < w i)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (i : ι) :
    (coordinate (((b.baseChange ℝ).coord i).toAddMonoidHom)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))).totalDegree ≤ s := by
  classical
  apply (degreeLE_one_iff_basis_totalDegree (b.baseChange ℝ) s _).mp ?_ i
  have hd := (F.realification.adaptedBCHToOrbit w g).degreeLE
  intro α hα
  apply hd α
  apply hα.trans_le
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Pi.one_apply, mul_one]
  exact Finset.sum_le_sum (fun j _ => Nat.le_mul_of_pos_right _ (hw j))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

theorem exists_rational_polynomial_of_grid {σ : Type*} (P : MvPolynomial σ ℝ)
    (q : ℕ) (hq : 0 < q)
    (hP : ∀ α, ∃ a : ℤ, (a : ℝ) = (q : ℝ) * P.coeff α) :
    ∃ Q : MvPolynomial σ ℚ,
      Q.map (algebraMap ℚ ℝ) = P ∧ Q.totalDegree = P.totalDegree ∧
      ∀ α, (Q.coeff α).den ∣ q := by
  classical
  choose a ha using hP
  let Q : MvPolynomial σ ℚ := ∑ α ∈ P.support, monomial α ((a α : ℚ) / q)
  have hcoeff (α : σ →₀ ℕ) : Q.coeff α = if α ∈ P.support then (a α : ℚ) / q else 0 := by
    simp [Q, coeff_sum, coeff_monomial]
  have hcast (α : σ →₀ ℕ) : (((a α : ℚ) / q : ℚ) : ℝ) = P.coeff α := by
    push_cast
    apply (div_eq_iff (show (q : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hq.ne')).mpr
    simpa only [mul_comm] using ha α
  have hmap : Q.map (algebraMap ℚ ℝ) = P := by
    ext α
    rw [coeff_map, hcoeff]
    by_cases hα : α ∈ P.support
    · rw [if_pos hα]
      exact hcast α
    · rw [if_neg hα, map_zero, notMem_support_iff.mp hα]
  refine ⟨Q, hmap, ?_, ?_⟩
  · rw [← hmap, totalDegree, totalDegree,
      support_map_of_injective Q (algebraMap ℚ ℝ).injective]
  · intro α
    rw [hcoeff]
    split_ifs
    · have h := Rat.den_dvd (a α) (q : ℤ)
      rw [Rat.divInt_eq_div, Int.cast_natCast] at h
      exact Int.natCast_dvd_natCast.mp h
    · simp

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

theorem polynomial_integer_value_common_denominator {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (q : ℕ)
    (hP : ∀ α, ∃ a : ℤ, (a : ℝ) = (q : ℝ) * P.coeff α) (x : σ → ℤ) :
    ∃ a : ℤ, (a : ℝ) = (q : ℝ) * eval (fun j => (x j : ℝ)) P := by
  classical
  choose a ha using hP
  refine ⟨∑ α ∈ P.support, a α * ∏ j, x j ^ α j, ?_⟩
  rw [eval_eq', Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_prod, Int.cast_pow]
  apply Finset.sum_congr rfl
  intro α _
  rw [ha α]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeResidueNiltests
namespace OAI

section

namespace Erdos3.RationalTorus

open CircleFourier
open scoped TensorProduct NNReal

theorem residueObservable_lipschitz {q : ℕ} [NeZero q] (j : ZMod q) :
    LipschitzWith (q : ℝ≥0) (fun v : Fin 1 → CircleFourier.Circle => residueCutoff j (v 0)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  exact ((residueCutoff_lipschitz j).dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (dist_le_pi_dist v w 0) (Nat.cast_nonneg q))

end Erdos3.RationalTorus

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeIntervalCoordinate
namespace OAI

section

namespace Erdos3.RationalTorus

open scoped TensorProduct NNReal

noncomputable def intervalOrbit (N : ℕ) :
    (nilmanifold 1).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
  affineOrbit 1 (fun _ => 0) (fun _ : Unit => fun _ => 1 / (N : ℝ))

theorem intervalOrbit_phase (N : ℕ) [NeZero N] (x : ZMod N) :
    phaseProjection 1 ((nilmanifold 1).cyclicOrbitPoint (intervalOrbit N) N (fun _ : Unit => x)) 0 =
      ZMod.toAddCircle x := by
  unfold RationalFilteredNilmanifold.cyclicOrbitPoint intervalOrbit
  rw [phaseProjection_mk, affineOrbit_phases]
  simp [ZMod.toAddCircle_apply, div_eq_mul_inv]

end Erdos3.RationalTorus

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem squareObservableLipschitz_le_exp (A B K J : ℝ≥0) {p q r : ℝ}
    (hr : 0 ≤ r) (hA : (A : ℝ) ≤ Real.exp r) (hB : (B : ℝ) ≤ Real.exp p)
    (hK : (K : ℝ) ≤ Real.exp p) (hJ : (J : ℝ) ≤ Real.exp q) :
    ((B * (K * J) + B * (K * (A * J)) : ℝ≥0) : ℝ) ≤ Real.exp (2 * p + q + r + 1) := by
  have hfirst : (B : ℝ) * (K * J) ≤ Real.exp (2 * p + q) := by
    calc
      _ ≤ Real.exp p * (Real.exp p * Real.exp q) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hsecond : (B : ℝ) * (K * (A * J)) ≤ Real.exp (2 * p + q + r) := by
    calc
      _ ≤ Real.exp p * (Real.exp p * (Real.exp r * Real.exp q)) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hfirst' := hfirst.trans (Real.exp_le_exp.mpr (by linarith : 2 * p + q ≤ 2 * p + q + r))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  change (B : ℝ) * (K * J) + B * (K * (A * J)) ≤ _
  calc
    _ ≤ 2 * Real.exp (2 * p + q + r) := by linarith
    _ ≤ Real.exp 1 * Real.exp (2 * p + q + r) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem reducedSquareRealRelativePart_of_factors
    (k : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : F.quotientTop.RealPolynomialSymbolGroup w)
    (hk : F.reducedSquareRealSymbolHom w k = 1) :
    F.reducedSquareRealRelativePart w (k * F.reducedSquareRealDiagonalHom w x) = k := by
  change (k * F.reducedSquareRealDiagonalHom w x) *
    (F.reducedSquareRealDiagonalHom w
      (F.reducedSquareRealSymbolHom w (k * F.reducedSquareRealDiagonalHom w x)))⁻¹ = k
  rw [map_mul, F.reducedSquareRealSymbolHom_diagonal, hk, one_mul]
  group

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem realReducedRelativeCoefficient_of_preimage
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hx : F.realReducedRelativeSquareSymbolMap w hw x = (F.reducedSquareRealRelativePart w g).coord) :
    F.realNormalizedFirstCoefficientMap w x = F.realReducedRelativeCoefficient w hw g :=
  commonKernelSubmoduleEquiv_symm_apply (F.realNormalizedFirstCoefficientMap w)
    (F.realReducedRelativeSquareSymbolMap w hw)
    (LinearMap.ker (F.realFirstCoefficientHorizontal w))
    (LinearMap.ker ((F.reducedSquareSndSymbolMap w).toLinearMap.baseChange ℝ))
    (F.realNormalizedFirstCoefficientMap_ker w hw)
    (F.realNormalizedFirstCoefficientMap_range w)
    (F.realReducedRelativeSquareSymbolMap_range w hw) x
    ⟨(F.reducedSquareRealRelativePart w g).coord, F.reducedSquareRealRelativePart_coord_kernel w g⟩ hx

end Erdos3.NilpotentLieFiltration

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

theorem nativePolynomialOrbit_surjective (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    Function.Surjective (F.nativePolynomialOrbit w) := by
  intro q
  obtain ⟨g, hg⟩ := F.realAdaptedPolynomialGroupHom_surjective w b ω hF ⟨⟨q.log, q.property⟩⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  exact congrArg (fun z : (F.realification.adaptedPolynomialFiltration w).Group => z.coord.val) hg

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFirstCoefficientBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realShiftedMonomialBasis_repr (w : σ → ℕ) (k : ℕ)
    (x : F.realShiftedCoefficientSubmodule w k) (z : ShiftedMonomialIndex w ω k) :
    (F.realShiftedMonomialBasis b ω hF w k).repr x z =
      ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x.val z.val :=
  supportedSubmoduleBasis_repr _ _ _ _ x z

theorem realFirstCoefficientBasis_repr_map (w : σ → ℕ)
    (x : F.realShiftedCoefficientSubmodule w 1) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientMap w x) z =
      ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x.val
        ((firstCoefficientSurvivorEquiv w ω).symm z).val.val := by
  rw [realFirstCoefficientBasis, Basis.repr_reindex_apply]
  change (supportedQuotientBasis _ _ _ _).repr
    (((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype).mkQ x) _ = _
  rw [supportedQuotientBasis_repr_mk, F.realShiftedMonomialBasis_repr]

theorem realFirstCoefficientBasis_polynomial_coordinate (w : σ → ℕ)
    (x : F.realShiftedCoefficientSubmodule w 1) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientMap w x) z =
      (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x.val) z.val.1) z.val.2 := by
  rw [F.realFirstCoefficientBasis_repr_map]
  exact (F.realAdaptedPolynomialTensor_coordinates w b ω hF x.val
    ((firstCoefficientSurvivorEquiv w ω).symm z).val.val).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealCoefficientPolynomialProjection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realFirstCoefficientOfPolynomial :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) →ₗ[ℚ] F.RealFirstCoefficientModule w :=
  ((F.realFirstCoefficientBasis b ω hF w).repr.symm.restrictScalars ℚ).toLinearMap.comp
    (supportedCoordinates (b.baseChange ℝ)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 + 1 = ω z.2})

theorem realFirstCoefficientOfPolynomial_coordinate
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr
      (F.realFirstCoefficientOfPolynomial b ω hF w p) z =
      (b.baseChange ℝ).repr (coefficients p z.val.1) z.val.2 := by
  change ((F.realFirstCoefficientBasis b ω hF w).repr
    ((F.realFirstCoefficientBasis b ω hF w).repr.symm _)) z = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem realFirstCoefficientOfPolynomial_map (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x.val) =
      F.realFirstCoefficientMap w x := by
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [F.realFirstCoefficientOfPolynomial_coordinate, F.realFirstCoefficientBasis_polynomial_coordinate]

theorem realFirstCoefficientOfPolynomial_eq_of_firstJet
    (p q : F.realification.adaptedLieSubalgebra w)
    (hpq : F.realification.filteredFirstJetMap w p = F.realification.filteredFirstJetMap w q) :
    F.realFirstCoefficientOfPolynomial b ω hF w p.val =
      F.realFirstCoefficientOfPolynomial b ω hF w q.val := by
  have hdiff := (F.realification.filteredFirstJetMap_eq_iff w p q).mp hpq
  apply (F.realFirstCoefficientBasis b ω hF w).repr.injective
  ext z
  rw [F.realFirstCoefficientOfPolynomial_coordinate, F.realFirstCoefficientOfPolynomial_coordinate]
  have hc := (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp (hdiff z.val.1)
    z.val.2 (by have hz := z.property; omega)
  rw [map_sub, Finsupp.sub_apply, map_sub, Finsupp.sub_apply] at hc
  exact sub_eq_zero.mp hc

include b ω hF in
theorem realShiftedCoefficient_mem_iff_tensor (k : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    x ∈ F.realShiftedCoefficientSubmodule w k ↔
      F.realAdaptedPolynomialTensor w x ∈ F.realification.shiftedPolynomialIdeal w k := by
  rw [F.realShiftedCoefficient_eq_span b ω hF, basis_mem_span_image_iff]
  constructor
  · intro hx α
    apply (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mpr
    intro i hi
    by_cases hai : Finsupp.weight w α ≤ ω i
    · change (b.baseChange ℝ).repr (coefficients (F.realAdaptedPolynomialMap w x) α) i = 0
      rw [F.realAdaptedPolynomialTensor_coordinates w b ω hF x ⟨(α, i), hai⟩]
      exact hx ⟨(α, i), hai⟩ hi
    · exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
        ((F.realAdaptedPolynomialTensor w x).property α) i hai
  · intro hx z hz
    rw [← F.realAdaptedPolynomialTensor_coordinates w b ω hF x z]
    exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp (hx z.val.1) z.val.2 hz

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FirstCoefficientDerivativeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realAdaptedPolynomialTensor_injective (w : σ → ℕ) :
    Function.Injective (F.realAdaptedPolynomialTensor w) := by
  intro x y hxy
  apply ((F.adaptedMonomialBasis e ω hF w).baseChange ℝ).repr.injective
  apply Finsupp.ext
  intro z
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra w =>
    (e.baseChange ℝ).repr (VectorPolynomial.coefficients p.val z.val.1) z.val.2) hxy
  exact (F.realAdaptedPolynomialTensor_coordinates w e ω hF x z).symm.trans
    (hc.trans (F.realAdaptedPolynomialTensor_coordinates w e ω hF y z))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def FirstCoefficientGrid (w : σ → ℕ) (l : ℕ) (x : F.RealFirstCoefficientModule w) : Prop :=
  (fun z : FirstCoefficientIndex w ω => (F.realFirstCoefficientBasis b ω hF w).repr x z) ∈
    realDenominatorGrid l

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem realAdaptedConstant_tensor (x : ℝ ⊗[ℚ] L) :
    F.realAdaptedPolynomialTensor w (F.realAdaptedConstant w x) =
      F.realification.adaptedConstant w x := by
  classical
  change F.realAdaptedPolynomialTensor w (F.realAdaptedConstant w x) =
    F.realification.adaptedConstantLieHom w x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    apply Subtype.ext
    apply coefficients.injective
    ext α
    change coefficients (F.realAdaptedPolynomialMap w (r ⊗ₜ[ℚ] F.adaptedConstant w x)) α =
      coefficients (monomial 0 (r ⊗ₜ[ℚ] x)) α
    rw [F.realAdaptedPolynomialMap_coefficient_tmul]
    change r ⊗ₜ[ℚ] coefficients (monomial 0 x) α = _
    simp only [coefficients_monomial, Finsupp.single_apply]
    split_ifs <;> simp

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realFirstCoefficientOfPolynomial_constant (x : ℝ ⊗[ℚ] L) :
    F.realFirstCoefficientOfPolynomial b ω hF w (monomial 0 x) =
      F.realFirstCoefficientConstant w x := by
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra w => p.val)
    (F.realAdaptedConstant_tensor w x)
  change F.realAdaptedPolynomialMap w (F.realAdaptedConstant w x) = monomial 0 x at hc
  rw [← hc]
  exact F.realFirstCoefficientOfPolynomial_map b ω hF w
    ⟨F.realAdaptedConstant w x, F.realAdaptedConstant_mem_first w x⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realFirstCoefficientOfPolynomial_adjoint (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientOfPolynomial b ω hF w
      (dualAdjoint (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialTensor w x.val)).val =
      F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientMap w x) := by
  rw [← F.realAdaptedAdjoint_tensor, F.realFirstCoefficientAdjoint_map]
  let y : F.realShiftedCoefficientSubmodule w 1 :=
    ⟨dualAdjoint g x.val, dualAdjoint_real_mem_of_invariant ⊤ _
      (fun a _ c hc => F.realShiftedCoefficient_lie_mem w 1 a c hc) g (by trivial) x.val x.property⟩
  change F.realFirstCoefficientOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w y.val) =
    F.realFirstCoefficientMap w y
  exact F.realFirstCoefficientOfPolynomial_map b ω hF w y

theorem realFirstCoefficientOfPolynomial_adjoint_constant (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] L) :
    F.realFirstCoefficientOfPolynomial b ω hF w
      (dualAdjoint (F.realAdaptedPolynomialGroupHom w g) (F.realification.adaptedConstant w x)).val =
      F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientConstant w x) := by
  rw [← F.realAdaptedConstant_tensor]
  exact F.realFirstCoefficientOfPolynomial_adjoint b ω hF w g
    ⟨F.realAdaptedConstant w x, F.realAdaptedConstant_mem_first w x⟩

variable [Fintype σ]

theorem realFirstCoefficientOfPolynomial_logDerivative (h : σ → ℚ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
      (F.realification.adaptedLogDerivative h (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val =
      F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) := by
  rw [← F.realAdaptedLogDerivative_tensor, F.realFirstCoefficientDirectionMap_rat]
  let y : F.realShiftedCoefficientSubmodule (fun _ : σ => 1) 1 :=
    ⟨F.realAdaptedLogDerivative h g.coord, F.realAdaptedLogDerivative_mem_first h g.coord⟩
  change F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
    (F.realAdaptedPolynomialMap (fun _ => 1) y.val) = F.realFirstCoefficientMap (fun _ => 1) y
  exact F.realFirstCoefficientOfPolynomial_map b ω hF (fun _ => 1) y

theorem realFirstCoefficientOfPolynomial_normalizedRelativeLog (h : σ → ℚ)
    (e m : ℝ ⊗[ℚ] L) (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
      (F.realification.normalizedRelativeLog h e m
        (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val =
      F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
        F.realFirstCoefficientConstant (fun _ => 1) e -
        F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) := by
  have he := F.realification.filteredFirstJet_normalizedRelativeLog h e m
    (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)
  rw [F.realFirstCoefficientOfPolynomial_eq_of_firstJet b ω hF (fun _ => 1) _ _ he]
  change F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
    ((F.realification.adaptedLogDerivative h
        (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val - monomial 0 e -
      (dualAdjoint (F.realAdaptedPolynomialGroupHom (fun _ => 1) g)
        (F.realification.adaptedConstant (fun _ => 1) m)).val) = _
  rw [map_sub, map_sub, F.realFirstCoefficientOfPolynomial_logDerivative,
    F.realFirstCoefficientOfPolynomial_constant, F.realFirstCoefficientOfPolynomial_adjoint_constant]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def normalizedRelativeInFirst :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.shiftedPolynomialIdeal w 1 :=
  (F.normalizedRelativeSubmodule w).subtype.codRestrict
    (F.shiftedPolynomialIdeal w 1).toSubmodule (fun p => p.property.1)

noncomputable def realNormalizedRelativeInFirst :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) →ₗ[ℝ] F.realShiftedCoefficientSubmodule w 1 :=
  (realificationSubmoduleEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule).toLinearMap.comp
    ((F.normalizedRelativeInFirst w).baseChange ℝ)

theorem realNormalizedRelativeInFirst_coe (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    (F.realNormalizedRelativeInFirst w x).val = (F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x := by
  change (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype.baseChange ℝ
    ((F.normalizedRelativeInFirst w).baseChange ℝ x) = _
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  rfl

theorem realNormalizedFirstCoefficientMap_eq (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realNormalizedFirstCoefficientMap w x =
      F.realFirstCoefficientMap w (F.realNormalizedRelativeInFirst w x) := by
  change F.firstCoefficientRealEquiv w
    (((F.firstCoefficientMap w).comp (F.normalizedRelativeInFirst w)).baseChange ℝ x) = _
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply, F.firstCoefficientRealEquiv_map]
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealSquarePolynomialFactors
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem realSquareFstPolynomialHom_polynomial (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
      VectorPolynomial.map ((realificationLieHom F.squareFst).toLinearMap.restrictScalars ℚ)
        (F.squareFiltration.realAdaptedPolynomialMap w r.coord) :=
  F.squareFiltration.realFilteredPolynomialMap_polynomial F F.squareFst (fun _ _ hx => hx.1) w r.coord

theorem realSquareSndPolynomialHom_polynomial (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    F.realAdaptedPolynomialMap w (F.realSquareSndPolynomialHom w r).coord =
      VectorPolynomial.map ((realificationLieHom F.squareSnd).toLinearMap.restrictScalars ℚ)
        (F.squareFiltration.realAdaptedPolynomialMap w r.coord) :=
  F.squareFiltration.realFilteredPolynomialMap_polynomial F F.squareSnd (fun _ _ hx => hx.2.1) w r.coord

theorem realSquarePolynomial_ext {r q : F.squareFiltration.RealAdaptedPolynomialGroup w}
    (hf : F.realSquareFstPolynomialHom w r = F.realSquareFstPolynomialHom w q)
    (hs : F.realSquareSndPolynomialHom w r = F.realSquareSndPolynomialHom w q) : r = q := by
  let P := (F.squareFstPolynomialMap w).toLinearMap.prod (F.squareSndPolynomialMap w).toLinearMap
  have hP : Function.Injective P := by
    intro x y hxy
    exact F.square_polynomial_ext w (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  have hPR := Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) P hP
  apply NilpotentLieBCHGroup.ext
  apply hPR
  apply (TensorProduct.prodRight ℚ ℝ ℝ (F.adaptedLieSubalgebra w) (F.adaptedLieSubalgebra w)).injective
  change TensorProduct.prodRight ℚ ℝ ℝ _ _ (P.baseChange ℝ r.coord) =
    TensorProduct.prodRight ℚ ℝ ℝ _ _ (P.baseChange ℝ q.coord)
  rw [realification_prod, realification_prod]
  exact Prod.ext (congrArg NilpotentLieBCHGroup.coord hf) (congrArg NilpotentLieBCHGroup.coord hs)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem exists_realSquarePolynomial_lift (p : F.squareFiltration.realification.adaptedLieSubalgebra w) :
    ∃ r : F.squareFiltration.RealAdaptedPolynomialGroup w,
      F.squareFiltration.realAdaptedPolynomialMap w r.coord = p.val ∧
      F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
        VectorPolynomial.map ((realificationLieHom F.squareFst).toLinearMap.restrictScalars ℚ) p.val ∧
      F.realAdaptedPolynomialMap w (F.realSquareSndPolynomialHom w r).coord =
        VectorPolynomial.map ((realificationLieHom F.squareSnd).toLinearMap.restrictScalars ℚ) p.val := by
  obtain ⟨x, hx⟩ := F.squareFiltration.realAdaptedPolynomialTensor_surjective w
    (F.adaptedSquareBasis b ω (hF 2)) (squareBasisWeight ω) (F.adaptedSquareBasis_layers b ω hF) p
  have hp := congrArg (fun z : F.squareFiltration.realification.adaptedLieSubalgebra w => z.val) hx
  change F.squareFiltration.realAdaptedPolynomialMap w x = p.val at hp
  refine ⟨⟨x⟩, hp, ?_, ?_⟩
  · rw [F.realSquareFstPolynomialHom_polynomial, hp]
  · rw [F.realSquareSndPolynomialHom_polynomial, hp]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedPolynomialMap_coefficient
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedPolynomialMap w x) α = (F.adaptedCoefficientMap w α).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r p => rw [F.realAdaptedPolynomialMap_coefficient_tmul]; rfl

include b ω hF in
theorem realNormalizedRelative_mem_iff_tensor
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    x ∈ (F.normalizedRelativeSubmodule w).baseChange ℝ ↔
      F.realAdaptedPolynomialTensor w x ∈ F.realification.normalizedRelativeSubmodule w := by
  change x ∈ ((F.shiftedAdaptedIdeal w).toSubmodule ⊓
    (F.layer 2).comap (F.adaptedCoefficientMap w 0)).baseChange ℝ ↔ _
  rw [realification_inf, realification_comap]
  change (x ∈ F.realShiftedCoefficientSubmodule w 1 ∧
    (F.adaptedCoefficientMap w 0).baseChange ℝ x ∈ F.realification.layer 2) ↔
    (F.realAdaptedPolynomialTensor w x ∈ F.realification.shiftedPolynomialIdeal w 1 ∧
      coefficients (F.realAdaptedPolynomialMap w x) 0 ∈ F.realification.layer 2)
  rw [F.realShiftedCoefficient_mem_iff_tensor b ω hF,
    F.realAdaptedPolynomialMap_coefficient]

include b ω hF in
theorem realNormalizedRelative_polynomial_surjective
    (p : F.realification.normalizedRelativeSubmodule w) :
    ∃ x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w,
      F.realAdaptedPolynomialTensor w ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x) = p.val := by
  obtain ⟨x, hx⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p.val
  have hmem : x ∈ (F.normalizedRelativeSubmodule w).baseChange ℝ := by
    apply (F.realNormalizedRelative_mem_iff_tensor b ω hF w x).mpr
    rw [hx]
    exact p.property
  let y := (realificationSubmoduleEquiv (F.normalizedRelativeSubmodule w)).symm ⟨x, hmem⟩
  have hy : (F.normalizedRelativeSubmodule w).subtype.baseChange ℝ y = x :=
    congrArg Subtype.val ((realificationSubmoduleEquiv (F.normalizedRelativeSubmodule w)).apply_symm_apply ⟨x, hmem⟩)
  exact ⟨y, by rw [hy]; exact hx⟩

theorem realFirstCoefficientOfPolynomial_normalized
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realFirstCoefficientOfPolynomial b ω hF w
      (F.realAdaptedPolynomialMap w ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x)) =
      F.realNormalizedFirstCoefficientMap w x := by
  rw [F.realNormalizedFirstCoefficientMap_eq, ← F.realNormalizedRelativeInFirst_coe]
  exact F.realFirstCoefficientOfPolynomial_map b ω hF w _

variable [Fintype σ]

include b ω hF in
theorem exists_real_normalizedRelative_preimage (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hzero : coefficients (normalizedShiftLog (s + 1) h (-e) (-m)
      (F.realAdaptedPolynomialMap (fun _ => 1) g.coord) -
        F.realAdaptedPolynomialMap (fun _ => 1) g.coord) 0 ∈ F.realification.layer 2) :
    ∃ x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule (fun _ : σ => 1),
      F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
          F.realification.normalizedRelativeLog h e m
            (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) ∧
      F.realNormalizedFirstCoefficientMap (fun _ => 1) x =
        F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          F.realFirstCoefficientConstant (fun _ => 1) e -
          F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) := by
  have hmem := F.realification.normalizedRelativeLog_mem h e m
    (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) hzero
  obtain ⟨x, hx⟩ := F.realNormalizedRelative_polynomial_surjective b ω hF (fun _ => 1) ⟨_, hmem⟩
  refine ⟨x, hx, ?_⟩
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => p.val) hx
  have he := F.realFirstCoefficientOfPolynomial_normalized b ω hF (fun _ => 1) x
  change F.realAdaptedPolynomialMap (fun _ => 1)
      ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
    (F.realification.normalizedRelativeLog h e m
      (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val at hc
  rw [hc] at he
  exact he.symm.trans (F.realFirstCoefficientOfPolynomial_normalizedRelativeLog b ω hF h e m g)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realSquareDiagonalPolynomialHom :
    F.RealAdaptedPolynomialGroup w →* F.squareFiltration.RealAdaptedPolynomialGroup w :=
  realificationMap (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (F.squareFiltration.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (F.squareDiagonalPolynomialMap w)

noncomputable def realRelativeSquarePolynomial (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.squareFiltration.RealAdaptedPolynomialGroup w :=
  ⟨(F.relativeSquareLift w hw).baseChange ℝ x⟩

theorem realSquareFstPolynomialHom_diagonal (g : F.RealAdaptedPolynomialGroup w) :
    F.realSquareFstPolynomialHom w (F.realSquareDiagonalPolynomialHom w g) = g := by
  have hcomp : (F.squareFstPolynomialMap w).toLinearMap.comp
      (F.squareDiagonalPolynomialMap w).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro p
    exact F.squareFstPolynomialMap_diagonal w p
  apply NilpotentLieBCHGroup.ext
  change (F.squareFstPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.squareDiagonalPolynomialMap w).toLinearMap.baseChange ℝ g.coord) = g.coord
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_id,
    LinearMap.id_apply]

theorem realSquareSndPolynomialHom_diagonal (g : F.RealAdaptedPolynomialGroup w) :
    F.realSquareSndPolynomialHom w (F.realSquareDiagonalPolynomialHom w g) = g := by
  have hcomp : (F.squareSndPolynomialMap w).toLinearMap.comp
      (F.squareDiagonalPolynomialMap w).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro p
    exact F.squareSndPolynomialMap_diagonal w p
  apply NilpotentLieBCHGroup.ext
  change (F.squareSndPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.squareDiagonalPolynomialMap w).toLinearMap.baseChange ℝ g.coord) = g.coord
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_id,
    LinearMap.id_apply]

theorem realSquareFstPolynomialHom_relative (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realSquareFstPolynomialHom w (F.realRelativeSquarePolynomial w hw x) =
      (⟨(F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x⟩ : F.RealAdaptedPolynomialGroup w) := by
  have hcomp : (F.squareFstPolynomialMap w).toLinearMap.comp (F.relativeSquareLift w hw) =
      (F.normalizedRelativeSubmodule w).subtype := by
    apply LinearMap.ext
    intro p
    exact F.squareFstPolynomialMap_relative w hw p
  apply NilpotentLieBCHGroup.ext
  change (F.squareFstPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.relativeSquareLift w hw).baseChange ℝ x) = _
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp]

theorem realSquareSndPolynomialHom_relative (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realSquareSndPolynomialHom w (F.realRelativeSquarePolynomial w hw x) = 1 := by
  have hcomp : (F.squareSndPolynomialMap w).toLinearMap.comp (F.relativeSquareLift w hw) = 0 := by
    apply LinearMap.ext
    intro p
    exact F.squareSndPolynomialMap_relative w hw p
  apply NilpotentLieBCHGroup.ext
  change (F.squareSndPolynomialMap w).toLinearMap.baseChange ℝ
    ((F.relativeSquareLift w hw).baseChange ℝ x) = 0
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_zero,
    LinearMap.zero_apply]

theorem realSquarePolynomial_factorization (hw : ∀ i, 0 < w i)
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (g : F.RealAdaptedPolynomialGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hf : F.realSquareFstPolynomialHom w r =
      (⟨(F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x⟩ : F.RealAdaptedPolynomialGroup w) * g)
    (hs : F.realSquareSndPolynomialHom w r = g) :
    r = F.realRelativeSquarePolynomial w hw x * F.realSquareDiagonalPolynomialHom w g := by
  apply F.realSquarePolynomial_ext w
  · rw [map_mul, F.realSquareFstPolynomialHom_relative, F.realSquareFstPolynomialHom_diagonal, hf]
  · rw [map_mul, F.realSquareSndPolynomialHom_relative, F.realSquareSndPolynomialHom_diagonal, one_mul, hs]

theorem realSquareDifference_mem_two (x : ℝ ⊗[ℚ] F.squareLieSubalgebra) :
    realificationLieHom F.squareFst x - realificationLieHom F.squareSnd x ∈ F.realification.layer 2 := by
  rw [← F.realifiedSquareEquiv_fst, ← F.realifiedSquareEquiv_snd]
  exact (F.realification.mem_squareLieSubalgebra (F.realifiedSquareEquiv x).val).mp
    (F.realifiedSquareEquiv x).property

theorem realSquarePolynomial_horizontal (r : F.squareFiltration.RealAdaptedPolynomialGroup w) :
    coefficients (F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord -
      F.realAdaptedPolynomialMap w (F.realSquareSndPolynomialHom w r).coord) 0 ∈ F.realification.layer 2 := by
  rw [map_sub, Finsupp.sub_apply, F.realSquareFstPolynomialHom_polynomial,
    F.realSquareSndPolynomialHom_polynomial, coefficients_map, coefficients_map]
  exact F.realSquareDifference_mem_two _

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem realAdaptedPolynomialGroupHom_injective :
    Function.Injective (F.realAdaptedPolynomialGroupHom w) := by
  intro g h hgh
  apply NilpotentLieBCHGroup.ext
  apply F.realAdaptedPolynomialTensor_injective b ω hF w
  exact congrArg NilpotentLieBCHGroup.coord hgh

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSquareOrbit
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem nativeSquareOrbit_fst (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (x : σ → ℤ) :
    F.realSquareFstHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.squareFiltration.nativePolynomialOrbit w r)) =
        F.realification.polynomialOrbitEval w x
          (F.nativePolynomialOrbit w (F.realSquareFstPolynomialHom w r)) := by
  apply NilpotentLieBCHGroup.ext
  have h := congrArg (eval (fun i => (x i : ℚ))) (F.realSquareFstPolynomialHom_polynomial w r)
  rw [eval_map] at h
  exact h.symm

theorem nativeSquareOrbit_snd (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (x : σ → ℤ) :
    F.realSquareSndHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.squareFiltration.nativePolynomialOrbit w r)) =
        F.realification.polynomialOrbitEval w x
          (F.nativePolynomialOrbit w (F.realSquareSndPolynomialHom w r)) := by
  apply NilpotentLieBCHGroup.ext
  have h := congrArg (eval (fun i => (x i : ℚ))) (F.realSquareSndPolynomialHom_polynomial w r)
  rw [eval_map] at h
  exact h.symm

theorem nativeNormalizedSquareOrbit_fst (h : σ → ℤ) (ε γ : F.realification.Group)
    (g : F.RealAdaptedPolynomialGroup w) (r : F.squareFiltration.RealAdaptedPolynomialGroup w)
    (hf : F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
      normalizedShiftLog s (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
        (F.realAdaptedPolynomialMap w g.coord)) (x : σ → ℤ) :
    F.realSquareFstHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.squareFiltration.nativePolynomialOrbit w r)) =
        ε⁻¹ * F.realification.polynomialOrbitEval w (fun i => x i + h i)
          (F.nativePolynomialOrbit w g) * γ⁻¹ := by
  rw [F.nativeSquareOrbit_fst, mul_assoc]
  apply NilpotentLieBCHGroup.ext
  have hh := congrArg (eval (fun i => (x i : ℚ))) hf
  rw [eval_normalizedShiftLog] at hh
  change eval (fun i => (x i : ℚ))
      (F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord) =
    lieBCH s (-ε.coord)
      (lieBCH s (eval (fun i => ((x i + h i : ℤ) : ℚ))
        (F.realAdaptedPolynomialMap w g.coord)) (-γ.coord))
  simpa only [Int.cast_add] using hh

theorem nativeNormalizedSquareObservable_product (Γ : Subgroup F.Group)
    (h : σ → ℤ) (ε γ : F.realification.Group)
    (hγ : γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom)
    (u : F.realification.Group ⧸ Γ.map NilpotentLieBCHGroup.realificationHom → ℂ)
    (g : F.RealAdaptedPolynomialGroup w) (r : F.squareFiltration.RealAdaptedPolynomialGroup w)
    (hf : F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
      normalizedShiftLog s (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
        (F.realAdaptedPolynomialMap w g.coord))
    (hs : F.realSquareSndPolynomialHom w r = g) (x : σ → ℤ) :
    F.realSquareObservable Γ ε u
      (QuotientGroup.mk (F.squareFiltration.realification.polynomialOrbitEval w x
        (F.squareFiltration.nativePolynomialOrbit w r))) =
      u (QuotientGroup.mk (F.realification.polynomialOrbitEval w (fun i => x i + h i)
        (F.nativePolynomialOrbit w g))) *
      star (u (QuotientGroup.mk (F.realification.polynomialOrbitEval w x
        (F.nativePolynomialOrbit w g)))) := by
  apply F.realSquareObservable_recovers_product Γ ε γ _ _ hγ u
  · exact F.nativeNormalizedSquareOrbit_fst w h ε γ g r hf x
  · rw [F.nativeSquareOrbit_snd, hs]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealReducedSquarePolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem adaptedReducedRealSymbolHom_square_diagonal (g : F.RealAdaptedPolynomialGroup w) :
    F.squareFiltration.adaptedReducedRealSymbolHom w (F.realSquareDiagonalPolynomialHom w g) =
      F.reducedSquareRealDiagonalHom w (F.adaptedReducedRealSymbolHom w g) := by
  have hcomp : (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.comp
      (F.squareDiagonalPolynomialMap w).toLinearMap =
        (F.reducedSquareDiagonalSymbolMap w).toLinearMap.comp (F.adaptedReducedSymbolMap w).toLinearMap := by
    apply LinearMap.ext
    intro p
    change F.reducedSquareSymbolMap w
        (F.squareFiltration.polynomialSymbolMap w (F.squareDiagonalPolynomialMap w p)) =
      F.reducedSquareDiagonalSymbolMap w (F.quotientTopSymbolMap w (F.polynomialSymbolMap w p))
    rw [← F.squareDiagonalSymbolMap_symbol, F.reducedSquareDiagonalSymbolMap_quotient]
  apply NilpotentLieBCHGroup.ext
  change (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
    ((F.squareDiagonalPolynomialMap w).toLinearMap.baseChange ℝ g.coord) =
      (F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ
        ((F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ g.coord)
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_comp,
    LinearMap.comp_apply]

theorem adaptedReducedRealSymbolHom_square_relative (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.squareFiltration.adaptedReducedRealSymbolHom w (F.realRelativeSquarePolynomial w hw x) =
      (⟨F.realReducedRelativeSquareSymbolMap w hw x⟩ :
        F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) := by
  have hcomp : (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.comp
      (F.relativeSquareLift w hw) = F.reducedRelativeSquareSymbolMap w hw := by
    apply LinearMap.ext
    intro p
    rfl
  apply NilpotentLieBCHGroup.ext
  change (F.squareFiltration.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ
    ((F.relativeSquareLift w hw).baseChange ℝ x) = (F.reducedRelativeSquareSymbolMap w hw).baseChange ℝ x
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCommonFamily
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

universe uσ uι uL

def NativeNormalizedSquareSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (p : ℝ) (_hp : 0 ≤ p) (_hD : D.GeometryComplexityLE p)
    (h : σ → ℚ) (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
    ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
      (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
      ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
        D.filtration.realAdaptedPolynomialMap (fun _ => 1)
            (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
          normalizedShiftLog (s + 1) h (-ε.coord) (-γ.coord)
            (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
        D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
        D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
            D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
            D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
              (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
          D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
            (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_many_biased_box_shifts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) (hT : ∀ i, 0 < T i) (u : (ι → ℤ) → ℂ)
    {p : ℝ} (_hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hu : ∀ x ∈ translatedIntegerBox a T, ‖u x‖ ≤ Real.exp p)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox a T, u x‖) :
    ∃ H : Finset (ι → ℤ), H.Nonempty ∧
      Real.exp (-(4 * p + 6)) * (∏ i, (T i : ℝ)) ≤ H.card ∧
      ∀ h ∈ H,
        (∀ i, |(h i : ℝ)| ≤ T i) ∧
        (∀ i, Real.exp (-(5 * p + 6)) * T i < (((T i : ℤ) - |h i|).toNat : ℝ)) ∧
        Real.exp (-(2 * p + 1)) ≤
          ‖𝔼 x ∈ derivativeSupport (translatedIntegerBox a T) h, u (x + h) * star (u x)‖ := by
  classical
  let : ∀ i, NeZero (T i) := fun i => ⟨(hT i).ne'⟩
  let Q := translatedIntegerBox a T
  let δ := Real.exp (-(5 * p + 6))
  let P := fun h : ι → ℤ =>
    Real.exp (-p) ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
      (multiplicativeDerivative (fun _ : ι → ℤ => 1) h) (multiplicativeDerivative u h)‖ ∧
    δ * Q.card < ((derivativeSupport Q h).card : ℝ)
  let H := (cubeDifferenceSupport Q).filter P
  have hQ : Q.Nonempty := translatedIntegerBox_nonempty T a
  have hcorr : Real.exp (-p) ≤ ‖finiteCorrelation Q (fun _ => 1) u‖ := by
    rw [norm_finiteCorrelation_one]
    exact hbias
  have hw := weight_correlating_large_box_overlaps a T (fun _ => 1) u
    (Real.exp_nonneg (-p)) (Real.exp_pos (p + 1)) (Real.exp_nonneg (-(5 * p + 6)))
    (fun _ _ => by norm_num) (fun x hx => (hu x hx).trans (Real.exp_le_exp.mpr (by linarith))) hcorr
  have hret := retained_exponential_weight (Fintype.card ι) (r := p) hι
  have hμ : Real.exp (-(4 * p + 6)) ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if P h then (1 : ℝ) else 0) := by
    have he₁ : 2 * p + 2 * p + 6 = 4 * p + 6 := by ring
    have he₂ : 4 * p + 6 + p = 5 * p + 6 := by ring
    have hret' : Real.exp (-(4 * p + 6)) ≤
        Real.exp (-p) ^ 2 / (2 * Real.exp (p + 1) ^ 2) -
          (2 : ℝ) ^ Fintype.card ι * Real.exp (-(5 * p + 6)) := by
      simpa only [he₁, he₂] using hret
    exact hret'.trans hw
  have hcount : Real.exp (-(4 * p + 6)) * (∏ i, (T i : ℝ)) ≤ H.card := by
    have hc := cardinality_ge_overlap_weight hQ (cubeDifferenceSupport Q) P hμ
    simpa only [H, Q, translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod] using hc
  have hnonempty : H.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < H.card :=
      (mul_pos (Real.exp_pos _) (Finset.prod_pos (fun i _ => by exact_mod_cast hT i))).trans_le hcount
    exact_mod_cast hpos
  refine ⟨H, hnonempty, hcount, ?_⟩
  intro h hh
  obtain ⟨hsupport, hc, hlarge⟩ := Finset.mem_filter.mp hh
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi := box_overlap_length_pos a T hsupport i
    have habs : |h i| ≤ (T i : ℤ) := by omega
    exact_mod_cast habs
  · exact box_overlap_side_gt_of_card_gt a T hT h hlarge
  · have he : Real.exp (-p) ^ 2 = Real.exp (-2 * p) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hsmall : Real.exp (-(2 * p + 1)) ≤ Real.exp (-p) ^ 2 / 2 := by
      have he' : -(2 * p + 1) = -2 * p - 1 := by ring
      rw [he, he']
      exact exp_sub_one_le_half_exp (-2 * p)
    rw [finiteCorrelation_one_derivative] at hc
    exact hsmall.trans hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankBracketFactorizationMonotone
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

theorem real_refiltered_rank_bracket_frequency (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ D.filtration.AssociatedGraded) (ξ η : L →ₗ[ℚ] ℚ)
    (hξ : ∀ x ∈ U,
      basisGradeProjection (D.filtration.associatedGradedBasis b ω hF) ω s x = x →
        D.filtration.gradedFrequency b ω hF ξ x = 0)
    (hrestrict : ∀ x ∈ R.filtration.layer s r, ξ x = η x)
    (d : I → ℕ) (a : FreeMagma I) (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (v : I → ℝ ⊗[ℚ] L) (hv : ∀ i, v i ∈ D.filtration.realGradedRefiltrationLayer U (d i)) :
    realifyFunctional η (lieTreeEval v a) = 0 := by
  have htop : lieTreeEval v a ∈ D.filtration.realGradedRefiltrationLayer U s := by
    simpa only [hd] using D.filtration.real_refiltered_lieTreeEval_mem U d v hv a
  have hleaves (i : I) : v i ∈ R.filtration.realification.layer (d i) 1 := by
    have h : v i ∈ D.filtration.realification.layer (d i) :=
      D.filtration.realGradedRefiltrationLayer_le U (d i) (hv i)
    rw [← R.real_associated] at h
    change v i ∈ R.filtration.realification.layer (d i) 0 at h
    rwa [R.filtration.realification.rank_zero_eq_one] at h
  have hrank : lieTreeEval v a ∈ (R.filtration.layer s r).baseChange ℝ := by
    have h : lieTreeEval v a ∈ R.filtration.realification.layer s r := by
      simpa only [hd, hr] using R.filtration.realification.lieTreeEval_mem_length v d hleaves a
    exact h
  rw [← realifyFunctional_eq_on_submodule (R.filtration.layer s r) ξ η hrestrict _ hrank]
  exact D.filtration.real_frequency_zero_on_refiltered_top b ω hF U ξ hξ _ htop

end RationalFilteredNilmanifold.DegreeRankStructure

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

def ControlledRankBracketFactorization (_R : D.DegreeRankStructure r) (ω : Fin n → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (η : L →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) : Prop :=
  ∃ (m : ℕ) (A P B : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (U : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : Fin n → D.filtration.AssociatedGraded),
    0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ A * P * B = X ∧
    D.filtration.SymbolSlowBound D.basis ω hF (fun _ => 1) T (Real.exp p) A ∧
    D.filtration.SymbolRationalGrid D.basis ω hF (fun _ => 1) m B ∧
    Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
    BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
    (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v i) j) ≤ p) ∧
    (∀ (k : ℕ) (d : Fin k → ℕ) (a : FreeMagma (Fin k)),
      lieTreeWeight d a = s → a.length = r →
      ∀ u : Fin k → ℝ ⊗[ℚ] L,
        (∀ i, u i ∈ D.filtration.realGradedRefiltrationLayer U (d i)) →
        realifyFunctional η (lieTreeEval u a) = 0) ∧
    P.coord ∈ realificationLieSubalgebra (D.filtration.symbolPointwiseSubalgebra D.basis ω hF (fun _ => 1) U)

theorem controlledRankBracketFactorization_of_frequency_restriction (ω : Fin n → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (ξ η : L →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (h : D.filtration.ControlledSymbolFactorization D.basis ω hF ξ T X p)
    (hrestrict : ∀ x ∈ R.filtration.layer s r, ξ x = η x) :
    R.ControlledRankBracketFactorization ω hF η T X p := by
  obtain ⟨m, A, P, B, U, v, hm, hmp, hprod, hA, hB, hv, hU, hheight, hξ, hP⟩ := h
  refine ⟨m, A, P, B, U, v, hm, hmp, hprod, hA, hB, hv, hU, hheight, ?_, hP⟩
  intro k d a hd hr u hu
  exact R.real_refiltered_rank_bracket_frequency D.basis ω hF U ξ η hξ hrestrict d a hd hr u hu

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)
  (ω : Fin n → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))

theorem ControlledRankBracketFactorization.exists_in {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : R.ControlledRankBracketFactorization ω hF η T X p) :
    ∃ (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : Fin n → D.filtration.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v i) j) ≤ p) ∧
      (∀ (k : ℕ) (d : Fin k → ℕ) (a : FreeMagma (Fin k)),
        lieTreeWeight d a = s → a.length = r → ∀ u : Fin k → ℝ ⊗[ℚ] L,
        (∀ i, u i ∈ D.filtration.realGradedRefiltrationLayer U (d i)) →
        realifyFunctional η (lieTreeEval u a) = 0) ∧
      D.filtration.SymbolFactorizationIn D.basis ω hF T X p l U := by
  obtain ⟨l, A, P, B, U, v, hl, hlp, hprod, hA, hB, hv, hU, hh, hker, hP⟩ := h
  exact ⟨l, U, v, hl, hlp, hv, hU, hh, hker, A, P, B, hprod, hA, hB, hP⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)
  (ω : Fin n → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))

theorem ControlledRankBracketFactorization.mono {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ}
    (h : R.ControlledRankBracketFactorization ω hF η T X p) (hpq : p ≤ q)
    (hT : ∀ i, 0 < T i) : R.ControlledRankBracketFactorization ω hF η T X q := by
  obtain ⟨m, A, P, B, U, v, hm, hmp, hprod, hA, hB, hv, hU, hh, hη, hP⟩ := h
  exact ⟨m, A, P, B, U, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    D.filtration.symbolSlowBound_mono D.basis ω hF (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hpq) A hA,
    hB, hv, hU, (fun i j => (hh i j).trans hpq), hη, hP⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
end


