-- Prove2me | Definitions.Def_OAIE3v2B202
-- name    : OAIE3v2B202
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:06:14.812999+00:00
-- url     : https://prove2.me/theorems/cc094170-258c-4af5-983c-b12c94354383
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 206 of 311
-- statement:
--   Definitions bundle 206 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B179`, `OAIE3v2B180`, `OAIE3v2B182`, `OAIE3v2B184`, `OAIE3v2B185`, `OAIE3v2B186` of this split.
--
--   Modules: `Estimates/CubicAntisymmetricTransfer.lean`, `Estimates/NativeDilationDescent.lean`, `Estimates/NativeDilationObservable.lean`, `Estimates/NativeMultilinearQuadruples.lean`, `Estimates/NativeMultilinearityCorrelation.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/UniformControlledCurrentStage.lean`, `Fourier/DilationFrequencyPhase.lean`, `Geometry/NativeCoordinatePairs.lean`, `Geometry/NativeTernaryCoordinate.lean`, `Lattices/NativeIntegerHalving.lean`, `Nilpotent/PreparedAdditionNiltest.lean`, `Nilpotent/UniformControlledBracketStage.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B179
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B182
import Definitions.Def_OAIE3v2B184
import Definitions.Def_OAIE3v2B185
import Definitions.Def_OAIE3v2B186

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationObservable
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (q : ℚ)
  (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s r)
  (hEL : E.lattice = M.dilationPairLattice q)

theorem dilationSpaceProjection_top_smul (ε : D.RealGroup) (j : Fin 2) (k : E.RealGroup)
    (hk : k ∈ (M.filtration.ordinary.dilationPairFiltration q).realification.subgroup s)
    (x : E.Space) :
    ε • M.dilationSpaceProjection q E hEL j (k • x) =
      M.filtration.ordinary.realDilationPairProjection q j k •
        (ε • M.dilationSpaceProjection q E hEL j x) := by
  have hz := M.filtration.ordinary.realDilationPairProjection_mem q j hk
  rw [M.dilationSpaceProjection_smul, ← mul_smul, ← mul_smul,
    (M.filtration.realification.ordinary.top_commutes _ hz ε).eq]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerHalving
namespace OAI

section

namespace Erdos3

namespace NativeIntegerVectorEquivalence

theorem tensor {σ J K L M : Type*} [Fintype J] [Fintype K] [Fintype L] [Fintype M]
    {s : ℕ} {p : ℝ} {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
    {psi : L → (σ → ℤ) → ℂ} {phi : M → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p chi eta)
    (F : NativeIntegerVectorEquivalence s p psi phi) (hp : 2 ≤ p) :
    NativeIntegerVectorEquivalence s (productNiltestBudget p + 2 * p)
      (fun jl : J × L => fun x => chi jl.1 x * psi jl.2 x)
      (fun km : K × M => fun x => eta km.1 x * phi km.2 x) := by
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ productNiltestBudget p :=
    (sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp0)
  have hcost : Real.exp (2 * p) ≤ Real.exp (productNiltestBudget p + 2 * p) :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_left hB)
  refine ⟨(card_product_le_exp_two E.left_dimension F.left_dimension).trans hcost,
    (card_product_le_exp_two E.right_dimension F.right_dimension).trans hcost, ?_⟩
  intro jl km
  obtain ⟨A⟩ := E.expansion jl.1 km.1
  obtain ⟨B⟩ := F.expansion jl.2 km.2
  exact ⟨A.tensorCrossProduct B hp⟩

theorem exists_tensor_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K L M : Type*}
      [Fintype J] [Fintype K] [Fintype L] [Fintype M] {s : ℕ} {p : ℝ}
      {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
      {psi : L → (σ → ℤ) → ℂ} {phi : M → (σ → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p chi eta →
      NativeIntegerVectorEquivalence s p psi phi →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun jl : J × L => fun x => chi jl.1 x * psi jl.2 x)
        (fun km : K × M => fun x => eta km.1 x * phi km.2 x) := by
  obtain ⟨a, _, ha⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 2 + Polynomial.C a) ^ a + 2 * (X + 2))
  refine ⟨C, hC, ?_⟩
  intro σ J K L M _ _ _ _ s p chi eta psi phi hp E F
  have hpq : p ≤ p + 2 := by linarith
  have hcost : (p + 2 + a) ^ a + 2 * (p + 2) ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hbound : productNiltestBudget (p + 2) + 2 * (p + 2) ≤ (p + C) ^ C :=
    (add_le_add (ha _ (by linarith)) (le_refl _)).trans hcost
  exact ((E.mono hpq).tensor (F.mono hpq) (by linarith)).mono hbound

end NativeIntegerVectorEquivalence

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem positivePolynomialEvaluationCosetMap_mk (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) (g) :
    M.positivePolynomialEvaluationCosetMap p B hB hstable hmap (QuotientGroup.mk g) =
      QuotientGroup.mk (realificationMap
        (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation g) := rfl

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.DilationFrequencyPhase
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem NilpotentLieFiltration.realDilationPair_frequency_phase
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (q : ℤ) (η : L →ₗ[ℚ] ℚ)
    (g : (F.dilationPairFiltration (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairFiltration (q : ℚ)).realification.subgroup s) :
    (realifyFunctional η (F.realDilationPairProjection (q : ℚ) 0 g).coord : CircleFourier.Circle) =
      (q ^ s) • (realifyFunctional η
        (F.realDilationPairProjection (q : ℚ) 1 g).coord : CircleFourier.Circle) := by
  rw [F.realDilationPair_top_group_relation q g hg, NilpotentLieBCHGroup.coord_zpow,
    map_zsmul, AddCircle.coe_zsmul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationDescent
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 1)
  (hs : ∑ j, bound j = s + 1)

variable (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) (s + 1) r)
  (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  (hEL : E.lattice = M.additiveTripleLattice i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  [TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))] [T2Space (ℝ ⊗[ℚ] (M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)))]

variable (Q : RationalFilteredNilmanifold ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))) s n)
  (hQL : Q.lattice = E.lattice.map (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))] [T2Space (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ (E.filtration.layerIdeal (s + 1))))]

include hs hEF hQL

theorem exists_unitVertical_triple_quotient_niltest {τ : Type*} {w : τ → ℕ}
    (hQF : Q.filtration = E.filtration.quotientTop)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (ε : D.RealGroup) (a : Fin 3 → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j))))
    (g : E.filtration.realification.PolynomialOrbit w) :
    ∃ T : Q.Niltest w, T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      T.orbit = E.topQuotientOrbit Q hQF g ∧
      ∀ x : τ → ℤ, T.eval x =
        M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
          E hEL ε (fun j => V.observable (a j))
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval w x g)) := by
  obtain ⟨v, hv, hvlip, hvnorm⟩ := M.exists_lipschitz_unitVertical_triple_descent
    i hi hs E hEF hEL Q hQL hH hentries hstructure V ε a A hLip
  let T : Q.Niltest w :=
    { orbit := E.topQuotientOrbit Q hQF g
      observable := v
      normBound := 1
      lipBound := rationalReconstructionLipschitzBound s r n H A 1
      norm_le := hvnorm
      lipschitz := hvlip }
  refine ⟨T, rfl, rfl, rfl, fun x => ?_⟩
  change v (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval w x
    (E.topQuotientOrbit Q hQF g))) = _
  rw [E.topQuotientOrbit_eval Q hQF]
  exact hv _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PreparedAdditionNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s + 1)
  (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) (s + 1) r)
  (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  (hEL : E.lattice = M.additiveTripleLattice i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  (Q : RationalFilteredNilmanifold ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  (hQF : Q.filtration = E.filtration.quotientTop)
  (hQL : Q.lattice = E.lattice.map (E.filtration.quotientStepHom
    (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]

include hs hEF hQF hQL

theorem exists_addition_niltest_of_data {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j k, RationalHeightLE
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) H)
    (hstructure : ∀ a b c, RationalHeightLE (lieStructureConstants Q.basis a b c) H)
    {p : ℝ} (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (a : Fin 3 → I) (A : ℝ≥0)
    (hLip : letI := E.metricSpace
      LipschitzWith A (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j)))) :
    ∃ T : Q.Niltest (fun _ : Option σ => 1), T.normBound = 1 ∧
      T.lipBound = rationalReconstructionLipschitzBound s r n H A 1 ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x = coordinateAdditionProduct
        (fun j y => V.observable j (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g)))
        a i x := by
  obtain ⟨q, hq0, hq⟩ := M.exists_native_addition_orbit i hi.le E hEF g ε γ hγ hfactor
  obtain ⟨T, hTnorm, hTlip, hTorbit, hTval⟩ := M.exists_unitVertical_triple_quotient_niltest
    i hi hs E hEF hEL Q hQL hQF hH hentries hstructure V ε a A hLip q
  refine ⟨T, hTnorm, hTlip, ?_, ?_⟩
  · rw [hTorbit, E.topQuotientOrbit_eval Q hQF, hq0, map_one]
  · intro x
    rw [hTval]
    exact M.tripleObservable_of_addition_values i hi.le E hEL g ε q hq
      (fun j => V.observable (a j)) x

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {σ L I : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [Fintype I] {s d r n : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) (i : σ) (hi : bound i = 1) (hs : ∑ j, bound j = s + 1)
  (E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) (s + 1) r)
  (hEF : E.filtration = M.filtration.additiveTripleFiltration i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  (hEL : E.lattice = M.additiveTripleLattice i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i))]
  (Q : RationalFilteredNilmanifold ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  (hQF : Q.filtration = E.filtration.quotientTop)
  (hQL : Q.lattice = E.lattice.map (E.filtration.quotientStepHom
    (E.filtration.layerIdeal (s + 1)) (t := s) le_rfl))
  [TopologicalSpace (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] ((M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)) ⧸ E.filtration.layerIdeal (s + 1)))]

include hs hEF hEL hQF hQL

theorem exists_prepared_addition_niltest
    {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE (MultilinearityBudget.ambient p))
    (hE : E.GeometryComplexityLE (MultilinearityBudget.ambient p))
    (he : ∀ j a k, rationalLogHeight (D.basis.repr
      (M.filtration.additiveTripleProjection i hi.le _ (omittedCoordinateWeight_le_one i) j (E.basis a)) k) ≤
        MultilinearityBudget.ambient p)
    (hQ : Q.GeometryComplexityLE (MultilinearityBudget.quotient p))
    (hq : ∀ j k, rationalLogHeight
      (Q.basis.repr (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis k)) j) ≤
        MultilinearityBudget.quotient p)
    (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
    (g : M.filtration.realification.PolynomialOrbit) (C : ℕ) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp ((p + C) ^ C))
    (hε : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x))
    (a : Fin 3 → I) :
    ∃ T : Q.Niltest (fun _ : Option σ => 1), T.normBound = 1 ∧
      T.ComplexityLE (MultilinearityBudget.total C (MultilinearityBudget.reconstructionExponent s) p) ∧
      Q.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x = coordinateAdditionProduct
        (fun j y => V.observable j (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g)))
        a i x := by
  let H := ⌈Real.exp (MultilinearityBudget.quotient p)⌉₊
  let A₃ : ℝ≥0 := 3 * (V.lipBound * (A *
    ⟨Real.exp ((MultilinearityBudget.ambient p + 3) ^ 2), (Real.exp_pos _).le⟩))
  have hLip : letI := E.metricSpace
      LipschitzWith A₃ (M.tripleObservable i hi.le _ (omittedCoordinateWeight_le_one i)
        E hEL ε (fun j => V.observable (a j))) :=
    M.tripleObservable_lipschitz i hi.le _ (omittedCoordinateWeight_le_one i) E hEL
      (MultilinearityBudget.ambient_bounds hp).1 hD hE he ε (fun j => V.observable (a j))
      V.lipBound A (fun j x => V.norm (a j) x) (fun j => V.lipschitz (a j)) hε
  obtain ⟨T, hTnorm, hTlip, hTzero, hTeval⟩ := M.exists_addition_niltest_of_data
    i hi hs E hEF hEL Q hQF hQL (one_le_ceil_exp _)
    (fun j k => rationalHeightLE_ceil_exp (hq j k))
    (fun j k l => rationalHeightLE_ceil_exp (hQ.2.2.1 j k l))
    V g ε γ hγ hfactor a A₃ hLip
  have hR := MultilinearityBudget.reconstruction_bounds C hp
  have hHb : (H : ℝ) ≤ Real.exp (MultilinearityBudget.reconstruction C p) :=
    (ceil_exp_le_exp_add_one (MultilinearityBudget.quotient_bounds hp).1).trans
      (Real.exp_le_exp.mpr hR.2.2.1)
  have hA₃ : (A₃ : ℝ) ≤ Real.exp (MultilinearityBudget.reconstruction C p) := by
    change (3 : ℝ) * (V.lipBound * (A * Real.exp ((MultilinearityBudget.ambient p + 3) ^ 2))) ≤ _
    exact (MultilinearityBudget.observable_bound C p V.lipBound A V.lip_bound hA).trans
      (Real.exp_le_exp.mpr hR.2.2.2)
  exact ⟨T, hTnorm, MultilinearityBudget.niltest_complexity Q T C r H A₃ hp hQ
    (hE.1.trans hR.2.1) hHb hA₃ hTnorm hTlip, hTzero, hTeval⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultilinearityCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct BigOperators NNReal

theorem exists_controlled_addition_family (s : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ {σ I : Type*} {L : Type}
      [Fintype σ] [DecidableEq σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
      (M : D.MultidegreeStructure bound) (i : σ) (_hi : bound i = 1)
      (_hs : ∑ j, bound j = t) (_ht : t = s + 1) {p : ℝ}, M.ComplexityLE p →
      ∀ (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
        (g : M.filtration.realification.PolynomialOrbit),
      ∃ R : NativeIntegerModelFamily (fun _ : Option σ => 1) s ((p + Z) ^ Z)
        (fun a => coordinateAdditionProduct
          (fun j y => V.observable j
            (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g))) a i),
        R.dim ≤ 3 * d := by
  obtain ⟨C, _, hnormal⟩ := exists_controlled_group_normalization (s + 1)
  obtain ⟨Z, hZ, hbudget⟩ := MultilinearityBudget.exists_total_bound C
    (MultilinearityBudget.reconstructionExponent s)
  refine ⟨Z, hZ, ?_⟩
  intro σ I L _ _ _ _ _ _ _ _ _ t d bound D M i hi hs ht p hM V g
  subst ht
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hR := MultilinearityBudget.ambient_bounds hp
  obtain ⟨E, hEF, hEL, hE, he, hdim⟩ := M.exists_controlled_addition_model
    i hi (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i) hM
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hq, _⟩ := E.exists_controlled_top_quotient hR.1 hE
  obtain ⟨ε, γ, A, hγ, hfactor, _, hA, hε⟩ := hnormal D p hp hM.1
    (M.filtration.realification.polynomialOrbitEval 0 g)
  let K := M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)
  let J := K ⧸ E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] J)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] J) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] J) := realification_moduleTopology_t2 Q.basis
  have hall (a : Fin 3 → I) := M.exists_prepared_addition_niltest i hi hs
    E hEF hEL Q hQF hQL hp (hM.1.mono D hR.2.1) hE he hQ
    (fun j k => (hq k j).trans (MultilinearityBudget.quotient_bounds hp).2.2)
    V g C ε γ hγ hfactor A hA hε a
  choose T hnorm hcomplex hzero heval using hall
  refine ⟨{
    L := J
    dim := n
    model := Q
    test := T
    norm := fun a => (hnorm a).le
    complexity := fun a => (hcomplex a).mono (hbudget p hp)
    normalized := hzero
    eval := heval }, hn.trans hdim⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_addition_family {σ : Type*} [Fintype σ] [DecidableEq σ] (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 →
      ∃ R : NativeIntegerModelFamily (fun _ : Option σ => 1) ((∑ j, bound j) - 1)
        ((p + C) ^ C) (fun a => coordinateAdditionProduct W.eval a i),
        R.dim ≤ 3 * W.dim := by
  obtain ⟨C, hC, hcontrol⟩ := exists_controlled_addition_family ((∑ j, bound j) - 1)
  refine ⟨C, hC, ?_⟩
  intro p W i hi
  have hle : bound i ≤ ∑ j, bound j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpos : 1 ≤ ∑ j, bound j := by simpa only [hi] using hle
  exact hcontrol W.model W.multi i hi rfl (Nat.sub_add_cancel hpos).symm
    W.complexity W.vertical W.orbit

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_addition_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 →
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (coordinateSumVector W.eval i) (coordinateTensorVector W.eval i) := by
  obtain ⟨a, _, hadd⟩ := exists_addition_family bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + 2 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W i hi
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : 0 ≤ (p + a) ^ a := pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) a
  have hb : (p + a) ^ a + 2 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by linarith only [hp, hpow, hb]
  have h2pr : 2 * p ≤ (p + C) ^ C := by linarith only [hpow, hb]
  have hqr : (p + a) ^ a ≤ (p + C) ^ C := by linarith only [hp, hb]
  obtain ⟨R, _⟩ := hadd W i hi
  exact NativeIntegerVectorEquivalence.of_addition_family W.eval i R
    (by simpa only [Fintype.card_fin] using W.output_bound) hpr h2pr hqr

theorem exists_multilinearity_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (i : σ), NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (coordinateSumVector W.eval i) (coordinateTensorVector W.eval i) := by
  obtain ⟨C, hC, h⟩ := exists_addition_equivalence (fun _ : σ => 1)
  exact ⟨C, hC, fun W i => by simpa using h W i rfl⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeTernaryCoordinate
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_coordinate_translation_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (l : List σ) (i : σ), i ∉ l →
      NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k x => W.eval k (coordinateTranslatedInput (i :: l) x))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateTranslatedInput l x) *
            W.eval k.2 (coordinateTranslatedInput l (coordinateReplaceInput i x))) := by
  obtain ⟨C, hC, hadd⟩ := exists_multilinearity_equivalence (σ := σ)
  refine ⟨C, hC, ?_⟩
  intro p W l i hi
  have E := (hadd W i).linearPullbackHom (coordinateTranslationHom l)
  simpa only [coordinateSumVector, coordinateTensorVector,
    coordinateTranslation_sum l i hi, coordinateTranslation_left,
    coordinateTranslation_right l i hi] using E

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinatePairs
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_coordinate_sum_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 → ∀ {τ : Type*} [Fintype τ] (a b n : (τ → ℤ) →+ ℤ),
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (fun k x => W.eval k (coordinateConstantInput i (a x + b x) (n x)))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateConstantInput i (a x) (n x)) *
            W.eval k.2 (coordinateConstantInput i (b x) (n x))) := by
  obtain ⟨C, hC, hadd⟩ := exists_addition_equivalence bound
  refine ⟨C, hC, ?_⟩
  intro p W i hi τ _ a b n
  let A : Option σ → ((τ → ℤ) →+ ℤ) := fun j => match j with
    | none => b
    | some j => if j = i then a else n
  have hinput (x : τ → ℤ) : (fun j => A j x) = coordinatePairInput i (a x) (b x) (n x) := by
    funext j
    cases j with
    | none => rfl
    | some j =>
      by_cases hji : j = i <;> simp [A, coordinatePairInput, coordinateConstantInput, hji]
  have E := (hadd W i hi).linearPullbackHom A
  simpa only [coordinateSumVector, coordinateTensorVector, hinput,
    coordinatePairInput_sum, coordinatePairInput_left, coordinatePairInput_right] using E

theorem exists_coordinate_parallelogram_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 → ∀ {τ : Type*} [Fintype τ] (u v w n : (τ → ℤ) →+ ℤ),
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateConstantInput i (v x) (n x)) *
            W.eval k.2 (coordinateConstantInput i (w x) (n x)))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateConstantInput i (u x) (n x)) *
            W.eval k.2 (coordinateConstantInput i (v x + w x - u x) (n x))) := by
  obtain ⟨a, _, hadd⟩ := exists_coordinate_sum_equivalence bound
  obtain ⟨c, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p W i hi τ _ u v w n
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let u₄ := v + w - u
  have hu₄ (x : τ → ℤ) : u₄ x = v x + w x - u x := rfl
  have hsum (x : τ → ℤ) : u x + u₄ x = v x + w x := by rw [hu₄]; ring
  have E₁ := hadd W i hi u u₄ n
  have E₂ := hadd W i hi v w n
  have E₁' : NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) q
      (fun k x => W.eval k (coordinateConstantInput i (v x + w x) (n x)))
      (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval k.1 (coordinateConstantInput i (u x) (n x)) *
          W.eval k.2 (coordinateConstantInput i (u₄ x) (n x))) := by
    simpa only [hsum] using E₁
  have R := htrans hq E₂.symm E₁' (fun x => W.unit_eval _)
  have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  simpa only [hu₄] using R.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

namespace NativeCorrelationStructure

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem mixed_correlation_transfer {K : Type*} [Fintype K] {q : ℝ}
    {eta : K → (Fin 2 → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s q W.mixed.eval eta)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) (h : W.shifts) :
    ∃ (k : K) (a : Fin (E.selectedExpansion (W.selectedWitness h).coordinate.1 k).count),
      Real.exp (-(p + 2 * q)) ≤
        ‖𝔼 x, multiplicativeDerivative f h.val x * star
          (eta k (correlationInput (h.val.val : ℤ) (x.val : ℤ)) *
            W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x *
            (W.selectedWitness h).test.evalCyclic N (fun _ => x) *
            ((E.selectedExpansion (W.selectedWitness h).coordinate.1 k).test a).eval
              (correlationInput (h.val.val : ℤ) (x.val : ℤ)))‖ := by
  have hinput (x : ZMod N) :
      (fun i => ((correlationInput h.val x i).val : ℤ)) =
        correlationInput (h.val.val : ℤ) (x.val : ℤ) :=
    map_correlationInput (fun z : ZMod N => (z.val : ℤ)) h.val x
  have hcorr : Real.exp (-p) ≤
      ‖𝔼 x, (multiplicativeDerivative f h.val x *
          star (W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x) *
          star ((W.selectedWitness h).test.evalCyclic N (fun _ => x))) *
        star (W.mixed.eval (W.selectedWitness h).coordinate.1
          (correlationInput (h.val.val : ℤ) (x.val : ℤ)))‖ := by
    simpa only [nativeCorrelationResidual, NativeMultidegreeNilcharacter.evalCyclic,
      hinput, mul_assoc, mul_left_comm, mul_comm]
      using (W.selectedWitness h).correlation
  obtain ⟨k, a, hka⟩ := E.transfer_sample_correlation Finset.univ
    (fun x : ZMod N => correlationInput (h.val.val : ℤ) (x.val : ℤ))
    (W.selectedWitness h).coordinate.1
    (fun x => multiplicativeDerivative f h.val x *
      star (W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x) *
      star ((W.selectedWitness h).test.evalCyclic N (fun _ => x)))
    (fun x _ => hunit _) hcorr
  refine ⟨k, a, ?_⟩
  simpa only [star_mul, mul_assoc, mul_left_comm, mul_comm] using hka

end NativeCorrelationStructure

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultilinearQuadruples
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem exists_fixed_transferred_correlation {K : Type*} [Fintype K] {q : ℝ}
    {eta : K → (Fin 2 → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s q W.mixed.eval eta)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) :
    ∃ (j : Fin W.mixed.outputDim) (k : K)
      (a : Fin (E.selectedExpansion j k).count) (i : Fin W.family.outputDim)
      (H : Finset (ZMod N)), H ⊆ W.shifts ∧ H.Nonempty ∧
      Real.exp (-(3 * p + 2 * q)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, ∃ hh : h ∈ W.shifts,
        (W.selectedWitness ⟨h, hh⟩).coordinate = (j, i) ∧
        Real.exp (-(p + 2 * q)) ≤
          ‖𝔼 x, multiplicativeDerivative f h x * star
            (eta k (correlationInput (h.val : ℤ) (x.val : ℤ)) *
              W.family.evalCyclic N i h x *
              (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
              ((E.selectedExpansion j k).test a).eval
                (correlationInput (h.val : ℤ) (x.val : ℤ)))‖ := by
  classical
  let P := E.ExpansionIndex × Fin W.family.outputDim
  let rel (h : ZMod N) (_ : Unit) (c : P) : Prop :=
    ∃ hh : h ∈ W.shifts,
      (W.selectedWitness ⟨h, hh⟩).coordinate = (c.1.1, c.2) ∧
      Real.exp (-(p + 2 * q)) ≤
        ‖𝔼 x, multiplicativeDerivative f h x * star
          (eta c.1.2.1 (correlationInput (h.val : ℤ) (x.val : ℤ)) *
            W.family.evalCyclic N c.2 h x *
            (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
            ((E.selectedExpansion c.1.1 c.1.2.1).test c.1.2.2).eval
              (correlationInput (h.val : ℤ) (x.val : ℤ)))‖
  have hchoice : ∀ h ∈ W.shifts, ∀ u, ∃ c, rel h u c := by
    intro h hh _
    obtain ⟨k, a, hcorr⟩ := W.mixed_correlation_transfer E hunit ⟨h, hh⟩
    refine ⟨(⟨(W.selectedWitness ⟨h, hh⟩).coordinate.1, k, a⟩,
      (W.selectedWitness ⟨h, hh⟩).coordinate.2), hh, ?_, hcorr⟩
    exact (Prod.eta _).symm
  have hcount : (Fintype.card P : ℝ) ≤ Real.exp (2 * p + 2 * q) := by
    have hleft : (Fintype.card (Fin W.mixed.outputDim) : ℝ) ≤ Real.exp p := by
      simpa only [Fintype.card_fin] using W.mixed.output_bound
    have hindex := E.expansionIndex_card_bound hleft E.right_dimension
    change (Fintype.card (E.ExpansionIndex × Fin W.family.outputDim) : ℝ) ≤ _
    rw [Fintype.card_prod, Nat.cast_mul, Fintype.card_fin]
    calc
      _ ≤ Real.exp (p + q + q) * Real.exp p :=
        mul_le_mul hindex W.family.output_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨c, H, hsub, hH, hsize, hfixed⟩ :=
    exists_large_fixed_choices W.shifts W.nonempty rel hchoice hcount
  have hsize' : Real.exp (-(2 * p + 2 * q)) * (W.shifts.card : ℝ) ≤ (H.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize
  refine ⟨(c ()).1.1, (c ()).1.2.1, (c ()).1.2.2, (c ()).2, H, hsub, hH,
    ?_, fun h hh => hfixed h hh ()⟩
  calc
    _ = Real.exp (-(2 * p + 2 * q)) *
        (Real.exp (-p) * Fintype.card (ZMod N)) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(2 * p + 2 * q)) * (W.shifts.card : ℝ) :=
      mul_le_mul_of_nonneg_left W.density (Real.exp_nonneg _)
    _ ≤ _ := hsize'

end Erdos3.NativeCorrelationStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_parallelogram_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k : Fin V.outputDim × Fin V.outputDim => fun x : Fin 4 → ℤ =>
          V.eval k.1 (fun j => correlationInput (x 1) (x 3) j.1) *
            V.eval k.2 (fun j => correlationInput (x 2) (x 3) j.1))
        (fun k : Fin V.outputDim × Fin V.outputDim => fun x : Fin 4 → ℤ =>
          V.eval k.1 (fun j => correlationInput (x 0) (x 3) j.1) *
            V.eval k.2 (fun j => correlationInput (x 1 + x 2 - x 0) (x 3) j.1)) := by
  obtain ⟨C, hC, hpair⟩ := exists_coordinate_parallelogram_equivalence
    (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1)
  refine ⟨C, hC, ?_⟩
  intro p V
  let v (i : Fin 4) : ((Fin 4 → ℤ) →+ ℤ) := ⟨⟨fun x => x i, rfl⟩, fun _ _ => rfl⟩
  have hv (i : Fin 4) (x : Fin 4 → ℤ) : v i x = x i := rfl
  have E := hpair V (mixedShiftCoordinate s) rfl (v 0) (v 1) (v 2) (v 3)
  have hdegree : (∑ _j : ReplicatedIndex (mixedCorrelationDegree s), (1 : ℕ)) - 1 = s := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, replicatedMixed_card,
      Nat.add_sub_cancel]
  simpa only [hdegree, hv, ← mixed_input_eq_coordinateConstant] using E

theorem exists_mixed_parallelogram_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
      (k : Fin 4 → Fin V.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) s ((p + C) ^ C)
        (mixedParallelogramProduct V k)) := by
  obtain ⟨C, hC, hpair⟩ := exists_mixed_parallelogram_equivalence s
  refine ⟨C, hC, ?_⟩
  intro p V k
  obtain ⟨R⟩ := (hpair V).expansion (k 1, k 2) (k 0, k 3)
  have heq : (fun x : Fin 4 → ℤ =>
      (V.eval (k 1) (fun j => correlationInput (x 1) (x 3) j.1) *
        V.eval (k 2) (fun j => correlationInput (x 2) (x 3) j.1)) *
      star (V.eval (k 0) (fun j => correlationInput (x 0) (x 3) j.1) *
        V.eval (k 3) (fun j => correlationInput (x 1 + x 2 - x 0) (x 3) j.1))) =
      mixedParallelogramProduct V k := by
    funext x
    simp only [mixedParallelogramProduct, untranslatedMixedProduct, star_mul]
    ring
  exact ⟨heq ▸ R⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledCurrentStage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_derivative_removal_control (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
      BasisHomogeneousBrackets b ω →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
      A.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) →
      B.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) →
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) A.coord →
      CoefficientGrid (b.baseChange ℝ) l B.coord →
      ∀ {κ : Type*} (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
        (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      (∀ k, S k ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ k, R k ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) →
      (∀ k, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) (S k)) →
      (∀ k, CoefficientGrid (b.baseChange ℝ) l (R k)) →
      (∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a) / T i) (small i)) →
      (∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)) →
      (∀ k, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) (dualAdjoint A⁻¹ (S k)) ∧
        CoefficientGrid (b.baseChange ℝ) m (dualAdjoint B (R k))) ∧
      (∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) / T i)
          (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)) ∧
        CoefficientGrid (b.baseChange ℝ) m (dualAdjoint B (rational i) - formalLogDerivative i B)) ∧
      (∀ k, dualAdjoint A⁻¹ (S k) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1 ∧
        dualAdjoint B (R k) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1) ∧
      ∀ i, dualAdjoint A⁻¹ (small i - formalLogDerivative i A) ∈
          shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1 ∧
        dualAdjoint B (rational i) - formalLogDerivative i B ∈
          shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ => 1) 1 := by
  obtain ⟨D, _, hbound⟩ := exists_formal_polynomial_operation_bound s a
  obtain ⟨E, _, hgrid⟩ := exists_formal_polynomial_operation_grid s
  let P : Polynomial ℕ := 2 * (Polynomial.X + Polynomial.C D) ^ D +
    (Polynomial.X + 2) ^ a + (Polynomial.X + Polynomial.C E) ^ E + Polynomial.C (s + 2)
  obtain ⟨C, hC, hCbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF hgraded H p hH hp hι hσ hHp hc l hl hlp
  have hbig : 2 * (p + D) ^ D + (p + 2) ^ a + (p + E) ^ E + (s + 2 : ℝ) ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hCbound p hp
  let d := (p + D) ^ D
  let n := (p + 2) ^ a
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have he : 0 ≤ (p + E) ^ E := by positivity
  have hgridCap : (p + E) ^ E ≤ (p + C) ^ C := by
    have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
    change 2 * d + n + (p + E) ^ E + (s + 2 : ℝ) ≤ _ at hbig
    linarith
  have hliftCap : d + n ≤ (p + C) ^ C := by
    have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
    change 2 * d + n + (p + E) ^ E + (s + 2 : ℝ) ≤ _ at hbig
    linarith
  have hremCap : 2 * d + n + (s + 1 : ℝ) ≤ (p + C) ^ C := by
    change 2 * d + n + (p + E) ^ E + (s + 2 : ℝ) ≤ _ at hbig
    linarith
  have hslowCap : Real.exp d * (Real.exp n + Real.exp d * ((s : ℝ) * Real.exp n)) ≤
      Real.exp ((p + C) ^ C) := by
    have h1 : 1 ≤ Real.exp d := Real.one_le_exp hd
    calc
      _ = Real.exp d * Real.exp n * (1 + Real.exp d * s) := by ring
      _ ≤ Real.exp d * Real.exp n * (Real.exp d * (1 + s)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      _ = (Real.exp d * Real.exp d * Real.exp n) * (s + 1) := by ring
      _ ≤ (Real.exp d * Real.exp d * Real.exp n) * Real.exp (s + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (s + 1 : ℝ)]) (by positivity)
      _ = Real.exp (2 * d + n + (s + 1 : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hremCap
  obtain ⟨m, hm, hmp, hlm, hlogGrid, hadGrid⟩ := hgrid F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hgridCap), hlm, ?_⟩
  intro T hT A B hA hB hAbound hBgrid κ S R small rational hS hR hsmall hrational hSbound hRgrid hsmallBound hrationalGrid
  have hg := hgraded.baseChange b ω
  have hAi : A⁻¹.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ : σ => 1) :=
    (gradedPolynomialSubmodule (b.baseChange ℝ) ω _).neg_mem hA
  have hAa := F.gradedPolynomial_mem_adapted b ω hF (fun _ : σ => 1) A.coord hA
  have hAia := F.gradedPolynomial_mem_adapted b ω hF (fun _ : σ => 1) A⁻¹.coord hAi
  have hBa := F.gradedPolynomial_mem_adapted b ω hF (fun _ : σ => 1) B.coord hB
  have hAib : CoefficientBound (b.baseChange ℝ) T (Real.exp n) A⁻¹.coord :=
    CoefficientBound.neg _ _ hAbound
  have hoperations := hbound F b ω hF H p hH hp hι hσ hHp hc T hT
  have hYA (i : σ) := formalLogDerivative_mem_shiftedGradedPolynomialSubmodule
    (b.baseChange ℝ) ω hg i A hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have hslow := hoperations.1 A⁻¹ hAia hAib (Real.exp n) (Real.exp_nonneg _) (S k)
      (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ (hS k)) (hSbound k)
    have hfactor : Real.exp d * Real.exp n ≤ Real.exp ((p + C) ^ C) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hliftCap
    exact ⟨CoefficientBound.mono _ T hT hslow hfactor,
      hadGrid B (R k) hBa (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ (hR k)) hBgrid (hRgrid k)⟩
  · intro i
    have hyBound := hoperations.2 A hAa hAbound i
    have hdiff := CoefficientBound.sub (b.baseChange ℝ) T (hsmallBound i) hyBound
    have hdiffGrade := (shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω (fun _ : σ => 1) 1).sub_mem
      (hsmall i) (hYA i)
    have hslow := hoperations.1 A⁻¹ hAia hAib
      (Real.exp n / T i + Real.exp d * ((s : ℝ) * Real.exp n / T i)) (by have hTi := hT i; positivity)
      (small i - formalLogDerivative i A)
      (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ hdiffGrade) hdiff
    have hfactor : Real.exp d * (Real.exp n / T i + Real.exp d * ((s : ℝ) * Real.exp n / T i)) ≤
        Real.exp ((p + C) ^ C) / T i := by
      calc
        _ = (Real.exp d * (Real.exp n + Real.exp d * ((s : ℝ) * Real.exp n))) / T i := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hslowCap (hT i).le
    exact ⟨CoefficientBound.mono _ T hT hslow hfactor,
      CoefficientGrid.sub _ m
        (hadGrid B (rational i) hBa (F.shiftedGradedPolynomial_mem_adapted b ω hF _ 1 _ (hrational i))
          hBgrid (hrationalGrid i)) (hlogGrid B hBa hBgrid i)⟩
  · intro k
    exact ⟨dualAdjoint_mem_shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω hg _ 1 A⁻¹ (S k) hAi (hS k),
      dualAdjoint_mem_shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω hg _ 1 B (R k) hB (hR k)⟩
  · intro i
    exact polynomial_derivative_removal_preserves_shifted_grading (b.baseChange ℝ) ω hg i A B
      (small i) (rational i) hA hB (hsmall i) (hrational i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_controlled_current_stage (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    (_hstructure : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    {p M : ℝ} (_hp : 0 ≤ p) (_hM : 0 ≤ M)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hrows : (Fintype.card ι : ℝ) ≤ p)
    (_hcols : (Fintype.card ν : ℝ) ≤ p) (_hvariables : (Fintype.card σ : ℝ) ≤ p)
    (_hjp : (j : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p) (_hMp : M ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P.coord α) ∈ E.baseChange ℝ)
    (_hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (_hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ)
    (_hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hsmall : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hrational : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (_hSgraded : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hslow : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (_hgrid : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l)
    {κ : Type*} (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : κ → ℝ ⊗[ℚ] L)
    (_hS : ∀ t, S t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1)
    (_hR : ∀ t, R t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1)
    (_hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (_hSres : ∀ t α, coefficients (S t - monomial 0 (k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hRres : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hSbound : ∀ t, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (S t))
    (_hRgrid : ∀ t, CoefficientGrid (b.baseChange ℝ) l (R t))
    (_hsmallBound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i))
    (_hrationalGrid : ∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, coefficients (VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) α ∈ (E ⊓ V).baseChange ℝ) ∧
        (∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i, small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        (∀ i α, coefficients (small' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (rational' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K) ∧
        (∀ α d, 2 ≤ d → d < j + 1 →
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V.baseChange ℝ) ∧
        (∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
          V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P'
          (fun t => dualAdjoint A⁻¹ (S t)) (fun t => dualAdjoint B (R t)) ∧
        (∀ t α, coefficients (dualAdjoint A⁻¹ (S t) - monomial 0 (k t)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (dualAdjoint B (R t) - monomial 0 (k t)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ t, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) (dualAdjoint A⁻¹ (S t)) ∧
          CoefficientGrid (b.baseChange ℝ) n (dualAdjoint B (R t)) ∧
          dualAdjoint A⁻¹ (S t) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1 ∧
          dualAdjoint B (R t) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1) 1) ∧
        ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) / T i) (small' i) ∧
          CoefficientGrid (b.baseChange ℝ) n (rational' i) := by
  obtain ⟨D, _, hstage⟩ := exists_uniform_formal_current_layer_step
  obtain ⟨E, _, hremove⟩ := exists_formal_derivative_removal_control s 1
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C D) ^ D
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D + (Q + Polynomial.C E) ^ E + 1
  obtain ⟨C, hC, hCbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro L μ ι ν σ _ _ _ _ _ _ F b w hF Vsource V hgraded hs U K hUV hV e f j H J Qheight l
    hj hE hEU hH hl hA he hf hstructure p M hp hM hambient hrows hcols hvariables hjp
    hHp hJp hQp hlp hMp T hT P hPU hPgraded hPE hK hlower hbracket small rational extra
    hsmall hrational hextra hsystem hSgraded hRgraded hslow hgrid κ S R k hS hR hSR hSres hRres
    hSbound hRgrid hsmallBound hrationalGrid
  let d := (p + D) ^ D
  let q := p + d
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hqE : 0 ≤ (q + E) ^ E := by positivity
  have htotal : d + (q + E) ^ E + 1 ≤ (p + C) ^ C := by
    simpa [B, Q, q, d, Polynomial.eval₂_pow] using hCbound p hp
  have hdCap : d ≤ (p + C) ^ C := by linarith
  have hremCap : (q + E) ^ E ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTD : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hdCap).trans (hT i)
  obtain ⟨n₀, A, Bcorr, hn₀, hn₀bound, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra⟩ :=
    hstage F b w hF hgraded hs U K hUV hV e f hj hE hEU hH hl hA he hf hp hM
      hambient hrows hcols hvariables hjp hHp hJp hQp hlp hMp T hTD
      P hPU hPgraded hPE hK hlower hbracket small rational extra hsmall hrational hextra
      hsystem hSgraded hRgraded hslow hgrid
  let Lden := l * n₀
  have hLden : 0 < Lden := Nat.mul_pos hl hn₀
  have hLbound : (Lden : ℝ) ≤ Real.exp q := by
    calc
      _ = (l : ℝ) * (n₀ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp p * Real.exp d := mul_le_mul hlp hn₀bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp q := (Real.exp_add _ _).symm
  obtain ⟨m, hm, hmbound, hLm, hcontrol⟩ := hremove F b w hF hgraded H q hH hq
    (hambient.trans hpq) (hvariables.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
    hstructure Lden hLden hLbound
  have hlL : l ∣ Lden := dvd_mul_right l n₀
  have hnL : n₀ ∣ Lden := dvd_mul_left n₀ l
  have hAg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j A.coord hAhom (fun α => hE _ (hAB α).1)
  have hBg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j Bcorr.coord hBhom (fun α => hE _ (hAB α).2)
  have hAraw : CoefficientBound (b.baseChange ℝ) T (Real.exp d) A.coord :=
    (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) A.coord).mpr hAnorm
  have hAinput : CoefficientBound (b.baseChange ℝ) T (Real.exp ((q + 2) ^ 1)) A.coord := by
    apply CoefficientBound.mono _ T hTpos hAraw
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    dsimp [q]
    linarith
  have hBinput : CoefficientGrid (b.baseChange ℝ) Lden Bcorr.coord :=
    fun α => realDenominatorGrid_subset_of_dvd hn₀ hnL (hBgrid α)
  have hinputCap : Real.exp p ≤ Real.exp ((q + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  obtain ⟨hboundLifts, hboundDerivative, hshiftLifts, _⟩ := hcontrol T hTpos A Bcorr hAg hBg hAinput hBinput
    S R small rational hS hR hSgraded hRgraded
    (fun t => CoefficientBound.mono _ T hTpos (hSbound t) hinputCap)
    (fun t α => realDenominatorGrid_subset_of_dvd hl hlL (hRgrid t α))
    (fun i => CoefficientBound.mono _ T hTpos (hsmallBound i)
      (div_le_div_of_nonneg_right hinputCap (hTpos i).le))
    (fun i α => realDenominatorGrid_subset_of_dvd hl hlL (hrationalGrid i α))
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hE _ (hAB α).1]
    exact F.realGradeProjection_mem_layer b w hF j _
  have hBlayer : ∀ α, coefficients Bcorr.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hE _ (hAB α).2]
    exact F.realGradeProjection_mem_layer b w hF j _
  have hWiff (x : ℝ ⊗[ℚ] L) :
      x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔ F.realification.layer (j + 1) ↔
        x ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
    change x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔
      (F.realLayer (j + 1)).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hkeep := F.formal_current_layer_correction_preserves_lifts_mod hs Uq
    ((V.baseChange ℝ).restrictScalars ℚ) hUV j P A Bcorr
    (fun α => hEU _ (hAB α).1) hAlayer hBlayer S R k hSR
    (fun t α => (hWiff _).mpr (hSres t α)) (fun t α => (hWiff _).mpr (hRres t α))
  have hfinalCap : Real.exp ((q + E) ^ E) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hremCap
  refine ⟨m, A, Bcorr, hm, hmbound.trans hfinalCap, hAB, hAhom, hBhom, ?_, ?_,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra, hkeep.1, ?_, ?_, ?_⟩
  · intro α
    exact (hAnorm α).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hdCap)
      (monomialScale_pos T hTpos α).le)
  · intro α
    exact realDenominatorGrid_subset_of_dvd hn₀ (dvd_trans hnL hLm) (hBgrid α)
  · intro t α
    exact ⟨(hWiff _).mp (hkeep.2 t α).1, (hWiff _).mp (hkeep.2 t α).2⟩
  · intro t
    exact ⟨CoefficientBound.mono _ T hTpos (hboundLifts t).1 hfinalCap,
      (hboundLifts t).2, (hshiftLifts t).1, (hshiftLifts t).2⟩
  · intro i
    exact ⟨CoefficientBound.mono _ T hTpos (hboundDerivative i).1
      (div_le_div_of_nonneg_right hfinalCap (hTpos i).le), (hboundDerivative i).2⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UniformControlledBracketStage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_controlled_bracket_stage (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (_hk : ∀ z, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k z) = (1 : ℝ) ⊗ₜ[ℚ] k z)
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    (_hstructure : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hquotient : (Fintype.card ι : ℝ) ≤ p)
    (_hkernel : (Fintype.card κ : ℝ) ≤ p) (_hsource : (Fintype.card ν : ℝ) ≤ p)
    (_hvariables : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) ∈ E.baseChange ℝ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (_hSgraded : ∀ z, S z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ z, R z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hS : ∀ z α, coefficients (S z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hR : ∀ z α, coefficients (R z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hlower : ∀ d < j - 1, ∀ z α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ)
    (_hsmall : ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (S z))
    (_hrational : ∀ z, CoefficientGrid (b.baseChange ℝ) l (R z))
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (_hsmallShift : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hrationalShift : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hsmallBound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i))
    (_hrationalGrid : ∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈ realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let S' := fun z => dualAdjoint A⁻¹ (S z)
      let R' := fun z => dualAdjoint B (R z)
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ d < j - 1,
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        (∀ d < j, ∀ z α,
          ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' S' R' ∧
        (∀ z α,
          coefficients (S' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (R' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          ⁅coefficients P'.coord α, (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) (S' z) ∧
          CoefficientGrid (b.baseChange ℝ) n (R' z) ∧
          S' z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          R' z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) / T i) (small' i) ∧
          CoefficientGrid (b.baseChange ℝ) n (rational' i) ∧
          small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 := by
  obtain ⟨D, _, hstage⟩ := exists_uniform_formal_bracket_step
  obtain ⟨E, _, hremove⟩ := exists_formal_derivative_removal_control s 1
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C D) ^ D
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D + (Q + Polynomial.C E) ^ E + 1
  obtain ⟨C, hC, hCbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ ν σ _ _ _ _ _ _ _ F b w hF Esource V hgraded hs U hUV hV e f k hk
    j H J Qheight l hj hE hEU hH hl hA he hf hstructure p hp
    hambient hquotient hkernel hsource hvariables hHp hJp hQp hlp T hT P hPU hPgraded hPE
    S R hSR hSgraded hRgraded hS hR hlower hsmall hrational
    small rational extra hsystem hsmallShift hrationalShift hsmallBound hrationalGrid
  let d := (p + D) ^ D
  let q := p + d
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hqE : 0 ≤ (q + E) ^ E := by positivity
  have htotal : d + (q + E) ^ E + 1 ≤ (p + C) ^ C := by
    simpa [B, Q, q, d, Polynomial.eval₂_pow] using hCbound p hp
  have hdCap : d ≤ (p + C) ^ C := by linarith
  have hremCap : (q + E) ^ E ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTD : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hdCap).trans (hT i)
  obtain ⟨n₀, A, Bcorr, hn₀, hn₀bound, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hbelow, hbrackets, hlifts, hremainders⟩ :=
    hstage F b w hF hgraded hs U hUV hV e f k hk hj hE hEU hH hl hA he hf hp
      (Real.exp_nonneg p) hambient hquotient hkernel hsource hHp hJp hQp hlp le_rfl
      T hTD P hPU hPgraded hPE S R hSR hSgraded hRgraded hS hR hlower
      (fun z => (coefficientBound_iff_norm (b.baseChange ℝ) T hTpos (Real.exp_nonneg p) (S z)).mp (hsmall z))
      hrational
  let Lden := l * n₀
  have hLden : 0 < Lden := Nat.mul_pos hl hn₀
  have hLbound : (Lden : ℝ) ≤ Real.exp q := by
    calc
      _ = (l : ℝ) * (n₀ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp p * Real.exp d := mul_le_mul hlp hn₀bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp q := (Real.exp_add _ _).symm
  obtain ⟨m, hm, hmbound, hLm, hcontrol⟩ := hremove F b w hF hgraded H q hH hq
    (hambient.trans hpq) (hvariables.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
    hstructure Lden hLden hLbound
  have hlL : l ∣ Lden := dvd_mul_right l n₀
  have hnL : n₀ ∣ Lden := dvd_mul_left n₀ l
  have hAg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    (j - 1) A.coord hAhom (fun α => hE _ (hAB α).1)
  have hBg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    (j - 1) Bcorr.coord hBhom (fun α => hE _ (hAB α).2)
  have hAraw : CoefficientBound (b.baseChange ℝ) T (Real.exp d) A.coord :=
    (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) A.coord).mpr hAnorm
  have hAinput : CoefficientBound (b.baseChange ℝ) T (Real.exp ((q + 2) ^ 1)) A.coord := by
    apply CoefficientBound.mono _ T hTpos hAraw
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    dsimp [q]
    linarith
  have hBinput : CoefficientGrid (b.baseChange ℝ) Lden Bcorr.coord :=
    fun α => realDenominatorGrid_subset_of_dvd hn₀ hnL (hBgrid α)
  have hinputCap : Real.exp p ≤ Real.exp ((q + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  obtain ⟨hboundLifts, hboundDerivative, hshiftLifts, hshiftDerivative⟩ :=
    hcontrol T hTpos A Bcorr hAg hBg hAinput hBinput S R small rational
      hSgraded hRgraded hsmallShift hrationalShift
      (fun z => CoefficientBound.mono _ T hTpos (hsmall z) hinputCap)
      (fun z α => realDenominatorGrid_subset_of_dvd hl hlL (hrational z α))
      (fun i => CoefficientBound.mono _ T hTpos (hsmallBound i)
        (div_le_div_of_nonneg_right hinputCap (hTpos i).le))
      (fun i α => realDenominatorGrid_subset_of_dvd hl hlL (hrationalGrid i α))
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hsystem' := PolynomialDerivativeSystemMod.remove Uq ((V.baseChange ℝ).restrictScalars ℚ)
    hUV P A Bcorr (fun α => hEU _ (hAB α).1) small rational extra hsystem
  have hfinalCap : Real.exp ((q + E) ^ E) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hremCap
  refine ⟨m, A, Bcorr, hm, hmbound.trans hfinalCap, hAB, hAhom, hBhom, ?_, ?_,
    hprod, hconstant, hnewgraded, hnewU, hbelow, hbrackets, hlifts, hremainders,
    hsystem', ?_, ?_⟩
  · intro α
    exact (hAnorm α).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hdCap)
      (monomialScale_pos T hTpos α).le)
  · intro α
    exact realDenominatorGrid_subset_of_dvd hn₀ (dvd_trans hnL hLm) (hBgrid α)
  · intro z
    exact ⟨CoefficientBound.mono _ T hTpos (hboundLifts z).1 hfinalCap,
      (hboundLifts z).2, (hshiftLifts z).1, (hshiftLifts z).2⟩
  · intro i
    exact ⟨CoefficientBound.mono _ T hTpos (hboundDerivative i).1
      (div_le_div_of_nonneg_right hfinalCap (hTpos i).le),
      (hboundDerivative i).2, (hshiftDerivative i).1, (hshiftDerivative i).2⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end


