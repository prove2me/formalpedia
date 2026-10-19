-- Prove2me | Definitions.Def_OAIE3v2B207
-- name    : OAIE3v2B207
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:14:21.88301+00:00
-- url     : https://prove2.me/theorems/ef7bf0f2-ac24-4f9a-9f35-83c816799341
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 211 of 311
-- statement:
--   Definitions bundle 211 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B178`, `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B181`, `OAIE3v2B187`, `OAIE3v2B188`, `OAIE3v2B189` of this split.
--
--   Modules: `Estimates/AntisymmetricPairVerticalModel.lean`, `Estimates/ControlledDetectedTranslationBaseBounds.lean`, `Estimates/ControlledPrescribedMarkedNativeFactorization.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/NativeCommonModelQuadruples.lean`, `Estimates/NativeGraphSmallDifference.lean`, `Estimates/NativeProductCoefficient.lean`, `Estimates/NativeProductVerticalization.lean`, `Estimates/NativeResidualCrossInduction.lean`, `Estimates/QuadraticBoundedFamily.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Estimates/SharedFreeComparisonLift.lean`, `Estimates/SharedFreeRoundingThreshold.lean`, `Estimates/TranslationMajorTwistedCorrelationStepDrop.lean`, `Estimates/UnitProductOrbitFamily.lean`, `Geometry/AntisymmetricPairCoordinateTest.lean`, `Geometry/DetectedTranslationLogCoordinates.lean`, `Lattices/NativeProperAffineRecovery.lean`, `Linear/AntisymmetricPairProjections.lean`, `Linear/NativePairSymbolProjection.lean`, `Linear/SharedFreeComparisonBasis.lean`, `Nilpotent/MajorTranslationPartnerNiltest.lean`, `Polynomial/AntisymmetricPairPolynomial.lean`, `Polynomial/DegreewiseProperAffineRecovery.lean`, `Polynomial/MajorPhaseVectorDecomposition.lean`, `Polynomial/NativeRankPolynomialFactorization.lean`, `Polynomial/OrdinaryPhasePairFunctionalBounds.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`, `Polynomial/PolynomialOrbitLogSum.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B178
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B187
import Definitions.Def_OAIE3v2B188
import Definitions.Def_OAIE3v2B189

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3

structure NativeRetainedMultilinearIntervalFamily {s r N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℂ} (W : NativeCorrelationStructure s r N p f) (q : ℝ)
    extends NativeMultilinearIntervalFamily W q where
  equivalence : NativeIntegerVectorEquivalence s q W.mixed.eval
    (fun k x => mixed.eval k (fun j => x j.1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductCoefficient
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  {E : RationalFilteredNilmanifold L s n} (T : E.DegreeRankStructure r)

theorem orbit_log_mul_mod_rank_two (hs : 1 ≤ s) (c : Basis ι ℚ L) (τ : ι → ℕ)
    (hF : ∀ j, T.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (g h : E.filtration.realification.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      (T.filtration.layer (Finsupp.weight w α) 2).baseChange ℝ := by
  have hp := T.filtration.polynomialOrbit_log_mul_mod_rank_two hs c τ hF w α
    (T.orbitEquiv w g) (T.orbitEquiv w h)
  have hprod : ((T.orbitEquiv w g) * (T.orbitEquiv w h)).log = (g * h).log :=
    (congrArg (fun z => z.log) (map_mul (T.orbitEquiv w) g h).symm).trans
      (T.orbitEquiv_log w (g * h))
  have heq := congrArg₂ (fun x y => x - y) (congrArg (fun z => coefficients z α) hprod)
    (congrArg₂ (fun x y => x + y)
      (congrArg (fun z => coefficients z α) (T.orbitEquiv_log w g))
      (congrArg (fun z => coefficients z α) (T.orbitEquiv_log w h)))
  exact (congrArg (fun z => z ∈ (T.filtration.layer (Finsupp.weight w α) 2).baseChange ℝ) heq).mp hp

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGraphSmallDifference
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem variable_coefficient_graph_energy {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    Real.exp (-(P + 13 * Fintype.card I)) * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
        (additiveGraph H (fun h => variableRoundedCoefficient M l (a h))) : ℝ) := by
  apply variable_graph_energy_density H D.quadruples a c M l ε _ hsmall _ _
  · intro t ht
    let J := R.interval ⟨t, D.subset ht⟩
    exact ⟨J.first_mem, J.second_mem, J.third_mem, J.fourth_mem⟩
  · intro t ht
    exact hnear t ht
  · have hcard : (H.card : ℝ) ≤ Fintype.card (ZMod N) := by
      exact_mod_cast Finset.card_le_univ H
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 3)
      (Real.exp_nonneg _)).trans D.density

theorem variable_graph_small_difference {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    ∃ J ⊆ H, J.Nonempty ∧ (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card ≤ (J.card : ℝ) ∧
      ((additiveGraph J (fun h => variableRoundedCoefficient M l (a h)) -
        additiveGraph J (fun h => variableRoundedCoefficient M l (a h))).card : ℝ) ≤
          (2 ^ 14 : ℝ) * K ^ 6 * J.card := by
  intro K
  classical
  obtain ⟨t, ht⟩ := D.nonempty
  have hH : H.Nonempty := ⟨t.2.1, (R.interval ⟨t, D.subset ht⟩).first_mem⟩
  apply exists_large_graph_subset_small_difference H hH (fun h => variableRoundedCoefficient M l (a h))
    (Real.exp_pos _) _
  simpa only [Real.exp_neg] using D.variable_coefficient_graph_energy a c M l ε hsmall hnear

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitProductOrbitFamily
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

variable {ι σ τ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  {I : ι → Type*} [∀ i, Fintype (I i)] {w : σ → ℕ}
  (K : ∀ i, I i → (D i).Niltest w)

theorem exists_normalized_product_unit_family
    (R : ∀ i, (D i).DegreeRankStructure r) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hR : ∀ i, (R i).ComplexityLE p)
    (hKn : ∀ i j, (K i j).normBound ≤ 1)
    (hKc : ∀ i j, (K i j).ComplexityLE p)
    (hKu : ∀ i x, ∑ j, ‖(K i j).observable x‖ ^ 2 = 1)
    (a : τ → ∀ i, (D i).filtration.realification.PolynomialOrbit w)
    (ha0 : ∀ t i, (D i).filtration.realification.polynomialOrbitEval w 0 (a t i) = 1) :
    (piRank D R).ComplexityLE (productNiltestBudget p) ∧
    ∃ U : (∀ i, I i) → (pi D).Niltest w,
      (∀ j, (U j).normBound = 1) ∧
      (∀ j, (U j).ComplexityLE (productNiltestBudget p)) ∧
      (∀ x, ∑ j, ‖(U j).observable x‖ ^ 2 = 1) ∧
      (∀ t, (pi D).filtration.realification.polynomialOrbitEval w 0
        (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (a t)) = 1) ∧
      ∀ t j x, ((U j).withOrbit
        (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (a t))).eval x =
          ∏ i, ((K i (j i)).withOrbit (a t i)).eval x := by
  classical
  refine ⟨(piRank_complexity D R hp hι hR).mono _ (productNiltestBudget_geometry hp),
    (fun j => unitBoundedPiNiltest D (fun i => K i (j i)) hp hι
      (fun i => hKc i (j i)) (fun i => hKn i (j i))),
    (fun _ => rfl), (fun j => unitBoundedPiNiltest_complexity D _ hp hι _ _),
    (fun x => productObservable_unit D K hKu x),
    (fun t => NilpotentLieFiltration.piRealOrbit_normalized _ _ (ha0 t)), ?_⟩
  intro t j x
  change (∏ i, (K i (j i)).observable (productProjection D i
    (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval w x
      (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (a t)))))) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_mk]
  exact congrArg (fun g : (D i).RealGroup => (K i (j i)).observable (QuotientGroup.mk g))
    (NilpotentLieFiltration.piRealOrbit_eval (fun i => (D i).filtration) (a t) x i)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeRoundingThreshold
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

noncomputable def sharedLogCoefficientTuple
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s N : ℕ}
    (F : NilpotentLieFiltration L s)
    (ξ : F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) (t : ZMod N × ZMod N × ZMod N) : Fin 4 → ℝ ⊗[ℚ] L :=
  fun k => coefficients ξ.log α + coefficients
    (v (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α

theorem sharedLogCoefficientTuple_mem_common
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s N : ℕ}
    (F : NilpotentLieFiltration L s) (C D : Submodule ℚ L) (hDC : D ≤ C)
    (ξ : F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) (t : ZMod N × ZMod N × ZMod N)
    (hξ : coefficients ξ.log α ∈ C.baseChange ℝ)
    (hv : ∀ h, coefficients (v h).log α ∈ D.baseChange ℝ) :
    sharedLogCoefficientTuple F ξ v α t ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
  apply (mem_fourCommonModulo _ _ _).mpr
  constructor
  · intro k
    exact (C.baseChange ℝ).add_mem hξ (Submodule.baseChange_mono ℝ hDC (hv _))
  · intro k
    change (coefficients ξ.log α + coefficients (v _).log α) -
      (coefficients ξ.log α + coefficients (v _).log α) ∈ D.baseChange ℝ
    rw [add_sub_add_left_eq_sub]
    exact (D.baseChange ℝ).sub_mem (hv _) (hv _)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

theorem sharedLogCoefficientTuple_annihilator_decomposition
    {L J : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype J] {s N : ℕ}
    (F : NilpotentLieFiltration L s) (C D : Submodule ℚ L) (hDC : D ≤ C)
    (ℓ : (Fin 4 → L) →ₗ[ℚ] (J → ℚ))
    (hℓ : fourBalancedDependent D ≤ LinearMap.ker ℓ)
    (ξ : F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) (t : ZMod N × ZMod N × ZMod N)
    (hξ : coefficients ξ.log α ∈ C.baseChange ℝ)
    (hv : ∀ h, coefficients (v h).log α ∈ D.baseChange ℝ) :
    let φ := ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => L) 0)
    let a := fun h => realifyCoordinateMap φ (coefficients (v h).log α)
    realFourCoordinateMap ℓ (sharedLogCoefficientTuple F ξ v α t) =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (coefficients ξ.log α) +
        (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
          a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) := by
  intro φ a
  have h := realFourCoordinateMap_shared_decomposition C D hDC ℓ hℓ
    (coefficients ξ.log α) hξ
    (fun k => coefficients (v (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α)
    (fun k => hv _)
  change realFourCoordinateMap ℓ (sharedLogCoefficientTuple F ξ v α t) =
    realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (coefficients ξ.log α) +
      realifyCoordinateMap φ
        (coefficients (v (rankQuadrupleParameters t 1)).log α +
          coefficients (v (rankQuadrupleParameters t 2)).log α -
          coefficients (v (rankQuadrupleParameters t 0)).log α -
          coefficients (v (rankQuadrupleParameters t 3)).log α) at h
  simpa only [map_add, map_sub] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise BigOperators
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem integer_graph_affine_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    let v := fun h => variableRoundedCoefficient M l (a h)
    ∃ J' ⊆ H, J'.Nonempty ∧
      δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J'.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ)
        (Φ : (Fin r → ℤ) →+ (Option I → ℤ))
        (base : Option I → ℤ),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        Set.InjOn Φ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        ∀ h ∈ J', ∃ x : Fin r → ℤ,
          (∀ i, |x i| ≤ (R i : ℤ)) ∧
            FreimanModel.variableIntegerGraphLift N M (h, v h) = base + Φ x := by
  intro K z δ v
  classical
  obtain ⟨J, hJH, hJ, hsize, hsmallJ⟩ :=
    D.variable_graph_small_difference a c M l ε hsmall hnear
  let A := additiveGraph J v
  have hA : A.Nonempty := hJ.image _
  have hAsmall : ((A - A).card : ℝ) ≤ (2 ^ 14 : ℝ) * K ^ 6 * A.card := by
    simpa only [A, additiveGraph_card] using hsmallJ
  obtain ⟨Q, S, B, f, hQ, hS, hSA, hASsize, hB, _hBimage, _hBcard, hf,
      hQsize, hdensity⟩ :=
    FreimanModel.exists_variableIntegerGraph_cyclic_model N M A hA
      (by dsimp [K]; positivity) hAsmall
  let _ : NeZero Q := ⟨hQ.ne'⟩
  have hdensity' : Real.exp (-z) * Q ≤ (B.card : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hQ : (0 : ℝ) < Q)).mp
    exact (exp_neg_roundedModelLogBudget_le_density P (Fintype.card I)).trans hdensity
  obtain ⟨F, hFS, hF, hFsize, r, R, Φ, base, hrank, hbox, hinj, hrepr⟩ :=
    FreimanModel.exists_bounded_affine_box_of_cyclic_model S hS B hB f hf
      (roundedModelLogBudget_nonneg P (Fintype.card I)) hdensity'
  have hboxSize : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
      2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card := by
    have hcast : ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤ Q := by exact_mod_cast hbox
    have hJcard : (A.card : ℝ) ≤ H.card := by
      rw [show A.card = J.card from additiveGraph_card J v]
      exact_mod_cast Finset.card_le_card hJH
    exact hcast.trans (hQsize.trans (mul_le_mul_of_nonneg_left hJcard (by positivity)))
  have hFA : F ⊆ A.image (FreimanModel.variableIntegerGraphLift N M) := hFS.trans hSA
  let π : (Option I → ℤ) → ZMod N := fun z => (z none : ZMod N)
  have hback (z : Option I → ℤ) (hz : z ∈ F) :
      π z ∈ J ∧ FreimanModel.variableIntegerGraphLift N M (π z, v (π z)) = z := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hFA hz)
    obtain ⟨hyJ, hyv⟩ := (mem_additiveGraph_iff J v y).mp hy
    have hπ : π (FreimanModel.variableIntegerGraphLift N M y) = y.1 := by
      simp [π]
    rw [hπ]
    exact ⟨hyJ, congrArg (FreimanModel.variableIntegerGraphLift N M) (Prod.ext rfl hyv.symm)⟩
  let J' := F.image π
  have hπinj : Set.InjOn π (F : Set _) := by
    intro x hx y hy hxy
    calc
      x = FreimanModel.variableIntegerGraphLift N M (π x, v (π x)) := (hback x hx).2.symm
      _ = FreimanModel.variableIntegerGraphLift N M (π y, v (π y)) := by rw [hxy]
      _ = y := (hback y hy).2
  have hFcard : F.card = J'.card := (Finset.card_image_of_injOn hπinj).symm
  have hJ' : J' ⊆ H := by
    intro h hh
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
    exact hJH (hback z hz).1
  have hJS : (J.card : ℝ) ≤ 16 ^ (Fintype.card I + 2) * (S.card : ℝ) := by
    have h : J.card ≤ 16 ^ (Fintype.card I + 2) * S.card := by
      simpa only [A, additiveGraph_card] using hASsize
    exact_mod_cast h
  have hretain : δ * (S.card : ℝ) ≤ (J'.card : ℝ) := by
    simpa only [hFcard] using hFsize
  refine ⟨J', hJ', hF.image _, ?_, r, R, Φ, base, hrank, hboxSize, hinj, ?_⟩
  · calc
      _ ≤ δ * (J.card : ℝ) := mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
      _ ≤ δ * (16 ^ (Fintype.card I + 2) * (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hJS (Real.exp_pos _).le
      _ = 16 ^ (Fintype.card I + 2) * (δ * S.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hretain (by positivity)
  · intro h hh
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
    rw [(hback z hz).2]
    exact hrepr z hz

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise BigOperators
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem proper_integer_graph_affine_model {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    let v := fun h => variableRoundedCoefficient M l (a h)
    ∃ J₀ ⊆ H, J₀.Nonempty ∧
      δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ)),
        (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
        ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
          2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
        (let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
         let reduce := FreimanModel.variableIntegerGraphReduction N M
         let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
         ∃ J ⊆ J₀, J.Nonempty ∧ J₀.card ≤ (4 * k) ^ r * J.card ∧
           ∃ base : Option I → ℤ,
             Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
             ∀ h ∈ J, ∃ x : Fin r → ℤ,
               (∀ i, |x i| ≤ (R i / (2 * k) : ℕ)) ∧
               FreimanModel.variableIntegerGraphLift N M (h, v h) = base + Φ x) := by
  intro K z δ v
  classical
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, base, hrank, hvolume, _hfull, hrepr⟩ :=
    D.integer_graph_affine_model a c M l ε hsmall hnear
  let reduce := FreimanModel.variableIntegerGraphReduction N M
  let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  have hall (h : {h // h ∈ J₀}) : ∃ x : Fin r → ℤ,
      (∀ i, |x i| ≤ (R i : ℤ)) ∧
      FreimanModel.variableIntegerGraphLift N M (h.val, v h.val) = base + Φ x :=
    hrepr h.val h.property
  choose x hx hgraph using hall
  have hspace (h : {h // h ∈ J₀}) : h.val = (reduce base).1 + η (x h) := by
    change h.val = (reduce base).1 + (reduce (Φ (x h))).1
    have hh := congrArg (fun y => (reduce y).1) (hgraph h)
    simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add,
      Prod.fst_add] using hh
  obtain ⟨J, hJJ₀, hJ, hretain, t, hproper, hsmallBox⟩ :=
    exists_dense_proper_coordinate_restriction J₀ hJ₀ R η (reduce base).1 x hx hspace
  refine ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume, J, hJJ₀,
    hJ, hretain, base + Φ t, hproper, ?_⟩
  intro h hh
  let h₀ : {h // h ∈ J₀} := ⟨h, hJJ₀ hh⟩
  refine ⟨x h₀ - t, hsmallBox ⟨h, hh⟩, ?_⟩
  rw [hgraph h₀, map_sub]
  abel

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem proper_affine_graph_recovery {I : Type*} [Fintype I] (hP : 0 ≤ P)
    (a : ZMod N → I → ℝ) (c : I → ℝ) (l : I → ℕ) (hl : ∀ i, 0 < l i)
    (ε : I → ℝ) (hε : ∀ i, 0 < ε i) (hsmall : ∀ i, 2 * (l i : ℝ) * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    let z := roundedModelLogBudget P (Fintype.card I)
    let δ := Real.exp (-(quarticBogolyubovProgressionConstant * (z + 1) ^ 8))
    ∃ M : I → ℕ, (∀ i, 0 < M i) ∧
      (∀ i, (M i : ℝ) * l i * ε i ≤ 1) ∧
      (∀ i, 1 / ((M i : ℝ) * l i) ≤ 2 * ε i) ∧
      ∃ J₀ ⊆ H, J₀.Nonempty ∧
        δ * ((2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card) ≤ 16 ^ (Fintype.card I + 2) * (J₀.card : ℝ) ∧
        ∃ (r : ℕ) (R : Fin r → ℕ) (Φ : (Fin r → ℤ) →+ (Option I → ℤ)),
          (r : ℝ) ≤ 2 + quarticBogolyubovConstant * (z + 1) ^ 4 ∧
          ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤
            2 * ((2 ^ 14 : ℝ) * K ^ 6 * 16 ^ (Fintype.card I + 1)) ^ 16 * H.card ∧
          (let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
           let reduce := FreimanModel.variableIntegerGraphReduction N M
           let η := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
           ∃ J ⊆ J₀, J.Nonempty ∧ J₀.card ≤ (4 * k) ^ r * J.card ∧
             Real.exp (-properAffineRecoveryLogLoss P (Fintype.card I)) * H.card ≤ (J.card : ℝ) ∧
             (k : ℝ) ≤ Real.exp (properAffineScaleLog P (Fintype.card I)) ∧
             ∃ base : Option I → ℤ,
               Set.InjOn η (centeredIntegerBox (fun i => R i / (2 * k)) : Set _) ∧
               (let ψ := (AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
                let α := variableCoefficientLift l (reduce base).2
                let β := fun j => variableCoefficientLift l (ψ (Pi.single j 1))
                (∀ i, α i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
                (∀ j i, β j i ∈ Set.Ico (0 : ℝ) (1 / l i)) ∧
                ∀ h ∈ J, ∃ x : Fin r → ℤ,
                  (∀ i, |x i| ≤ (R i / (2 * k) : ℕ)) ∧
                  h = (reduce base).1 + η x ∧
                  FreimanModel.variableIntegerGraphLift N M
                    (h, variableRoundedCoefficient M l (a h)) = base + Φ x ∧
                  ∃ q ∈ coordinateDenominatorGrid l, ∀ i,
                    |a h i - (α + ∑ j, (x j : ℝ) • β j) i - q i| ≤ 2 * ε i)) := by
  intro K z δ
  obtain ⟨M, hM, hMsmall, hMerror⟩ := exists_coordinate_rounding_moduli l hl ε hε hsmall
  let _ : ∀ i, NeZero (M i) := fun i => ⟨(hM i).ne'⟩
  obtain ⟨J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume,
      J, hJJ₀, hJ, hretain, base, hproper, hrepr⟩ :=
    D.proper_integer_graph_affine_model a c M l ε hMsmall hnear
  have hcost := properAffineSelection_bounds hP (Fintype.card I) r
    (∏ i, (2 * R i + 1)) H.card J₀.card J.card hJ₀.card_pos hrank hvolume
    (exp_neg_affineRecoveryLogLoss_card_le P (Fintype.card I) H.card J₀.card hsize) hretain
  refine ⟨M, hM, hMsmall, hMerror, J₀, hJ₀H, hJ₀, hsize, r, R, Φ, hrank, hvolume,
    J, hJJ₀, hJ, hretain, hcost.2, hcost.1, base, hproper, ?_⟩
  dsimp only
  refine ⟨variableCoefficientLift_mem_Ico l hl _, ?_, ?_⟩
  · intro j
    exact variableCoefficientLift_mem_Ico l hl _
  · intro h hh
    obtain ⟨x, hx, heq⟩ := hrepr h hh
    let reduce := FreimanModel.variableIntegerGraphReduction N M
    have hred : (h, variableRoundedCoefficient M l (a h)) =
        reduce base + reduce (Φ x) := by
      have hr := congrArg reduce heq
      simpa only [reduce, FreimanModel.variableIntegerGraphReduction_lift, map_add] using hr
    refine ⟨x, hx, congrArg Prod.fst hred, heq, ?_⟩
    obtain ⟨q, hq, herr⟩ := exists_variable_unrounded_affine l hl (reduce base).2
      ((AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)) x (a h)
      (congrArg Prod.snd hred)
    exact ⟨q, hq, fun i => (herr i).trans (hMerror i)⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

def NativeTwoSiteModelingData (degree N : ℕ) [NeZero N]
    (p₁ p₂ K₁ K₂ beta₁ beta₂ eta : ℝ)
    (X₁ : Seminorm ℂ (ZMod N → ℂ))
    (X₂ : (ZMod N → ℂ) → Seminorm ℂ (ZMod N → ℂ)) (a b : ZMod N → ℂ) : Prop :=
  let tau₁ := eta / 4
  let tau₂ := eta * beta₁ / 8
  let length₁ := 1 + 4 * K₁ ^ 2 / (beta₁ ^ 2 * tau₁ ^ 2)
  let length₂ := 1 + 4 * K₂ ^ 2 / (beta₂ ^ 2 * tau₂ ^ 2)
  ∃ (n : ℕ) (_ : 0 < n) (f : Fin n → ZMod N → ℂ)
    (F : ∀ i, NativeCyclicModel degree N p₁ (f i))
    (c : Fin n → ℂ) (ea : ZMod N → ℂ)
    (m : Fin n → ℕ) (_ : ∀ i, 0 < m i)
    (g : ∀ i, Fin (m i) → ZMod N → ℂ)
    (G : ∀ i j, NativeCyclicModel degree N p₂ (g i j))
    (d : ∀ i, Fin (m i) → ℂ) (eb : Fin n → ZMod N → ℂ),
    (∀ x, a x = (∑ i, c i * (F i).test.evalCyclic N (fun _ => x)) + ea x) ∧
    (∀ i x, b x = (∑ j, d i j * (G i j).test.evalCyclic N (fun _ => x)) + eb i x) ∧
    (∑ i, ‖c i‖) ≤ 2 / beta₁ ∧ (∀ i, (∑ j, ‖d i j‖) ≤ 2 / beta₂) ∧
    X₁ ea + ∑ i, ‖c i‖ * X₂ (f i) (eb i) ≤ eta ∧
    (n : ℝ) ≤ length₁ ∧ (∀ i, (m i : ℝ) ≤ length₂) ∧
    (Fintype.card (Σ i, Fin (m i)) : ℝ) ≤ length₁ * length₂

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3.NativeUnitRankFamily

open scoped TensorProduct

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

theorem withOrbit_eval {σ τ I : Type*} [Fintype I] {w : σ → ℕ} {s r : ℕ} {p : ℝ}
    (F : NativeUnitRankFamily w s r τ I p) (i : I) (t : τ) (x : σ → ℤ) :
    ((F.test i).withOrbit (F.orbit t)).eval x = F.eval t i x := rfl

end Erdos3.NativeUnitRankFamily

end

section

namespace Erdos3

open scoped TensorProduct

namespace NativeUnitRankFamily

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

variable {τ τ' I : Type*} [Fintype I] {s r : ℕ} {p q : ℝ}
  (F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ I p)
  (e : τ' → τ) (hpq : p ≤ q) {n : ℕ} (hn : (n + 1 : ℝ) ≤ Real.exp q)
  (V : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s) (Fin (n + 1)) q)

noncomputable def toVerticalFamily : NativeDegreeRankFamily s r τ' q where
  L := F.L
  dim := F.dim
  model := F.model
  rank := F.rank
  complexity := F.complexity.mono F.rank hpq
  orbit := fun t => F.orbit (e t)
  normalized := fun t => F.normalized (e t)
  outputDim := n + 1
  output_pos := Nat.succ_pos n
  output_bound := by simpa only [Nat.cast_add, Nat.cast_one] using hn
  vertical := {
    V with
    vertical := fun i z hz x => V.vertical i z (F.rank.realSubgroup_le_degree s r hz) x
    integral := fun z hz hL => V.integral z (F.rank.realSubgroup_le_degree s r hz) hL
  }

theorem toVerticalFamily_eval (i : Fin (n + 1)) (t : τ') (x : ℤ) :
    (F.toVerticalFamily e hpq hn V).eval i t x = V.observable i (QuotientGroup.mk
      (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => x) (F.orbit (e t)))) := rfl

end NativeUnitRankFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductVerticalization
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra
  NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd
  NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff
  NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem NativeUnitRankFamily.withOrbit_observable
    {σ τ I : Type*} [Fintype I] {w : σ → ℕ} {s r : ℕ} {p : ℝ}
    (F : NativeUnitRankFamily w s r τ I p) (i : I) (t : τ) :
    ((F.test i).withOrbit (F.orbit t)).observable = (F.test i).observable := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AntisymmetricPairPolynomial
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

def antisymmetricPairProjection (k : Fin 2) : V.AntisymmetricPairAlgebra →ₗ⁅ℚ⁆ W.L :=
  liePiEval (some k)

theorem antisymmetricPairFrequency_apply (x : V.AntisymmetricPairAlgebra) :
    piFrequency V.antisymmetricPairFrequencies x =
      W.vertical.frequency (V.antisymmetricPairProjection 1 x) -
        W.vertical.frequency (V.antisymmetricPairProjection 0 x) := by
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  change 0 + (-W.vertical.frequency (x (some 0)) + W.vertical.frequency (x (some 1))) =
    W.vertical.frequency (x (some 1)) - W.vertical.frequency (x (some 0))
  ring

theorem antisymmetricPairFrequency_real (x : ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :
    realifyFunctional (piFrequency V.antisymmetricPairFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 1) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 0) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul scalar element =>
    simp only [realifyFunctional_tmul, V.antisymmetricPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add left right hleft hright => simp only [map_add, hleft, hright]; ring

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

theorem pair_top_agreement (x : ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)
    (hx : x ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ k, mixedCorrelationDegree 1 k)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 1) x) := by
  have h := R.kills_top x hx
  rw [V.antisymmetricPairFrequency_real] at h
  linarith

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

noncomputable def pairComparisonTests (a b : Fin W.outputDim) :
    ∀ k, (V.antisymmetricPairModels k).Niltest (fun _ : Fin 2 => 1)
  | none => (V.test.raiseStep (by decide)).oneOnOrbit
  | some k => ![(W.pairComponent a 0 1).conjugate, W.pairComponent b 1 0] k

end NativeSampleCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AntisymmetricPairCoordinateTest
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

noncomputable def pairCoordinateTests (k : Fin 2) (out : Fin W.outputDim) :
    ∀ l, (V.antisymmetricPairModels l).Niltest (fun _ : Fin 2 => 1)
  | none => (V.test.raiseStep (by decide)).oneOnOrbit
  | some l =>
      ![![W.pairComponent out 0 1, (W.pairComponent out 1 0).oneOnOrbit],
        ![(W.pairComponent out 0 1).oneOnOrbit, W.pairComponent out 1 0]] k l

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AntisymmetricPairProjections
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

theorem antisymmetricPairProjection_layers (k : Fin 2) (a : ℕ)
    (x : V.AntisymmetricPairAlgebra) (hx : x ∈ (pi V.antisymmetricPairModels).filtration.layer a) :
    V.antisymmetricPairProjection k x ∈ W.model.filtration.layer a :=
  (NilpotentLieFiltration.mem_pi_layer (fun l => (V.antisymmetricPairModels l).filtration) a x).mp hx (some k)

noncomputable def antisymmetricPairPolynomialMap (k : Fin 2) :
    ((pi V.antisymmetricPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 2 => 1)).Group →*
        (W.model.filtration.realification.adaptedPolynomialFiltration (fun _ : Fin 2 => 1)).Group :=
  (pi V.antisymmetricPairModels).filtration.realPolynomialGroupMap W.model.filtration
    (V.antisymmetricPairProjection k) (V.antisymmetricPairProjection_layers k) (fun _ : Fin 2 => 1)

theorem antisymmetricPairPolynomialMap_constant (k : Fin 2)
    (c : (pi V.antisymmetricPairModels).RealGroup) :
    V.antisymmetricPairPolynomialMap k
        ((pi V.antisymmetricPairModels).filtration.realification.adaptedConstantGroupHom
          (fun _ : Fin 2 => 1) c) =
      W.model.filtration.realification.adaptedConstantGroupHom (fun _ : Fin 2 => 1)
        (productProjectionHom V.antisymmetricPairModels (some k) c) :=
  (pi V.antisymmetricPairModels).filtration.realPolynomialGroupMap_constant W.model.filtration
    (V.antisymmetricPairProjection k) (V.antisymmetricPairProjection_layers k) (fun _ : Fin 2 => 1) c

theorem antisymmetricPairProjection_lattice (k : Fin 2)
    (c : (pi V.antisymmetricPairModels).RealGroup) (hc : c ∈ (pi V.antisymmetricPairModels).realLattice) :
    productProjectionHom V.antisymmetricPairModels (some k) c ∈ W.model.realLattice :=
  NilpotentLieBCHGroup.realificationMap_subgroup _ _ _
    (productProjection_lattice V.antisymmetricPairModels (some k)) hc

end NativeSampleCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AntisymmetricPairVerticalModel
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}

theorem NativeSampleCorrelation.antisymmetricPairPolynomialMap_value
    (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))
    (k : Fin 2)
    (g : ((pi V.antisymmetricPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 2 => 1)).Group) (x : Fin 2 → ℝ) :
    W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) x
        (V.antisymmetricPairPolynomialMap k g) =
      productProjectionHom V.antisymmetricPairModels (some k)
        ((pi V.antisymmetricPairModels).filtration.adaptedPolynomialRealValueHom
          (fun _ : Fin 2 => 1) x g) :=
  (pi V.antisymmetricPairModels).filtration.realPolynomialGroupMap_value W.model.filtration
    (V.antisymmetricPairProjection k) (V.antisymmetricPairProjection_layers k)
    (fun _ : Fin 2 => 1) g x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop
namespace OAI

universe u

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial CircleFourier
open scoped TensorProduct BigOperators NNReal

theorem exists_translation_major_vertical_selection :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X U L : Type*} [LieRing L] [LieAlgebra ℚ L]
      {m d t e : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (htd : t < d) (ω : U → ℕ)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
      (_hdegree : D₀.totalDegree ≤ d) (_hD : realPolynomialMass D₀ ≤ M)
      (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit ω)
      (R : D.Niltest ω) (p : ℝ), 0 ≤ p →
      (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p →
      Real.log (3 + (2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → U → ℤ) (multiplier : X → ℂ),
      (∀ x ∈ B, ‖multiplier x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, multiplier x *
        bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
          ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω (sample x) orbit)) *
        R.eval (sample x)‖ →
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (V : (weightedTranslationNilmanifold w d hw hwd).Niltest ω)
        (W : (D.raiseStep htd.le).Niltest ω),
        V.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        V.orbit = orbit ∧ V.normBound = 1 ∧
        W.ComplexityLE ((raisedNiltestBudget p + C) ^ C) ∧
        W.orbit = D.raiseStepRealOrbit htd.le R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight (η ((weightedTranslationNilmanifold w d hw hwd).basis i)) ≤
          (raisedNiltestBudget p + C) ^ C) ∧
        η (centralRationalElement w d hd 1) = 1 ∧
        (∀ z, z ∈ (weightedFiltration w d hwd).realification.subgroup d → ∀ x,
          V.observable (z • x) =
            character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
        (∀ z, z ∈ (D.raiseStep htd.le).filtration.realification.subgroup d → ∀ x,
          W.observable (z • x) =
            character ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
              W.observable x) ∧
        (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
        Real.exp (-((raisedNiltestBudget p + C) ^ C)) ≤
          ‖𝔼 x ∈ B, multiplier x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨C, hC, hselect⟩ := exists_native_vertical_pair_preserving_characters_power
  refine ⟨C, hC, ?_⟩
  intro X U L _ _ m d t e w hw hd hwd _ _ _ _ _ _ _ _ _ D htd ω Ψ D₀ M hdegree hD
    orbit R p hp hgeometry hbound hR hRcap B hB sample multiplier hmultiplier hcorr
  let Q := weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD orbit
  have hQ : Q.ComplexityLE p :=
    weightedTranslationBufferedNiltest_complexity w d hw hwd ω hd Ψ D₀ M hdegree hD orbit
      hgeometry hbound
  have hraise := le_raisedNiltestBudget p
  have hraisedcorr : Real.exp (-(raisedNiltestBudget p)) ≤
      ‖𝔼 x ∈ B, multiplier x * Q.eval (sample x) * (R.raiseStep htd.le).eval (sample x)‖ := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hraise)).trans
    simpa only [Q, weightedTranslationBufferedNiltest_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval] using hcorr
  obtain ⟨η, η', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, _, hvertV, _,
      hpresV, _, hVne, hWne, hbias⟩ :=
    hselect (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le)
      Q (R.raiseStep htd.le) (raisedNiltestBudget p) (hp.trans hraise)
      (hQ.mono hraise) (R.raiseStep_complexity htd.le hp hR)
      (by change (1 : ℝ) ≤ 1; exact le_rfl) hRcap
      B hB sample multiplier hmultiplier hraisedcorr
  have hη : η (centralRationalElement w d hd 1) = 1 :=
    weightedTranslation_selected_frequency_one w d hw hd hwd Ψ D₀ η V.observable
      hvertV hVne hpresV
  exact ⟨η, V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hη, hvertV,
    D.raiseStep_observable_top_vertical htd W.observable, hVne, hWne, hbias⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}

variable (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    {σ ι : Type*} {w : σ → ℕ}

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

section ProductTopology

variable [TopologicalSpace (ℝ ⊗[ℚ] PairAlgebra L M)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra L M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PairAlgebra L M)]
    [T2Space (ℝ ⊗[ℚ] PairAlgebra L M)]

theorem pairNiltest_eval (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) (x : σ → ℤ) :
    (pairNiltest D E V W hp hV hW).eval x = V.eval x * W.eval x := by
  rw [pairNiltest, piNiltest_eval, Fintype.prod_bool]
  rfl

theorem pairNiltest_complexity (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    (pairNiltest D E V W hp hV hW).ComplexityLE (productNiltestBudget p) :=
  piNiltest_complexity (pairModels D E) (pairTests D E V W) (by linarith)
    (by simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp)
    (pairTests_complexity D E V W hV hW)

end ProductTopology
end RationalFilteredNilmanifold

open RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem pairFrequency_logHeight
    {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ) {p : ℝ}
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hθ : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
    (k : Fin (Fintype.card (Σ i : Bool, Fin (Bool.rec e d i)))) :
    rationalLogHeight (pairFrequency η θ ((pi (pairModels D E)).basis k)) ≤ p := by
  apply piFrequency_logHeight (pairModels D E) (pairFrequencies η θ)
  intro i
  cases i
  · exact hθ
  · exact hη

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativePairSymbolProjection
namespace OAI

universe sourceLevel

section

namespace Erdos3.RationalFilteredNilmanifold
open Module
variable {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

 theorem productProjection_repr (x : ∀ i, L i) (i : ι) (j : Fin (d i)) :
    (D i).basis.repr (x i) j =
      (pi D).basis.repr x (Fintype.equivFin (Σ i, Fin (d i)) ⟨i, j⟩) := by
  change _ = (productFinBasis D).repr x _
  rw [productFinBasis, Basis.repr_reindex_apply]
  simp only [Equiv.symm_apply_apply, Pi.basis_repr]

 theorem productProjection_coordinate_logHeight {p : ℝ} (x : ∀ i, L i)
    (hx : ∀ k, rationalLogHeight ((pi D).basis.repr x k) ≤ p) (i : ι) (j : Fin (d i)) :
    rationalLogHeight ((D i).basis.repr (x i) j) ≤ p := by
  rw [productProjection_repr D x i j]
  exact hx _

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module VectorPolynomial
open scoped TensorProduct

variable {L M : Type sourceLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ ι κ : Type*} (w : σ → ℕ)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ j, (pi (pairModels D E)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hG : ∀ j, D.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem pairOrbit_first_projection_log
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w) :
    VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
      (M := BoolLieFamily L M) true)).toLinearMap.restrictScalars ℚ) (pairOrbit D E p q).log = p.log := by
  let g : ∀ i : Bool, (pairModels D E i).filtration.realification.PolynomialOrbit w :=
    fun i => by cases i; exact q; exact p
  have h := NilpotentLieFiltration.piRealOrbit_projection_log
    (fun i => (pairModels D E i).filtration) g true
  change VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
      (M := BoolLieFamily L M) true)).toLinearMap.restrictScalars ℚ) (pairOrbit D E p q).log = p.log at h
  exact h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledDetectedTranslationBaseBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (w : σ → ℕ)

theorem realSymbolRepresentative_homogeneous_coefficient (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) :
    coefficients (F.realSymbolRepresentative b ω hF w x) α =
      realificationLieHom (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom
        (coefficients (F.realGradedSymbolPolynomial b ω hF w x) α) :=
  F.realSymbolRepresentative_coefficient_splitting b ω hF w x α

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ)

 theorem realGradedSymbolPolynomial_filteredMap_coefficient
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (G.realGradedSymbolPolynomial c ν hG w
      (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) α =
      realificationLieHom (F.associatedGradedMap G φ hφ)
        (coefficients (F.realGradedSymbolPolynomial b ω hF w x) α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [realificationLieHom_tmul, G.realGradedSymbolPolynomial_coefficient_tmul,
      F.realGradedSymbolPolynomial_coefficient_tmul, realificationLieHom_tmul,
      F.gradedSymbolPolynomial_filteredMap_coefficient G b ω hF c ν hG φ hφ w]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

 theorem projected_realSymbolRepresentative_coefficient
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (G.realSymbolRepresentative c ν hG w
      (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) α =
      realificationLieHom (F.homogeneousGradedProjection G c ν hG hc φ hφ)
        (coefficients (F.realGradedSymbolPolynomial b ω hF w x) α) := by
  rw [G.realSymbolRepresentative_homogeneous_coefficient c ν hG hc,
    F.realGradedSymbolPolynomial_filteredMap_coefficient G b ω hF c ν hG φ hφ w]
  change (G.homogeneousAssociatedGradedEquiv c ν hG hc).toLinearEquiv.toLinearMap.baseChange ℝ
      ((F.associatedGradedMap G φ hφ).toLinearMap.baseChange ℝ _) =
    (((G.homogeneousAssociatedGradedEquiv c ν hG hc).toLinearEquiv.toLinearMap.comp
      (F.associatedGradedMap G φ hφ).toLinearMap).baseChange ℝ) _
  rw [LinearMap.baseChange_comp]
  rfl

theorem homogeneousProjected_scalar_coordinate (η : M →ₗ[ℚ] ℚ)
    (x : F.RealPolynomialSymbol w) :
    coordinate (realifyFunctional
      (η.comp (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap)).toAddMonoidHom
        (F.realGradedSymbolPolynomial b ω hF w x) =
      coordinate (realifyFunctional η).toAddMonoidHom
        (G.realSymbolRepresentative c ν hG w
          (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) := by
  apply MvPolynomial.ext
  intro α
  rw [coeff_coordinate, coeff_coordinate,
    F.projected_realSymbolRepresentative_coefficient G b ω hF c ν hG hc φ hφ w]
  exact realifyFunctional_comp η
    (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem homogeneousProjected_scalar_identity
    {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ) (η : M →ₗ[ℚ] ℚ)
    (x : F.RealPolynomialSymbol w) (y : G.RealPolynomialSymbol w)
    (P : MvPolynomial σ ℝ)
    (hmap : realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x = y)
    (hread : coordinate (realifyFunctional η).toAddMonoidHom
      (G.realSymbolRepresentative c ν hG w y) = P) :
    coordinate (realifyFunctional
      (η.comp (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap)).toAddMonoidHom
      (F.realGradedSymbolPolynomial b ω hF w x) = P := by
  rw [F.homogeneousProjected_scalar_coordinate G b ω hF c ν hG hc φ hφ w η x,
    hmap, hread]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledPrescribedMarkedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct NNReal

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (w : σ → ℕ)
  [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w ν)]

theorem filteredSymbolMapDenominator_pos :
    0 < F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w :=
  matrixDenominator_pos _

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeRankPolynomialFactorization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {E : RationalFilteredNilmanifold L s n} (T : E.DegreeRankStructure r)

theorem polynomialOrbit_mul_coefficient_sub_mem_rank_two
    (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : E.filtration.realification.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      (T.filtration.layer (Finsupp.weight w α) 2).baseChange ℝ := by
  have hh := T.filtration.realification.polynomialOrbit_mul_coefficient_sub_mem_rank_two
    hs w α (T.orbitEquiv w g) (T.orbitEquiv w h)
  rw [← map_mul, T.orbitEquiv_log, T.orbitEquiv_log, T.orbitEquiv_log] at hh
  exact hh

theorem exists_polynomialOrbit_factorization_rank_two
    (hs : 1 ≤ s) (w : σ → ℕ) (α : ι → σ →₀ ℕ)
    (g ε A U ρ : E.filtration.realification.PolynomialOrbit w)
    (hg : E.filtration.realification.polynomialOrbitEval w 0 g = 1)
    (hε : E.filtration.realification.polynomialOrbitEval w 0 ε = 1)
    (hA : E.filtration.realification.polynomialOrbitEval w 0 A = 1)
    (hU : E.filtration.realification.polynomialOrbitEval w 0 U = 1)
    (hρ : E.filtration.realification.polynomialOrbitEval w 0 ρ = 1)
    (hcoeff : ∀ i, coefficients g.log (α i) -
      (coefficients ε.log (α i) + coefficients A.log (α i) +
        coefficients U.log (α i) + coefficients ρ.log (α i)) ∈
          (T.filtration.layer (Finsupp.weight w (α i)) 2).baseChange ℝ) :
    ∃ K : E.filtration.realification.PolynomialOrbit w,
      E.filtration.realification.polynomialOrbitEval w 0 K = 1 ∧ ε * A * K * U * ρ = g ∧
      ∀ i, coefficients K.log (α i) ∈
        (T.filtration.layer (Finsupp.weight w (α i)) 2).baseChange ℝ := by
  obtain ⟨K, hK0, hprod, hK⟩ := T.filtration.realification.exists_polynomialOrbit_factorization_rank_two
    hs w α (T.orbitEquiv w g) (T.orbitEquiv w ε) (T.orbitEquiv w A)
    (T.orbitEquiv w U) (T.orbitEquiv w ρ)
    ((T.orbitEquiv_eval w g 0).trans hg) ((T.orbitEquiv_eval w ε 0).trans hε)
    ((T.orbitEquiv_eval w A 0).trans hA) ((T.orbitEquiv_eval w U 0).trans hU)
    ((T.orbitEquiv_eval w ρ 0).trans hρ) (by
      intro i
      change coefficients (T.orbitEquiv w g).log (α i) -
        (coefficients (T.orbitEquiv w ε).log (α i) + coefficients (T.orbitEquiv w A).log (α i) +
          coefficients (T.orbitEquiv w U).log (α i) + coefficients (T.orbitEquiv w ρ).log (α i)) ∈
        (T.filtration.layer (Finsupp.weight w (α i)) 2).baseChange ℝ
      simpa only [T.orbitEquiv_log] using hcoeff i)
  let K' := (T.orbitEquiv w).symm K
  have hK'eq : T.orbitEquiv w K' = K := (T.orbitEquiv w).apply_symm_apply K
  have hK'log : K'.log = K.log := by
    rw [← hK'eq, T.orbitEquiv_log]
  refine ⟨K', ?_, ?_, ?_⟩
  · have hh := T.orbitEquiv_eval w K' 0
    rw [hK'eq] at hh
    exact hh.symm.trans hK0
  · apply (T.orbitEquiv w).injective
    simpa only [map_mul, hK'eq] using hprod
  · intro i
    rw [hK'log]
    exact hK i

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeComparisonBasis
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

theorem exists_layer_basis_of_eq
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
    {E : RationalFilteredNilmanifold L s n} (T : E.DegreeRankStructure r)
    {p : ℝ} (hT : T.ComplexityLE p) (i j : Fin (s + 1))
    (K : Submodule ℚ L) (hK : T.filtration.layer i.val j.val = K) :
    ∃ k : Basis (Fin (finrank ℚ K)) ℚ K,
      ∀ a b, rationalLogHeight (E.basis.repr (k a : L) b) ≤ p := by
  subst K
  exact ⟨T.basis i j, hT.2 i j⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix NNReal

theorem exists_controlled_subspace_image_section
    {μ ι κ V : Type*} [Fintype μ] [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (φ : V →ₗ[ℚ] (ι → ℚ))
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hφH : ∀ j i, RationalHeightLE (φ (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (σ : (ι → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] V)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      (∀ y, σ y ∈ U.baseChange ℝ) ∧
      (∀ x ∈ U.baseChange ℝ,
        realifyCoordinateMap φ (σ (realifyCoordinateMap φ x)) = realifyCoordinateMap φ x) ∧
      (∀ y, ‖(b.baseChange ℝ).equivFun (σ y)‖ ≤
        Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18) * ‖y‖) ∧
      ∀ y ∈ realDenominatorGrid l, (b.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m := by
  classical
  let A : Matrix ι κ ℚ := fun i j => φ (v j) i
  let B : Matrix μ κ ℚ := fun i j => b.repr (v j) i
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH (fun i j => hφH j i)
  let σ := (b.baseChange ℝ).equivFun.symm.toLinearMap.comp
    ((Matrix.mulVecLin (fun i j => (B i j : ℝ))).comp
      (Matrix.mulVecLin (fun i j => (S i j : ℝ))))
  have hσ (y : ι → ℝ) :
      σ y = realGeneratorCombination v ((fun i j => (S i j : ℝ)) *ᵥ y) := by
    apply (b.baseChange ℝ).equivFun.injective
    change (b.baseChange ℝ).equivFun ((b.baseChange ℝ).equivFun.symm
      ((fun i j => (B i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ y))) = _
    rw [LinearEquiv.apply_symm_apply, realGeneratorCombination_coordinates]
  have hcoord (y : ι → ℝ) : (b.baseChange ℝ).equivFun (σ y) =
      (fun i j => (B i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ y) := by
    rw [hσ, realGeneratorCombination_coordinates]
  have hvU (j : κ) : v j ∈ U := hv ▸ Submodule.subset_span (Set.mem_range_self j)
  have hvφ : Submodule.span ℚ (Set.range (fun j => φ (v j))) = U.map φ := by
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
    hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hBden : (matrixDenominator B : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power B hp 1 hμ hκ
      (fun i j => (Nat.cast_le.mpr (hvH j i).2).trans hHp')
  have hSden := real_image_section_denominator_bound S H l hSH hp hι hκ hHp hlp
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hBnorm (y : κ → ℝ) :
      ‖(fun i j => (B i j : ℝ)) *ᵥ y‖ ≤ Real.exp ((p + 2) ^ 3) * ‖y‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hvH j i).abs_real_le) y).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg y))
  refine ⟨σ, matrixDenominator B * (matrixDenominator S * l),
    Nat.mul_pos (matrixDenominator_pos B) (Nat.mul_pos (matrixDenominator_pos S) hl),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hBden hSden (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro y
    rw [hσ]
    exact realGeneratorCombination_mem U v hvU _
  · intro x hx
    have himg : realifyCoordinateMap φ x ∈
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
      rw [← realRationalCoordinateSpan_eq_image (U.map φ) (fun j => φ (v j)) hvφ,
        realifyCoordinateMap_eq_coordinates]
      refine ⟨φ.baseChange ℝ x, ?_, rfl⟩
      rw [realification_map]
      exact ⟨x, hx, rfl⟩
    rw [hσ, realifyCoordinateMap_eq_coordinates, realGeneratorCombination_map_coordinates]
    exact real_matrix_image_section_apply A S hS _ himg
  · intro y
    rw [hcoord]
    calc
      _ ≤ Real.exp ((p + 2) ^ 3) * ‖(fun i j => (S i j : ℝ)) *ᵥ y‖ := hBnorm _
      _ ≤ Real.exp ((p + 2) ^ 3) * (Real.exp ((p + 2) ^ 18) * ‖y‖) :=
        mul_le_mul_of_nonneg_left (real_image_section_norm_bound S H hSH hp hι hκ hHp y)
          (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, ← Real.exp_add]
  · intro y hy
    rw [hcoord]
    exact real_matrix_denominator_grid B _ _ (real_matrix_denominator_grid S l y hy)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_controlled_subspace_projector
    {μ κ V : Type*} [Fintype μ] [Fintype κ] [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (l : ℕ) (hl : 0 < l)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ j i, rationalLogHeight (b.repr (v j) i) ≤ p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := p + 1
    ∃ (P : (ℝ ⊗[ℚ] V) →ₗ[ℝ] (ℝ ⊗[ℚ] V)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 3 + (q + 2) ^ 36) ∧
      (∀ x, P x ∈ U.baseChange ℝ) ∧ (∀ x ∈ U.baseChange ℝ, P x = x) ∧
      (∀ x, ‖(b.baseChange ℝ).equivFun (P x)‖ ≤
        Real.exp ((q + 2) ^ 3 + (q + 2) ^ 18) * ‖(b.baseChange ℝ).equivFun x‖) ∧
      ∀ x, (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l →
        (b.baseChange ℝ).equivFun (P x) ∈ realDenominatorGrid m := by
  intro q
  have hpq : p ≤ q := by dsimp [q]; linarith
  obtain ⟨σ, m, hm, hmp, hσU, hσfix, hσnorm, hσgrid⟩ :=
    exists_controlled_subspace_image_section b U v hv b.equivFun.toLinearMap
      (one_le_ceil_exp p) hl (fun j i => rationalHeightLE_ceil_exp (hvH j i))
      (fun j i => rationalHeightLE_ceil_exp (hvH j i))
      (hp.trans hpq) (hμ.trans hpq) (hμ.trans hpq) (hκ.trans hpq)
      (ceil_exp_le_exp_add_one hp) (hlp.trans (Real.exp_le_exp.mpr hpq))
  let P := σ.comp (b.baseChange ℝ).equivFun.toLinearMap
  refine ⟨P, m, hm, hmp, (fun x => hσU _), ?_, (fun x => hσnorm _), ?_⟩
  · intro x hx
    apply (b.baseChange ℝ).equivFun.injective
    change (b.baseChange ℝ).equivFun (σ ((b.baseChange ℝ).equivFun x)) = _
    simpa only [realify_basis_coordinates] using hσfix x hx
  · intro x hx
    exact hσgrid _ hx

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_logHeight_subspace_image_section
    {μ ι κ V : Type*} [Fintype μ] [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (φ : V →ₗ[ℚ] (ι → ℚ))
    (l : ℕ) (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hμ : (Fintype.card μ : ℝ) ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ j i, rationalLogHeight (b.repr (v j) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (φ (b i) j) ≤ p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    let t := (p + 2) ^ 4 + 1
    ∃ (σ : (ι → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] V)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
      (∀ y, σ y ∈ U.baseChange ℝ) ∧
      (∀ x ∈ U.baseChange ℝ,
        realifyCoordinateMap φ (σ (realifyCoordinateMap φ x)) = realifyCoordinateMap φ x) ∧
      (∀ y, ‖(b.baseChange ℝ).equivFun (σ y)‖ ≤
        Real.exp ((t + 2) ^ 3 + (t + 2) ^ 18) * ‖y‖) ∧
      ∀ y ∈ realDenominatorGrid l, (b.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m := by
  intro t
  have hp4 : p ≤ (p + 2) ^ 4 := le_power_budget hp (by decide)
  have hpt : p ≤ t := hp4.trans (le_add_of_nonneg_right (by norm_num))
  have ht : 0 ≤ t := hp.trans hpt
  apply exists_controlled_subspace_image_section b U v hv φ
    (one_le_ceil_exp ((p + 2) ^ 4)) hl _ _ ht (hμ.trans hpt) (hι.trans hpt) (hκ.trans hpt)
    (ceil_exp_le_exp_add_one (by positivity)) (hlp.trans (Real.exp_le_exp.mpr hpt))
  · intro j i
    exact rationalHeightLE_ceil_exp ((hvH j i).trans hp4)
  · intro j i
    apply rationalHeightLE_ceil_exp
    exact linearMap_coordinate_logHeight b (Pi.basisFun ℚ ι) φ hp hμ hφH (v j) (hvH j) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreewiseProperAffineRecovery
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators Pointwise
open CyclicCrootSisask

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem degreewise_proper_affine_recovery {B : Type*} [Fintype B] {I : B → Type*}
    [∀ d, Fintype (I d)] (hP : 0 ≤ P) (a : ZMod N → ∀ d, I d → ℝ) (c : ∀ d, I d → ℝ)
    (l : B → ℕ) (hl : ∀ d, 0 < l d) (ε : B → ℝ) (hε : ∀ d, 0 < ε d)
    (hsmall : ∀ d, 2 * (l d : ℝ) * ε d ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∀ d, ∃ q ∈ realDenominatorGrid (l d),
      ‖c d + (a (rankQuadrupleParameters t 1) d + a (rankQuadrupleParameters t 2) d -
        a (rankQuadrupleParameters t 0) d - a (rankQuadrupleParameters t 3) d) - q‖ ≤ ε d) :
    let n := Fintype.card (Σ d, I d)
    ∃ J' ⊆ H, J'.Nonempty ∧
      Real.exp (-properAffineRecoveryLogLoss P n) * H.card ≤ (J'.card : ℝ) ∧
      ∃ (r : ℕ) (R : Fin r → ℕ) (ξ : (Fin r → ℤ) →+ ZMod N)
        (h₀ : ZMod N) (α : ∀ d, I d → ℝ) (β : Fin r → ∀ d, I d → ℝ),
        (r : ℝ) ≤ properAffineRankBound P n ∧
        Set.InjOn ξ {x | ∀ i, |x i| ≤ (R i : ℤ)} ∧
        (∀ d i, α d i ∈ Set.Ico (0 : ℝ) (1 / l d)) ∧
        (∀ j d i, β j d i ∈ Set.Ico (0 : ℝ) (1 / l d)) ∧
        ∀ h ∈ J', ∃ x : Fin r → ℤ,
          (∀ j, |x j| ≤ (R j : ℤ)) ∧ h = h₀ + ξ x ∧
          ∀ d, ∃ q ∈ realDenominatorGrid (l d),
            ‖a h d - (α d + ∑ j, (x j : ℝ) • β j d) - q‖ ≤ 2 * ε d := by
  intro n
  let a' : ZMod N → (Σ d, I d) → ℝ := fun h i => a h i.1 i.2
  let c' : (Σ d, I d) → ℝ := fun i => c i.1 i.2
  let l' : (Σ d, I d) → ℕ := fun i => l i.1
  let ε' : (Σ d, I d) → ℝ := fun i => ε i.1
  have hnear' : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l',
      ∀ i, |c' i + (a' (rankQuadrupleParameters t 1) i + a' (rankQuadrupleParameters t 2) i -
        a' (rankQuadrupleParameters t 0) i - a' (rankQuadrupleParameters t 3) i) - q i| ≤ ε' i := by
    intro t ht
    choose q hq he using hnear t ht
    have hq' : ∀ d, ∃ v : I d → ℤ, ∀ i, (v i : ℝ) = (l d : ℝ) * q d i := by
      intro d
      obtain ⟨v, hv⟩ := hq d
      exact ⟨v, fun i => congrFun hv i⟩
    choose v hv using hq'
    refine ⟨fun i => q i.1 i.2, ⟨fun i => v i.1 i.2, fun i => hv i.1 i.2⟩, ?_⟩
    intro i
    have hi := (norm_le_pi_norm (c i.1 +
      (a (rankQuadrupleParameters t 1) i.1 + a (rankQuadrupleParameters t 2) i.1 -
        a (rankQuadrupleParameters t 0) i.1 - a (rankQuadrupleParameters t 3) i.1) - q i.1)
      i.2).trans (he i.1)
    simpa only [a', c', ε', Pi.add_apply, Pi.sub_apply, Real.norm_eq_abs] using hi
  obtain ⟨M, _hM, _hMsmall, _hMerror, J₀, hJ₀H, _hJ₀, _hsize₀, r, R, Φ,
      hrank, _hvolume, J', hJ'J₀, hJ, _hretain, hsize, _hscale, base, hproper, hα, hβ, hrepr⟩ :=
    D.proper_affine_graph_recovery hP a' c' l' (fun i => hl i.1) ε' (fun i => hε i.1)
      (fun i => hsmall i.1) hnear'
  let k := (2 ^ r * ∏ i, (2 * R i + 1)) / J₀.card + 1
  let R' := fun i => R i / (2 * k)
  let reduce := FreimanModel.variableIntegerGraphReduction N M
  let ξ := (AddMonoidHom.fst (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  let ψ := (AddMonoidHom.snd (ZMod N) (∀ i, ZMod (M i))).comp (reduce.comp Φ)
  let α := variableCoefficientLift l' (reduce base).2
  let β := fun j => variableCoefficientLift l' (ψ (Pi.single j 1))
  have hinj : Set.InjOn ξ {x | ∀ i, |x i| ≤ (R' i : ℤ)} := by
    intro x hx y hy hxy
    exact hproper ((mem_centeredIntegerBox R' x).mpr hx)
      ((mem_centeredIntegerBox R' y).mpr hy) hxy
  refine ⟨J', hJ'J₀.trans hJ₀H, hJ, hsize, r, R', ξ, (reduce base).1,
    (fun d i => α ⟨d, i⟩), (fun j d i => β j ⟨d, i⟩), hrank, hinj,
    (fun d i => hα ⟨d, i⟩), (fun j d i => hβ j ⟨d, i⟩), ?_⟩
  intro h hh
  obtain ⟨x, hx, hspace, _hgraph, q, hq, he⟩ := hrepr h hh
  obtain ⟨v, hv⟩ := hq
  refine ⟨x, hx, hspace, ?_⟩
  intro d
  refine ⟨fun i => q ⟨d, i⟩, ⟨fun i => v ⟨d, i⟩, funext (fun i => hv ⟨d, i⟩)⟩, ?_⟩
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (hε d).le)).mpr
  intro i
  simpa only [a', ε', Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    Real.norm_eq_abs] using he ⟨d, i⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialOrbitLogSum
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {F : NilpotentLieFiltration L s} {w : σ → ℕ}

theorem PolynomialOrbit.logSum_normalized (g h : F.PolynomialOrbit w)
    (hg : F.polynomialOrbitEval w 0 g = 1) (hh : F.polynomialOrbitEval w 0 h = 1) :
    F.polynomialOrbitEval w 0 (g.logSum h) = 1 := by
  rw [F.polynomialOrbitEval_zero_iff_coefficient_zero] at hg hh ⊢
  simp only [logSum_log, map_add, Finsupp.add_apply, hg, hh, add_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

def NativeResidualCrossRowDetection (s C : ℕ) : Prop :=
  ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} (D : RationalFilteredNilmanifold L (s + 2) d)
    (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
    ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
    ∀ (f g : ZMod N → ℂ) (R : ZMod N → (Unit → ℤ) → ℂ),
    (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
    (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
    (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R h))) →
    Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      ((f n * star (g (n + h))) * star (R h (fun _ => (n.val : ℤ)))) *
        star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
    Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 3) g

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DetectedTranslationLogCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators TensorProduct

variable {U B κ : Type*} [Fintype B] [Fintype κ]

noncomputable def nativeTranslationGroupPolynomial (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) :
    PolynomialTranslationGroupOver (MvPolynomial U ℝ) B :=
  translationLogGroupPolynomial w d b (nativeTranslationLogCoordinate w d b p)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct BigOperators

namespace PolynomialTranslationLie

open RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def detectedTranslationLogProjectionMatrix : Matrix (WeightedBasisIndex w d) ι ℚ :=
  fun k i => if ω i = weightedBasisGrade w d k then (weightedBasis w d hw).repr (b i true) k else 0

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.MajorTranslationPartnerNiltest
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module RationalFilteredNilmanifold
open scoped NNReal TensorProduct

noncomputable abbrev majorTranslationPartnerModel {L : Type}
    [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
    (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)]
    (D : RationalFilteredNilmanifold L t e) (htd : t ≤ d) :=
  pi (pairModels (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd))

theorem exists_majorTranslation_partner_niltest (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [LieRing L] [LieAlgebra ℚ L]
      {m t e : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (htd : t ≤ d)
      (R : D.Niltest (fun _ : U => 1)) (_hd : 0 < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (_hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (_hA : ∀ i, (A i).totalDegree ≤ w i)
      (p : ℝ), 0 ≤ p → (Fintype.card U + m : ℕ) ≤ p →
      (Ψ.lip : ℝ) ≤ Real.exp p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      let N := majorTranslationPartnerModel w d hw hwd D htd
      letI : FiniteDimensional ℚ (PairAlgebra (weightedSubalgebra w d) L) :=
        N.basis.finiteDimensional_of_finite
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L)
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
        IsModuleTopology.topologicalAddGroup ℝ _
      letI : T2Space (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
        realification_moduleTopology_t2 N.basis
      ∃ S : N.Niltest (fun _ : U => 1), S.normBound = 1 ∧ S.ComplexityLE ((p + C) ^ C) ∧
        ∀ u : U → ℤ, ∀ β : Fin m → ℤ,
          (∀ i, |eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2) →
          S.eval u =
            ((Ψ.value (fun i => eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
              (Real.fourierChar (eval (fun j => ((Sum.elim u β j : ℤ) : ℝ)) F) : ℂ)) *
                R.eval u := by
  obtain ⟨a, ha, hmajor⟩ := exists_majorTranslation_degree_reduced_niltest d
  obtain ⟨C, hC, hbudget⟩ := exists_majorTranslationPartnerBudget_bound a
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ D htd R hd Ψ F hF A hA p
    hp hdim hΨ hR hcap
  let N := majorTranslationPartnerModel w d hw hwd D htd
  let : FiniteDimensional ℚ (PairAlgebra (weightedSubalgebra w d) L) :=
    N.basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    realification_moduleTopology_t2 N.basis
  obtain ⟨V, hVnorm, hV, _, hVeval⟩ := hmajor w hw hwd hd Ψ F hF A hA hp hdim hΨ
  let q : ℝ := (p + a) ^ a + raisedNiltestBudget p + 2
  have hraise : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hq : 2 ≤ q := by dsimp [q]; linarith
  have hVq : V.ComplexityLE q := hV.mono (by dsimp [q]; linarith)
  have hRq : (R.raiseStep htd).ComplexityLE q :=
    (R.raiseStep_complexity htd hp hR).mono (by dsimp [q]; linarith)
  let models := pairModels (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd)
  let tests := pairTests (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd)
    V (R.raiseStep htd)
  have htests : ∀ i, (tests i).ComplexityLE q :=
    pairTests_complexity _ _ V (R.raiseStep htd) hVq hRq
  have hcaps : ∀ i, (tests i).normBound ≤ 1 := by
    intro i
    cases i
    · change R.normBound ≤ 1
      exact_mod_cast hcap
    · change V.normBound ≤ 1
      exact hVnorm.le
  have hcard : (Fintype.card Bool : ℝ) ≤ q := by simpa using hq
  let S := unitBoundedPiNiltest models tests (by linarith : 0 ≤ q) hcard htests hcaps
  refine ⟨S, rfl, ?_, ?_⟩
  · exact (unitBoundedPiNiltest_complexity models tests (by linarith : 0 ≤ q)
      hcard htests hcaps).mono (hbudget p hp)
  · intro u β hβ
    change (unitBoundedPiNiltest models tests _ _ _ _).eval u = _
    rw [unitBoundedPiNiltest_eval, Fintype.prod_bool]
    change V.eval u * (R.raiseStep htd).eval u = _
    rw [hVeval u β hβ, R.raiseStep_eval]

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorPhaseVectorDecomposition
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

def MajorPhaseDetectedConclusion {m : ℕ} {X L : Type}
    [Fintype X] [LieRing L] [LieAlgebra ℚ L]
    (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (N : X → ℕ) (B : ℝ) : Prop :=
  let w := lowTaggedWeight J d
  ∃ (fast : LieSubalgebra ℚ (weightedSubalgebra w d))
    (g : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → weightedSubalgebra w d)
    (S : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (R : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ) (q : ℕ),
    (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L) : ℝ) ≤ B ∧
    Submodule.span ℚ (Set.range g) = fast.toSubmodule ∧
    BasisGradedSubmodule (weightedBasis w d (lowTaggedWeight_pos J d))
      (weightedBasisGrade w d) fast.toSubmodule ∧
    (∀ j i, rationalLogHeight ((weightedBasis w d (lowTaggedWeight_pos J d)).repr (g j) i) ≤ B) ∧
    BasisGradedSubmodule (Pi.basisFun ℝ _) w ((fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
    (∀ h, lowTaggedRetained J d U h ≤ (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
    realPolynomialMass S ≤ Real.exp B ∧
    (∀ α, |S.coeff α| ≤ Real.exp B) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp B ∧
    (fun α => R.coeff α) ∈ denominatorGrid q ∧
    (∀ α, (R.coeff α).den ≤ q) ∧
    S ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) w) d ∧
    R ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) w) d ∧
    ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ),
      z ∈ (fast.toSubmodule.baseChange ℝ).map
        (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) →
      MvPolynomial.eval (Sum.elim u z)
          (weightedHomogeneousComponent (Sum.elim (fun _ : X => 1) w) d F) =
        MvPolynomial.eval (Sum.elim (fun i => u i / (N i : ℝ))
          (fun j => z j - MvPolynomial.eval u
            (majorTranslationTopCoordinates w
              (fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)) j))) S +
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) R

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module RationalFilteredNilmanifold PolynomialTranslationLie

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] (d : ℕ)

 theorem majorPhaseTaggedGenerators_span {A : Type*}
    (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d))
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d)
    (hg : Submodule.span ℚ (Set.range g) = fast.toSubmodule)
    (hgraded : BasisGradedSubmodule
      (weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d))
      (weightedBasisGrade (lowTaggedWeight J d) d) fast.toSubmodule)
    (j : Fin m) (hj : j.val + 1 ≤ d) :
    lowTaggedSubspaceFamily J d
      ((fast.toSubmodule.baseChange ℝ).map
        (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))) j =
      Submodule.span ℝ (Set.range (fun a i => (majorPhaseTaggedGenerators J d g j hj a i : ℝ))) := by
  have hK := weightedTranslationBase_real_image_graded (lowTaggedWeight J d) d
    (lowTaggedWeight_pos J d) fast.toSubmodule hgraded g hg
  have hspan := realifyCoordinateMap_image_eq_span fast.toSubmodule g hg
    (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype)
  rw [hspan] at hK ⊢
  exact lowTaggedSubspaceFamily_span J d _ hK j hj

theorem majorPhaseTaggedGenerators_mem_iff {A : Type*}
    (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d))
    (g : A → weightedSubalgebra (lowTaggedWeight J d) d)
    (hg : Submodule.span ℚ (Set.range g) = fast.toSubmodule)
    (hgraded : BasisGradedSubmodule
      (weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d))
      (weightedBasisGrade (lowTaggedWeight J d) d) fast.toSubmodule)
    (x : ∀ j, J j → ℝ) :
    lowTaggedCoordinates J d x ∈ (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype)) ↔
      ∀ j (hj : j.val + 1 ≤ d), x j ∈
        Submodule.span ℝ (Set.range (fun a i => (majorPhaseTaggedGenerators J d g j hj a i : ℝ))) := by
  have hK := weightedTranslationBase_real_image_graded (lowTaggedWeight J d) d
    (lowTaggedWeight_pos J d) fast.toSubmodule hgraded g hg
  rw [lowTaggedCoordinates_mem_iff_low J d _ hK x]
  constructor
  · intro hx j hj
    rw [← majorPhaseTaggedGenerators_span J d fast g hg hgraded j hj]
    exact hx j hj
  · intro hx j hj
    rw [majorPhaseTaggedGenerators_span J d fast g hg hgraded j hj]
    exact hx j hj

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

variable {m : ℕ} {X L : Type} [Fintype X] [LieRing L] [LieAlgebra ℚ L]
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)

variable {η V : Type*} [Fintype η] [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
variable (N : X → ℕ) (B : ℝ) (eV : Basis η ℝ V)
variable (p : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ V)

def MajorPhaseVectorDetectedConclusion : Prop :=
  let w := lowTaggedWeight J d
  let wt := Sum.elim (fun _ : X => 1) w
  ∃ (fast : η → LieSubalgebra ℚ (weightedSubalgebra w d))
    (g : η → Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → weightedSubalgebra w d)
    (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ V) (q : ℕ),
    (∀ i, (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L) : ℝ) ≤ B ∧
      Submodule.span ℚ (Set.range (g i)) = (fast i).toSubmodule ∧
      BasisGradedSubmodule (weightedBasis w d (lowTaggedWeight_pos J d))
        (weightedBasisGrade w d) (fast i).toSubmodule ∧
      ∀ j a, rationalLogHeight ((weightedBasis w d (lowTaggedWeight_pos J d)).repr (g i j) a) ≤ B) ∧
    (∀ i, BasisGradedSubmodule (Pi.basisFun ℝ _) w (majorPhaseDetectedRealBase J d (fast i))) ∧
    (∀ i h, lowTaggedRetained J d U h ≤ majorPhaseDetectedRealBase J d (fast i)) ∧
    (∀ i, realPolynomialMass (coordinate (eV.coord i).toAddMonoidHom slow) ≤ Real.exp B) ∧
    (∀ i α, |eV.coord i (coefficients slow α)| ≤ Real.exp B) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * B) ∧
    (∀ i, realPolynomialCoefficientGrid q (coordinate (eV.coord i).toAddMonoidHom rat)) ∧
    (∀ i, coordinate (eV.coord i).toAddMonoidHom slow ∈ weightedSupportLE wt d) ∧
    (∀ i, coordinate (eV.coord i).toAddMonoidHom rat ∈ weightedSupportLE wt d) ∧
    ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ),
      (∀ i, z ∈ majorPhaseDetectedRealBase J d (fast i)) →
      eval₂ (Sum.elim u z) p =
        eval₂ (Sum.elim u z) (realChartSubstitute
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (majorTranslationTopCoordinates w
              (fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)))) slow) +
        eval₂ (Sum.elim u z) rat

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPhasePairFunctionalBounds
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module _root_.MvPolynomial PolynomialTranslationLie

theorem mem_top (s : ℕ) (x : weightedSubalgebra weight s) :
    x ∈ (weightedFiltration weight s (weight_le s)).layer s := by
  change (∀ i, weight i < s → x.val.base i = 0) ∧
    x.val.polynomial ∈ weightedSupportDrop weight s s
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  intro α _
  have hα : α = 0 := Subsingleton.elim _ _
  change Finsupp.weight weight α + s ≤ s
  simp only [hα, map_zero, zero_add, le_refl]

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem projection_filtered (F : NilpotentLieFiltration L s)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) :
    ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration weight s (weight_le s)).layer j := by
  intro j x hx
  by_cases hj : j ≤ s
  · exact (weightedFiltration weight s (weight_le s)).antitone hj (mem_top s (φ x))
  · have hz : x ∈ F.layer (s + 1) := F.antitone (by omega) hx
    rw [F.terminal] at hz
    have hx0 : x = 0 := hz
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

noncomputable def gradedProjection (F : NilpotentLieFiltration L s)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) :
    F.AssociatedGraded →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
  F.homogeneousGradedProjection (weightedFiltration weight s (weight_le s))
    (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
    (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ (projection_filtered F φ)

theorem gradedProjection_image_eq_bot
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF ((constantCoefficient s).comp φ.toLinearMap) x = 0) :
    W.map (gradedProjection F φ) = ⊥ := by
  apply bot_unique
  intro y hy
  change y = 0
  apply (constantCoefficient_eq_zero_iff s y).mp
  exact F.homogeneousGradedProjection_top_frequency_zero
    (weightedFiltration weight s (weight_le s))
    (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
    (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ (projection_filtered F φ)
    b ω hF W hW (constantCoefficient s) hη hy (mem_top s y)

theorem gradedProjection_eq_zero
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF ((constantCoefficient s).comp φ.toLinearMap) x = 0)
    (x : F.AssociatedGraded) (hx : x ∈ W) : gradedProjection F φ x = 0 := by
  have hm : gradedProjection F φ x ∈ W.map (gradedProjection F φ) := ⟨x, hx, rfl⟩
  rw [gradedProjection_image_eq_bot F b ω hF φ W hW hη] at hm
  exact (LieSubalgebra.mem_bot _).mp hm

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module PolynomialTranslationLie

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

noncomputable def projectedScalarFunctional
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) : F.AssociatedGraded →ₗ[ℚ] ℚ :=
  (constantCoefficient s).comp (gradedProjection F φ).toLinearMap

theorem projectedScalarFunctional_lie
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) (x y : F.AssociatedGraded) :
    projectedScalarFunctional F φ ⁅x, y⁆ = 0 := by
  change constantCoefficient s (gradedProjection F φ ⁅x, y⁆) = 0
  rw [(gradedProjection F φ).map_lie, constantCoefficient_lie]

theorem controlledFactorization_approximation [Fintype ι]
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) (hs : 0 < s)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hθ : ∀ i, rationalLogHeight
      (projectedScalarFunctional F φ (F.associatedGradedBasis b ω hF i)) ≤ p)
    (hfactor : F.ControlledSymbolFactorization b ω hF
      ((constantCoefficient s).comp φ.toLinearMap) T X p) :
    PolynomialRationalApproximation T (Real.exp ((p + 3) ^ 3))
      (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) (projectedScalarFunctional F φ) X) := by
  obtain ⟨m, E, P, Q, W, v, hm, hmp, hprod, hE, hQ, _, hW, _, hη, hP⟩ := hfactor
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hθH : ∀ i, RationalHeightLE
      (projectedScalarFunctional F φ (F.associatedGradedBasis b ω hF i)) H :=
    fun i => rationalHeightLE_ceil_exp (hθ i)
  have hc : (Fintype.card ι : ℝ) ≤ Real.exp p :=
    hdim.trans (by linarith [Real.add_one_le_exp p])
  have hcube : 0 ≤ p ^ 3 := by positivity
  have hden : ((H ^ Fintype.card ι * m : ℕ) : ℝ) ≤ Real.exp ((p + 3) ^ 3) := by
    calc
      _ ≤ (Real.exp (p + 1)) ^ Fintype.card ι * Real.exp p := by
        push_cast
        gcongr
      _ = Real.exp ((Fintype.card ι : ℝ) * (p + 1) + p) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hn := mul_le_mul_of_nonneg_right hdim (show 0 ≤ p + 1 by linarith)
        nlinarith [sq_nonneg p]
  have hslow : (Fintype.card ι : ℝ) * H * Real.exp p ≤ Real.exp ((p + 3) ^ 3) := by
    calc
      _ ≤ Real.exp p * Real.exp (p + 1) * Real.exp p := by gcongr
      _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  apply F.scalarSymbolPolynomial_approximation_of_factorization b ω hF (fun _ : σ => 1)
    (projectedScalarFunctional F φ) (projectedScalarFunctional_lie F φ) hs T hT
    (Real.exp ((p + 3) ^ 3)) (Real.exp p) (Real.exp_nonneg p) hm hθH hden hslow
    E P Q X hprod hE hQ W _ hP
  intro x hx
  change constantCoefficient s (gradedProjection F φ x) = 0
  rw [gradedProjection_eq_zero F b ω hF φ W hW hη x hx, map_zero]

theorem controlledFactorization_approximation_of_normalized_frequency [Fintype ι]
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) (hs : 0 < s)
    (η : weightedSubalgebra weight s →ₗ[ℚ] ℚ)
    (hη : η (centralRationalElement weight s hs 1) = 1)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hθ : ∀ i, rationalLogHeight
      (projectedScalarFunctional F φ (F.associatedGradedBasis b ω hF i)) ≤ p)
    (hfactor : F.ControlledSymbolFactorization b ω hF (η.comp φ.toLinearMap) T X p) :
    PolynomialRationalApproximation T (Real.exp ((p + 3) ^ 3))
      (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) (projectedScalarFunctional F φ) X) := by
  rw [frequency_eq_constantCoefficient s hs η hη] at hfactor
  exact controlledFactorization_approximation F b ω hF φ hs T hT X p hp hdim hθ hfactor

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module PolynomialTranslationLie RationalFilteredNilmanifold

variable {L : Type} [LieRing L] [LieAlgebra ℚ L] {e : ℕ}

noncomputable def pairScalarFunctional (s : ℕ)
    (D : RationalFilteredNilmanifold L s e) :
    (pi (pairModels (nilmanifold s) D)).filtration.AssociatedGraded →ₗ[ℚ] ℚ :=
  (constantCoefficient s).comp
    (gradedProjection (pi (pairModels (nilmanifold s) D)).filtration
      (liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true)).toLinearMap

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

theorem factorizationInputBudget_le_power (s c : ℕ) (hc : 2 ≤ c)
    {p : ℝ} (hp : 0 ≤ p) :
    p + factorizationInputOffset s ≤ (p + factorizationInputOffset s + c) ^ c := by
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hbase : 1 ≤ p + factorizationInputOffset s + c := by
    linarith [factorizationInputBudget_nonneg s hp]
  calc
    p + factorizationInputOffset s ≤ p + factorizationInputOffset s + c :=
      le_add_of_nonneg_right (Nat.cast_nonneg _)
    _ = (p + factorizationInputOffset s + c) ^ 1 := (pow_one _).symm
    _ ≤ (p + factorizationInputOffset s + c) ^ c := pow_le_pow_right₀ hbase (by omega)

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

variable {U : Type*}

noncomputable def orbit (s : ℕ) (_hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    (nilmanifold s).filtration.realification.PolynomialOrbit (fun _ : U => 1) :=
  translationCoordinatePolynomialOrbit weight s weight_pos (weight_le s)
    (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i)
    (rename Sum.inl P)
    (majorParameterRename_degree (fun _ : U => 1) weight
      ((mem_weightedSupportLE_one_iff P s).mpr hP))

theorem orbit_realEval (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) (u : U → ℝ) :
    bchRealTranslationHom weight s (weight_le s)
      ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
        (fun _ : U => 1) u (orbit s hs P hP)) = ⟨0, C (eval u P)⟩ := by
  have hslot : ∀ u : U → ℝ,
      specializeMajorParameters (RingHom.id ℝ) (rename (Sum.inl : U → U ⊕ Fin 0) P) u ∈
        weightedSupportLT weight s := by
    intro u α _
    have hα : α = 0 := Subsingleton.elim _ _
    change Finsupp.weight weight α < s
    simpa only [hα, map_zero] using hs
  change bchRealTranslationHom weight s (weight_le s)
    ((weightedFiltration weight s (weight_le s)).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u _) = _
  rw [orbit, translationCoordinatePolynomialOrbit_realEval _ _ _ _ _ _ _ _ hslot,
    specialize_rename]
  rfl

theorem orbit_buffered_eval (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) (u : U → ℝ) :
    bufferedTranslationPhase (localTentKernel 0 8 (by decide)) 0
      (bchRealTranslationHom weight s (weight_le s)
        ((nilmanifold s).filtration.realification.polynomialOrbitRealEval
          (fun _ : U => 1) u (orbit s hs P hP))) =
      (Real.fourierChar (eval u P) : ℂ) := by
  rw [orbit_realEval]
  rw [bufferedTranslationPhase_eq_chart (localTentKernel 0 8 (by decide)) 0 _ 0
    (fun i => Fin.elim0 i)]
  have hd : ∀ x y : Fin 0 → ℝ, dist x y = 0 := by
    intro x y
    rw [Subsingleton.elim x y, dist_self]
  simp [bufferedTranslationTerm, translationPhaseArgument, localTentKernel, hd]

theorem zero_base_orbit (s : ℕ) :
    translationBasePolynomialOrbit weight s weight_pos (weight_le s)
      (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i) = 1 := by
  let := phaseBasisFintype s
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (translationBasePolynomialOrbit weight s weight_pos (weight_le s)
    (fun _ : Fin 0 => (0 : MvPolynomial U ℝ)) (fun i => Fin.elim0 i)).log = 0
  rw [translationBasePolynomialOrbit_log]
  apply VectorPolynomial.coefficients.injective
  ext α
  rw [VectorPolynomial.coefficients_ofCoordinates]
  simp [translationBaseCoordinatePolynomial]

theorem orbit_eq_pure (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    orbit s hs P hP = translationPurePolynomialOrbit weight s weight_pos (weight_le s)
      (rename Sum.inl P)
      (majorParameterRename_degree (fun _ : U => 1) weight
        ((mem_weightedSupportLE_one_iff P s).mpr hP)) := by
  rw [orbit, translationCoordinatePolynomialOrbit, zero_base_orbit, one_mul]

theorem orbit_log (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    letI := phaseBasisFintype s
    (orbit s hs P hP).log =
      VectorPolynomial.ofCoordinates (R := ℚ) ((weightedBasis weight s weight_pos).baseChange ℝ)
        (translationPolynomialCoordinatePolynomial weight s (rename Sum.inl P)) := by
  rw [orbit_eq_pure]
  rfl

theorem orbit_coordinate (s : ℕ) (hs : 0 < s)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s)
    (i : WeightedBasisIndex weight s) :
    VectorPolynomial.coordinate
      (((weightedBasis weight s weight_pos).baseChange ℝ).coord i).toAddMonoidHom
      (orbit s hs P hP).log = P := by
  let := phaseBasisFintype s
  rw [orbit_log, VectorPolynomial.coordinate_ofCoordinates]
  cases i with
  | inl i => exact Fin.elim0 i
  | inr α =>
      change polynomialSlotCoefficient α.val (rename Sum.inl P) = P
      rw [Subsingleton.elim α.val 0, phaseSlotCoefficient_rename]

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

theorem phasePair_finrank_le_of_geometry
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {s t e : ℕ}
    (D : RationalFilteredNilmanifold L t e) {p : ℝ}
    (hD : D.GeometryComplexityLE p) :
    (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤ budget s + p := by
  let : FiniteDimensional ℚ (weightedSubalgebra weight s) :=
    (nilmanifold s).basis.finiteDimensional_of_finite
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let : ∀ i : Bool, Module.Finite ℚ (BoolLieFamily (weightedSubalgebra weight s) L i) := by
    intro i
    cases i
    · exact (inferInstance : Module.Finite ℚ L)
    · exact (inferInstance : Module.Finite ℚ (weightedSubalgebra weight s))
  have hphase : (finrank ℚ (weightedSubalgebra weight s) : ℝ) ≤ budget s := by
    rw [Module.finrank_eq_card_basis (nilmanifold s).basis, Fintype.card_fin]
    exact (nilmanifold_geometry s).1
  have hdim : (finrank ℚ L : ℝ) ≤ p := by
    rw [Module.finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  have hpair : finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) =
      finrank ℚ (weightedSubalgebra weight s) + finrank ℚ L := by
    change finrank ℚ (∀ i : Bool, BoolLieFamily (weightedSubalgebra weight s) L i) = _
    rw [Module.finrank_pi_fintype, Fintype.sum_bool]
    rfl
  rw [hpair, Nat.cast_add]
  exact add_le_add hphase hdim

theorem phasePair_finrank_le
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {s t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L t e) {U : Type*} {ω : U → ℕ}
    (R : D.Niltest ω) {p : ℝ} (hR : R.ComplexityLE p) :
    (finrank ℚ (PairAlgebra (weightedSubalgebra weight s) L) : ℝ) ≤ budget s + p :=
  phasePair_finrank_le_of_geometry D hR.1

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem orbit_symbol_constantCoefficient {U : Type*} (s : ℕ) (hs : 0 < s)
    (G : NilpotentLieFiltration (weightedSubalgebra weight s) s)
    (hG : ∀ j, G.layer j = Submodule.span ℚ
      (weightedBasis weight s weight_pos '' {i | j ≤ weightedBasisGrade weight s i}))
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ s) :
    coordinate (realifyFunctional (constantCoefficient s)).toAddMonoidHom
      (G.realSymbolRepresentative
        (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
        hG (fun _ : U => 1)
        (G.realSymbolOfPolynomial
          (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
          hG (fun _ : U => 1)
          (orbit s hs P hP).log)) = homogeneousComponent s P := by
  let := phaseBasisFintype s
  rw [orbit_log, NilpotentLieFiltration.realSymbolRepresentative_ofCoordinates,
    constantCoefficient_coordinate_ofCoordinates s hs]
  have hcoord := orbit_coordinate s hs P hP (constantBasisIndex s hs)
  rw [orbit_log, coordinate_ofCoordinates] at hcoord
  rw [hcoord, constantBasisIndex_grade]
  rfl

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end


