-- Prove2me | Definitions.Def_OAIE3v2B179
-- name    : OAIE3v2B179
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:20:26.557978+00:00
-- url     : https://prove2.me/theorems/40ce187c-8b05-4290-8431-a5ea87fe7fb0
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 181 of 311
-- statement:
--   Definitions bundle 181 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162` of this split.
--
--   Modules: `Estimates/AntisymmetricPairVerticalModel.lean`, `Estimates/CommonDependentWordLayers.lean`, `Estimates/ControlledDetectedTranslationBaseBounds.lean`, `Estimates/CorrelatingVerticalPair.lean`, `Estimates/MixedPairFrozenEquivalence.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/NativeCommonModelQuadruples.lean`, `Estimates/NativeGlobalErrorSplitting.lean`, `Estimates/NativeMixedReflectionBridge.lean`, `Estimates/NativeProductCoefficient.lean`, `Estimates/NativeProductVerticalization.lean`, `Estimates/NativeResidualMultiplier.lean`, `Estimates/NativeRetainedTargetCubeIntervals.lean`, `Estimates/NativeSeparatedSumIntervals.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/QuadraticBoundedFamily.lean`, `Estimates/QuadraticPairCorrelator.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Estimates/TranslationMajorTwistedCorrelationStepDrop.lean`, `Geometry/CubeSignalCoordinates.lean`, `Geometry/NativeCoordinateErrorReduction.lean`, `Lattices/NativeProperAffineRecovery.lean`, `Lattices/NativeRetainedIntegerMultilinearQuadruples.lean`, `Lattices/SelectedResidueCutoffDomination.lean`, `Linear/BinaryLowerRankFamily.lean`, `Linear/BoundedRankIntegralModel.lean`, `Linear/CommonRankCoefficientCorrections.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/NativePairSymbolProjection.lean`, `Linear/NativeRankRelationExistence.lean`, `Linear/UnconditionedJointFrameDomination.lean`, `Polynomial/AntisymmetricPairPolynomial.lean`, `Polynomial/CommonAnchorPolynomialCorrections.lean`, `Polynomial/MixedPairPolynomial.lean`, `Polynomial/NativeDegreeRankFamily.lean`, `Polynomial/TranslationPolynomialSymbolLiftHom.lean`, `Probability/PositiveDensityNormalization.lean`, `Sampling/AveragedNormalizedTwistForecastJointModel.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeDegreeRankFamily
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

namespace NativeDegreeRankFamily

variable {s r : ℕ} {A : Type*} {p q : ℝ} (W : NativeDegreeRankFamily s r A p)

noncomputable def evalCyclic (N : ℕ) [NeZero N] (i : Fin W.outputDim) (a : A) (n : ZMod N) : ℂ :=
  W.eval i a (n.val : ℤ)

end NativeDegreeRankFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
namespace OAI

section

namespace Erdos3

noncomputable def nativeCorrelationResidual {s r N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (family : NativeDegreeRankFamily s r (ZMod N) p) (h : ZMod N)
    (ij : Fin mixed.outputDim × Fin family.outputDim) (x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (mixed.evalCyclic N ij.1 (correlationInput h x)) *
    star (family.evalCyclic N ij.2 h x)

structure NativeCorrelationStructure (s r N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-p) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p
  family : NativeDegreeRankFamily s r (ZMod N) p
  correlation : ∀ h ∈ shifts, Nonempty (NativeVectorCorrelation (s - 1) N p
    (nativeCorrelationResidual f mixed family h))

end Erdos3

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def selectedWitness (h : W.shifts) :
    NativeVectorCorrelation (s - 1) N p (nativeCorrelationResidual f W.mixed W.family h) :=
  Classical.choice (W.correlation h h.property)

end Erdos3.NativeCorrelationStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGlobalErrorSplitting
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

def GlobalErrorSplittingStatement (s C : ℕ) : Prop :=
    ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f)
      {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d}
      (T : D.Niltest (fun _ : Fin 2 => 1)) (b : ℝ),
      2 ≤ b → p ≤ b → T.ComplexityLE b →
      ∀ (H : Finset (ZMod N)) (hsub : H ⊆ W.shifts), H.Nonempty →
      ∀ m : ZMod N → ZMod N → ℂ, (∀ h x, ‖m h x‖ ≤ 1) → (∀ x, ‖f x‖ ≤ 1) →
      (∀ h (hh : h ∈ H), Real.exp (-b) ≤
        ‖𝔼 x, multiplicativeDerivative f h x * star
          (m h x * (W.selectedWitness ⟨h, hsub hh⟩).test.evalCyclic N (fun _ => x) *
            T.eval ![(h.val : ℤ), (x.val : ℤ)])‖) →
      ∃ (weight : ZMod N → ℂ) (S : Finset (ZMod N)),
        (∀ x, ‖weight x‖ ≤ 1) ∧ S ⊆ H ∧ S.Nonempty ∧
        Real.exp (-((b + C) ^ C)) * (H.card : ℝ) ≤ (S.card : ℝ) ∧
        ∀ h ∈ S, Nonempty (NativeVectorCorrelation (s - 1) N ((b + C) ^ C)
          (fun _ : Unit => fun x => multiplicativeDerivative f h x * star (m h x * weight x)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateErrorReduction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

def CoordinateErrorReductionStatement (σ : Type) [Fintype σ] [DecidableEq σ] (s C : ℕ) : Prop :=
  ∀ (i : σ) {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
    (T : D.Niltest (fun _ : σ => 1)), 2 ≤ p → T.ComplexityLE p →
    ∀ {G X : Type} (H : Finset G), H.Nonempty →
    ∀ (S : G → Finset X) (b : G → σ → ℤ) (n : G → X → ℤ) (f : G → X → ℂ),
    (∀ h ∈ H, (S h).Nonempty) → (∀ h ∈ H, ∀ x ∈ S h, ‖f h x‖ ≤ Real.exp p) →
    (∀ h ∈ H, Real.exp (-p) ≤
      ‖𝔼 x ∈ S h, f h x * T.eval (Function.update (b h) i (n h x))‖) →
    ∃ (weight : ℤ → ℂ) (Q : Finset G), (∀ z, ‖weight z‖ ≤ 1) ∧ Q ⊆ H ∧ Q.Nonempty ∧
      Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (Q.card : ℝ) ∧
      ∀ h ∈ Q, ∃ v : ℤ → ℂ,
        (∀ z, ‖v z‖ ≤ 1) ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => v (x ()))) ∧
        Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x ∈ S h, f h x * weight (n h x) * v (n h x)‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeCorrelationStructure

noncomputable def multilinearFactor {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s r N p f)
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) q)
    (k : Fin V.outputDim) (i : Fin W.family.outputDim) (h : ZMod N) (n : ℤ) : ℂ :=
  V.eval k (fun j => correlationInput (h.val : ℤ) n j.1) * W.family.eval i h n

end NativeCorrelationStructure

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3

structure NativeMultilinearIntervalFamily {s r N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℂ} (W : NativeCorrelationStructure s r N p f) (q : ℝ) where
  mixed : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) q
  mixed_dim : mixed.dim ≤ 2 ^ (s + 1) * W.mixed.dim
  mixed_symmetric : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
    mixed.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
      mixed.eval k x
  coordinate : Fin mixed.outputDim
  rankCoordinate : Fin W.family.outputDim
  weight : ZMod N → ℂ
  weight_norm : ∀ x, ‖weight x‖ ≤ 1
  shifts : Finset (ZMod N)
  shifts_subset : shifts ⊆ W.shifts
  shifts_nonempty : shifts.Nonempty
  shifts_short : CyclicShortShiftSet shifts
  shifts_density : Real.exp (-q) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  lower : NativeCrossWitnesses (s - 1) N q (fun x => f x * star (weight x)) f
    (fun h x => W.multilinearFactor mixed coordinate rankCoordinate h x.val) shifts
  quadruples : Finset (ZMod N × ZMod N × ZMod N)
  quadruples_nonempty : quadruples.Nonempty
  quadruples_density : Real.exp (-q) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (quadruples.card : ℝ)
  interval : ∀ t : quadruples, NativeIntegerQuadrupleWitness lower
    (W.multilinearFactor mixed coordinate rankCoordinate) q t

end Erdos3

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

def delta (t : B.quadruples) : ℤ := cyclicBranchOffset t.val.1 (B.interval t).branch

def sample (t : B.quadruples) (n : ℤ) : Fin 5 → ℤ :=
  ![(t.val.2.1.val : ℤ), (t.val.2.1 - t.val.1).val, t.val.2.2.val, n, B.delta t]

end Erdos3.NativeMultilinearIntervalFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3

structure NativeRankRelation {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (H : Finset (ZMod N)) (p q : ℝ) where
  quadruples : Finset (ZMod N × ZMod N × ZMod N)
  quadruples_nonempty : quadruples.Nonempty
  density : Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ quadruples.card
  branch : Bool
  interval : ∀ t : quadruples, NativeRankInterval W out H t.val branch p q

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductCoefficient
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem nativeHorizontalCoefficientHom_eq_realHorizontalMap (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w)
    (v : (F.layer (Finsupp.weight w α) 1).baseChange ℝ)
    (hv : v.val = coefficients g.log α) :
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
      F.realHorizontalMap (Finsupp.weight w α) v := by
  obtain ⟨x, hx⟩ := F.associatedDegree.realAdaptedPolynomialTensor_surjective w b ω hF
    (⟨g.log, g.property⟩ : F.associatedDegree.realification.adaptedLieSubalgebra w)
  have hlog : g.log = F.associatedDegree.realAdaptedPolynomialMap w x :=
    (congrArg Subtype.val hx).symm
  have heq : v = realificationSubmoduleEquiv (F.layer (Finsupp.weight w α) 1)
      ((F.rankLayerCoefficient w α).baseChange ℝ x) := by
    apply Subtype.ext
    rw [realificationSubmoduleEquiv_coe, F.rankLayerCoefficient_tensor_coe, hv, hlog]
  rw [F.nativeHorizontalCoefficientHom_tensor hs b ω hF w α g x hlog, heq,
    F.realHorizontalMap_baseChange, F.rankLayerCoefficient_tensor_horizontal]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ)

theorem native_coefficient_mem_horizontalPreimage {σ ι : Type*} (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w)
    (U : Submodule ℚ (F.HigherHorizontal (Finsupp.weight w α))) :
    coefficients g.log α ∈ (F.horizontalPreimage (Finsupp.weight w α) U).baseChange ℝ ↔
      Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) ∈
        U.baseChange ℝ := by
  obtain ⟨x, hx⟩ := F.associatedDegree.realAdaptedPolynomialTensor_surjective w b ω hF
    (⟨g.log, g.property⟩ : F.associatedDegree.realification.adaptedLieSubalgebra w)
  have hlog : g.log = F.associatedDegree.realAdaptedPolynomialMap w x :=
    (congrArg Subtype.val hx).symm
  let v := realificationSubmoduleEquiv (F.layer (Finsupp.weight w α) 1)
    ((F.rankLayerCoefficient w α).baseChange ℝ x)
  have hv : v.val = coefficients g.log α := by
    rw [hlog]
    exact F.rankLayerCoefficient_tensor_coe w α x
  rw [F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α g v hv,
    ← hv, F.mem_real_horizontalPreimage]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem polynomialOrbit_coefficient_mem_rank_one (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w) :
    coefficients g.log α ∈ (F.layer (Finsupp.weight w α) 1).baseChange ℝ := by
  have h := (F.associatedDegree.realification.adapted_iff_coefficients w g.log).mp g.adapted α
  change coefficients g.log α ∈ (F.layer (Finsupp.weight w α) 0).baseChange ℝ at h
  rwa [F.rank_zero_eq_one] at h

theorem polynomialOrbit_log_mul_mod_rank_two (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : F.associatedDegree.realification.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      (F.layer (Finsupp.weight w α) 2).baseChange ℝ := by
  let x : (F.layer (Finsupp.weight w α) 1).baseChange ℝ :=
    ⟨coefficients g.log α, F.polynomialOrbit_coefficient_mem_rank_one w α g⟩
  let y : (F.layer (Finsupp.weight w α) 1).baseChange ℝ :=
    ⟨coefficients h.log α, F.polynomialOrbit_coefficient_mem_rank_one w α h⟩
  let z : (F.layer (Finsupp.weight w α) 1).baseChange ℝ :=
    ⟨coefficients (g * h).log α, F.polynomialOrbit_coefficient_mem_rank_one w α (g * h)⟩
  apply (F.realHorizontalMap_eq (Finsupp.weight w α) z (x + y)).mp
  rw [← F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α (g * h) z rfl,
    map_mul]
  change Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) +
      Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α h) = _
  rw [F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α g x rfl,
    F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α h y rfl, map_add]

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)
  (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)

noncomputable def refilteredProjectionImage (d : ℕ) : Submodule ℚ (Fin 4 → W.L) :=
  ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U d).map (I.rankProjection i).toLinearMap

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}

namespace SunflowerWitness

variable {I : NativeRankInterval W out H t branch p q} {P : ℝ} (D : I.SunflowerWitness P)

noncomputable def projection (d : ℕ) : Submodule ℚ (Fin 4 → W.L) :=
  I.refilteredProjectionImage D.index D.subalgebra d

end SunflowerWitness

end NativeRankInterval

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
namespace OAI

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankRelation

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)}

structure CommonData (R : NativeRankRelation W out H p q) (P : ℝ) where
  quadruples : Finset (ZMod N × ZMod N × ZMod N)
  subset : quadruples ⊆ R.quadruples
  nonempty : quadruples.Nonempty
  density : Real.exp (-P) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ quadruples.card
  spaces : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L)
  witness : ∀ t, (ht : t ∈ quadruples) → (R.interval ⟨t, subset ht⟩).SunflowerWitness P
  projection : ∀ t (ht : t ∈ quadruples) (d : Fin (s + 1)),
    (witness t ht).projection d.val = spaces d

end NativeRankRelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CommonAnchorPolynomialCorrections
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

namespace DegreeRankLieFiltration

theorem positiveUnivariate_horizontal_mem {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : ∀ d : Fin s,
      (F.layer (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () (d.val + 1))) 1).baseChange ℝ) :
    positiveUnivariate (fun d => (v d).val) ∈
      F.realification.associatedDegree.adaptedLieSubalgebra (fun _ : Unit => 1) := by
  apply positiveUnivariate_coefficients_mem
  intro d
  change (v d).val ∈
    (F.layer (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () (d.val + 1))) 0).baseChange ℝ
  rw [F.rank_zero_eq_one]
  exact (v d).property

end DegreeRankLieFiltration

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BinaryLowerRankFamily
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeUnitRankFamily {σ : Type*} (w : σ → ℕ) (s r : ℕ)
    (τ I : Type*) [Fintype I] (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L s dim
  rank : model.DegreeRankStructure r
  complexity : rank.ComplexityLE p
  test : I → model.Niltest w
  test_norm : ∀ i, (test i).normBound = 1
  test_complexity : ∀ i, (test i).ComplexityLE p
  unit : ∀ x, ∑ i, ‖(test i).observable x‖ ^ 2 = 1
  orbit : τ → model.filtration.realification.PolynomialOrbit w
  normalized : ∀ t, model.filtration.realification.polynomialOrbitEval w 0 (orbit t) = 1

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra
  NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd
  NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff

namespace NativeUnitRankFamily

variable {σ τ I : Type*} [Fintype I] {w : σ → ℕ} {s r : ℕ} {p q : ℝ}
  (F : NativeUnitRankFamily w s r τ I p)

noncomputable def eval (t : τ) (i : I) (x : σ → ℤ) : ℂ :=
  (F.test i).observable (QuotientGroup.mk
    (F.model.filtration.realification.polynomialOrbitEval w x (F.orbit t)))

noncomputable def mono (hpq : p ≤ q) : NativeUnitRankFamily w s r τ I q :=
  { F with
    complexity := F.complexity.mono F.rank hpq
    test_complexity := fun i => (F.test_complexity i).mono hpq }

@[simp] theorem mono_eval (hpq : p ≤ q) (t : τ) (i : I) (x : σ → ℤ) :
    (F.mono hpq).eval t i x = F.eval t i x := rfl

end NativeUnitRankFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_dense_cyclic_model_of_integer_vectors {I : Type*} [Fintype I]
    (A : Finset (I → ℤ)) (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) (s : ℕ) (hs : 0 < s) :
    ∃ (N : ℕ) (J : Finset (I → ℤ)) (B : Finset (ZMod N)) (f : (I → ℤ) → ZMod N),
      0 < N ∧ J.Nonempty ∧ J ⊆ A ∧ A.card ≤ (2 * s) * J.card ∧
      B.Nonempty ∧ B = J.image f ∧ B.card = J.card ∧
      IsAddFreimanIso s (J : Set _) (B : Set _) f ∧
      (N : ℝ) ≤ 2 * K ^ (2 * s) * A.card ∧
      (4 * (s : ℝ) * K ^ (2 * s))⁻¹ ≤ (B.card : ℝ) / N := by
  classical
  obtain ⟨e, he⟩ := exists_integer_freiman_embedding A s
  let X := A.image e
  have hX : X.Nonempty := hA.image e
  have hXcard : X.card = A.card := Finset.card_image_of_injOn he.bijOn.injOn
  have hXsmall : ((X - X).card : ℝ) ≤ K * X.card := by
    have hdiff : X - X = (A - A).image e := by
      ext z
      simp only [X, Finset.mem_sub, Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨x - y, ⟨x, hx, y, hy, rfl⟩, e.map_sub x y⟩
      · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
        exact ⟨e x, ⟨x, hx, rfl⟩, e y, ⟨y, hy, rfl⟩, (e.map_sub x y).symm⟩
    rw [hdiff, hXcard]
    exact (show (((A - A).image e).card : ℝ) ≤ (A - A).card by
      exact_mod_cast Finset.card_image_le).trans hsmall
  obtain ⟨N, X', B, g, hN, hX'ne, hX'sub, hsize, hBne, hB, hBcard,
      hg, hNsize, hdensity⟩ := exists_dense_cyclic_model X hX hK hXsmall s hs
  let J := A.filter fun x => e x ∈ X'
  have hJA : J ⊆ A := Finset.filter_subset _ _
  have hJimage : J.image e = X' := by
    ext z
    constructor
    · rintro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hX'sub hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  have heJ : IsAddFreimanIso s (J : Set _) (X' : Set ℤ) e := by
    apply he.subset hJA
    refine ⟨?_, he.bijOn.injOn.mono hJA, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro z hz
      rw [← hJimage] at hz
      exact Finset.mem_image.mp hz
  have hJcard : X'.card = J.card := by
    rw [← hJimage]
    exact Finset.card_image_of_injOn heJ.bijOn.injOn
  have hJne : J.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hJcard]
    exact hX'ne.card_pos
  have hJsize : A.card ≤ (2 * s) * J.card := by
    simpa only [hXcard, hJcard] using hsize
  have hBimage : B = J.image (g ∘ e) := by
    rw [hB, ← hJimage, Finset.image_image]
  have hNsize' : (N : ℝ) ≤ 2 * K ^ (2 * s) * A.card := by
    simpa only [hXcard] using hNsize
  exact ⟨N, J, B, g ∘ e, hN, hJne, hJA, hJsize, hBne, hBimage,
    hBcard.trans hJcard, hg.comp heJ, hNsize', hdensity⟩

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_dense_cyclicProduct_integer_model {I : Type*} [Fintype I]
    (q : I → ℕ) [∀ i, NeZero (q i)] (A : Finset (∀ i, ZMod (q i)))
    (hA : A.Nonempty) {K : ℝ} (hK : 0 < K)
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) :
    ∃ (N : ℕ) (J : Finset (∀ i, ZMod (q i))) (B : Finset (ZMod N))
      (g : (I → ℤ) → ZMod N),
      0 < N ∧ J.Nonempty ∧ J ⊆ A ∧
      A.card ≤ 16 ^ (Fintype.card I + 1) * J.card ∧
      B.Nonempty ∧ B = (J.image (cyclicProductLift q)).image g ∧ B.card = J.card ∧
      IsAddFreimanIso 8 (J : Set _) (J.image (cyclicProductLift q) : Set (I → ℤ))
        (cyclicProductLift q) ∧
      IsAddFreimanIso 8 (J.image (cyclicProductLift q) : Set (I → ℤ)) (B : Set _) g ∧
      (N : ℝ) ≤ 2 * (K * 16 ^ Fintype.card I) ^ 16 * A.card ∧
      (32 * (K * 16 ^ Fintype.card I) ^ 16)⁻¹ ≤ (B.card : ℝ) / N := by
  classical
  obtain ⟨A₀, hA₀, hA₀A, hlarge, he⟩ := exists_large_cyclicProduct_integer_lift q A hA
  let e := cyclicProductLift q
  let X := A₀.image e
  let R : ℝ := K * 16 ^ Fintype.card I
  have hR : 0 < R := mul_pos hK (by positivity)
  have hX : X.Nonempty := hA₀.image e
  have hXcard : X.card = A₀.card := Finset.card_image_of_injOn he.bijOn.injOn
  have hdiff : (X - X).card = (A₀ - A₀).card :=
    card_difference_image_of_freiman A₀ e (he.mono (hmn := by decide))
  have hsub : A₀ - A₀ ⊆ A - A := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    exact Finset.mem_sub.mpr ⟨a, hA₀A ha, b, hA₀A hb, rfl⟩
  have hlargeR : (A.card : ℝ) ≤ 16 ^ Fintype.card I * A₀.card := by
    exact_mod_cast hlarge
  have hXsmall : ((X - X).card : ℝ) ≤ R * X.card := by
    rw [hdiff, hXcard]
    calc
      ((A₀ - A₀).card : ℝ) ≤ (A - A).card := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ K * A.card := hsmall
      _ ≤ K * (16 ^ Fintype.card I * A₀.card) := mul_le_mul_of_nonneg_left hlargeR hK.le
      _ = R * A₀.card := by simp only [R, mul_assoc]
  obtain ⟨N, X', B, g, hN, hX', hX'X, hsize, hB, hBimage, hBcard, hg, hNsize, hdensity⟩ :=
    exists_dense_cyclic_model_of_integer_vectors X hX hR hXsmall 8 (by decide)
  let J := A₀.filter fun x => e x ∈ X'
  have hJA₀ : J ⊆ A₀ := Finset.filter_subset _ _
  have hJimage : J.image e = X' := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hx).2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hX'X hz)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hz⟩, rfl⟩
  have heJ : IsAddFreimanIso 8 (J : Set _) (X' : Set (I → ℤ)) e := by
    apply he.subset hJA₀
    refine ⟨?_, he.bijOn.injOn.mono hJA₀, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro z hz
      rw [← hJimage] at hz
      exact Finset.mem_image.mp hz
  have hJcard : X'.card = J.card := by
    rw [← hJimage]
    exact Finset.card_image_of_injOn heJ.bijOn.injOn
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hJcard]
    exact hX'.card_pos
  have hsize₀ : A₀.card ≤ 16 * J.card := by
    simpa only [hXcard, hJcard, Nat.reduceMul] using hsize
  have hsize' : A.card ≤ 16 ^ (Fintype.card I + 1) * J.card := by
    calc
      A.card ≤ 16 ^ Fintype.card I * A₀.card := hlarge
      _ ≤ 16 ^ Fintype.card I * (16 * J.card) := Nat.mul_le_mul_left _ hsize₀
      _ = _ := by rw [pow_succ, mul_assoc]
  have hBimage' : B = (J.image e).image g := by
    rw [hJimage]
    exact hBimage
  have hNsize' : (N : ℝ) ≤ 2 * R ^ 16 * A.card := by
    have hcard : (X.card : ℝ) ≤ A.card := by rw [hXcard]; exact_mod_cast Finset.card_le_card hA₀A
    have hn : (N : ℝ) ≤ 2 * R ^ 16 * X.card := by
      simpa only [Nat.reduceMul] using hNsize
    exact hn.trans
      (mul_le_mul_of_nonneg_left hcard (by positivity))
  refine ⟨N, J, B, g, hN, hJ, hJA₀.trans hA₀A, hsize', hB, hBimage',
    hBcard.trans hJcard, ?_, ?_, hNsize', ?_⟩
  · change IsAddFreimanIso 8 (J : Set _) (J.image e : Set (I → ℤ)) e
    rw [hJimage]
    exact heJ
  · change IsAddFreimanIso 8 (J.image e : Set (I → ℤ)) (B : Set _) g
    rw [hJimage]
    exact hg
  · norm_num only [Nat.reduceMul, Nat.cast_ofNat, mul_one] at hdensity
    simpa only [R, show (4 : ℝ) * 8 = 32 by norm_num] using hdensity

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

variable {I : Type*}

theorem exists_variableIntegerGraph_cyclic_model [Fintype I]
    (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)]
    (A : Finset (ZMod N × (∀ i, ZMod (M i)))) (hA : A.Nonempty)
    {K : ℝ} (hK : 0 < K) (hsmall : ((A - A).card : ℝ) ≤ K * A.card) :
    ∃ (Q : ℕ) (S : Finset (Option I → ℤ)) (B : Finset (ZMod Q))
      (g : (Option I → ℤ) → ZMod Q),
      0 < Q ∧ S.Nonempty ∧ S ⊆ A.image (variableIntegerGraphLift N M) ∧
      A.card ≤ 16 ^ (Fintype.card I + 2) * S.card ∧
      B.Nonempty ∧ B = S.image g ∧ B.card = S.card ∧
      IsAddFreimanIso 8 (S : Set _) (B : Set _) g ∧
      (Q : ℝ) ≤ 2 * (K * 16 ^ (Fintype.card I + 1)) ^ 16 * A.card ∧
      (32 * (K * 16 ^ (Fintype.card I + 1)) ^ 16)⁻¹ ≤ (B.card : ℝ) / Q := by
  classical
  let q : Option I → ℕ := variableRoundedGraphModuli N M
  let _ : ∀ i, NeZero (q i) := variableRoundedGraphModuli_neZero N M
  let e := variableRoundedGraphCoordinateEquiv (I := I) N M
  let X := A.image e
  have he : IsAddFreimanIso 8 (A : Set _) (X : Set _) e :=
    isAddFreimanIso_of_injOn_iterated_sums e.toAddMonoidHom A 8
      e.injective.injOn e.injective.injOn
  have hX : X.Nonempty := hA.image e
  have hXcard : X.card = A.card := Finset.card_image_of_injOn e.injective.injOn
  have hXsmall : ((X - X).card : ℝ) ≤ K * X.card := by
    rw [card_difference_image_of_freiman A e (he.mono (hmn := by decide)), hXcard]
    exact hsmall
  obtain ⟨Q, J, B, g, hQ, hJ, hJX, hsize, hB, hBimage, hBcard, hlift, hg,
      hQsize, hdensity⟩ := exists_dense_cyclicProduct_integer_model q X hX hK hXsmall
  let S := J.image (cyclicProductLift q)
  have hScard : S.card = J.card := Finset.card_image_of_injOn hlift.bijOn.injOn
  have hSA : S ⊆ A.image (variableIntegerGraphLift N M) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hJX hx)
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  refine ⟨Q, S, B, g, hQ, hJ.image _, hSA, ?_, hB, hBimage,
    hBcard.trans hScard.symm, hg, ?_, ?_⟩
  · simpa only [hXcard, hScard, Fintype.card_option, Nat.add_assoc] using hsize
  · simpa only [hXcard, Fintype.card_option] using hQsize
  · simpa only [Fintype.card_option] using hdensity

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct Pointwise

structure NativeCyclicModel (degree N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest (fun _ : Unit => 1)
  norm : test.normBound ≤ 1
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = test.evalCyclic N (fun _ => x)

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

def nativeCyclicFunctions (degree N : ℕ) [NeZero N] (p : ℝ) : Set (ZMod N → ℂ) :=
  {f | Nonempty (NativeCyclicModel degree N p f)}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def CyclicNativeInverse (s C : ℕ) : Prop :=
  ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → ∀ f : ZMod N → ℂ,
    (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 1) f →
    ∃ g ∈ nativeCyclicFunctions s N ((p + C) ^ C),
      Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x, f x * star (g x)‖

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeCommonDerivativeModels (degree N : ℕ) [NeZero N] (p : ℝ)
    (f : ZMod N → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  geometry : model.GeometryComplexityLE p
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-p) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  test : ZMod N → model.Niltest (fun _ : Unit => 1)
  norm : ∀ h, (test h).normBound ≤ 1
  complexity : ∀ h, (test h).ComplexityLE p
  common_observable : ∀ h k, (test h).observable = (test k).observable
  correlation : ∀ h ∈ shifts, Real.exp (-p) ≤
    ‖𝔼 x, multiplicativeDerivative f h x * star ((test h).evalCyclic N (fun _ => x))‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
namespace OAI

section

namespace Erdos3.FreeDegreeRankLieAlgebra

open VectorPolynomial

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (hr : r ≤ s) {σ : Type*} (g : X → σ →₀ ℕ)

theorem gradingHom_tree (a : FreeMagma X) :
    gradingHom X s r w hw hr g (lieTreeEval (of X s r w hw) a) =
      monomial (lieTreeMultidegree g a) (lieTreeEval (of X s r w hw) a) := by
  induction a using FreeMagma.rec with
  | of x => exact gradingHom_of X s r w hw hr g x
  | mul a b ha hb =>
    change gradingHom X s r w hw hr g
      ⁅lieTreeEval (of X s r w hw) a, lieTreeEval (of X s r w hw) b⁆ = _
    rw [LieHom.map_lie, ha, hb, lie_monomial]
    rfl

theorem gradingHom_eval_one (x : FreeDegreeRankLieAlgebra X s r w hw) :
    eval (fun _ : σ => (1 : ℚ)) (gradingHom X s r w hw hr g x) = x := by
  have h : (evalLie (fun _ : σ => (1 : ℚ))).comp (gradingHom X s r w hw hr g) =
      (LieHom.id : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw) := by
    apply hom_ext w hw
    intro y
    change eval (fun _ : σ => (1 : ℚ)) (gradingHom X s r w hw hr g (of X s r w hw y)) = _
    rw [gradingHom_of]
    simp
  exact LieHom.congr_fun h x

noncomputable def gradingExpansion : LieGradingExpansion (of X s r w hw) g where
  expand := (gradingHom X s r w hw hr g).toLinearMap
  expand_tree := gradingHom_tree X s r w hw hr g
  eval_one := gradingHom_eval_one X s r w hw hr g

include hr in
theorem homogeneousSpan_inter (S T : Set (σ →₀ ℕ)) :
    homogeneousLieSpan (of X s r w hw) g (S ∩ T) =
      homogeneousLieSpan (of X s r w hw) g S ⊓ homogeneousLieSpan (of X s r w hw) g T :=
  (gradingExpansion X s r w hw hr g).span_inter S T

end Erdos3.FreeDegreeRankLieAlgebra

end

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem FreeDegreeRankLieAlgebra.lift_top_mem_degreeLengthSpan {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ i, 0 < w i)
    (f : X → L) (hf : ∀ i, f i ∈ F.layer (w i) 0)
    {x : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ (filtration X s r w hw F.rank_le_degree).layer s r) :
    lift F w hw f hf x ∈ weightedLieDegreeLengthSpan f w s r := by
  obtain ⟨a, ha, rfl⟩ := hx
  change FreeWeightedNilpotentLieAlgebra.lift F.associatedDegree w f hf a ∈
    weightedLieDegreeLengthSpan f w s r
  exact (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).top_rank_map_mem_degreeLengthSpan
    (FreeWeightedNilpotentLieAlgebra.lift F.associatedDegree w f hf) f w
    (fun _ _ _ h => FreeWeightedNilpotentLieAlgebra.lift_layer_mem_degreeLengthSpan
      F.associatedDegree w hw f hf h) ha

theorem FreeDegreeRankLieAlgebra.lift_top_frequency_zero
    {A : Type*} [AddCommGroup A] [Module ℚ A] {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ i, 0 < w i)
    (f : X → L) (hf : ∀ i, f i ∈ F.layer (w i) 0) (η : L →ₗ[ℚ] A)
    (hzero : ∀ a : FreeMagma X, lieTreeWeight w a = s → a.length = r → η (lieTreeEval f a) = 0)
    {x : FreeDegreeRankLieAlgebra X s r w hw}
    (hx : x ∈ (filtration X s r w hw F.rank_le_degree).layer s r) :
    η (lift F w hw f hf x) = 0 := by
  exact weightedLieDegreeLengthSpan_top_le_ker F f w
    (fun i => by rw [← F.rank_zero_eq_one]; exact hf i) η hzero
    (lift_top_mem_degreeLengthSpan F w hw f hf hx)

end Erdos3

end

section

namespace Erdos3

namespace FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (marked : X → Bool)

theorem markedLayer_eq_homogeneousSpan (d k l : ℕ) :
    markedLayer X s r w hw marked d k l =
      homogeneousLieSpan (of X s r w hw) (markedGeneratorGrade w marked) (markedGradeRegion d k l) := by
  unfold markedLayer markedLieSpan homogeneousLieSpan
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, markedGradeRegion, markedTreeGrade_weight,
    markedTreeGrade_count, markedTreeGrade_length, and_assoc]

theorem markedLayer_inf (hr : r ≤ s) (d k l e m n : ℕ) :
    markedLayer X s r w hw marked d k l ⊓ markedLayer X s r w hw marked e m n =
      markedLayer X s r w hw marked (max d e) (max k m) (max l n) := by
  rw [markedLayer_eq_homogeneousSpan, markedLayer_eq_homogeneousSpan,
    markedLayer_eq_homogeneousSpan, markedGradeRegion_inter,
    homogeneousSpan_inter X s r w hw hr]

theorem markedLayer_separate_inter (hr : r ≤ s) (d k l : ℕ) :
    markedLayer X s r w hw marked d 0 l ⊓ markedLayer X s r w hw marked 0 k 0 =
      markedLayer X s r w hw marked d k l := by
  rw [markedLayer_inf X s r w hw marked hr]
  simp only [Nat.max_zero, Nat.zero_max]

theorem topLayer_eq_markedLayer (hr : r ≤ s) :
    (filtration X s r w hw hr).layer s r = markedLayer X s r w hw marked s 0 r := by
  apply le_antisymm
  · intro x hx
    change x ∈ markedLieSpan (of X s r w hw) w marked s 0 r
    rw [markedLieSpan_zero_marked]
    let F := filtration X s r w hw hr
    have hf (i : X) : of X s r w hw i ∈ F.layer (w i) 0 := by
      rw [F.rank_zero_eq_one]
      exact of_mem_layer X s r w hw hr i
    have hid : lift F w hw (of X s r w hw) hf =
        (LieHom.id : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw) := by
      apply hom_ext w hw
      intro i
      rw [lift_of]
      rfl
    have h := lift_top_mem_degreeLengthSpan F w hw (of X s r w hw) hf hx
    simpa only [hid, LieHom.id_apply] using h
  · exact markedLayer_le_degreeRank X s r w hw marked hr s 0 r

theorem topLayer_inter_markedIdeal (hr : r ≤ s) (k : ℕ) :
    (filtration X s r w hw hr).layer s r ⊓ (markedLayerIdeal X s r w hw marked 0 k 0).toSubmodule =
      markedLayer X s r w hw marked s k r := by
  change (filtration X s r w hw hr).layer s r ⊓ markedLayer X s r w hw marked 0 k 0 = _
  rw [topLayer_eq_markedLayer X s r w hw marked hr,
    markedLayer_separate_inter X s r w hw marked hr]

end FreeDegreeRankLieAlgebra
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedRankIntegralModel
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (e : Basis (Fin d) ℚ L)
  (b : ∀ i : Fin (s + 1), Basis (Fin (finrank ℚ (F.associatedDegree.layer (i.val + 1))))
    ℚ (F.associatedDegree.layer (i.val + 1)))
  (c : ∀ i j : Fin (s + 1), Basis (Fin (finrank ℚ (F.layer i.val j.val)))
    ℚ (F.layer i.val j.val))
  (B : ℕ) (hB : 0 < B)
  (hstable : ∀ x ∈ coordinateGridModule e B, ∀ y ∈ coordinateGridModule e B,
    lieBCH s x y ∈ coordinateGridModule e B)

omit B hB hstable in
theorem exists_bounded_rank_integral_model {H : ℕ}
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (d ^ 3) * l ∧
      ∃ D : RationalFilteredNilmanifold L s d, ∃ T : D.DegreeRankStructure r,
        T.filtration = F ∧ D.basis = e ∧ D.grid = B ∧
        bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
        ∀ p : ℝ, (d : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p → (H : ℝ) ≤ Real.exp p → T.ComplexityLE p := by
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ :=
    exists_bch_stable_integral_grid e F.associatedDegree.lowerCentralSeries_eq_bot l hl hbracket
  exact ⟨B, hB, hdiv, by simpa only [Fintype.card_fin] using hbound,
    F.boundedRankIntegralModel e b B hB hstable,
    F.boundedRankIntegralStructure e b c B hB hstable, rfl, rfl, rfl,
    F.boundedRankIntegralModel_coordinates e b B hB hstable,
    fun _ hd hg hh => F.boundedRankIntegralStructure_complexity e b c B hB hstable
      hb hc hbracket hd hg hh⟩

omit B hB hstable in
theorem exists_bounded_rank_integral_model_with_frequency {H : ℕ}
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (ξ : L →ₗ[ℚ] ℚ) (hξ : ∀ i, RationalHeightLE (ξ (e i)) H)
    (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
      B ≤ bchIntegralDenominatorBound s * H ^ (d ^ 3) * (l * H ^ d) ∧
      ∃ D : RationalFilteredNilmanifold L s d, ∃ T : D.DegreeRankStructure r,
        T.filtration = F ∧ D.basis = e ∧ D.grid = B ∧
        bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
        (∀ z : D.filtration.Group, z ∈ D.lattice → ∃ n : ℤ, ξ z.coord = n) ∧
        ∀ p : ℝ, (d : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p → (H : ℝ) ≤ Real.exp p → T.ComplexityLE p := by
  classical
  let k := arrayDenominator (fun i => ξ (e i))
  have hk : 0 < k := arrayDenominator_pos _
  have hkH : k ≤ H ^ d := by
    simpa only [Fintype.card_fin] using arrayDenominator_le (fun i => ξ (e i)) (fun i => (hξ i).2)
  obtain ⟨B, hB, hdiv, hbound, D, T, hTF, hDe, hDB, hcoords, hcomplex⟩ :=
    F.exists_bounded_rank_integral_model e b c hb hc hbracket (l * k) (Nat.mul_pos hl hk)
  refine ⟨B, hB, (dvd_mul_right l k).trans hdiv,
    hbound.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left l hkH)),
    D, T, hTF, hDe, hDB, hcoords, ?_, hcomplex⟩
  intro z hz
  have hgrid : D.basis.equivFun z.coord ∈ scaledIntegerGrid B := by
    rw [← hcoords]
    change (⟨D.basis.equivFun.symm (D.basis.equivFun z.coord)⟩ : D.filtration.Group) ∈ D.lattice
    simpa only [LinearEquiv.symm_apply_apply] using hz
  rw [hDe] at hgrid
  exact coordinateGrid_functional_integral e ξ k B ((dvd_mul_left k l).trans hdiv)
    (fun i => ⟨clearedArray (fun j => ξ (e j)) i, (clearedArray_cast _ i).symm⟩) hgrid

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

structure NativeBoundedMultidegreeFamily {σ : Type*} [Fintype σ]
    (bound : σ → ℕ) (I : Type*) (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L (∑ i, bound i) dim
  multi : model.MultidegreeStructure bound
  complexity : multi.ComplexityLE p
  orbit : multi.filtration.realification.PolynomialOrbit
  test : I → model.Niltest (fun _ : σ => 1)
  test_orbit : ∀ i, (test i).orbit = multi.orbitToOrdinary orbit
  test_norm : ∀ i, (test i).normBound = 1
  test_complexity : ∀ i, (test i).ComplexityLE p

attribute [local instance] NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

namespace NativeBoundedMultidegreeFamily

variable {σ I : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (F : NativeBoundedMultidegreeFamily bound I p)

noncomputable def eval (i : I) (x : σ → ℤ) : ℂ := (F.test i).eval x

noncomputable def mono (hpq : p ≤ q) : NativeBoundedMultidegreeFamily bound I q :=
  { F with
    complexity := F.complexity.mono F.multi hpq
    test_complexity := fun i => (F.test_complexity i).mono hpq }

@[simp] theorem mono_eval (hpq : p ≤ q) (i : I) (x : σ → ℤ) :
    (F.mono hpq).eval i x = F.eval i x := rfl

end NativeBoundedMultidegreeFamily

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

def HasBoundedProductCorrelation {τ I : Type} [Fintype I]
    {s r degree N : ℕ} [NeZero N] (h : τ → ZMod N) (f : τ → ZMod N → ℂ)
    (mixedDim : ℕ) (B C Q : ℝ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp B ∧
    ∃ F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ ((I × I) × (I × Fin k)) C,
      ∃ M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) (Fin mixedDim × Fin k) Q,
        ∀ z, Nonempty (NativeVectorCorrelation degree N (B + 1)
          (fun ij : (Fin mixedDim × Fin k) × ((I × I) × (I × Fin k)) => fun a =>
            f z a * star (M.eval ij.1 (correlationInput ((h z).val : ℤ) (a.val : ℤ))) *
              star (F.eval z ij.2 (fun _ => (a.val : ℤ)))))

theorem HasBoundedProductCorrelation.mono {τ I : Type} [Fintype I]
    {s r degree N : ℕ} [NeZero N] {h : τ → ZMod N} {f : τ → ZMod N → ℂ}
    {mixedDim : ℕ} {B C Q B' C' Q' : ℝ}
    (hfamily : HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := degree)
      h f mixedDim B C Q) (hBB' : B ≤ B') (hCC' : C ≤ C') (hQQ' : Q ≤ Q') :
    HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := degree)
      h f mixedDim B' C' Q' := by
  obtain ⟨k, hk, hkB, F, M, hcorr⟩ := hfamily
  refine ⟨k, hk, hkB.trans (Real.exp_le_exp.mpr hBB'), F.mono hCC', M.mono hQQ', ?_⟩
  intro z
  obtain ⟨Cz⟩ := hcorr z
  exact ⟨Cz.mono (show B + 1 ≤ B' + 1 by linarith)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairCorrelator
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

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def pairComponent (out : Fin W.outputDim) (a b : Fin 2) :
    W.model.Niltest (fun _ : Fin 2 => 1) :=
  (W.component out).linearPullbackHom
    ![{ toFun := fun n => n a, map_zero' := rfl, map_add' := fun _ _ => rfl },
      { toFun := fun n => n b, map_zero' := rfl, map_add' := fun _ _ => rfl }]

end NativeMultidegreeNilcharacter

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

noncomputable def antisymmetricPairModels : ∀ k : Option (Fin 2),
    RationalFilteredNilmanifold (optionLieSpace V.L (fun _ : Fin 2 => W.L) k)
      (∑ l, mixedCorrelationDegree 1 l) (optionDimension V.dim (fun _ : Fin 2 => W.dim) k) :=
  optionFactors (V.model.raiseStep (by decide)) (fun _ : Fin 2 => W.model)

noncomputable def antisymmetricPairTests :
    ∀ k, (V.antisymmetricPairModels k).Niltest (fun _ : Fin 2 => 1)
  | none => (V.test.raiseStep (by decide)).conjugate
  | some k => ![(W.pairComponent i 0 1).conjugate, W.pairComponent j 1 0] k

noncomputable def antisymmetricPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![-W.vertical.frequency, W.vertical.frequency] k

end NativeSampleCorrelation

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

noncomputable def antisymmetricPairPolynomial :
    ((pi V.antisymmetricPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 2 => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun k => (V.antisymmetricPairModels k).filtration)
    (fun k => (V.antisymmetricPairTests k).orbit)
  ⟨⟨o.log, o.property⟩⟩

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
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

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

noncomputable def pairFrozenVector (k : Fin 2)
    (a b : (pi V.antisymmetricPairModels).RealGroup) (out : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.vertical.observable out (productProjection V.antisymmetricPairModels (some k)
    (QuotientGroup.mk (R.frozenMiddleValue a b x)))

end NativePolynomialOrbitFactors

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

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

noncomputable def pairAnchoredVector (y : Fin 2 → ℤ) (k : Fin 2) :
    Fin W.outputDim → (Fin 2 → ℤ) → ℂ :=
  R.pairFrozenVector k (R.slowValue y) (R.rationalValue y)

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop
namespace OAI

universe u

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}

def pairModels (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e) :
    ∀ i : Bool, RationalFilteredNilmanifold (BoolLieFamily L M i) s (Bool.rec e d i)
  | false => E
  | true => D

def pairFrequencies (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ) :
    ∀ i : Bool, BoolLieFamily L M i →ₗ[ℚ] ℚ
  | false => θ
  | true => η

noncomputable def pairFrequency (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ) :
    PairAlgebra L M →ₗ[ℚ] ℚ := piFrequency (pairFrequencies η θ)

@[simp] theorem pairFrequency_apply (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ)
    (x : PairAlgebra L M) : pairFrequency η θ x = η (x true) + θ (x false) := by
  rw [pairFrequency, piFrequency_apply, Fintype.sum_bool]
  rfl

variable (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    {σ ι : Type*} {w : σ → ℕ}

noncomputable def pairOrbit (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w) :
    (pi (pairModels D E)).filtration.realification.PolynomialOrbit w :=
  NilpotentLieFiltration.piRealOrbit (fun i => (pairModels D E i).filtration)
    (fun i => by cases i; exact q; exact p)

noncomputable def pairOrbitSymbol (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    (pi (pairModels D E)).filtration.RealPolynomialSymbolGroup w :=
  (pi (pairModels D E)).filtration.realPolynomialSymbolHom b ω hF w
    ⟨⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩⟩

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

noncomputable def pairTests (V : D.Niltest w) (W : E.Niltest w) :
    ∀ i : Bool, (pairModels D E i).Niltest w
  | false => W
  | true => V

theorem pairTests_complexity (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    ∀ i, (pairTests D E V W i).ComplexityLE p := by
  intro i
  cases i
  · exact hW
  · exact hV

section ProductTopology

variable [TopologicalSpace (ℝ ⊗[ℚ] PairAlgebra L M)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra L M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PairAlgebra L M)]
    [T2Space (ℝ ⊗[ℚ] PairAlgebra L M)]

noncomputable def pairNiltest (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    (pi (pairModels D E)).Niltest w :=
  piNiltest (pairModels D E) (pairTests D E V W) (by linarith)
    (by simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp)
    (pairTests_complexity D E V W hV hW)

@[simp] theorem pairNiltest_orbit (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p) :
    (pairNiltest D E V W hp hV hW).orbit = pairOrbit D E V.orbit W.orbit := rfl

@[simp] theorem pairNiltest_symbol (V : D.Niltest w) (W : E.Niltest w) {p : ℝ}
    (hp : 2 ≤ p) (hV : V.ComplexityLE p) (hW : W.ComplexityLE p)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i})) :
    (pairNiltest D E V W hp hV hW).symbol b ω hF =
      pairOrbitSymbol D E V.orbit W.orbit b ω hF := rfl

end ProductTopology
end RationalFilteredNilmanifold

open RationalFilteredNilmanifold

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
variable {L M : Type sourceLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}

 theorem pairFirstProjection_filtered (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e) (j : ℕ)
    (x : PairAlgebra L M) (hx : x ∈ (pi (pairModels D E)).filtration.layer j) :
    liePiEval (R := ℚ) true x ∈ D.filtration.layer j :=
  (NilpotentLieFiltration.mem_pi_layer (fun i => (pairModels D E i).filtration) j x).mp hx true

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

theorem realSymbolRepresentative_eq_homogeneous_map (x : F.RealPolynomialSymbol w) :
    F.realSymbolRepresentative b ω hF w x =
      VectorPolynomial.map
        ((realificationLieHom (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom).toLinearMap.restrictScalars ℚ)
        (F.realGradedSymbolPolynomial b ω hF w x) :=
  F.realSymbolRepresentative_eq_map b ω hF w x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold

variable {B L : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationBaseMap :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded →ₗ[ℚ]
      (B → ℚ) :=
  (baseLinear.comp (weightedSubalgebra w d).subtype).comp
    (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
      w d hw hwd (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).toLinearMap

noncomputable def detectedTranslationBaseFunctional (i : B) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded →ₗ[ℚ] ℚ :=
  (LinearMap.proj i).comp (detectedTranslationBaseMap w d hw hwd M hM D)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelatingVerticalPair
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

section Data

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}

structure NativePairPartition
    (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
      V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
      (fun _ : Fin 2 => (N : ℝ)) r) (b ε : ℝ) where
  I : Type
  [finite : Fintype I]
  card_bound : (Fintype.card (Fin 2 → I) : ℝ) ≤ Real.exp b
  weight : I → ZMod N → ℝ
  positive : ∀ j, PositiveCyclicNiltest.{0} 1 N b (weight j)
  total : ∀ x, ∑ j, weight j x = 1
  anchor : (Fin 2 → I) → (Fin 2 → ZMod N)
  equivalence : ∀ j, NativeIntegerVectorEquivalence 1 b
    (R.pairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 0)
    (R.pairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 1)
  approximation : ∀ (k : Fin 2) (out : Fin W.outputDim),
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
        ∑ j, ((∏ l, weight (j l) (x l) : ℝ) : ℂ) * R.pairAnchoredVector
          (fun l => ((anchor j l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖) ≤ ε

attribute [local instance] NativePairPartition.finite

end Data

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def mixedAntisymmetric {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (a b : Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ℂ :=
  W.eval a (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ)) *
    star (W.eval b (mixedSlotInput (x 1) (x 0) (fun j => x j.succ.succ)))

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {n : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)

noncomputable def mixedPairComponent (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2)) :
    W.model.Niltest (fun _ : Fin (n + 2) => 1) :=
  (W.component out).linearPullbackHom (fun j =>
    { toFun := fun x => x (v (mixedInputCoordinate n j))
      map_zero' := rfl
      map_add' := fun _ _ => rfl })

end NativeMultidegreeNilcharacter

end Erdos3

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

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

abbrev MixedPairAlgebra := ∀ k : Option (Fin 2), optionLieSpace V.L (fun _ : Fin 2 => W.L) k

noncomputable def mixedPairModels : ∀ k : Option (Fin 2),
    RationalFilteredNilmanifold (optionLieSpace V.L (fun _ : Fin 2 => W.L) k)
      (∑ _ : MixedReplicatedIndex (n + 1), 1) (optionDimension V.dim (fun _ : Fin 2 => W.dim) k) :=
  optionFactors (V.model.raiseStep (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)) (fun _ : Fin 2 => W.model)

noncomputable def mixedPairTests :
    ∀ k, (V.mixedPairModels k).Niltest (fun _ : Fin (n + 2) => 1)
  | none => (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).conjugate
  | some k => ![W.mixedPairComponent i id,
      (W.mixedPairComponent j (mixedExchangeCoordinate n)).conjugate] k

noncomputable def mixedPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![W.vertical.frequency, -W.vertical.frequency] k

end NativeSampleCorrelation
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedPairPolynomial
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

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

noncomputable def mixedPairPolynomial :
    ((pi V.mixedPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin (n + 2) => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun k => (V.mixedPairModels k).filtration)
    (fun k => (V.mixedPairTests k).orbit)
  ⟨⟨o.log, o.property⟩⟩

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairFrozenEquivalence
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

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

noncomputable def mixedPairFrozenVector (k : Fin 2)
    (a b : (pi V.mixedPairModels).RealGroup) (out : Fin W.outputDim)
    (x : Fin (n + 2) → ℤ) : ℂ :=
  W.vertical.observable out (productProjection V.mixedPairModels (some k)
    (QuotientGroup.mk (R.frozenMiddleValue a b x)))

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRetainedTargetCubeIntervals
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def HasFixedTargetCubeIntervals {J : Type*} [Fintype J] {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin 2 → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ r u : ℝ, 0 ≤ r ∧ r ≤ q ∧ 0 ≤ u ∧ u ≤ q ∧
    ∃ E : ∀ b : (Fin (d + 1) → Bool) → Fin (d + 2),
      NativeIntegerVectorEquivalence (d + 2) r
        (M.mixed.mixedCubeWithShift (cubeCarryShift (d + 1) N b)) (M.mixed.mixedCubeWithShift 0),
    ∃ F : NativeIntegerVectorEquivalence (d + 2) u (M.mixed.mixedCubeWithShift 0)
      (mixedCubeObservable (d := d + 1) η),
    ∃ (i : Fin M.mixed.outputDim) (b : (Fin (d + 1) → Bool) → Fin (d + 2))
      (v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim)
      (l : Fin ((E b).selectedExpansion (fun _ => i) v).count),
    ∃ (w : (Fin (d + 1) → Bool) → J) (z : Fin (F.selectedExpansion v w).count),
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
              star (mixedCubeObservable η w (mixedDifferencePoint t n)) *
              star ((((E b).selectedExpansion (fun _ => i) v).test l).eval (mixedDifferencePoint t n)) *
              star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n))‖

theorem HasFixedTargetCubeIntervals.mono {J : Type*} [Fintype J] {d N : ℕ} [NeZero N]
    {p q q' : ℝ} {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin 2 → ℤ) → ℂ} (H : HasFixedTargetCubeIntervals f M η q) (hqq' : q ≤ q') :
    HasFixedTargetCubeIntervals f M η q' := by
  obtain ⟨r, u, hr, hrq, hu, huq, E, F, i, b, v, l, w, z, Q, hQ, hdense, hcorr⟩ := H
  refine ⟨r, u, hr, hrq.trans hqq', hu, huq.trans hqq', E, F, i, b, v, l, w, z, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqq'))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hcorr t ht
    exact ⟨hs, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hc⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CubeSignalCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedCubeInput_independent {d : ℕ} (ω : Fin d → Bool) (j : Fin d) (hj : ω j = false)
    (x y : Fin (d + 2) → ℤ) (hxy : ∀ k, k ≠ j.succ.succ → x k = y k) :
    mixedCubeInput ω x = mixedCubeInput ω y := by
  have hzero : (0 : Fin (d + 2)) ≠ j.succ.succ := (Fin.succ_ne_zero j.succ).symm
  have hone : (1 : Fin (d + 2)) ≠ j.succ.succ := by
    intro heq
    have h : (0 : Fin (d + 1)) = j.succ := Fin.succ_inj.mp heq
    exact (Fin.succ_ne_zero j).symm h
  unfold mixedCubeInput
  rw [hxy 0 hzero, hxy 1 hone]
  congr 2
  apply cubeShift_congr_selected
  intro k hk
  apply hxy
  intro heq
  have hkj : k = j := Fin.succ_inj.mp (Fin.succ_inj.mp heq)
  subst k
  simp only [hj, Bool.false_eq_true] at hk

theorem mixedCubeInput_true {d : ℕ} (x : Fin (d + 2) → ℤ) :
    mixedCubeInput (fun _ => true) x = correlationInput (x 0) (∑ j : Fin (d + 1), x j.succ) := by
  unfold mixedCubeInput
  rw [cubeShift_true]
  exact congrArg (correlationInput (x 0)) (Fin.sum_univ_succ (fun j : Fin (d + 1) => x j.succ)).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSeparatedSumIntervals
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_mixedCube_proper_factors {J : Type*} {d : ℕ}
    (η : J → (Fin 2 → ℤ) → ℂ) (hη : ∀ j x, ‖η j x‖ ≤ 1) (w : (Fin d → Bool) → J) :
    ∃ A : Fin (d + 2) → (Fin (d + 2) → ℤ) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, mixedCubeObservable η w x =
        conjugationPower d (η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 1), x j.succ))) *
          ∏ i, A i x := by
  classical
  let S : Finset (Fin d → Bool) := Finset.univ.erase (fun _ => true)
  let F (ω : S) (x : Fin (d + 2) → ℤ) :=
    conjugationPower (booleanWeight ω.val) (η (w ω.val) (mixedCubeInput ω.val x))
  have hF : ∀ ω x, ‖F ω x‖ ≤ 1 := by
    intro ω x
    exact (conjugationPower_norm _ _).trans_le (hη _ _)
  have hFi : ∀ ω, ∃ i, ∀ x y, (∀ k, k ≠ i → x k = y k) → F ω x = F ω y := by
    intro ω
    obtain ⟨j, hj⟩ := exists_false_of_ne_true (Finset.mem_erase.mp ω.property).1
    refine ⟨j.succ.succ, ?_⟩
    intro x y hxy
    exact congrArg (fun z => conjugationPower (booleanWeight ω.val) (η (w ω.val) z))
      (mixedCubeInput_independent ω.val j hj x y hxy)
  obtain ⟨A, hA, hAi, hprod⟩ := exists_missing_coordinate_product_factors F hF hFi
  refine ⟨A, hA, hAi, ?_⟩
  intro x
  calc
    mixedCubeObservable η w x =
        conjugationPower d (η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 1), x j.succ))) *
          ∏ ω ∈ S, conjugationPower (booleanWeight ω) (η (w ω) (mixedCubeInput ω x)) := by
      unfold mixedCubeObservable
      rw [← Finset.mul_prod_erase Finset.univ
        (fun ω => conjugationPower (booleanWeight ω) (η (w ω) (mixedCubeInput ω x)))
        (Finset.mem_univ (fun _ : Fin d => true))]
      rw [booleanWeight_true, mixedCubeInput_true]
    _ = _ := by
      rw [hprod]
      congr 1
      exact (Finset.prod_coe_sort S (fun ω => conjugationPower (booleanWeight ω)
        (η (w ω) (mixedCubeInput ω x)))).symm

theorem exists_full_mixed_cube_proper_factors {J : Type*} {d : ℕ}
    (f : ℤ → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1)
    (η : J → (Fin 2 → ℤ) → ℂ) (hη : ∀ j x, ‖η j x‖ ≤ 1) (w : (Fin (d + 1) → Bool) → J) :
    ∃ A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, fullCubeSignal f x * star (mixedCubeObservable η w x) =
        conjugationPower (d + 2) (f (∑ i, x i) *
          η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) *
            ∏ i, A i x := by
  obtain ⟨A, hA, hAi, hAfactor⟩ := exists_fullCube_proper_factors (d := d) f hf
  obtain ⟨B, hB, hBi, hBfactor⟩ := exists_mixedCube_proper_factors η hη w
  refine ⟨(fun i x => A i x * star (B i x)), ?_, ?_, ?_⟩
  · intro i x
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i x)).trans (hB i x)
  · intro i x y hxy
    change A i x * star (B i x) = A i y * star (B i y)
    rw [hAi i x y hxy, hBi i x y hxy]
  · intro x
    have hstep (z : ℂ) : conjugationPower (d + 2) z = star (conjugationPower (d + 1) z) := rfl
    rw [hAfactor, hBfactor]
    simp only [Finset.prod_mul_distrib, star_prod, map_mul, hstep, star_mul]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_normalized_cube_weights {J : Type*} {d : ℕ}
    (f : ℤ → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1)
    (η : J → (Fin 2 → ℤ) → ℂ) (hη : ∀ j x, ‖η j x‖ ≤ 1) (w : (Fin (d + 1) → Bool) → J)
    (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ) (hA : ∀ i x, ‖A i x‖ ≤ 1)
    (hAi : ∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) :
    ∃ B : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ,
      (∀ i x, ‖B i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y) ∧
      ∀ x, conjugationPower (d + 3)
          ((fullCubeSignal f x * star (mixedCubeObservable η w x)) * ∏ i, A i x) =
        star (f (∑ i, x i)) *
          star (η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) *
            ∏ i, B i x := by
  obtain ⟨P, hP, hPi, hfactor⟩ := exists_full_mixed_cube_proper_factors f hf η hη w
  refine ⟨(fun i x => conjugationPower (d + 3) (P i x * A i x)), ?_, ?_, ?_⟩
  · intro i x
    change ‖conjugationPower (d + 3) (P i x * A i x)‖ ≤ 1
    rw [conjugationPower_norm, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hP i x)).trans (hA i x)
  · intro i x y hxy
    change conjugationPower (d + 3) (P i x * A i x) = conjugationPower (d + 3) (P i y * A i y)
    rw [hPi i x y hxy, hAi i x y hxy]
  · intro x
    rw [hfactor]
    have hprod : (conjugationPower (d + 2) (f (∑ i, x i) *
        η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) * ∏ i, P i x) *
          (∏ i, A i x) =
        conjugationPower (d + 2) (f (∑ i, x i) *
          η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) *
            ∏ i, P i x * A i x := by
      rw [Finset.prod_mul_distrib]
      ring
    rw [hprod, map_mul, conjugationPower_next_self, map_prod, star_mul]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def HasSumTargetIntervals {J : Type*} [Fintype J] {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin 2 → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (correlationInput (mixedDifferencePoint t n 0)
                (∑ k : Fin (d + 2), mixedDifferencePoint t n k.succ))) *
              ∏ i, A i (mixedDifferencePoint t n)‖

theorem HasSumTargetIntervals.mono {J : Type*} [Fintype J] {d N : ℕ} [NeZero N]
    {p q q' : ℝ} {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin 2 → ℤ) → ℂ} (H : HasSumTargetIntervals f M η q) (hqq' : q ≤ q') :
    HasSumTargetIntervals f M η q' := by
  obtain ⟨j, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  refine ⟨j, A, hA, hAi, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqq'))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hcorr t ht
    exact ⟨hs, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hc⟩

theorem HasWeightedTargetCubeIntervals.to_sum {J : Type*} [Fintype J] {d N : ℕ} [NeZero N]
    {p q : ℝ} {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin 2 → ℤ) → ℂ} (H : HasWeightedTargetCubeIntervals f M η q)
    (hf : ∀ z, ‖f z‖ ≤ 1) (hη : ∀ j x, ‖η j x‖ ≤ 1) : HasSumTargetIntervals f M η q := by
  obtain ⟨w, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  obtain ⟨B, hB, hBi, hnorm⟩ := exists_normalized_cube_weights
    (fun z : ℤ => f (z : ZMod N)) (fun z => hf _) η hη w A hA hAi
  refine ⟨w (fun _ => true), B, hB, hBi, Q, hQ, hdense, ?_⟩
  intro t ht
  obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hcorr t ht
  refine ⟨hs, a, len, hlen, hend, hshort, hvol, ?_⟩
  have hpoint (n : ℤ) :
      conjugationPower (d + 3)
        ((cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
          star (mixedCubeObservable η w (mixedDifferencePoint t n))) * ∏ i, A i (mixedDifferencePoint t n)) =
      star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
        star (η (w (fun _ => true)) (correlationInput (mixedDifferencePoint t n 0)
          (∑ k : Fin (d + 2), mixedDifferencePoint t n k.succ))) *
        ∏ i, B i (mixedDifferencePoint t n) := by
    simpa only [fullCubeSignal_profile] using hnorm (mixedDifferencePoint t n)
  have hc' := hc.trans_eq (norm_expect_conjugationPower (Finset.Ico (a : ℤ) (a + len)) (d + 3)
    (fun n => (cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
      star (mixedCubeObservable η w (mixedDifferencePoint t n))) * ∏ i, A i (mixedDifferencePoint t n))).symm
  simpa only [hpoint] using hc'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem prod_reweightPositive_mean_le_of_conditional
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (D : X × Y → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hglobal : 0 < (p.prod q).mean D)
    (hlocal : ∀ x, 0 < q.mean (fun y => D (x, y)))
    (f : X × Y → ℝ) {ε : ℝ}
    (hbound : ∀ x,
      (q.reweightPositive (fun y => D (x, y)) (fun y => hD0 (x, y)) (hlocal x)).mean
        (fun y => f (x, y)) ≤ ε) :
    ((p.prod q).reweightPositive D hD0 hglobal).mean f ≤ ε := by
  have hraw (x) : q.mean (fun y => D (x, y) * f (x, y)) ≤
      ε * q.mean (fun y => D (x, y)) := by
    exact (div_le_iff₀ (hlocal x)).mp (by simpa only [reweightPositive_mean] using hbound x)
  rw [reweightPositive_mean]
  apply (div_le_iff₀ hglobal).mpr
  rw [mean_prod, mean_prod]
  calc
    _ ≤ p.mean (fun x => ε * q.mean (fun y => D (x, y))) := p.mean_mono hraw
    _ = _ := by
      change (∑ x, p.weight x * (ε * q.mean (fun y => D (x, y)))) =
        ε * ∑ x, p.weight x * q.mean (fun y => D (x, y))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueCutoffDomination
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem mean_mono_positive_support {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) {f g : X → ℝ}
    (h : ∀ x, 0 < p.weight x → f x ≤ g x) : p.mean f ≤ p.mean g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : 0 < p.weight x
  · exact mul_le_mul_of_nonneg_left (h x hx) (p.nonneg x)
  · have hz : p.weight x = 0 := le_antisymm (le_of_not_gt hx) (p.nonneg x)
    simp only [hz, zero_mul, le_refl]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.UnconditionedJointFrameDomination
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]

def selectedJointFrameBoxMap
    (bases : Finset (I → ℤ)) (width : Option K × I → ℝ)
    (sourceLo sourceHi : Option K × I → ℤ)
    (hframe : ∀ z : bases × rectangularWeightIndices 0 width 1, ∀ t,
      jointIntegerFrame (z.1.val,z.2.val) t.1 t.2 ∈ Finset.Ico (sourceLo t) (sourceHi t))
    (z : bases × rectangularWeightIndices 0 width 1) :
    ∀ t, Finset.Ico (sourceLo t) (sourceHi t) :=
  fun t => ⟨jointIntegerFrame (z.1.val,z.2.val) t.1 t.2, hframe z t⟩

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPolynomialSymbolLiftHom
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (w : σ → ℕ)

noncomputable def realHomogeneousAssociatedGradedMapQ :
    (ℝ ⊗[ℚ] F.AssociatedGraded) →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] L) where
  toLinearMap :=
    (realificationLieHom (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom).toLinearMap.restrictScalars ℚ
  map_lie' {x y} := (realificationLieHom
    (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom).map_lie x y

noncomputable def realHomogeneousSymbolRepresentativeLie :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ (MvPolynomial σ ℚ))
    (F.realHomogeneousAssociatedGradedMapQ b ω hF hb)).comp
      (F.realGradedSymbolPolynomial b ω hF w)

@[simp] theorem realHomogeneousSymbolRepresentativeLie_apply (x : F.RealPolynomialSymbol w) :
    F.realHomogeneousSymbolRepresentativeLie b ω hF hb w x =
      F.realSymbolRepresentative b ω hF w x := by
  exact (F.realSymbolRepresentative_eq_homogeneous_map b ω hF hb w x).symm

noncomputable def realHomogeneousAdaptedSymbolRepresentativeLie :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra w :=
  lieHomSubalgebra (F.realHomogeneousSymbolRepresentativeLie b ω hF hb w)
    (F.realification.adaptedLieSubalgebra w) (fun x => by
      rw [F.realHomogeneousSymbolRepresentativeLie_apply]
      exact (F.realification.mem_adaptedSubmodule w _).mpr
        (F.realSymbolRepresentative_adapted b ω hF w x))

noncomputable def realHomogeneousPolynomialSymbolLiftHom :
    F.RealPolynomialSymbolGroup w →* (F.realification.adaptedPolynomialFiltration w).Group :=
  NilpotentLieBCHGroup.map (F.realHomogeneousAdaptedSymbolRepresentativeLie b ω hF hb w)

@[simp] theorem realHomogeneousPolynomialSymbolLiftHom_apply (g : F.RealPolynomialSymbolGroup w) :
    F.realHomogeneousPolynomialSymbolLiftHom b ω hF hb w g =
      F.realPolynomialSymbolLift b ω hF w g := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact F.realHomogeneousSymbolRepresentativeLie_apply b ω hF hb w g.coord

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

theorem forecastAugmented_envelope_tail_le
    (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    {K F C ε : ℝ} (hK : 0 ≤ K) (hF : 0 ≤ F) (hC : 1 ≤ C)
    (hexcess : p.excessMass q C ≤ ε) :
    p.mean (fun x => if x ∈ Finset.univ.filter
      (fun y => p.relativeDensity q y ≤ 2 * C)
      then 0 else K * p.relativeDensity q x + F) ≤ 2 * (K + F) * ε := by
  let G := Finset.univ.filter (fun x => p.relativeDensity q x ≤ 2 * C)
  have htail : p.mean (fun x => if x ∈ G then 0 else p.relativeDensity q x) ≤ 2 * ε := by
    rw [p.relativeDensity_tail_mass q hp]
    exact mass_above_double_cap_le_of_excess p q hexcess
  have hpoint (x : Ω) :
      (if x ∈ G then 0 else K * p.relativeDensity q x + F) ≤
        (K + F) * (if x ∈ G then 0 else p.relativeDensity q x) := by
    by_cases hx : x ∈ G
    · simp only [hx, ↓reduceIte, mul_zero, le_refl]
    · have hbad : 2 * C < p.relativeDensity q x := by
        simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hx
      simp only [hx, ↓reduceIte]
      have hFscale := mul_le_mul_of_nonneg_left (show 1 ≤ p.relativeDensity q x by linarith) hF
      nlinarith
  calc
    _ ≤ p.mean (fun x => (K + F) * (if x ∈ G then 0 else p.relativeDensity q x)) :=
      p.mean_mono hpoint
    _ = (K + F) * p.mean (fun x => if x ∈ G then 0 else p.relativeDensity q x) := by
      unfold mean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ (K + F) * (2 * ε) := mul_le_mul_of_nonneg_left htail (add_nonneg hK hF)
    _ = 2 * (K + F) * ε := by ring

theorem forecastAugmented_envelope_le_on_good
    (p q : FiniteProbabilityWeights Ω) {K F C : ℝ} (hK : 0 ≤ K)
    (x : Ω) (hx : x ∈ Finset.univ.filter (fun y => p.relativeDensity q y ≤ 2 * C)) :
    K * p.relativeDensity q x + F ≤ 2 * K * C + F := by
  have h := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 hK
  nlinarith

end Erdos3.FiniteProbabilityWeights

end

end OAI
end


