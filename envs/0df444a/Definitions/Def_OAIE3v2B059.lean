-- Prove2me | Definitions.Def_OAIE3v2B059
-- name    : OAIE3v2B059
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:14:06.984253+00:00
-- url     : https://prove2.me/theorems/35a58000-6271-47f9-9067-feb82b257365
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 60 of 311
-- statement:
--   Definitions bundle 60 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B014`, `OAIE3v2B015`, `OAIE3v2B016`, `OAIE3v2B017`, `OAIE3v2B022`, `OAIE3v2B023`, `OAIE3v2B027`, `OAIE3v2B028` of this split.
--
--   Modules: `Dynamics/CandidateFrontSourceLossBudget.lean`, `Dynamics/FastSymbolCorrectionBudget.lean`, `Estimates/AllocatedCandidateCommonFastGeometry.lean`, `Estimates/ControlledLinearSubspaceLift.lean`, `Estimates/DependentPatchValue.lean`, `Estimates/PeelingCost.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/RationalTagConstraintSpaces.lean`, `Estimates/RealifiedMultidegree.lean`, `Estimates/RelativeFiberSlicePatch.lean`, `Estimates/RepresentativeWindowPatch.lean`, `Estimates/ScalarCubeDomain.lean`, `Estimates/WeightedLoweringTriangular.lean`, `Fourier/PivotAnnihilatorFrequencyCode.lean`, `Fourier/RationalLiftCharacterTwist.lean`, `Geometry/CertifiedFullChartRecoveredTerminal.lean`, `Geometry/CommonRefilteredFactorsSymbolTransport.lean`, `Geometry/CoordinateFiberPatch.lean`, `Geometry/LowTaggedCoordinateRestriction.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Geometry/SymbolCoordinateFreezeBounds.lean`, `Lattices/IntegerFrozenChart.lean`, `Lattices/TriangularAffineReset.lean`, `Linear/ActualOrdinaryPointwiseSpanning.lean`, `Linear/ControlledMarkedKernelNormalization.lean`, `Linear/ControlledProjectionUniformBudget.lean`, `Linear/KernelProjectionPresentPivotIdeal.lean`, `Linear/KernelScaleIndependence.lean`, `Polynomial/FrozenPolynomialAffineRange.lean`, `Polynomial/JointPolynomialDilationGrid.lean`, `Polynomial/LowestPolynomialLayer.lean`, `Polynomial/PolynomialCoefficientNormalization.lean`, `Polynomial/PolynomialDensityBudget.lean`, `Polynomial/PolynomialPatchProductBudget.lean`, `Polynomial/PolynomialPatchShearOrbit.lean`, `Polynomial/PolynomialShearObservableNet.lean`, `Polynomial/PolynomialSymbolicShearWeightedDegree.lean`, `Polynomial/SlowPolynomialSliceLogCost.lean`, `Probability/ScalarCubeDomainDensity.lean`, `Sampling/PrecenterForecastNativeAtomDictionary.lean`, `Sampling/RationalPowerGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B014
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B016
import Definitions.Def_OAIE3v2B017
import Definitions.Def_OAIE3v2B022
import Definitions.Def_OAIE3v2B023
import Definitions.Def_OAIE3v2B027
import Definitions.Def_OAIE3v2B028

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget
namespace OAI

section

namespace Erdos3

theorem iteratedPowerBudget_monotone {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 0 ≤ p) :
    Monotone (iteratedPowerBudget a p) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_power_budget (iteratedPowerBudget_nonneg a hp n) ha

theorem iteratedPowerBudget_ge {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    p ≤ iteratedPowerBudget a p n :=
  iteratedPowerBudget_monotone ha hp (Nat.zero_le n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget
namespace OAI

section

namespace Erdos3

theorem exists_majorPhaseDetectedDecomposition_budget (a b c m d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let E := (p + a) ^ a
      let Q := E + p + 1
      let P := (Q + b) ^ b + Q
      let D := (P + c) ^ c
      let B := (p + C) ^ C
      E ≤ B ∧ E + D ≤ B ∧ (m : ℝ) * p + D ≤ B ∧
        (m : ℝ) * E + D ≤ B ∧ (d : ℝ) * E + D ≤ B ∧
        (d : ℝ) * p + D ≤ B ∧ D ≤ B := by
  let E : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q : Polynomial ℕ := E + Polynomial.X + 1
  let P : Polynomial ℕ := (Q + Polynomial.C b) ^ b + Q
  let D : Polynomial ℕ := (P + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (E + D + Polynomial.C (m + d + 1) * (Polynomial.X + E) + 1)
  refine ⟨C, hC, ?_⟩
  intro p hp
  dsimp only
  let e : ℝ := (p + a) ^ a
  let q : ℝ := e + p + 1
  let r : ℝ := (q + b) ^ b + q
  let δ : ℝ := (r + c) ^ c
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have htotal : e + δ + ((m : ℝ) + d + 1) * (p + e) + 1 ≤ (p + C) ^ C := by
    simpa [E, Q, P, D, e, q, r, δ, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  change e ≤ _ ∧ e + δ ≤ _ ∧ (m : ℝ) * p + δ ≤ _ ∧
    (m : ℝ) * e + δ ≤ _ ∧ (d : ℝ) * e + δ ≤ _ ∧
    (d : ℝ) * p + δ ≤ _ ∧ δ ≤ _
  have hmp : 0 ≤ (m : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hme : 0 ≤ (m : ℝ) * e := mul_nonneg (Nat.cast_nonneg _) he
  have hdp : 0 ≤ (d : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hde : 0 ≤ (d : ℝ) * e := mul_nonneg (Nat.cast_nonneg _) he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastSymbolCorrectionBudget
namespace OAI

section

namespace Erdos3

theorem exists_fastSymbolCorrectionBudget (a ce cr : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (p : ℝ), 0 ≤ p →
      let p₀ : ℝ := p + (p + 2) ^ a + (p + 2) ^ 4 + 2
      let p₁ : ℝ := p₀ + (p₀ + ce) ^ ce + (p₀ + cr) ^ cr
      let p₂ : ℝ := p₁ + ((p₁ + 2) ^ 10 + 2) ^ 36 + ((p₁ + 2) ^ 10 + 2) ^ 18 + 2
      (p₂ + ce) ^ ce + (p₂ + cr) ^ cr ≤ (p + C) ^ C := by
  let B₀ : Polynomial ℕ := Polynomial.X + (Polynomial.X + 2) ^ a + (Polynomial.X + 2) ^ 4 + 2
  let B₁ : Polynomial ℕ := B₀ + (B₀ + Polynomial.C ce) ^ ce + (B₀ + Polynomial.C cr) ^ cr
  let B₂ : Polynomial ℕ := B₁ + ((B₁ + 2) ^ 10 + 2) ^ 36 + ((B₁ + 2) ^ 10 + 2) ^ 18 + 2
  let B : Polynomial ℕ := (B₂ + Polynomial.C ce) ^ ce + (B₂ + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, B₂, B₁, B₀, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RationalLiftCharacterTwist
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {m : ℕ}

theorem rationalLiftCharacterTwist_lipschitz (M : ℕ) (a : Fin m → ℤ) (c : Fin m → ℝ)
    (r : Fin m → ZMod M) :
    LipschitzWith (rationalLiftCharacterTwistLip M a) (fun y => rationalLiftCharacterTwist M a c y r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have hdiff : |(∑ i, (a i : ℝ) * (x i + (r i).val + c i)) / (M : ℝ) -
      (∑ i, (a i : ℝ) * (y i + (r i).val + c i)) / (M : ℝ)| ≤
      (∑ i, |(a i : ℝ)|) / (M : ℝ) * dist x y := by
    rw [← sub_div, ← Finset.sum_sub_distrib]
    have heq : (∑ i, ((a i : ℝ) * (x i + (r i).val + c i) -
        (a i : ℝ) * (y i + (r i).val + c i))) =
        ∑ i, (a i : ℝ) * (x i - y i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq, abs_div, abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    calc
      _ ≤ (∑ i, |(a i : ℝ) * (x i - y i)|) / (M : ℝ) :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg M)
      _ ≤ (∑ i, |(a i : ℝ)| * dist x y) / (M : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  change ‖(Real.fourierChar _ : ℂ) - (Real.fourierChar _ : ℂ)‖ ≤ _
  apply (real_fourierChar_norm_sub_le _ _).trans
  apply (mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ 2 * Real.pi)).trans_eq
  change 2 * Real.pi * ((∑ i, |(a i : ℝ)|) / (M : ℝ) * dist x y) =
    (2 * Real.pi * (∑ i, |(a i : ℝ)|) / (M : ℝ)) * dist x y
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace TriangularSlots

variable {d : ℕ} (A : TriangularSlots d) (Φ : PatchKernel d)

theorem patchValue_eq_zero (h : ∀ b : Fin d → ℤ, Φ.value (A.residual b) = 0) :
    A.patchValue Φ = 0 := by
  simp only [patchValue, h, tsum_zero]

end TriangularSlots

end Erdos3

end

section

namespace Erdos3

variable {D E : ℕ}

theorem dist_append_same_left_le (z : Fin D → ℝ) (x y : Fin E → ℝ) :
    dist (Fin.append z x) (Fin.append z y) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp
  · simpa only [Fin.append_right] using dist_le_pi_dist x y j

namespace PatchKernel

def freeze (Φ : PatchKernel (D + E)) (z : Fin D → ℝ) : PatchKernel E where
  value y := Φ.value (Fin.append z y)
  nonneg y := Φ.nonneg _
  le_one y := Φ.le_one _
  support y hy i := by simpa using Φ.support _ hy (i.natAdd D)
  lip := Φ.lip
  lipschitz := LipschitzWith.of_dist_le_mul (fun x y =>
    (Φ.lipschitz.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (dist_append_same_left_le z x y) Φ.lip.coe_nonneg))

end PatchKernel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d D E : ℕ} {w : Fin d → ℕ}

theorem prefixSubstitution_degree {w : Fin (D + E) → ℕ}
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E)))
    (i : Fin E) (v : σ ⊕ Fin (D + i.val)) :
    prefixSubstitution I i v ∈
      weightedSupportLE (patchVariableWeight (fun j => w (j.natAdd D)) i)
        (patchVariableWeight w (i.natAdd D) v) := by
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_left]
      apply weightedSupportLE_aeval (fun _ : σ => 1)
        (patchVariableWeight (fun j => w (j.natAdd D)) i)
        (fun a => (X (Sum.inl a) : MvPolynomial (σ ⊕ Fin i.val) ℝ))
      · intro a
        exact weightedSupportLE_X _ (Sum.inl a)
      · exact hI k
    · simp only [prefixSubstitution, Sum.elim_inr, Fin.addCases_right]
      exact weightedSupportLE_X (R := ℝ)
        (patchVariableWeight (fun j => w (j.natAdd D)) i) (Sum.inr k)

noncomputable def freezePrefix {w : Fin (D + E) → ℕ}
    (A : PolynomialSlots σ (D + E) w) (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (w (j.castAdd E))) :
    PolynomialSlots σ E (fun j => w (j.natAdd D)) where
  center i := aeval (prefixSubstitution I i) (A.center (i.natAdd D))
  degree i := weightedSupportLE_aeval _ _ _ (prefixSubstitution_degree I hI i)
    (A.degree (i.natAdd D))

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

noncomputable def freezePrefix (A : PolynomialPatch σ s (D + E))
    (I : Fin D → MvPolynomial σ ℝ)
    (hI : ∀ j, I j ∈ weightedSupportLE (fun _ : σ => 1) (A.weight (j.castAdd E)))
    (z : Fin D → ℝ) : PolynomialPatch σ s E where
  weight i := A.weight (i.natAdd D)
  weight_pos i := A.weight_pos _
  weight_le i := A.weight_le _
  weight_mono i j hij := A.weight_mono (by simpa only [Fin.le_def, Fin.val_natAdd,
    Nat.add_le_add_iff_left] using hij)
  form := A.form.freezePrefix I hI
  kernel := A.kernel.freeze z

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ τ : Type*} {s d : ℕ}

theorem affineLineParameters_degree (a q : σ → ℝ) (i : σ) :
    affineLineParameters a q i ∈ weightedSupportLE (fun _ : Unit => 1) 1 :=
  (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    ((weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ ()))

noncomputable def onAffineLine (A : PolynomialPatch σ s d) (a q : σ → ℝ) :
    PolynomialPatch Unit s d := A.reparam (affineLineParameters a q) (affineLineParameters_degree a q)

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open _root_.MvPolynomial

variable {X : Type*} {s d : ℕ}

noncomputable def shiftedKernel (A : PolynomialPatch X s d)
    (v : Fin d → ℝ) (Φ : PatchKernel d) : PolynomialPatch X s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := {
    center := fun i => A.form.center i + C (v i)
    degree := fun i => (weightedSupportLE _ _).add_mem (A.form.degree i)
      (weightedSupportLE_C _ _ _) }
  kernel := Φ

theorem shiftedKernel_residual (A : PolynomialPatch X s d)
    (v : Fin d → ℝ) (Φ : PatchKernel d) (t : X → ℝ) (b : Fin d → ℤ) :
    ((A.shiftedKernel v Φ).form.slots t).residual b = (A.form.slots t).residual b - v := by
  funext i
  simp only [shiftedKernel, TriangularSlots.residual, PolynomialSlots.slots,
    map_add, aeval_C, Pi.sub_apply, Algebra.algebraMap_self, RingHom.id_apply]
  ring

theorem shiftedKernel_value (A : PolynomialPatch X s d)
    (v : Fin d → ℝ) (Φ : PatchKernel d) (t : X → ℝ) :
    (A.shiftedKernel v Φ).value t =
      ∑' b, Φ.value ((A.form.slots t).residual b - v) := by
  simp only [value, TriangularSlots.patchValue, shiftedKernel_residual]
  rfl

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeDomain
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

theorem scalarCubeValue_empty {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) : scalarCubeValue a ∅ = a none := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature]

theorem scalarCubeValue_singleton {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) (i : α) : scalarCubeValue a {i} = a none + a (some i) := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature]

noncomputable def scalarCubeFace {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (a : Option α → ℝ) : ℝ :=
  if i.1 then 1 - scalarCubeValue a i.2 else scalarCubeValue a i.2

theorem positiveInequalityDomain_scalarCubeFace (α : Type*) [Fintype α] [DecidableEq α] :
    positiveInequalityDomain (@scalarCubeFace α _ _) = scalarCubeDomain α := by
  ext a
  constructor
  · intro ha t
    have hlo : 0 < scalarCubeValue a t := ha (false, t)
    have hhi : 0 < 1 - scalarCubeValue a t := ha (true, t)
    exact ⟨hlo, by linarith⟩
  · intro ha i
    rcases i with ⟨b, t⟩
    cases b with
    | false => exact (ha t).1
    | true => exact sub_pos.mpr (ha t).2

theorem scalarCubeDomain_coordinate_abs_lt_one {α : Type*} [Fintype α] [DecidableEq α]
    {a : Option α → ℝ} (ha : a ∈ scalarCubeDomain α) (r : Option α) : |a r| < 1 := by
  have hzero := ha ∅
  rw [scalarCubeValue_empty] at hzero
  cases r with
  | none => exact abs_lt.mpr ⟨by linarith [hzero.1], hzero.2⟩
  | some i =>
    have hi := ha {i}
    rw [scalarCubeValue_singleton] at hi
    exact abs_lt.mpr ⟨by linarith [hzero.1, hzero.2, hi.1], by linarith [hzero.1, hi.2]⟩

theorem scalarCubeDomain_isBounded (α : Type*) [Fintype α] [DecidableEq α] :
    Bornology.IsBounded (scalarCubeDomain α) := by
  apply (Metric.isBounded_closedBall (x := (0 : Option α → ℝ)) (r := 1)).subset
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro r
  simpa only [Real.norm_eq_abs] using (scalarCubeDomain_coordinate_abs_lt_one ha r).le

theorem scalarCubeValue_center {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    scalarCubeValue (scalarCubeCenter α) t = 1 / 2 := by
  simp [scalarCubeValue, Fintype.sum_option, scalarCubeCenter, booleanFeature]

theorem scalarCubeDomain_nonempty (α : Type*) [Fintype α] [DecidableEq α] :
    (scalarCubeDomain α).Nonempty := by
  refine ⟨scalarCubeCenter α, ?_⟩
  intro t
  rw [scalarCubeValue_center]
  norm_num

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomain_volume_lt_top (α : Type*) [Fintype α] [DecidableEq α] :
    volume (scalarCubeDomain α) < ⊤ :=
  (measure_mono subset_closure).trans_lt (scalarCubeDomain_isBounded α).isCompact_closure.measure_lt_top

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedMultidegree
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rationalLieInclusion_injective (e : Basis ι ℚ L) :
    Function.Injective (rationalLieInclusion : L →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] L)) := by
  intro x y h
  apply e.repr.injective
  ext i
  have hi := congrArg (fun z => (e.baseChange ℝ).repr z i) h
  rw [rationalLieInclusion_coordinates, rationalLieInclusion_coordinates] at hi
  exact_mod_cast hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI


namespace Erdos3


noncomputable def kernelJetCoefficientScale (J : Type*) (h : ℕ) (L H : ℝ)
    (e : BoundedIntegerExponent J h) : ℝ := H / monomialScale (fun _ => L) e.val

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientNormalization
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} {d : ℕ}

def slotPolynomialInput (t : σ → R) (b : Fin d → R) (i : Fin d) : σ ⊕ Fin i.val → R :=
  Sum.elim t (fun j => b (earlierSlot i j))

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

def patchParameterWeight {d : ℕ} (i : Fin d) : σ ⊕ Fin i.val → ℕ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ}

noncomputable def slotPrefixLift (k i : Fin d) (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) :
    MvPolynomial (σ ⊕ Fin i.val) ℝ :=
  aeval (PolynomialSlots.placementSubstitution id i k) R

noncomputable def slotShearSubstitution (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (σ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a)) (fun j =>
    X (Sum.inr j) + if earlierSlot i j = k then slotPrefixLift k i R else 0)

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] {d : ℕ}

noncomputable def slotPolynomialLift (i : Fin d) (P : MvPolynomial (σ ⊕ Fin i.val) R) :
    MvPolynomial (σ ⊕ Fin d) R := rename (Sum.map id (earlierSlot i)) P

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointPolynomialDilationGrid
namespace OAI


namespace Erdos3

open scoped BigOperators

theorem abs_monomialScale_le_pow {σ : Type*} (T : σ → ℝ) {K : ℝ}
    (hT : ∀ i, |T i| ≤ K) (α : σ →₀ ℕ) :
    |monomialScale T α| ≤ K ^ (α.sum fun _ n => n) := by
  classical
  calc
    _ = ∏ i ∈ α.support, |T i| ^ α i := by
      simp only [monomialScale, Finsupp.prod, Finset.abs_prod, abs_pow]
    _ ≤ ∏ i ∈ α.support, K ^ α i :=
      Finset.prod_le_prod (fun i _ => pow_nonneg (abs_nonneg _) _)
        (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hT i) _)
    _ = K ^ (α.sum fun _ n => n) := by
      rw [Finset.prod_pow_eq_pow_sum]
      rfl

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree
namespace OAI

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def residualCoordinate (A : PolynomialSlots σ d w) (i : Fin d) :
    MvPolynomial (σ ⊕ Fin d) ℝ := X (Sum.inr i) - slotPolynomialLift i (A.center i)

noncomputable def residualHom (A : PolynomialSlots σ d w) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (σ ⊕ Fin d) ℝ := aeval A.residualCoordinate

theorem residualHom_X (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualHom (X i) = A.residualCoordinate i := by
  simp only [residualHom, aeval_X]

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ}

noncomputable def patchParameterSpecialization (t : σ → ℝ) :
    MvPolynomial (σ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  aeval (Sum.elim (fun a => C (t a)) X)

theorem patchParameterSpecialization_X_slot (t : σ → ℝ) (i : Fin d) :
    patchParameterSpecialization t (X (Sum.inr i)) = X i := by
  simp only [patchParameterSpecialization, aeval_X, Sum.elim_inr]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

theorem regularizedTentPartition_sum (c : I → X) {r : ℝ} (hr : 0 < r) (x : X)
    (hx : ∃ i, dist x (c i) ≤ r) : ∑ i, regularizedTentPartition c r i x = 1 := by
  obtain ⟨i, hi⟩ := hx
  have hs : r ≤ metricTentSum c r x := by
    calc
      r ≤ metricTent (c i) r x := (by linarith : r ≤ 2 * r - dist x (c i)).trans (le_max_right _ _)
      _ ≤ metricTentSum c r x := Finset.single_le_sum (fun j _ => metricTent_nonneg (c j) r x) (Finset.mem_univ i)
  simp only [regularizedTentPartition, ← Finset.sum_div, max_eq_right hs]
  exact div_self (hr.trans_le hs).ne'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

theorem regularizedTentPartition_sum_le (c : I → X) {r : ℝ} (hr : 0 < r) (x : X) :
    (∑ i, regularizedTentPartition c r i x) ≤ 1 := by
  simp only [regularizedTentPartition, ← Finset.sum_div]
  apply (div_le_one (hr.trans_le (le_max_left _ _))).mpr
  exact le_max_right _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbit
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialPointEquiv
    (e : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) : Equiv.Perm (σ → R) where
  toFun := polynomialSubstitutionPoint e.symm.toAlgHom
  invFun := polynomialSubstitutionPoint e.toAlgHom
  left_inv x := by
    funext i
    change aeval (polynomialSubstitutionPoint e.symm.toAlgHom x) (e (X i)) = x i
    rw [polynomialSubstitutionPoint_aeval]
    change aeval x (e.symm (e (X i))) = x i
    rw [e.symm_apply_apply, aeval_X]
  right_inv x := by
    funext i
    change aeval (polynomialSubstitutionPoint e.toAlgHom x) (e.symm (X i)) = x i
    rw [polynomialSubstitutionPoint_aeval]
    change aeval x (e (e.symm (X i))) = x i
    rw [e.apply_symm_apply, aeval_X]

noncomputable def polynomialPointAction :
    (MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) →* Equiv.Perm (σ → R) where
  toFun := polynomialPointEquiv
  map_one' := by
    ext x i
    change aeval x (X i) = x i
    exact aeval_X x i
  map_mul' e f := by
    ext x i
    change aeval x (f.symm (e.symm (X i))) =
      aeval (polynomialSubstitutionPoint f.symm.toAlgHom x) (e.symm (X i))
    exact (polynomialSubstitutionPoint_aeval f.symm.toAlgHom x (e.symm (X i))).symm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem integerCoefficientPolynomials_aeval {P : MvPolynomial σ ℚ}
    (hP : P ∈ integerCoefficientPolynomials σ) (b : σ → ℤ) :
    ∃ z : ℤ, aeval (fun i => (b i : ℚ)) P = (z : ℚ) := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  exact ⟨aeval b Q, polynomial_map_aeval (Int.castRingHom ℚ) b Q⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedLoweringTriangular
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem aeval_eq_of_weightedSupportLT {w : σ → ℕ} {n : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLT w n) (x y : σ → R)
    (hxy : ∀ i, w i < n → x i = y i) : aeval x P = aeval y P := by
  classical
  rw [← P.support_sum_monomial_coeff]
  simp only [map_sum, aeval_monomial]
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun z => z ^ α i)
    (hxy i ((Finsupp.le_weight_of_ne_zero' w (Finsupp.mem_support_iff.mp hi)).trans_lt (hP hα)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {ι κ L M : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommGroup L] [Module ℚ L] [AddCommGroup M] [Module ℚ M]

theorem realified_linear_coordinate_matrix (b : Basis ι ℚ L) (c : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) :
    LinearMap.toMatrix (b.baseChange ℝ) (c.baseChange ℝ) (φ.baseChange ℝ) =
      (LinearMap.toMatrix b c φ).map (Rat.castHom ℝ) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Matrix.map_apply,
    scalarExtension_basis_coordinates, Rat.coe_castHom]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalPowerGrid
namespace OAI

section

namespace Erdos3

theorem realDenominatorGrid_rational_power_scale {ι : Type*}
    (degree : ι → ℕ) (D d s : ℕ) (a : ℤ) (hd : 0 < d) (hdegree : ∀ i, degree i ≤ s)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid D) :
    (fun i => ((a : ℝ) / d) ^ degree i * x i) ∈ realDenominatorGrid (D * d ^ s) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => a ^ degree i * (d : ℤ) ^ (s - degree i) * z i, ?_⟩
  funext i
  have hi : (z i : ℝ) = (D : ℝ) * x i := congrFun hz i
  change ((a ^ degree i * (d : ℤ) ^ (s - degree i) * z i : ℤ) : ℝ) =
    ((D * d ^ s : ℕ) : ℝ) * (((a : ℝ) / d) ^ degree i * x i)
  push_cast
  rw [hi]
  calc
    _ = (D : ℝ) * ((d : ℝ) ^ s * ((a : ℝ) / d) ^ degree i) * x i := by
      rw [rational_power_clear_denominator a d s (degree i) hd (hdegree i)]
      ring
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledLinearSubspaceLift
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

variable {η ι δ : Type*} [Fintype ι]

theorem jointMatrixImages_equation (Q : η → Matrix ι ι ℚ) (e r : η → ι → ℝ) (v : ι → ℝ)
    (h : ∀ b, (fun i j => (Q b i j : ℝ)) *ᵥ (v - e b - r b) = 0) :
    (fun bi j => (jointMatrix Q bi j : ℝ)) *ᵥ v = jointMatrixImages Q e + jointMatrixImages Q r := by
  funext bi
  have hb := h bi.1
  change Matrix.of (fun i j => (Q bi.1 i j : ℝ)) *ᵥ (v - e bi.1 - r bi.1) = 0 at hb
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub] at hb
  have hb' := congrFun hb bi.2
  change ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ v) bi.2 -
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ e bi.1) bi.2 -
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ r bi.1) bi.2 = 0 at hb'
  change ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ v) bi.2 =
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ e bi.1) bi.2 +
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ r bi.1) bi.2
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeFiberSlicePatch
namespace OAI

section

namespace Erdos3

variable {I X : Type*}

theorem finiteSplitPoint_restrict (p : I → Prop) [DecidablePred p] (x : I → X) :
    finiteSplitPoint p (fun i => x i) (fun i => x i) = x := by
  funext i
  by_cases hi : p i <;> simp only [finiteSplitPoint, hi, dite_true, dite_false]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateFiberPatch
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem coordinateFiberParameters_degree (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ)
    (i : I) : coordinateFiberParameters keep fixed i ∈ weightedSupportLE (fun _ => 1) 1 := by
  by_cases hi : keep i
  · simp only [coordinateFiberParameters, dif_pos hi]
    exact weightedSupportLE_X _ _
  · simp only [coordinateFiberParameters, dif_neg hi]
    exact weightedSupportLE_C _ _ _

theorem exists_integerBox_coordinate_fiber (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (keep : I → Prop) (f : (I → ℤ) → ℝ) {a : ℝ}
    (hmean : a ≤ 𝔼 x ∈ integerBox N, f x) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i, 0 ≤ fixed i ∧ fixed i < N i) ∧
      a ≤ 𝔼 x ∈ integerBox (fun i : {i // keep i} => N i), f (finiteSplitPoint keep x fixed) := by
  let X := fun i => Finset.Ico (0 : ℤ) (N i)
  let e := Equiv.piEquivPiSubtypeProd keep (fun i => X i)
  have hn (i : I) : Nonempty (X i) :=
    ⟨⟨0, Finset.mem_Ico.mpr ⟨le_rfl, by exact_mod_cast hN i⟩⟩⟩
  let : ∀ i, Nonempty (X i) := hn
  have hsplit : (𝔼 x : (∀ i, X i), f (fun i => (x i).val)) =
      𝔼 v : (∀ i : {i // ¬keep i}, X i),
        𝔼 u : (∀ i : {i // keep i}, X i),
          f (finiteSplitPoint keep (fun i => (u i).val) (fun i => (v i).val)) := by
    calc
      _ = 𝔼 uv : (∀ i : {i // keep i}, X i) × (∀ i : {i // ¬keep i}, X i),
          f (finiteSplitPoint keep (fun i => (uv.1 i).val) (fun i => (uv.2 i).val)) := by
        apply Fintype.expect_equiv e
        intro x
        change f (fun i => (x i).val) =
          f (finiteSplitPoint keep (fun i => (x i.val).val) (fun i => (x i.val).val))
        exact congrArg f (finiteSplitPoint_restrict keep (fun i => (x i).val)).symm
      _ = _ := by
        rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  have hfull : a ≤ 𝔼 x : (∀ i, X i), f (fun i => (x i).val) := by
    rw [← finiteBoxPoints_expect_finset X f]
    exact hmean
  rw [hsplit] at hfull
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hfull
  refine ⟨fun i => (v i).val, fun i => Finset.mem_Ico.mp (v i).property, ?_⟩
  rw [← finiteBoxPoints_expect_finset (fun i : {i // keep i} => X i)
    (fun x => f (finiteSplitPoint keep x (fun i => (v i).val)))] at hv
  exact hv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlowPolynomialSliceLogCost
namespace OAI

section

namespace Erdos3

noncomputable def slowPolynomialSliceRadius (d n : ℕ) (M : ℝ) : ℝ :=
  min 1 ((1 / (20 * Real.pi)) / (slowPolynomialSliceSlope d n M + 1))

theorem slowPolynomialSliceRadius_eq (d n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    slowPolynomialSliceRadius d n M =
      (1 / (20 * Real.pi)) / (slowPolynomialSliceSlope d n M + 1) := by
  apply min_eq_right
  have hK := slowPolynomialSliceSlope_nonneg d n hM
  have hδ : 1 / (20 * Real.pi) ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  exact (div_le_one (by linarith)).mpr (by linarith)

theorem slowPolynomialSliceRadius_pos (d n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 < slowPolynomialSliceRadius d n M := by
  rw [slowPolynomialSliceRadius_eq d n hM]
  have := slowPolynomialSliceSlope_nonneg d n hM
  positivity

theorem slowPolynomialSlice_log_cost (d n : ℕ) {M p q : ℝ}
    (hp : 1 ≤ p) (hn : (n : ℝ) ≤ p) (hM : 0 ≤ M)
    (hMexp : M ≤ Real.exp p) (hq : 0 < q) (hqexp : q ≤ Real.exp p) :
    Real.log (4 * q / slowPolynomialSliceRadius d n M) ≤
      (p + (d + 400 : ℕ)) ^ (d + 400) := by
  let A : ℝ := ((d : ℝ) + 2) * p + 3 * d + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK := slowPolynomialSliceSlope_nonneg d n hM
  have hKexp := slowPolynomialSliceSlope_le_exp d n (by linarith : 0 ≤ p) hn hM hMexp
  have hK1 : slowPolynomialSliceSlope d n M + 1 ≤ Real.exp (A + 1) := by
    simpa only [add_zero] using add_le_exp_add_one hA (le_refl (0 : ℝ))
      hKexp (by simp : (1 : ℝ) ≤ Real.exp 0)
  have hπ : 80 * Real.pi ≤ Real.exp 320 := by
    linarith [Real.pi_lt_four, Real.add_one_le_exp (320 : ℝ)]
  have hradius := slowPolynomialSliceRadius_pos d n hM
  have hratio : 4 * q / slowPolynomialSliceRadius d n M =
      (80 * Real.pi) * q * (slowPolynomialSliceSlope d n M + 1) := by
    rw [slowPolynomialSliceRadius_eq d n hM]
    field_simp
    ring
  have hexp : 4 * q / slowPolynomialSliceRadius d n M ≤
      Real.exp (320 + p + (A + 1)) := by
    rw [hratio]
    calc
      _ ≤ Real.exp 320 * Real.exp p * Real.exp (A + 1) := by
        gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hcost : 320 + p + (A + 1) ≤ (p + (d + 400 : ℕ)) ^ (d + 400) := by
    let t : ℝ := p + (d + 400 : ℕ)
    have hdt : (d : ℝ) + 400 ≤ t := by dsimp [t]; push_cast; linarith
    have hpt : p + 3 ≤ t := by dsimp [t]; push_cast; linarith
    have ht : 1 ≤ t := by dsimp [t]; push_cast; linarith
    calc
      _ ≤ ((d : ℝ) + 400) * (p + 3) := by dsimp [A]; nlinarith
      _ ≤ t * t := mul_le_mul hdt hpt (by linarith) (by linarith)
      _ = t ^ 2 := by ring
      _ ≤ t ^ (d + 400) := pow_le_pow_right₀ ht (by omega)
      _ = _ := rfl
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  exact hexp.trans (Real.exp_le_exp.mpr hcost)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualOrdinaryPointwiseSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem gradedImagePointwiseSpanning_heightBound {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  apply (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4)).trans
  apply Real.exp_le_exp.mpr
  have hpow : 1 ≤ (p + 2) ^ 4 := one_le_pow₀ (by linarith)
  calc
    (p + 2) ^ 4 + 1 ≤ (p + 2) ^ 4 + (p + 2) ^ 4 := by linarith only [hpow]
    _ = (p + 2) ^ 4 * 2 := by ring
    _ ≤ (p + 2) ^ 4 * (p + 2) :=
      mul_le_mul_of_nonneg_left (by linarith : 2 ≤ p + 2) (by positivity)
    _ = (p + 2) ^ 5 := by ring

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry
namespace OAI

section

namespace Erdos3

open Module
open scoped Classical TensorProduct

theorem allocatedCandidateCommonFastSectionInput_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedCandidateCommonFastSectionInput p ∧
    p ≤ allocatedCandidateCommonFastSectionInput p := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hp4 : p + 2 ≤ (p + 2) ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ (4 : ℕ) by omega)
  dsimp [allocatedCandidateCommonFastSectionInput]
  constructor <;> linarith

theorem allocatedCandidateCommonFastCoordinateHeight_bounds {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ allocatedCandidateCommonFastCoordinateHeight p ∧
    (allocatedCandidateCommonFastCoordinateHeight p : ℝ) ≤
      Real.exp (allocatedCandidateCommonFastGeometryLog p) := by
  refine ⟨one_le_ceil_exp _, ?_⟩
  have hq := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  apply (ceil_exp_le_exp_add_one (by positivity :
    0 ≤ (allocatedCandidateCommonFastSectionInput p + 2) ^ 7)).trans
  apply Real.exp_le_exp.mpr
  have hpow := pow_le_pow_right₀ (by linarith :
    1 ≤ allocatedCandidateCommonFastSectionInput p + 2) (by omega : 7 ≤ (47 : ℕ))
  dsimp [allocatedCandidateCommonFastGeometryLog]
  linarith only [hpow]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingCost
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

noncomputable def potentialCost (B : Finset G) (v : ℝ) : (G → ℝ) → List (Finset G) → ℝ
  | _, [] => 0
  | f, C :: cs => (C.card : ℝ) / B.card * ((𝔼 x ∈ C, f x) * v) ^ (1 / 4 : ℝ) +
      potentialCost B v (remainder C f) cs

end Erdos3.Peeling

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTagConstraintSpaces
namespace OAI

section

namespace Erdos3.VectorPolynomial.RationalTagConstraint

variable {m : ℕ} {J : Fin m → Type*} {X : Type*}

theorem retained_le_span (c : RationalTagConstraint J)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)}
    (hretained : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ U j) → point ∈ K)
    (hmember : ∀ point ∈ K, c.member point) :
    U c.tag ≤ Submodule.span ℝ (Set.range (fun a i => (c.generators a i : ℝ))) := by
  classical
  intro v hv
  let tags : ∀ j, J j → ℝ := Function.update (fun j => (0 : J j → ℝ)) c.tag v
  let point : (X ⊕ (Σ j, J j)) → ℝ := Sum.elim 0 (fun a => tags a.1 a.2)
  have hpoint : point ∈ K := by
    apply hretained
    intro j
    change tags j ∈ U j
    by_cases hj : j = c.tag
    · subst j
      simpa only [tags, Function.update_self] using hv
    · simpa only [tags, Function.update_of_ne hj] using (U j).zero_mem
  have hc := hmember point hpoint
  simpa only [member, point, Sum.elim_inr, tags, Function.update_self] using hc

end Erdos3.VectorPolynomial.RationalTagConstraint

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PivotAnnihilatorFrequencyCode
namespace OAI

section

namespace Erdos3

open Module
open scoped Classical

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

theorem mem_frequencyCodeKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    {D : ℕ} (code : Fin D → Option J) (v : V) :
    v ∈ frequencyCodeKernel P eta code ↔ v ∈ P ∧
      ∀ i j, code i = some j → eta j v = 0 := by
  simp only [frequencyCodeKernel, mem_finiteFrequencyKernel, List.mem_finRange, forall_true_left]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h i j hij
    simpa only [hij, Option.elim_some] using h i
  · intro h i
    cases hi : code i with
    | none => simp
    | some j => simpa only [Option.elim_some] using h i j hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelProjectionPresentPivotIdeal
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

noncomputable instance instFintypeKernelProjectionPresentPivot {J : Type*} {r : ℕ} (code : Fin r → Option J) :
    Fintype (KernelProjectionPresentPivot code) := inferInstanceAs (Fintype {i // ∃ j, code i = some j})

noncomputable def kernelProjectionSelectedPivot {J : Type*} {r : ℕ}
    (code : Fin r → Option J) (i : KernelProjectionPresentPivot code) : J :=
  Classical.choose i.property

theorem kernelProjectionSelectedPivot_spec {J : Type*} {r : ℕ}
    (code : Fin r → Option J) (i : KernelProjectionPresentPivot code) :
    code i.val = some (kernelProjectionSelectedPivot code i) := Classical.choose_spec i.property

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearObservableNet
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

abbrev PatchTopCoefficientIndex (d s : ℕ) := Fin d × BoundedIntegerExponent (Fin d) s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledMarkedKernelNormalization
namespace OAI

section

namespace Erdos3

theorem kernel_inclusion_height_mul_le_exp (n k H l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((H ^ (n * k) * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg H) hH (n * k)
  rw [← Real.exp_nat_mul] at hpow
  have hprod : ((n * k : ℕ) : ℝ) * p ≤ (p + 2) ^ 3 := by
    rw [Nat.cast_mul, show (3 : ℕ) = 2 + 1 by decide, pow_succ, pow_two]
    gcongr <;> linarith
  have hlog : ((n * k : ℕ) : ℝ) * p + p ≤ (p + 2) ^ 4 := by
    calc
      _ ≤ 2 * (p + 2) ^ 3 := by
        linarith [le_power_budget hp (by decide : 1 ≤ 3)]
      _ ≤ (p + 2) * (p + 2) ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp (((n * k : ℕ) : ℝ) * p) * Real.exp p :=
      mul_le_mul hpow hl (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((n * k : ℕ) : ℝ) * p + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem kernel_inclusion_denominator_mul_le_exp (n k H q l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hq : q ≤ H ^ (n * k))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((q * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hql : ((q * l : ℕ) : ℝ) ≤ ((H ^ (n * k) * l : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.mul_le_mul_right l hq)
  exact hql.trans (kernel_inclusion_height_mul_le_exp n k H l hp hn hk hH hl)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LowTaggedCoordinateRestriction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem lowTaggedEmbedding_pairing (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (a : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) (v : J j → ℝ) :
    (∑ i, a i * lowTaggedEmbedding J d j hj v i) =
      ∑ k : J j, a (lowTaggedSlot J d j hj k) * v k := by
  classical
  simp only [lowTaggedEmbedding, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.single_apply, LinearMap.proj_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [Pi.single_apply]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFrozenChart
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped Classical

variable {I R : Type*} [CommRing R]

theorem frozenCoordinate_zero_homogeneous (keep : I → Prop) (i : I) :
    (frozenCoordinate keep (0 : {i // ¬keep i} → R) i).IsWeightedHomogeneous
      (fun _ => 1) 1 := by
  by_cases hi : keep i
  · simp only [frozenCoordinate, dif_pos hi]
    exact isWeightedHomogeneous_X R (fun _ : {i // keep i} => 1) ⟨i, hi⟩
  · simp only [frozenCoordinate, dif_neg hi, Pi.zero_apply, map_zero]
    exact isWeightedHomogeneous_zero R (fun _ : {i // keep i} => 1) 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3
open scoped BigOperators TensorProduct Classical

variable {I : Type*} (keep : I → Prop)

theorem frozenLongExtension_shortStarts (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i) (x : {i // keep i} → ℤ) :
    frozenLongExtension keep (frozenShortStarts keep fixed) x =
      finiteSplitPoint keep x fixed := by
  funext i
  by_cases hi : keep i
  · simp only [frozenLongExtension, finiteSplitPoint, dif_pos hi]
  · simp only [frozenLongExtension, frozenShortStarts, finiteSplitPoint, dif_neg hi]
    exact Int.toNat_of_nonneg (hfixed ⟨i, hi⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowestPolynomialLayer
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {D : ℕ} {R : Type*} [CommRing R]

noncomputable def earlierSlotMatrix (m : (i : Fin D) → Fin i.val → R) :
    Matrix (Fin D) (Fin D) R := fun i j =>
  ∑ k : Fin i.val, if earlierSlot i k = j then m i k else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.TriangularAffineReset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {d : ℕ}

noncomputable def reducedLatticeColumn (T : Matrix (Fin d) (Fin d) ℝ)
    (j i : Fin d) : ℤ :=
  if i < j then 0 else if i = j then 1 else
    -round (∑ k : Fin i.val,
      T i (earlierSlot i k) * (reducedLatticeColumn T j (earlierSlot i k) : ℝ))
termination_by i.val
decreasing_by exact k.isLt

noncomputable def triangularReductionMatrix (T : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℤ := fun i j => reducedLatticeColumn T j i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FrozenPolynomialAffineRange
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem longChart_top_eval_mem {J Full Long : Type*} [Fintype J]
    (β : J → MvPolynomial Full ℤ) (f : Long ↪ Full) (r : ℕ)
    (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ α : Long →₀ ℕ, α.degree = r →
      (fun j => (((β j).coeff (α.mapDomain f) : ℤ) : ℝ)) ∈ K)
    (x : Long → ℝ) :
    (fun j => MvPolynomial.eval x
      (killCompl f.injective (homogeneousComponent r
        (MvPolynomial.map (Int.castRingHom ℝ) (β j))))) ∈ K := by
  apply polynomialFamily_eval_mem
  intro α
  simp only [coeff_killCompl, coeff_homogeneousComponent, Finsupp.degree_mapDomain,
    coeff_map, Int.coe_castRingHom]
  by_cases hα : α.degree = r
  · simp only [if_pos hα]
    exact hcoeff α hα
  · simp only [if_neg hα]
    exact K.zero_mem

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartRecoveredTerminal
namespace OAI

section

namespace Erdos3

theorem monomialScale_mapDomain_embedding {A B : Type*}
    (f : A ↪ B) (T : B → ℝ) (α : A →₀ ℕ) :
    monomialScale T (α.mapDomain f) = monomialScale (fun i => T (f i)) α := by
  exact Finsupp.prod_mapDomain_index_inj f.injective

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymbolCoordinateFreezeBounds
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial

variable {I R : Type*} [CommRing R]

theorem freezePolynomial_zero_eq_killCompl (keep : I → Prop) :
    freezePolynomial keep (0 : {i // ¬keep i} → R) =
      MvPolynomial.killCompl (f := (Subtype.val : {i // keep i} → I)) Subtype.val_injective := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  simp only [freezePolynomial, MvPolynomial.killCompl, aeval_X]
  by_cases hi : keep i
  · have hr : i ∈ Set.range (Subtype.val : {i // keep i} → I) := ⟨⟨i, hi⟩, rfl⟩
    simp only [frozenCoordinate, dif_pos hi, dif_pos hr]
    congr 1
    exact (Equiv.ofInjective_symm_apply Subtype.val_injective ⟨i, hi⟩).symm
  · have hr : i ∉ Set.range (Subtype.val : {i // keep i} → I) := by
      rintro ⟨⟨j, hj⟩, rfl⟩
      exact hi hj
    simp only [frozenCoordinate, dif_neg hi, dif_neg hr, Pi.zero_apply, map_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonRefilteredFactorsSymbolTransport
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical

variable {σ R : Type*} [CommRing R]

theorem nestedFrozenCoordinate_top_independent
    (keepOriginal keepLater : σ → Prop)
    (fixed fixed' : {i : {i // keepOriginal i} // ¬keepLater i.val} → R)
    (i : {i // keepOriginal i}) :
    weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
      (nestedFrozenCoordinate keepOriginal keepLater fixed i) =
    weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
      (nestedFrozenCoordinate keepOriginal keepLater fixed' i) := by
  by_cases hi : keepLater i.val
  · simp only [nestedFrozenCoordinate, dif_pos hi]
  · simp only [nestedFrozenCoordinate, dif_neg hi]
    rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_C (R := R) _ _),
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_C (R := R) _ _)]
    norm_num

theorem nestedFrozenCoordinate_zero_comp
    (keepOriginal keepLong keepLater : σ → Prop)
    (hsub : ∀ i, keepLater i → keepLong i) :
    (fun i => aeval
      (nestedFrozenCoordinate keepLong keepLater
        (0 : {i : {i // keepLong i} // ¬keepLater i.val} → R))
      (nestedFrozenCoordinate keepOriginal keepLong
        (0 : {i : {i // keepOriginal i} // ¬keepLong i.val} → R) i)) =
    nestedFrozenCoordinate keepOriginal keepLater
      (0 : {i : {i // keepOriginal i} // ¬keepLater i.val} → R) := by
  funext i
  by_cases hlater : keepLater i.val
  · have hlong := hsub i.val hlater
    simp [nestedFrozenCoordinate, hlater, hlong]
  · by_cases hlong : keepLong i.val <;>
      simp [nestedFrozenCoordinate, hlater, hlong]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration

open Module

noncomputable def controlledProjectionBudget (p : ℝ) : ℝ :=
  (((p + 2) ^ 10 + 2) ^ 36) + (((p + 2) ^ 10 + 2) ^ 18 + p) +
    (preimageBasisBudget p + 1)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PrecenterForecastNativeAtomDictionary
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

abbrev PrecenterForecastNativeAtomLabel {X Branch : Type*}
    (models : Branch → CenteredForecastModel X) :=
  {label : Σ b, Fin (models b).nterms // (models label.1).models label.2 ≠ 0}

end Erdos3

end

end OAI
end


