-- Prove2me | Definitions.Def_OAIE3v2B175
-- name    : OAIE3v2B175
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:39:07.827828+00:00
-- url     : https://prove2.me/theorems/2a6a8366-ebcf-4067-a73d-0e2e26cc00e8
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 177 of 311
-- statement:
--   Definitions bundle 177 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B153`, `OAIE3v2B157`, `OAIE3v2B158`, `OAIE3v2B159` of this split.
--
--   Modules: `Estimates/AllocatedMarkedDictionaryRecovery.lean`, `Estimates/CommonIntegralModelEquivalences.lean`, `Estimates/ControlledSingleRefilteredReconstruction.lean`, `Estimates/ExternalPhysicalMemberPivotMasks.lean`, `Estimates/LinearMapIntegralCover.lean`, `Estimates/MarkedRefilteredLowerNativeDiagram.lean`, `Estimates/NativeBoundedSubalgebraRepresentatives.lean`, `Estimates/NativeMarkedDiagramOrbitLift.lean`, `Estimates/NativeModelOrbit.lean`, `Estimates/NativeSquareRecovery.lean`, `Estimates/OptionComplementCover.lean`, `Estimates/PrescribedComplementInputPartition.lean`, `Estimates/PrescribedCoveredInputPartition.lean`, `Estimates/PrescribedSquareImagePartition.lean`, `Estimates/RealifiedTopQuotient.lean`, `Estimates/StrongRefiltrationReconstruction.lean`, `Estimates/UnconditionalStepDrop.lean`, `Estimates/UniformControlledNativeExternalNetsOfRecovery.lean`, `Geometry/CommonRationalModelCoordinates.lean`, `Lattices/AffineSampleAlphabet.lean`, `Lattices/FixedAffineResidueDescent.lean`, `Linear/ExternalFamilyPrecenterProjectionData.lean`, `Linear/NativeMarkedKernelRepresentatives.lean`, `Linear/SplitCoverProjection.lean`, `Nilpotent/FrozenComplexNiltest.lean`, `Nilpotent/LocalNiltestFixedNativePartners.lean`, `Sampling/MarkedKernelProjectionScoreRestoration.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B153
import Definitions.Def_OAIE3v2B157
import Definitions.Def_OAIE3v2B158
import Definitions.Def_OAIE3v2B159

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_frozen_external_test_net {L O R X Y Z IO IA IZ : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    [Fintype IO] [Fintype IA] [Fintype R] [Fintype IZ]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (φ : X → Y × Z)
    (b : X → D.RealGroup) (S : O → D.Space → ℂ) (A : Set D.RealGroup) (r : R → D.RealGroup)
    (K ℓ : ℝ≥0) (hS : ∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o))
    (hpositive : ∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1)
    (hreconstruct : ∀ o (a : A) j, ∃ (v : Y × Z → ℂ) (C : ℝ≥0),
      C ≤ K ∧ LipschitzWith C v ∧ ∀ x, v (φ x) = S o (QuotientGroup.mk (a.val * b x * r j)))
    (oc : IO → O) (ac : IA → A) (zc : IZ → Z) {δO δA δZ : ℝ}
    (hO : ∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ δO)
    (hA :
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ)
      ∀ a : A, ∃ i, dist a (ac i) ≤ δA)
    (hZ : ∀ z, ∃ i, dist z (zc i) ≤ δZ) :
    let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r j))
    let n := Fintype.card IO * Fintype.card IA * Fintype.card R * Fintype.card IZ
    ∃ centers : Fin n → Y → ℂ,
      (∀ i, LipschitzWith K (centers i)) ∧
      (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
      (∀ i y, ‖centers i y‖ ≤ 1) ∧
      (∀ o a j x, positiveImageSlice φ K (F o a j) (φ x).2 (φ x).1 =
        S o (QuotientGroup.mk (a.val * b x * r j))) ∧
      ∀ o a j z, ∃ i, ∀ y,
        ‖positiveImageSlice φ K (F o a j) z y - centers i y‖ ≤ δO + ℓ * δA + K * δZ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r j))
  have hvariation : ∀ o (a a' : A) j x, ‖F o a j x - F o a' j x‖ ≤ ℓ * dist a a' := by
    intro o a a' j x
    exact D.frozen_observable_change_left (S o) (hS o) a.val a'.val (b x) (r j)
  exact exists_external_test_net φ F K ℓ (fun o a j x => hpositive o _)
    hreconstruct hvariation oc ac zc
    (fun o => by obtain ⟨i, hi⟩ := hO o; exact ⟨i, fun a j x => hi _⟩) hA hZ

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_controlled_native_external_net (s t r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M O R IO X Y : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [Fintype IO] [Fintype R] [Nonempty X] [PseudoMetricSpace Y] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (B K ℓ : ℝ≥0) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ r) →
      (K : ℝ) ≤ Real.exp p → (ℓ : ℝ) ≤ Real.exp p →
      0 < ε → 1 / ε ≤ Real.exp p →
      (Fintype.card IO : ℝ) ≤ Real.exp p → (Fintype.card R : ℝ) ≤ Real.exp p →
      ∀ (S : O → D.Space → ℂ) (b : X → D.RealGroup) (r₀ : R → D.RealGroup)
        (φ : X → Y × E.Space) (oc : IO → O),
      (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
      (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
      (∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ ε / 3) →
      (∀ o (a : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ) B) j,
        ∃ (v : Y × E.Space → ℂ) (K' : ℝ≥0), K' ≤ K ∧
          (letI := E.metricSpace; LipschitzWith K' v) ∧
          ∀ x, v (φ x) = S o (QuotientGroup.mk (a.val * b x * r₀ j))) →
      letI := E.metricSpace
      let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B
      let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r₀ j))
      ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ ∃ centers : Fin n → Y → ℂ,
        (∀ i, LipschitzWith K (centers i)) ∧
        (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
        (∀ i y, ‖centers i y‖ ≤ 1) ∧
        (∀ o a j x, positiveImageSlice φ K (F o a j) (φ x).2 (φ x).1 = F o a j x) ∧
        ∀ o a j z, ∃ i, ∀ y, ‖positiveImageSlice φ K (F o a j) z y - centers i y‖ ≤ ε := by
  obtain ⟨cA, _, hgroup⟩ := exists_native_group_parameter_cover s r
  obtain ⟨cZ, _, hquot⟩ := exists_native_quotient_parameter_cover t
  let X : Polynomial ℕ := Polynomial.X
  let T := 2 * X + 7
  let P := 2 * X + (T + Polynomial.C cA) ^ cA + (T + Polynomial.C cZ) ^ cZ
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M O R IO X₀ Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E B K ℓ p ε
    hp hD hE hB hBp hK hℓ hε hεinv hIO hR S b r₀ φ oc hS hpositive hO hreconstruct
  let q := 2 * p + 7
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hBq : (B : ℝ) ≤ Real.exp ((q + 2) ^ r) := hBp.trans
    (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) r))
  obtain ⟨nA, _, hnA, ac, hAcov⟩ := hgroup D B hq (hD.mono D hpq) hB hBq
    (externalNetMesh_pos ℓ hε) (externalNetMesh_inverse_bound ℓ hε hp hℓ hεinv)
  obtain ⟨nZ, _, hnZ, zc, hZcov⟩ := hquot E hq (hE.mono E hpq)
    (externalNetMesh_pos K hε) (externalNetMesh_inverse_bound K hε hp hK hεinv)
  let := E.metricSpace
  have hnet := D.exists_frozen_external_test_net φ b S
    (coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B)
    r₀ K ℓ hS hpositive hreconstruct oc ac zc hO hAcov hZcov
  dsimp only at hnet
  obtain ⟨centers, hLip, hunit, hcap, heval, hcover⟩ := hnet
  have hfinal : 2 * p + (q + cA) ^ cA + (q + cZ) ^ cZ ≤ (p + C) ^ C := by
    simpa [P, T, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hcount : ((Fintype.card IO * nA * Fintype.card R * nZ : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    push_cast
    calc
      _ ≤ Real.exp p * Real.exp ((q + cA) ^ cA) * Real.exp p * Real.exp ((q + cZ) ^ cZ) := by
        gcongr
      _ = Real.exp (2 * p + (q + cA) ^ cA + (q + cZ) ^ cZ) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hfinal
  refine ⟨_, ?_, centers, hLip, hunit, hcap, heval, ?_⟩
  · simpa only [Fintype.card_fin] using hcount
  · intro o a j z
    obtain ⟨i, hi⟩ := hcover o a j z
    exact ⟨i, fun y => (hi y).trans (externalNetMesh_error K ℓ hε.le)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_controlled_native_external_nets (s t r netExponent : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M O R X Y : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [Fintype R] [Nonempty X] [PseudoMetricSpace Y] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (B K ℓ : ℝ≥0) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ r) →
      (K : ℝ) ≤ Real.exp p → (ℓ : ℝ) ≤ Real.exp p →
      (Fintype.card R : ℝ) ≤ Real.exp p →
      ∀ (S : O → D.Space → ℂ) (b : X → D.RealGroup) (r₀ : R → D.RealGroup)
        (φ : X → Y × E.Space),
      (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
      (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
      (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + netExponent) ^ netExponent) ∧
        ∃ oc : Fin n → O, ∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ η) →
      (∀ o (a : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ) B) j,
        ∃ (v : Y × E.Space → ℂ) (K' : ℝ≥0), K' ≤ K ∧
          (letI := E.metricSpace; LipschitzWith K' v) ∧
          ∀ x, v (φ x) = S o (QuotientGroup.mk (a.val * b x * r₀ j))) →
      letI := E.metricSpace
      let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B
      let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r₀ j))
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + Real.log (1 / ε) + C) ^ C) ∧ ∃ centers : Fin n → Y → ℂ,
        (∀ i, LipschitzWith K (centers i)) ∧
        (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
        (∀ i y, ‖centers i y‖ ≤ 1) ∧
        (∀ o a j x, positiveImageSlice φ K (F o a j) (φ x).2 (φ x).1 = F o a j x) ∧
        ∀ o a j z, ∃ i, ∀ y, ‖positiveImageSlice φ K (F o a j) z y - centers i y‖ ≤ ε := by
  obtain ⟨localExponent, _, hnet⟩ := exists_controlled_native_external_net s t r
  obtain ⟨C, hC, hscalar⟩ := exists_uniformExternalNetScalarBudget netExponent localExponent
  refine ⟨C, hC, ?_⟩
  intro L M O R X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E B K ℓ p
    hp hD hE hB hBp hK hℓ hR S b r₀ φ hS hpositive hO hreconstruct
  let := E.metricSpace
  dsimp only
  intro ε hε hε1
  obtain ⟨q, hq, hpq, hlogq, hmemberq, hqC⟩ := hscalar p ε hp hε hε1
  obtain ⟨nO, hnO, oc, hcoverO⟩ := hO (ε / 3) (by positivity) (by linarith)
  have hexp := Real.exp_le_exp.mpr hpq
  have hBq : (B : ℝ) ≤ Real.exp ((q + 2) ^ r) :=
    hBp.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) r))
  have hεinv : 1 / ε ≤ Real.exp q := by
    calc
      1 / ε = Real.exp (Real.log (1 / ε)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlogq
  have hnOq : (Fintype.card (Fin nO) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin] using hnO.trans (Real.exp_le_exp.mpr hmemberq)
  obtain ⟨n, hn, centers, hLip, hunit, hcap, heval, hcover⟩ :=
    hnet D E B K ℓ hq (hD.mono D hpq) (hE.mono E hpq)
      hB hBq (hK.trans hexp) (hℓ.trans hexp) hε hεinv hnOq (hR.trans hexp)
      S b r₀ φ oc hS hpositive hcoverO hreconstruct
  exact ⟨n, hn.trans (Real.exp_le_exp.mpr hqC), centers, hLip, hunit, hcap, heval, hcover⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTopQuotient
namespace OAI

section

namespace Erdos3
open Module

namespace RationalFilteredNilmanifold

theorem quotientInducedMark_native_logHeight
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t r d f n : ℕ}
    (D : RationalFilteredNilmanifold L s d) (Fmark : RationalFilteredNilmanifold M t f)
    (I : LieIdeal ℚ L) (Q : RationalFilteredNilmanifold (L ⧸ I) r n)
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, φ x = 0)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hQ : Q.GeometryComplexityLE p)
    (hprojection : ∀ i j, rationalLogHeight
      (Q.basis.repr (lieQuotientMap I (D.basis j)) i) ≤ p)
    (hmark : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis j)) i) ≤ p) :
    ∀ i j, rationalLogHeight
      (Fmark.basis.repr (quotientInducedMark I φ hker (Q.basis j)) i) ≤
      quotientInducedMarkHeightBudget p := by
  intro i j
  exact quotientInducedMark_basis_logHeight I D.basis Fmark.basis Q.basis φ hker hp
    (by simpa only [Fintype.card_fin] using hD.1)
    (by simpa only [Fintype.card_fin] using hQ.1)
    (fun a k => hprojection k a) (fun a k => hmark k a) j i

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type v} {H : Type u} {L : ι → Type u}
  [LieRing H] [LieAlgebra ℚ H] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem quotient_markedDiagram_injective {s : ℕ}
    (E : NilpotentLieFiltration H (s + 1)) (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (hker : ∀ x : H, x ∈ E.layer (s + 1) → (∀ i, ψ i x = 0) → x = 0) :
    Function.Injective (optionProductMap (lieQuotientMap (E.layerIdeal (s + 1))) ψ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker (x - y)
  · have hq : lieQuotientMap (E.layerIdeal (s + 1)) x =
        lieQuotientMap (E.layerIdeal (s + 1)) y := congrFun hxy none
    apply (E.mem_layerIdeal (s + 1) (x - y)).mp
    apply (lieQuotientMap_eq_zero (E.layerIdeal (s + 1)) (x - y)).mp
    rw [map_sub, hq, sub_self]
  · intro i
    have hi : ψ i x = ψ i y := congrFun hxy (some i)
    rw [map_sub, hi, sub_self]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

universe u

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)

theorem allocatedMarkedDiagram_injective_of_top_kernel
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (hker : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) →
      φ x = 0 → x = 0) :
    Function.Injective (optionProductMap
      (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)))
      (fun _ : Unit => D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)) := by
  apply quotient_markedDiagram_injective
  intro x hx hzero
  apply Subtype.ext
  apply hker (x : L)
  · rw [hDref] at hx
    exact (D.filtration.mem_gradedRefiltration_layer W (s + 1) x).mp hx
  · exact congrArg Subtype.val (hzero ())

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalNiltestFixedNativePartners
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem withOrbit_complexity (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) (p : ℝ) :
    (T.withOrbit g).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExternalPhysicalMemberPivotMasks
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {L σ I : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d)

noncomputable def externalNetNiltest (f : D.Space → ℂ) (K : ℝ≥0)
    (hcap : ∀ x, ‖f x‖ ≤ 1) (hLip : letI := D.metricSpace; LipschitzWith K f)
    {w : σ → ℕ} (orbit : D.filtration.realification.PolynomialOrbit w) : D.Niltest w where
  orbit := orbit
  observable := f
  normBound := 1
  lipBound := K
  norm_le := hcap
  lipschitz := hLip

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalFamilyPrecenterProjectionData
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem kernelProjection_observable_sub_norm_le (T : D.Niltest w) (U : D.Niltest v)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) {ε : ℝ}
    (hTU : ∀ x, ‖T.observable x - U.observable x‖ ≤ ε) :
    ∀ x, ‖(T.kernelProjection K hK).observable x - (U.kernelProjection K hK).observable x‖ ≤ ε := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  exact iteratedCircleAverage_sub_norm_le
    (fun i => D.centralRationalCircle (b i).val (hK (b i).property))
    (List.finRange (finrank ℚ K)) T.lipschitz U.lipschitz hTU

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier MeasureTheory
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_iteratedCentralCircle_translation (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (v : ι → K) (is : List ι)
    (t : CircleAverageTuple is) :
    let := D.metricSpace
    ∃ g : D.RealGroup, g.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅g.coord, y⁆ = 0) ∧
      ∀ x, iteratedCircleAction
        (fun i => D.centralRationalCircle (v i) (hK (v i).property)) is t x = g • x := by
  let := D.metricSpace
  induction is with
  | nil =>
    refine ⟨1, (K.baseChange ℝ).zero_mem, fun y => zero_lie y, ?_⟩
    intro x
    exact (one_smul D.RealGroup x).symm
  | cons i is ih =>
    obtain ⟨g, hg, hcentral, hact⟩ := ih t.2
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective t.1
    let z : D.RealGroup := realBCHLine (D.periodicRealDirection (v i)) r
    have hz : z.coord ∈ K.baseChange ℝ := by
      apply (K.baseChange ℝ).smul_mem r
      change (1 : ℝ) ⊗ₜ[ℚ] ((D.rationalDirectionPeriod (v i) : ℚ) • (v i : L)) ∈ _
      exact Submodule.tmul_mem_baseChange_of_mem 1 (K.smul_mem _ (v i).property)
    have hzc : ∀ y : ℝ ⊗[ℚ] L, ⁅z.coord, y⁆ = 0 := by
      intro y
      change ⁅r • D.periodicRealDirection (v i), y⁆ = 0
      rw [smul_lie, D.periodicRealDirection_central (v i) (hK (v i).property), smul_zero]
    have hcoord : (g * z).coord = g.coord + z.coord :=
      lieBCH_eq_add_of_lie_eq_zero D.filtration.realification.lowerCentralSeries_eq_bot
        (hcentral z.coord)
    refine ⟨g * z, ?_, ?_, ?_⟩
    · rw [hcoord]
      exact (K.baseChange ℝ).add_mem hg hz
    · intro y
      rw [hcoord, add_lie, hcentral, hzc, add_zero]
    · intro x
      change iteratedCircleAction _ is t.2
        ((D.centralRationalCircle (v i) (hK (v i).property)).act t.1 x) = _
      rw [hact, ← hr, D.centralRationalCircle_act_coe, mul_smul]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3
open Module CircleFourier
open scoped TensorProduct BigOperators Classical

attribute [instance] ExternalFamilyPrecenterProjectionData.instFintype

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MarkedKernelProjectionScoreRestoration
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {Ω Λ : Type*} [Fintype Ω] [MeasurableSpace Λ]

theorem exists_common_translation_retained_scores
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (μ : Measure Λ) [IsProbabilityMeasure μ]
    (f : Ω → Λ → ℝ) {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hf : ∀ a ∈ H, Measurable (f a))
    (hi : ∀ a ∈ H, Integrable (f a) μ)
    (hcap : ∀ a ∈ H, ∀ l, f a l ≤ B)
    (havg : ∀ a ∈ H, δ ≤ ∫ l, f a l ∂μ) :
    ∃ l, ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
      δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
      ∀ a ∈ H', δ / 2 ≤ f a l := by
  classical
  let E (a : Ω) : Set Λ := {l | δ / 2 ≤ f a l}
  let g (a : Ω) : Λ → ℝ := (E a).indicator (fun _ => 1)
  have hg : ∀ a ∈ H, Integrable (g a) μ := by
    intro a ha
    exact (integrable_const 1).indicator (measurableSet_le measurable_const (hf a ha))
  let m (l : Λ) : ℝ := ∑ a ∈ H, outer.weight a * g a l
  have hm : Integrable m μ :=
    integrable_finsetSum H (fun a ha => (hg a ha).const_mul (outer.weight a))
  have hmean : δ / (2 * B) * outer.mass H ≤ ∫ l, m l ∂μ := by
    dsimp only [m]
    rw [integral_finsetSum H (fun a ha => (hg a ha).const_mul (outer.weight a))]
    simp only [integral_const_mul, FiniteProbabilityWeights.mass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [mul_comm (δ / (2 * B))]
    exact mul_le_mul_of_nonneg_left
      (integral_threshold_indicator_lower μ hB hδ (hf a ha) (hi a ha)
        (hcap a ha) (havg a ha)) (outer.nonneg a)
  obtain ⟨l, hl⟩ := probabilityIntegralThresholdPoint μ hm hmean
  let H' := H.filter (fun a => δ / 2 ≤ f a l)
  have hmass : outer.mass H' = m l := by
    simp only [FiniteProbabilityWeights.mass, H', Finset.sum_filter, m, g, E,
      Set.indicator, Set.mem_ofPred_eq]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  refine ⟨l, H', Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · rw [hmass]
    exact (mul_pos (div_pos hδ (by positivity)) hH).trans_le hl
  · rwa [hmass]
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedDiagramOrbitLift
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (E : RationalFilteredNilmanifold M (s + 1) e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)

theorem topQuotientMarkedMap_basis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hQ : Q.GeometryComplexityLE p)
    (hproj : ∀ i j, rationalLogHeight (Q.basis.repr
      (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ p)
    (hmark : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p)
    (hprojF : ∀ i j, rationalLogHeight (QF.basis.repr
      (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ p)
    (i : Fin n) (j : Fin m) :
    rationalLogHeight (QF.basis.repr (D.topQuotientMarkedMap E φ hφ (Q.basis i)) j) ≤
      quotientInducedMapHeightBudget p := by
  exact lieQuotientProjection_basis_logHeight
    (D.filtration.layerIdeal (s + 1)) (E.filtration.layerIdeal (s + 1))
    D.basis E.basis Q.basis QF.basis φ (hφ (s + 1)) hp
    (by simpa only [Fintype.card_fin] using hD.1)
    (by simpa only [Fintype.card_fin] using hE.1)
    (by simpa only [Fintype.card_fin] using hQ.1)
    (fun i j => hproj j i) hmark (fun i j => hprojF j i) i j

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop)

include hQ hQF in

theorem topQuotientMarkedMap_layer_surjective
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (j : ℕ) (y : M ⧸ E.filtration.layerIdeal (s + 1)) (hy : y ∈ QF.filtration.layer j) :
    ∃ x ∈ Q.filtration.layer j, D.topQuotientMarkedMap E φ hφ x = y := by
  rw [hQF] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨x, hx, hφx⟩ := hsurj j z hz
  refine ⟨lieQuotientMap (D.filtration.layerIdeal (s + 1)) x, ?_, ?_⟩
  · rw [hQ]
    exact ⟨x, hx, rfl⟩
  · exact congrArg (lieQuotientMap (E.filtration.layerIdeal (s + 1))) hφx

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionComplementCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : Option ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [T2Space (ℝ ⊗[ℚ] (∀ i, L (some i)))]

theorem optionProductSpaceEquiv_symm_lipschitz :
    letI := (pi D).metricSpace
    letI := (D none).metricSpace
    letI := (pi (fun i => D (some i))).metricSpace
    LipschitzWith ((1 + productMetricBound (fun i => d (some i))) * productMetricBound d)
      (optionProductSpaceEquiv D).symm := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  let := (pi (fun i => D (some i))).metricSpace
  have hpair : LipschitzWith (1 + productMetricBound (fun i => d (some i)))
      (fun x : (D none).Space × (pi (fun i => D (some i))).Space =>
        (x.1, productSpaceEquiv (fun i => D (some i)) x.2)) := by
    have h := (LipschitzWith.prod_fst (α := (D none).Space)
      (β := (pi (fun i => D (some i))).Space)).prodMk
      ((productSpaceEquiv_lipschitz (fun i => D (some i))).comp
        (LipschitzWith.prod_snd (α := (D none).Space)))
    apply h.weaken
    simp only [mul_one]
    exact max_le (le_add_of_nonneg_right zero_le) (le_add_of_nonneg_left zero_le)
  have h := (productSpaceEquiv_symm_lipschitz D).comp
    ((optionPiIsometryEquiv (X := fun i => (D i).Space)).symm.isometry.lipschitz.comp hpair)
  have heq : ((optionProductSpaceEquiv D).symm : _ → (pi D).Space) =
      (fun x => (productSpaceEquiv D).symm
        ((optionPiIsometryEquiv (X := fun i => (D i).Space)).symm
          (x.1, productSpaceEquiv (fun i => D (some i)) x.2))) := rfl
  rw [heq]
  simpa only [one_mul, mul_comm, Function.comp_def] using h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (E : RationalFilteredNilmanifold L s d)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Unit → L))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Unit → L))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Unit → L))] [T2Space (ℝ ⊗[ℚ] (Unit → L))]

theorem singletonProductSpace_lipschitz :
    letI := E.metricSpace
    letI := (pi (fun _ : Unit => E)).metricSpace
    LipschitzWith (productMetricBound (fun _ : Unit => d)) E.singletonProductSpace := by
  let := E.metricSpace
  let : ∀ _ : Unit, MetricSpace E.Space := fun _ => E.metricSpace
  let := (pi (fun _ : Unit => E)).metricSpace
  have hconstant : LipschitzWith 1 (fun y : E.Space => fun _ : Unit => y) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    simp only [NNReal.coe_one, one_mul, le_refl]
  have h := (productSpaceEquiv_symm_lipschitz (fun _ : Unit => E)).comp hconstant
  rw [mul_one] at h
  exact h

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Unit → L))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Unit → L))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Unit → L))] [T2Space (ℝ ⊗[ℚ] (Unit → L))] in

theorem singletonProductSpace_realificationMap
    {H : Type*} [LieRing H] [LieAlgebra ℚ H] {r : ℕ}
    (F : NilpotentLieFiltration H r) (φ : H →ₗ⁅ℚ⁆ L)
    (x : F.realification.Group) :
    E.singletonProductSpace
        (QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) =
      QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi (fun _ : Unit => E)).filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun _ : Unit => φ)) x) := by
  apply (productSpaceEquiv (fun _ : Unit => E)).injective
  rw [singletonProductSpace, Equiv.apply_symm_apply]
  funext i
  rw [productSpaceEquiv_mk, productProjectionHom_realificationMap]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

def optionComplementMaps : ∀ j : {j : Option ι // j ≠ none},
    (∀ i, L i) →ₗ⁅ℚ⁆ optionLieSpace L₀ L j.val
  | ⟨none, h⟩ => False.elim (h rfl)
  | ⟨some i, _⟩ => liePiEval i

namespace RationalFilteredNilmanifold

variable [Fintype ι] [DecidableEq ι] {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def optionComplementFactors : ∀ j : {j : Option ι // j ≠ none},
    RationalFilteredNilmanifold (optionLieSpace L₀ L j.val) s (optionDimension d₀ d j.val) :=
  fun j => optionFactors D₀ D j.val

noncomputable def optionComplementOrbits {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w) :
    ∀ j, ((optionComplementFactors D₀ D) j).filtration.realification.PolynomialOrbit w
  | ⟨none, h⟩ => False.elim (h rfl)
  | ⟨some i, _⟩ => g i

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SplitCoverProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : Option ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (V : RationalFilteredNilmanifold (∀ i, L i) s (Fintype.card (Σ i, Fin (d i))))
  (hsub : (pi D).lattice ≤ V.lattice)

noncomputable def splitCoverProjection :
    (D none).Space × (pi (fun i => D (some i))).Space → V.Space :=
  sublatticeProjection V (pi D) hsub ∘ (optionProductSpaceEquiv D).symm

theorem splitCoverProjection_mk (x : (pi D).RealGroup) :
    splitCoverProjection D V hsub (optionProductSpaceEquiv D (QuotientGroup.mk x)) =
      QuotientGroup.mk x := by
  simp only [splitCoverProjection, Function.comp_apply, Equiv.symm_apply_apply,
    sublatticeProjection_mk]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FrozenComplexNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
  (φ : L →ₗ⁅ℚ⁆ M) (a r : E.RealGroup)
  (h : ∀ γ ∈ D.realLattice,
    r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)
  {w : σ → ℕ} (T : E.Niltest w) (g : D.filtration.realification.PolynomialOrbit w)
  (K : ℝ≥0)
  (hK : letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith K (frozenCosetMap D.realLattice E.realLattice
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h))

noncomputable def frozenComplexNiltest : D.Niltest w where
  orbit := g
  observable := T.observable ∘ frozenCosetMap D.realLattice E.realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ) a r h
  normBound := T.normBound
  lipBound := T.lipBound * K
  norm_le x := T.norm_le _
  lipschitz := by
    let := D.metricSpace
    let := E.metricSpace
    exact T.lipschitz.comp hK

theorem frozenComplexNiltest_eval (x : σ → ℤ) :
    (D.frozenComplexNiltest E φ a r h T g K hK).eval x =
      T.observable (QuotientGroup.mk
        (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          (D.filtration.realification.polynomialOrbitEval w x g) * r)) := rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearMapIntegralCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_native_integral_model_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ (B : ℕ) (Λ : Subgroup D.filtration.Group) (hB : 0 < B)
        (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ)
        (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B),
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ ≤ D.lattice ∧
        bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B ∧
        (D.withLattice Λ B hB hin hout).GeometryComplexityLE ((p + C) ^ C) := by
  obtain ⟨c, _, hcover⟩ := exists_integral_grid_subgroup_exp s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + 1 + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD
  have hp1 : p ≤ p + 1 := by linarith
  have hbud : p + (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcC : (p + 1 + c) ^ c ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by
    have hn : 0 ≤ (p + 1 + c) ^ c := by positivity
    linarith
  obtain ⟨B, Λ, hB, _, hBb, hΛ, hcoords⟩ :=
    hcover D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid ⌈Real.exp p⌉₊
      (p + 1) D.grid_pos
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) D.inner_grid
      (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans hp1)
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr hp1))
  have hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates D.basis Λ := hcoords.symm.le
  have hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid B := by
    rw [hcoords]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx
  have hBC : (B : ℝ) ≤ Real.exp ((p + C) ^ C) := hBb.trans (Real.exp_le_exp.mpr hcC)
  exact ⟨B, Λ, hB, hin, hout, hBC, hΛ, hcoords,
    D.withLattice_geometry Λ B hB hin hout hD hpC hBC⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeModelOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)
  (h : D.rationalModelCoordinates = E.rationalModelCoordinates)

theorem rationalModelEquiv_layer_succ (i : Fin (s + 1)) :
    (D.filtration.layer (i.val + 1)).map (D.rationalModelEquiv E h).toLinearEquiv.toLinearMap =
      E.filtration.layer (i.val + 1) := by
  rw [← D.paddedLayerVector_span i, ← E.paddedLayerVector_span i,
    Submodule.map_span, ← Set.range_comp]
  congr 2
  funext k
  exact D.rationalModelEquiv_paddedLayerVector E h i k

theorem rationalModelEquiv_layer (n : ℕ) :
    (D.filtration.layer n).map (D.rationalModelEquiv E h).toLinearEquiv.toLinearMap =
      E.filtration.layer n := by
  by_cases hn : n = 0
  · subst n
    have hD : D.filtration.layer 0 = ⊤ :=
      top_unique (D.filtration.one_eq_top ▸ D.filtration.antitone (by omega : 0 ≤ 1))
    have hE : E.filtration.layer 0 = ⊤ :=
      top_unique (E.filtration.one_eq_top ▸ E.filtration.antitone (by omega : 0 ≤ 1))
    rw [hD, hE]
    rw [Submodule.map_top]
    apply LinearMap.range_eq_top.mpr
    exact (D.rationalModelEquiv E h).surjective
  · by_cases hns : n ≤ s + 1
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        D.rationalModelEquiv_layer_succ E h ⟨n - 1, by omega⟩
    · have hD : D.filtration.layer n = ⊥ :=
        bot_unique ((D.filtration.antitone (by omega : s + 1 ≤ n)).trans D.filtration.terminal.le)
      have hE : E.filtration.layer n = ⊥ :=
        bot_unique ((E.filtration.antitone (by omega : s + 1 ≤ n)).trans E.filtration.terminal.le)
      rw [hD, hE, Submodule.map_bot]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)
  (h : D.rationalModelCoordinates = E.rationalModelCoordinates)

noncomputable def rationalModelGroupEquiv : D.filtration.Group ≃* E.filtration.Group :=
  { NilpotentLieBCHGroup.map (D.rationalModelEquiv E h).toLieHom with
    invFun := fun g => ⟨(D.rationalModelEquiv E h).symm g.coord⟩
    left_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact (D.rationalModelEquiv E h).symm_apply_apply g.coord
    right_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact (D.rationalModelEquiv E h).apply_symm_apply g.coord }

theorem rationalModelGroupEquiv_coordinates (g : D.filtration.Group) :
    E.basis.equivFun (D.rationalModelGroupEquiv E h g).coord = D.basis.equivFun g.coord := by
  funext k
  exact congrArg (fun v => v k) (D.rationalModelEquiv_repr E h g.coord)

theorem rationalModelGroupEquiv_mem_layer (n : ℕ) (g : D.filtration.Group) :
    D.rationalModelGroupEquiv E h g ∈ E.filtration.subgroup n ↔ g ∈ D.filtration.subgroup n := by
  change D.rationalModelEquiv E h g.coord ∈ E.filtration.layer n ↔ g.coord ∈ D.filtration.layer n
  rw [← D.rationalModelEquiv_layer E h n]
  constructor
  · rintro ⟨x, hx, heq⟩
    have hxg : x = g.coord := (D.rationalModelEquiv E h).injective heq
    change x ∈ D.filtration.layer n at hx
    exact hxg ▸ hx
  · intro hx
    exact ⟨g.coord, hx, rfl⟩

theorem rationalModelGroupEquiv_mem_integral_lattice
    (Λ : Subgroup D.filtration.Group) (Γ : Subgroup E.filtration.Group) (B : ℕ)
    (hΛ : bchSubgroupCoordinates D.basis Λ = scaledIntegerGrid B)
    (hΓ : bchSubgroupCoordinates E.basis Γ = scaledIntegerGrid B) (g : D.filtration.Group) :
    D.rationalModelGroupEquiv E h g ∈ Γ ↔ g ∈ Λ := by
  rw [← bchSubgroupCoordinates_repr E.basis Γ (D.rationalModelGroupEquiv E h g),
    ← bchSubgroupCoordinates_repr D.basis Λ g, hΛ, hΓ,
    rationalModelGroupEquiv_coordinates]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonRationalModelCoordinates
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_common_rational_model_power (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)] {d : ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s d) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (D h).GeometryComplexityLE p) →
      ∃ h₀ ∈ H, ∃ H' : Finset G, H' ⊆ H ∧ h₀ ∈ H' ∧
        (∀ h ∈ H', (D h).rationalModelCoordinates = (D h₀).rationalModelCoordinates) ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) := by
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (3 * (X ^ 3 + Polynomial.C (s + 1) * X ^ 2) * (X + 2))
  refine ⟨C, hC, ?_⟩
  intro G L _ _ d D H hH p hp hD
  obtain ⟨h₀, hh₀, H', hsub, hh₀', heq, hlarge⟩ :=
    exists_common_rational_model_coordinates D H hH hp hD
  have hd := (hD h₀ hh₀).1
  have hb : 3 * (d ^ 3 + (s + 1) * d ^ 2 : ℕ) * (p + 2) ≤ (p + C) ^ C := by
    have hb' : 3 * (p ^ 3 + (s + 1 : ℕ) * p ^ 2) * (p + 2) ≤ (p + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget p hp
    apply le_trans _ hb'
    push_cast
    gcongr
  exact ⟨h₀, hh₀, H', hsub, hh₀', heq,
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hb))
      (Nat.cast_nonneg _)).trans hlarge⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonIntegralModelEquivalences
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

theorem exists_common_integral_models (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)] {d : ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s d) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (D h).GeometryComplexityLE p) →
      ∃ (B : G → ℕ) (Λ : ∀ h, Subgroup (D h).filtration.Group)
        (hB : ∀ h, 0 < B h)
        (hin : ∀ h, scaledIntegerGrid (B h) ⊆ bchSubgroupCoordinates (D h).basis (Λ h))
        (hout : ∀ h, bchSubgroupCoordinates (D h).basis (Λ h) ⊆ denominatorGrid (B h)),
        (∀ h, (B h : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ Λ h ≤ (D h).lattice ∧
          bchSubgroupCoordinates (D h).basis (Λ h) = scaledIntegerGrid (B h) ∧
          ((D h).withLattice (Λ h) (B h) (hB h) (hin h) (hout h)).GeometryComplexityLE ((p + C) ^ C)) ∧
        ∃ h₀ ∈ H, ∃ H' : Finset G, H' ⊆ H ∧ h₀ ∈ H' ∧
          (∀ h ∈ H', B h = B h₀ ∧ (D h).rationalModelCoordinates = (D h₀).rationalModelCoordinates) ∧
          Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) := by
  classical
  obtain ⟨c, _, hcover⟩ := exists_native_integral_model_cover s
  obtain ⟨k, _, hmodel⟩ := exists_common_rational_model_power s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C c) ^ c + (X + Polynomial.C k) ^ k + X)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ d D H hH p hp hD
  let q := (p + c) ^ c
  let r := (p + k) ^ k
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hbud : q + r + p ≤ (p + C) ^ C := by
    simpa [q, r, X, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hqrC : q + r ≤ (p + C) ^ C := by linarith
  choose B Λ hB hin hout hBb hΛ hcoords hgeom using fun h => hcover (D h) hp (hD h)
  obtain ⟨h₁, _, H₁, hsub₁, hh₁, hcodes, hlarge₁⟩ :=
    hmodel D H hH hp (fun h _ => hD h)
  obtain ⟨h₀, hh₀, H', hsub₂, hh₀', hmoduli, hlarge₂⟩ :=
    exists_common_positive_nat H₁ ⟨h₁, hh₁⟩ B (p := q)
      (fun h _ => ⟨hB h, hBb h⟩)
  refine ⟨B, Λ, hB, hin, hout, ?_, h₀, hsub₁ hh₀, H', hsub₂.trans hsub₁, hh₀', ?_, ?_⟩
  · intro h
    exact ⟨(hBb h).trans (Real.exp_le_exp.mpr hqC), hΛ h, hcoords h,
      (hgeom h).mono _ hqC⟩
  · intro h hh
    exact ⟨hmoduli h hh, (hcodes h (hsub₂ hh)).trans (hcodes h₀ hh₀).symm⟩
  · calc
      Real.exp (-((p + C) ^ C)) * H.card ≤ Real.exp (-(q + r)) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqrC)) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-r) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H₁.card := mul_le_mul_of_nonneg_left hlarge₁ (Real.exp_pos _).le
      _ ≤ H'.card := hlarge₂

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedSubalgebraRepresentatives
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_native_subalgebra_rational_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ L : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (K : LieSubalgebra ℚ L)
      (bk : Basis κ ℚ K) (l H : ℕ) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      0 < l →
      scaledIntegerGrid l ⊆ bchSubgroupCoordinates bk
        (D.lattice.comap (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot
          D.filtration.lowerCentralSeries_eq_bot K) K.incl)) →
      (∀ i j k, RationalHeightLE (lieStructureConstants bk i j k) H) →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j, |(D.basis.repr (bk j : L) i : ℝ)| ≤ Real.exp p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup, g ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          ∃ r : D.RealGroup, r ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K ∧
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ := by
  obtain ⟨a, _, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hclosure⟩ := exists_real_bch_rational_closure s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a + 2 * X + (2 * X + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro κ L _ _ _ _ _ _ _ d D K bk l H p hp hD hκ hl hinner hc hH hlp hentries q hq hqp
  classical
  let t := 2 * p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let H0 := ⌈Real.exp p⌉₊
  have hH0 : (H0 : ℝ) ≤ Real.exp t := (ceil_exp_le_exp_add_one hp).trans
    (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ t by dsimp [t]; linarith)
  have hc0 : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H0 :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hprod : ((q * D.grid : ℕ) : ℝ) ≤ Real.exp t := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hqp hD.2.1 (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; linarith)
  obtain ⟨m, hm, hmb, _, hmul, _⟩ := hclosure D.basis H0 t
    D.filtration.lowerCentralSeries_eq_bot ht hd hH0 hc0 (q * D.grid)
    (Nat.mul_pos hq D.grid_pos) hprod
  have hsum : (p + a) ^ a + 2 * p + (t + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a + 2 * p ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (t + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (p + a) ^ a + 2 * p)).trans hsum
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hgK hg
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let hnilK := lie_subalgebra_lowerCentralSeries_eq_bot D.filtration.lowerCentralSeries_eq_bot K
  let f := realificationMap (hnil := hnilK) (hM := D.filtration.lowerCentralSeries_eq_bot) K.incl
  obtain ⟨gK, hgK⟩ := (show g ∈ f.range from by
    rwa [realificationMap_incl_range])
  obtain ⟨rK, hrK, γK, hγK, hfac⟩ := hrep bk hnilK
    (D.lattice.comap (map K.incl)) l H p hl hinner hc hp hκ hH hlp gK
  have hγ : f γK ∈ D.realLattice := by
    change γK ∈ D.realLattice.comap f
    dsimp only [realLattice, f]
    rw [realification_subgroup_comap_incl]
    exact hγK
  have heq : g = f rK * f γK := by rw [← hgK, hfac, map_mul]
  refine ⟨f rK, realificationMap_incl_mem K rK, ?_, ?_, f γK, hγ, heq⟩
  · intro i
    change |(D.basis.baseChange ℝ).repr (K.incl.toLinearMap.baseChange ℝ rK.coord) i| ≤ _
    rw [scalarExtension_coordinate_sum D.basis bk K.incl.toLinearMap rK.coord i]
    calc
      _ ≤ ∑ j, |(bk.baseChange ℝ).repr rK.coord j * (D.basis.repr (K.incl (bk j)) i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : κ, Real.exp ((p + a) ^ a) * Real.exp p := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hrK j) (hentries i j) (abs_nonneg _) (Real.exp_pos _).le
      _ = (Fintype.card κ : ℝ) * (Real.exp ((p + a) ^ a) * Real.exp p) := by simp
      _ ≤ Real.exp p * (Real.exp ((p + a) ^ a) * Real.exp p) := by
        exact mul_le_mul_of_nonneg_right (hκ.trans (by linarith [Real.add_one_le_exp p])) (by positivity)
      _ = Real.exp ((p + a) ^ a + 2 * p) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr haC
  · have hγgrid := realification_subgroup_grid D.basis D.lattice D.grid D.outer_grid
      (f γK)⁻¹ (D.realLattice.inv_mem hγ)
    have h := hmul g (f γK)⁻¹
      (realDenominatorGrid_subset_of_dvd hq (dvd_mul_right q D.grid) hg)
      (realDenominatorGrid_subset_of_dvd D.grid_pos (dvd_mul_left D.grid q) hγgrid)
    simpa only [heq, mul_inv_cancel_right] using h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_bounded_subalgebra_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ L : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (K : LieSubalgebra ℚ L)
      (bk : Basis κ ℚ K) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (bk j : L) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup,
          g ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          ∃ r : D.RealGroup,
            r ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot) K ∧
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ := by
  obtain ⟨a, _, hrep⟩ := exists_native_subalgebra_rational_representatives s
  let P : Polynomial ℕ := ((Polynomial.X + 3) ^ 12 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro κ L _ _ _ _ _ _ _ d D K bk p hp hD hκ hinc q hq hqp
  classical
  let H := ⌈Real.exp p⌉₊
  let p0 := p + 1
  let t := lieSubalgebraRepresentativeParameter p0
  have hp0 : 0 ≤ p0 := by dsimp [p0]; positivity
  have hpt : p ≤ t := (show p ≤ p0 by dsimp [p0]; linarith).trans
    (le_power_budget hp0 (by decide : 1 ≤ 12))
  have ht : 0 ≤ t := (lieSubalgebraRepresentativeParameter_pos hp0).le
  have hd0 : (Fintype.card (Fin d) : ℝ) ≤ p0 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p0 by dsimp [p0]; linarith)
  have hκ0 : (Fintype.card κ : ℝ) ≤ p0 := hκ.trans (by dsimp [p0]; linarith)
  have hH : (H : ℝ) ≤ Real.exp p0 := ceil_exp_le_exp_add_one hp
  have hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hincH : ∀ i j, RationalHeightLE (D.basis.repr (bk j : L) i) H :=
    fun i j => rationalHeightLE_ceil_exp (hinc i j)
  let HC := lieSubalgebraRepresentativeHeight (Fintype.card (Fin d)) (Fintype.card κ) H
  have hHC : (HC : ℝ) ≤ Real.exp t :=
    lieSubalgebraRepresentativeHeight_le_exp_parameter _ _ _ hp0 hd0 hκ0 hH
  have hcK : ∀ i j k, RationalHeightLE (lieStructureConstants bk i j k) HC :=
    lieSubalgebraRepresentative_bracket_height D.basis K bk (one_le_ceil_exp p) hc hincH
  let A : Matrix (Fin d) κ ℚ := fun i j => D.basis.repr (bk j : L) i
  let qI := matrixDenominator A
  have hqI : 0 < qI := matrixDenominator_pos A
  have hcolumns : ∀ j, D.basis.equivFun (bk j : L) ∈ denominatorGrid qI := by
    intro j
    refine ⟨fun i => clearedMatrix A i j, fun i => ?_⟩
    exact (congrFun (congrFun (clearedMatrix_cast A) i) j).symm
  have hqIb : (qI : ℝ) ≤ Real.exp ((p0 + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp0 1 hd0 hκ0
    intro i j
    exact ((Nat.cast_le.mpr (hincH i j).2).trans hH).trans
      (Real.exp_le_exp.mpr (le_power_budget hp0 (by decide : 1 ≤ 1)))
  have hlb : ((D.grid * qI : ℕ) : ℝ) ≤ Real.exp t := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p0 * Real.exp ((p0 + 2) ^ 3) :=
        mul_le_mul (hD.2.1.trans (Real.exp_le_exp.mpr (by dsimp [p0]; linarith)))
          hqIb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (p0 + (p0 + 2) ^ 3) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p0 + 2) ^ 4) := by
        apply Real.exp_le_exp.mpr
        have hpow := le_power_budget hp0 (by decide : 1 ≤ 3)
        have hnon : 0 ≤ (p0 + 2) ^ 3 := by positivity
        rw [pow_succ]
        nlinarith
      _ ≤ _ := Real.exp_le_exp.mpr
        (pow_le_pow_right₀ (by linarith : 1 ≤ p0 + 2) (by decide : 4 ≤ 12))
  have hinner := lieSubalgebra_comap_inner_grid_of_columns K bk D.basis D.lattice
    D.grid qI D.inner_grid hcolumns
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D K bk (D.grid * qI) HC t ht (GeometryComplexityLE.mono D hD hpt)
    (hκ.trans hpt) (Nat.mul_pos D.grid_pos hqI) hinner hcK hHC hlb
    (fun i j => ((hincH i j).abs_real_le.trans hH).trans
      (Real.exp_le_exp.mpr (le_power_budget hp0 (by decide : 1 ≤ 12))))
    q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  have hb : (t + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, t, lieSubalgebraRepresentativeParameter, p0, Polynomial.eval₂_pow, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num]
      using hbudget p hp
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hb), ?_⟩
  intro g hgK hg
  obtain ⟨r, hrK, hr, hrgrid, γ, hγ, hfac⟩ := hreps g hgK hg
  exact ⟨r, hrK, fun i => (hr i).trans (Real.exp_le_exp.mpr hb), hrgrid, γ, hγ, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeMarkedKernelRepresentatives
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)

theorem exists_topLayer_basis_logHeight (hs : 1 ≤ s) {p : ℝ}
    (hD : D.GeometryComplexityLE p) :
    ∃ r : ℕ, ∃ b : Basis (Fin r) ℚ ((D.filtration.layerIdeal s).toLieSubalgebra),
      ∀ a i, rationalLogHeight (D.basis.repr (b a : L) i) ≤ p := by
  obtain ⟨b, hb⟩ := D.exists_positive_layer_basis s hs hD
  exact ⟨finrank ℚ (D.filtration.layer s), b, hb⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

theorem exists_nativeTopMarkKernel_spanning_budget :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin e) ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ),
      1 ≤ s → 0 ≤ p → D.GeometryComplexityLE p → (e : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (b.repr (φ (D.basis j)) i) ≤ p) →
      ∃ vP : Fin d → L,
        Submodule.span ℚ (Set.range vP) =
          D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap ∧
        ∀ i j, rationalLogHeight (D.basis.repr (vP i) j) ≤ (p + 2) ^ C := by
  let P : Polynomial ℕ := ((((Polynomial.X + 3) ^ 7 + 4) ^ 2 + 2) ^ 63 + 3)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s d e D b φ p hs hp hD he hφ
  classical
  obtain ⟨r, btop, hbtop⟩ := D.exists_topLayer_basis_logHeight hs hD
  obtain ⟨rk, _, bk, hbk⟩ := exists_lie_kernel_subalgebra_basis_logHeight
    D.basis b φ hp (by simpa only [Fintype.card_fin] using he) hφ
  let q : ℝ := (p + 3) ^ 7
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ p + 3 by linarith)
      (show 1 ≤ (7 : ℕ) by decide)
    have h' : p + 3 ≤ q := by simpa only [pow_one] using h
    linarith
  have htop : ∀ a i, rationalLogHeight (D.basis.repr (btop a : L) i) ≤ q :=
    fun a i => (hbtop a i).trans hpq
  have hk : ∀ a i, rationalLogHeight (D.basis.repr (bk a : L) i) ≤ q :=
    fun a i => (rationalLogHeight_le_iff _ _).mpr (hbk a i)
  let U := (D.filtration.layerIdeal s).toLieSubalgebra
  let V := φ.ker.toLieSubalgebra
  obtain ⟨bP, hbP⟩ := exists_binary_intersection_basis_logHeight
    D.basis U V btop bk hq
    (by simpa only [Fintype.card_fin] using hD.1.trans hpq) htop hk
  let B : ℝ := ((q + 4) ^ 2 + 2) ^ 63 + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hspan := exists_bounded_ambient_spanning D.basis (U ⊓ V) bP bP.span_eq
    (one_le_ceil_exp B) (fun a i => rationalHeightLE_ceil_exp (hbP a i))
  obtain ⟨vP, hvP, hvPh⟩ := hspan
  let indexEquiv : Fin d ≃ Fin (Fintype.card (Fin d)) := finCongr (Fintype.card_fin d).symm
  refine ⟨fun i => vP (indexEquiv i), ?_, ?_⟩
  · have hrange : Set.range (fun i => vP (indexEquiv i)) = Set.range vP := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨indexEquiv i, rfl⟩
      · rintro ⟨i, rfl⟩
        obtain ⟨j, rfl⟩ := indexEquiv.surjective i
        exact ⟨j, rfl⟩
    rw [hrange]
    exact hvP
  intro a i
  have hheight : rationalLogHeight (D.basis.repr (vP (indexEquiv a)) i) ≤ B + 1 :=
    rationalLogHeight_le_of_height (hvPh (indexEquiv a) i) (ceil_exp_le_exp_add_one hB)
  apply hheight.trans
  simpa [P, q, B, Polynomial.eval₂_pow, add_assoc,
    show (2 : ℝ) + 1 = 3 by norm_num] using hbudget p hp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_marked_kernel_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ L M : Type*} [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d)
      (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup,
          g ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
            φ.ker.toLieSubalgebra →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          ∃ r : D.RealGroup,
            r ∈ realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
              φ.ker.toLieSubalgebra ∧
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ := by
  obtain ⟨a, _, hrep⟩ := exists_native_bounded_subalgebra_representatives s
  let P : Polynomial ℕ := ((Polynomial.X + 3) ^ 7 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro κ L M _ _ _ _ _ _ _ _ _ d D c φ p hp hD hκ hφ q hq hqp
  obtain ⟨n, hn, bk, hbk⟩ :=
    exists_lie_kernel_subalgebra_basis_logHeight D.basis c φ hp hκ hφ
  let t := (p + 3) ^ 7
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    exact (le_power_budget hp (by decide : 1 ≤ 7)).trans
      (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2) (by linarith : p + 2 ≤ p + 3) 7)
  have hn' : (Fintype.card (Fin n) : ℝ) ≤ t := by
    have hnd : n ≤ d := by simpa only [Fintype.card_fin] using hn
    simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hnd).trans (hD.1.trans hpt)
  have hinc : ∀ i j, rationalLogHeight (D.basis.repr (bk j : L) i) ≤ t :=
    fun i j => (rationalLogHeight_le_iff _ t).mpr (hbk j i)
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D φ.ker.toLieSubalgebra bk t ht
    (GeometryComplexityLE.mono D hD hpt)
    hn' hinc q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  have hb : (t + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hb), ?_⟩
  intro g hgK hg
  obtain ⟨r, hrK, hr, hrgrid, γ, hγ, hfac⟩ := hreps g hgK hg
  exact ⟨r, hrK, fun i => (hr i).trans (Real.exp_le_exp.mpr hb), hrgrid, γ, hγ, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSquareRecovery
namespace OAI

section

namespace Erdos3

open Module

theorem bchSubgroup_inner_grid_of_reindex {ι κ L : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (b : Basis ι ℚ L) (e : ι ≃ κ) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) {N : ℕ}
    (h : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (b.reindex e) Γ) :
    scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ := by
  have hb : (b.reindex e).reindex e.symm = b := by
    ext i
    simp only [Basis.reindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  have h' := bchSubgroup_inner_grid_reindex (b.reindex e) e.symm Γ h
  rwa [hb] at h'

namespace RationalFilteredNilmanifold

theorem exists_native_factorwise_covers :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (Λ : Subgroup (pi D).filtration.Group) (m : ℕ), 0 < m →
      (scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi D).basis Λ) →
      ∀ {p : ℝ}, 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (m : ℝ) ≤ Real.exp p →
      ∃ (Δ : ∀ i, Subgroup (D i).filtration.Group) (N : ι → ℕ)
        (hN : ∀ i, 0 < N i)
        (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i))
        (hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i)),
        let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
        (∀ i, Δ i ≤ (D i).lattice ∧ ((Δ i).subgroupOf (D i).lattice).Characteristic ∧
          ((Δ i).subgroupOf (D i).lattice).Normal ∧ ((Δ i).subgroupOf (D i).lattice).FiniteIndex ∧
          ((Δ i).relIndex (D i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
        (pi E).GeometryComplexityLE ((p + C) ^ C) ∧ (pi E).lattice ≤ Λ := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + 2) ^ 2
  let P := 2 * X ^ 2 + Q + (Q + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ s d D Λ m hm hΛ p hp hι hD hmp
  have hraw : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis (fun i => (D i).basis)) Λ :=
    bchSubgroup_inner_grid_of_reindex _ (Fintype.equivFin _) Λ hΛ
  obtain ⟨Δ, N, hdata, hsubset⟩ := exists_factorwise_bch_covers
    (fun i => (D i).filtration) (fun i => (D i).basis) (fun i => (D i).lattice)
    (fun i => (D i).grid) (fun i => (D i).grid_pos) (fun i => (D i).inner_grid)
    (fun i => (D i).outer_grid) Λ m hm hraw hp
    (fun i => by simpa only [Fintype.card_fin] using (hD i).1) (fun i => (hD i).2.1) hmp
  have hN : ∀ i, 0 < N i := fun i => by rcases hdata i with ⟨_, _, _, _, _, h, _, _, _⟩; exact h
  have hNb : ∀ i, (N i : ℝ) ≤ Real.exp ((p + 2) ^ 2) :=
    fun i => by rcases hdata i with ⟨_, _, _, _, _, _, h, _, _⟩; exact h
  have hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i) :=
    fun i => by rcases hdata i with ⟨_, _, _, _, _, _, _, h, _⟩; exact h
  have hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i) :=
    fun i => by rcases hdata i with ⟨_, _, _, _, _, _, _, _, h⟩; exact h
  let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  have hpq : p ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  have hE : ∀ i, (E i).GeometryComplexityLE ((p + 2) ^ 2) := fun i =>
    (D i).withLattice_geometry (Δ i) (N i) (hN i) (hin i) (hout i) (hD i) hpq (hNb i)
  have hprod := pi_geometry E (sq_nonneg (p + 2)) (hι.trans hpq) hE
  have hsum : 2 * p ^ 2 + (p + 2) ^ 2 + ((p + 2) ^ 2 + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, Q, X, Polynomial.eval₂_pow] using hbudget p hp
  have hidx : 2 * p ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (p + 2), sq_nonneg ((p + 2) ^ 2 + 2)]
  have hgeom : (p + 2) ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg p, sq_nonneg ((p + 2) ^ 2 + 2)]
  have hprodgeom : ((p + 2) ^ 2 + 2) ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg p, sq_nonneg (p + 2)]
  refine ⟨Δ, N, hN, hin, hout, ?_, fun i => (hE i).mono (E i) hgeom,
    hprod.mono (pi E) hprodgeom, hsubset⟩
  intro i
  rcases hdata i with ⟨hle, hchar, hnormal, hfinite, hindex, _, _, _, _⟩
  exact ⟨hle, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hidx)⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedMarkedDictionaryRecovery
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)

noncomputable def loweredCoverMap :
    (D.loweredCover hst Λ N hN hin hout).Space →
      ((D.raiseStep hst).withLattice Λ N hN hin hout).Space :=
  cosetMap (D.loweredCover hst Λ N hN hin hout).realLattice
    ((D.raiseStep hst).withLattice Λ N hN hin hout).realLattice
    (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L))
    (realificationMap_subgroup (LieHom.id : L →ₗ⁅ℚ⁆ L) (D.lowerCoverLattice hst Λ) Λ
      (D.lowerCoverLattice_forward hst Λ))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L Z : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)
  (v : ((D.raiseStep hst).withLattice Λ N hN hin hout).Space × Z → ℂ)

noncomputable def loweredCoverPullback : (D.loweredCover hst Λ N hN hin hout).Space × Z → ℂ :=
  fun y => v (D.loweredCoverMap hst Λ N hN hin hout y.1, y.2)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledSingleRefilteredReconstruction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e n : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def SingleRefilteredRecoveryFamily (p : ℝ) (q k : ℕ) (cost : ℝ) : Prop :=
  let H := D.filtration.gradedRefiltrationSubalgebra W
  let N := H ⧸ E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  let := realification_moduleTopology_t2 Q.basis
  let T := Q.raiseStep (Nat.le_succ s)
  ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
    (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
    (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
    ∃ (B : ℕ) (hB : 0 < B)
      (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates Q.basis Λ)
      (hout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid B),
      let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
      V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧
      V.GeometryComplexityLE cost ∧
      ∀ l r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
        ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
          (let := D.metricSpace; LipschitzWith ℓ S) →
          (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
          (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W (s + 1) →
            ∀ x, S (z • x) = S x) →
          ∃ (v : V.Space → ℂ) (K : ℝ≥0),
            (K : ℝ) ≤ Real.exp cost ∧ (let := V.metricSpace; LipschitzWith K v) ∧
            (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
            ∀ x : E.RealGroup,
              v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := V.filtration.lowerCentralSeries_eq_bot)
                (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x)) =
              S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := D.filtration.lowerCentralSeries_eq_bot) H.incl x * r))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedRefilteredLowerNativeDiagram
namespace OAI


namespace Erdos3

open Module

variable {L M ι κ α β : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] [Fintype ι] [Fintype κ] [Fintype β]

theorem restrictedLieMap_coordinate_logHeight
    (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (U : LieSubalgebra ℚ L) (V : LieSubalgebra ℚ M)
    (b : Basis α ℚ U) (c : Basis β ℚ V)
    (φ : L →ₗ⁅ℚ⁆ M) (hUV : ∀ x ∈ U, φ x ∈ V)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hβ : (Fintype.card β : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (f.repr (φ (e i)) j) ≤ p)
    (hb : ∀ i j, rationalLogHeight (e.repr (b i : L) j) ≤ p)
    (hc : ∀ i j, rationalLogHeight (f.repr (c i : M) j) ≤ p)
    (i : α) (j : β) :
    rationalLogHeight (c.repr ⟨φ (b i), hUV _ (b i).property⟩ j) ≤
      ((p + 2) ^ 4 + p + 4) ^ 8 := by
  let q := (p + 2) ^ 4 + p + 1
  have hp4 : 0 ≤ (p + 2) ^ 4 := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hp4q : (p + 2) ^ 4 ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have himage (k : κ) : rationalLogHeight (f.repr (φ (b i)) k) ≤ q :=
    (linearMap_coordinate_logHeight e f φ.toLinearMap hp hι hφ (b i) (hb i) k).trans hp4q
  let x : V := ⟨φ (b i), hUV _ (b i).property⟩
  apply rationalLogHeight_le_of_height
    (embedding_basis_coordinate_height c f V.incl.toLinearMap
      (fun _ _ h => Subtype.ext h) (one_le_ceil_exp q)
      (fun k l => rationalHeightLE_ceil_exp ((hc l k).trans hpq)) x
      (fun k => rationalHeightLE_ceil_exp (himage k)) j)
  have hraw := embedding_coordinate_height_budget (Fintype.card κ) (Fintype.card β)
    ⌈Real.exp q⌉₊ ⌈Real.exp q⌉₊ (show 0 ≤ q + 1 by linarith)
    (hκ.trans (hpq.trans (by linarith))) (hβ.trans (hpq.trans (by linarith)))
    (ceil_exp_le_exp_add_one hq) (ceil_exp_le_exp_add_one hq)
  convert hraw using 1
  dsimp [q]
  congr 2
  ring

end Erdos3


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

universe u

def MarkedRefilteredNativeDiagramData
    {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (P : ℝ) : Prop :=
      let V := W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)
      let mark := D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE (P) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (E.basis j : L) i) ≤ P) ∧
        ∃ EF : RationalFilteredNilmanifold (Fmark.filtration.gradedRefiltrationSubalgebra V) (s + 1)
            (finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra V)),
          EF.filtration = Fmark.filtration.gradedRefiltration V ∧
          EF.lattice = Fmark.lattice.comap
            (NilpotentLieBCHGroup.map
              (hnil := (Fmark.filtration.gradedRefiltration V).lowerCentralSeries_eq_bot)
              (Fmark.filtration.gradedRefiltrationSubalgebra V).incl) ∧
          EF.GeometryComplexityLE (P) ∧
          (∀ i j, rationalLogHeight (Fmark.basis.repr (EF.basis j : M) i) ≤ P) ∧
          (∀ i j, rationalLogHeight (EF.basis.repr (mark (E.basis i)) j) ≤ P) ∧
          (∀ j, ∀ x ∈ E.filtration.layer j, mark x ∈ EF.filtration.layer j) ∧
          (∀ j, ∀ y ∈ EF.filtration.layer j, ∃ x ∈ E.filtration.layer j, mark x = y) ∧
          (∃ m : ℕ, m ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W) ∧
            ∃ Q : RationalFilteredNilmanifold
                ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s m,
              Q.filtration = E.filtration.quotientTop ∧
              Q.lattice = E.lattice.map
                (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
              Q.GeometryComplexityLE (P) ∧
              ∀ i j, rationalLogHeight (Q.basis.repr
                (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ P) ∧
          (∃ m : ℕ, m ≤ finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra V) ∧
            ∃ QF : RationalFilteredNilmanifold
                ((Fmark.filtration.gradedRefiltrationSubalgebra V) ⧸ EF.filtration.layerIdeal (s + 1)) s m,
              QF.filtration = EF.filtration.quotientTop ∧
              QF.lattice = EF.lattice.map
                (EF.filtration.quotientStepHom (EF.filtration.layerIdeal (s + 1)) le_rfl) ∧
              QF.GeometryComplexityLE (P) ∧
              ∀ i j, rationalLogHeight (QF.basis.repr
                (lieQuotientMap (EF.filtration.layerIdeal (s + 1)) (EF.basis j)) i) ≤ P)

end Erdos3.RationalFilteredNilmanifold


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedSquareImagePartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

def PrescribedSquareImagePartitionSpec (s t k₀ a C : ℕ) : Prop :=
    ∀ {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d dV dQ : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      (V : RationalFilteredNilmanifold D.filtration.squareLieSubalgebra s dV)
      (Q : RationalFilteredNilmanifold M t dQ)
      (φ : D.filtration.squareLieSubalgebra →ₗ⁅ℚ⁆ M)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (c : ℤ) (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      1 ≤ s → 2 ≤ p → D.GeometryComplexityLE p → V.GeometryComplexityLE p →
      Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
        (D.filtration.squarePairMap (V.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (φ (V.basis j)) i) ≤ p) →
      (q : ℝ) ≤ Real.exp p → 0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 1 / δ ≤ Real.exp ((p + C) ^ C) ∧
        ∃ n k : ℕ, 0 < n ∧ 0 < k ∧
          (Fintype.card ((Fin n × ZMod q) × Fin k) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : ((Fin n × ZMod q) × Fin k) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
            (∀ j x y, 0 < A j x → 0 < A j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ δ) ∧
            (∀ h : ZMod N, ((cyclicWrapExceptional h δ).card : ℝ) / N ≤ 6 * δ + 3 / N) ∧
            letI := Q.metricSpace
            let ψ := realificationMap (hnil := D.filtration.squareFiltration.lowerCentralSeries_eq_bot)
              (hM := Q.filtration.lowerCentralSeries_eq_bot) φ
            ∀ (h : ZMod N) (branch : Fin 2) (η γ : D.RealGroup)
              (rSq : D.filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
                γ ∈ D.realLattice →
                (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp ((p + 2) ^ k₀)) →
                (∀ z : Unit → ℤ,
                  D.filtration.realSquareFstHom
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) z rSq) =
                      η⁻¹ * D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (z + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) g * γ⁻¹ ∧
                  D.filtration.realSquareSndHom
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) z rSq) =
                      D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (z + fun _ => c) g) →
                ∀ i j x y,
                  x ∉ cyclicWrapExceptional h δ → y ∉ cyclicWrapExceptional h δ →
                  0 < A i x * A j (x + h) → 0 < A i y * A j (y + h) →
                  dist (QuotientGroup.mk (ψ
                      (D.filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) rSq)) : Q.Space)
                    (QuotientGroup.mk (ψ
                      (D.filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) rSq))) ≤ ε

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedCoveredInputPartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def PrescribedCoveredInputPartitionSpec (s k₀ a C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ (Λ : ∀ i, Subgroup (Q i).filtration.Group) (_hΛ : ∀ i, Λ i ≤ (Q i).lattice)
        (l : ι → ℕ) (hl : ∀ i, 0 < l i)
        (hlin : ∀ i, scaledIntegerGrid (l i) ⊆ bchSubgroupCoordinates (Q i).basis (Λ i))
        (hlout : ∀ i, bchSubgroupCoordinates (Q i).basis (Λ i) ⊆ denominatorGrid (l i)),
      let Q' := fun i => (Q i).withLattice (Λ i) (l i) (hl i) (hlin i) (hlout i)
      ∀ (E : ∀ j, RationalFilteredNilmanifold (K j) s (e j))
        (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (c : ι → ℤ)
        (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i, (Q' i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      let Z := sumFactors E Q'
      let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1))
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := realification_moduleTopology_t2 (pi Z).basis
      letI := (pi Z).metricSpace
      ∃ (I : Type) (inst : Fintype I), letI := inst;
        (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (A : I → ZMod N → ℝ) (label : I → ZMod q),
          (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = label j) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
          ∀ (h : ZMod N) (branch : ι → Fin 2) (η γ : ∀ i, (D i).RealGroup)
            (rSq : ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
            (qSq : ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ i, γ i ∈ (D i).realLattice) →
            (∀ i b, |((D i).basis.baseChange ℝ).repr (η i).coord b| ≤ Real.exp ((p + 2) ^ k₀)) →
            (∀ i (z : Unit → ℤ),
              (D i).filtration.realSquareFstHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (η i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) (g₀ i) * (γ i)⁻¹ ∧
              (D i).filtration.realSquareSndHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => c i) (g₀ i)) →
            (∀ i, qSq i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
              ((D i).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq i)) →
            let G := piRealOrbit (fun i => (Z i).filtration) (sumOrbits E Q' g qSq)
            ∀ j b x y,
              x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
              0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
              dist ((pi Z).cyclicOrbitPoint G N (fun _ : Unit => x))
                ((pi Z).cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                  Real.exp ((2 * p + 4) ^ 4) * ε

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedComplementInputPartition
namespace OAI


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def PrescribedAmbientInputPartitionSpec (s k₀ a B C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) s (e j),
      let Z := sumFactors E Q
      ∀ (Γ : Subgroup (pi Z).filtration.Group) (mΓ : ℕ) (hmΓ : 0 < mΓ)
        (hinΓ : scaledIntegerGrid mΓ ⊆ bchSubgroupCoordinates (pi Z).basis Γ)
        (houtΓ : bchSubgroupCoordinates (pi Z).basis Γ ⊆ denominatorGrid mΓ),
      let W := (pi Z).withLattice Γ mΓ hmΓ hinΓ houtΓ
      let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1))
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := realification_moduleTopology_t2 (pi Z).basis
      letI := W.metricSpace
      ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (c : ι → ℤ)
        (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → (mΓ : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ (I : Type) (inst : Fintype I), letI := inst;
        (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (A : I → ZMod N → ℝ) (label : I → ZMod q),
          (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = label j) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
          ∀ (h : ZMod N) (branch : ι → Fin 2) (η γ : ∀ i, (D i).RealGroup)
            (rSq : ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
            (qSq : ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ i, γ i ∈ (D i).realLattice) →
            (∀ i b, |((D i).basis.baseChange ℝ).repr (η i).coord b| ≤ Real.exp ((p + 2) ^ k₀)) →
            (∀ i (z : Unit → ℤ),
              (D i).filtration.realSquareFstHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (η i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) (g₀ i) * (γ i)⁻¹ ∧
              (D i).filtration.realSquareSndHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => c i) (g₀ i)) →
            (∀ i, qSq i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
              ((D i).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq i)) →
            let G := piRealOrbit (fun i => (Z i).filtration) (sumOrbits E Q g qSq)
            ∀ j b x y,
              x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
              0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
              dist (W.cyclicOrbitPoint G N (fun _ : Unit => x))
                (W.cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                  Real.exp ((p + B) ^ B) * ε

end Erdos3.RationalFilteredNilmanifold


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionalStepDrop
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra U) s e)
  (hEF : E.filtration = D.filtration.gradedRefiltration U)
  (u : D.Space → ℂ)
  (hu : ∀ z : D.RealGroup,
    z.coord ∈ D.filtration.realGradedRefiltrationLayer U s → ∀ x, u (z • x) = u x)

include hEF hu in
theorem frozen_refiltered_top_invariant (a r : D.RealGroup)
    (z : E.RealGroup) (hz : z ∈ E.filtration.realification.subgroup s) (x : E.RealGroup) :
    u (QuotientGroup.mk (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl (z * x) * r)) =
    u (QuotientGroup.mk (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra U).incl x * r)) := by
  let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot)
    (D.filtration.gradedRefiltrationSubalgebra U).incl
  have hz' : (φ z).coord ∈ D.filtration.realGradedRefiltrationLayer U s := by
    apply (D.filtration.mem_native_refiltration_layer U s z.coord).mp
    have h : z.coord ∈ E.filtration.realification.layer s := hz
    simpa only [hEF] using h
  have hcomm := D.filtration.realification.top_commutes (φ z)
    (D.filtration.realGradedRefiltrationLayer_le U s hz') a
  have heq : a * φ (z * x) * r = φ z * (a * φ x * r) := by
    calc
      a * φ (z * x) * r = (a * φ z) * φ x * r := by simp only [map_mul, mul_assoc]
      _ = (φ z * a) * φ x * r := by rw [← hcomm.eq]
      _ = φ z * (a * φ x * r) := by simp only [mul_assoc]
  change u (QuotientGroup.mk (a * φ (z * x) * r)) = _
  rw [heq]
  exact hu (φ z) hz' (QuotientGroup.mk (a * φ x * r))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

noncomputable def FixedResidueDescent {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (V : RationalFilteredNilmanifold K t e) (w : σ → ℕ)
    (b : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (child : V.filtration.realification.PolynomialOrbit w)
    (p : ℝ) (q P : ℕ) (hP : 0 < P) (C a : ℕ) (cost : ℝ) : Prop :=
  ∀ S : D.Niltest w, S.ComplexityLE p → S.UnitIntervalValued →
    (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W s →
      ∀ x, S.observable (z • x) = S.observable x) →
    ∀ (E R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
      (κ : D.RealGroup), κ ∈ D.realLattice →
      E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
        ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
      D.filtration.PolynomialRationalGrid D.basis w q R →
      ∀ A : σ → ℝ, (∀ i, 0 < A i) →
        D.filtration.PolynomialSlowBound D.basis w A (Real.exp ((p + 2) ^ a)) E →
        ∀ (M : ℕ) (hM : 0 < M) (lo : σ → ℤ) (N H : σ → ℕ)
          (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (u v : σ → ℤ) (J : σ → ℕ),
          (∀ i, 0 < J i) → ∀ (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]),
          (∀ i, (M * (M * P)).Coprime (J i)) →
          ∀ (δ ε : ℝ), 0 ≤ δ → ε < 1 / 2 →
          (∀ i, 2 * (H i : ℝ) ≤ (M : ℝ) * A i * δ) →
          (∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (lo i : ℝ) ∧
            (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i) →
          (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (H i : ℝ)) ≤ ε →
          let Q := comparableBoxPartitions N H hH hHN
          let c₀ := baseAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P)
            (fun _ => Nat.mul_pos hM hP) u
          let c₁ := refinedAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P) J
            (fun _ => Nat.mul_pos hM hP) u v hv
          let F : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u → ℂ :=
            residueBoxStrideValue S.eval u M
          let G : IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v → ℂ :=
            residueBoxStrideValue S.eval u M
          ∃ k : AuxiliaryBoxLabels Q (fun _ => M) (fun _ => M * P) u,
            0 < (partitionCell c₀ k).card ∧ 0 < (partitionCell c₁ k).card ∧
            ∃ U : V.Niltest w, U.orbit = child ∧ U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
              ‖(𝔼 x, F x) - (𝔼 x, G x)‖ - 8 * ε - 2 * (Real.exp ((p + 2) ^ C) * δ) ≤
                ‖(𝔼 x ∈ partitionCell c₀ k, residueBoxStrideValue U.eval u M x) -
                  (𝔼 x ∈ partitionCell c₁ k, residueBoxStrideValue U.eval u M x)‖

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def primeCoordinateReference {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] : ∀ i, FiniteProbabilityWeights (σ → ZMod (q i)) :=
  fun i => FiniteProbabilityWeights.uniform (σ → ZMod (q i))

end Erdos3

end

end OAI
end


