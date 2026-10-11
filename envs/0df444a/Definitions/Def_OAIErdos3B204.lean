-- Prove2me | Definitions.Def_OAIErdos3B204
-- name    : OAIErdos3B204
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T14:56:37.537982+00:00
-- url     : https://prove2.me/theorems/0d982860-4c67-47c4-aec1-3b6172815b3a
-- title:
--   OpenAI Erdős-3 split, definitions bundle 205 of 207
-- statement:
--   Definitions bundle 205 of 207 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B203`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 205 available.
--
--   Modules: `OAI.Erdos3.LocalMajorSliceTest.expect_freezeShort`, `OAI.Erdos3.LocalMajorSliceTest.freezeShort`, `OAI.Erdos3.LocalMajorSliceTest.freezeShort_weight`, `OAI.Erdos3.LocalMajorSliceTest.full`, `OAI.Erdos3.LocalMajorSliceTest.mono`, `OAI.Erdos3.LocalMajorSliceTest.mono_weight`, `OAI.Erdos3.LocalMajorSliceTest.rec`, `OAI.Erdos3.LocalMajorSliceTest.weight`, `OAI.Erdos3.LocalMajorSliceTest.weight_norm`, `OAI.Erdos3.NativeMixedCorrelation.exists_degree_one_cube_residuals`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_antisymmetric_anchor_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_diagonal_niltest`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_primitive_niltest_budget`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_separated_family`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_quadratic_primitive_niltest_budget`, `OAI.Erdos3.NativeMultidegreeNilcharacter.pairComponent`, `OAI.Erdos3.NativeMultidegreeNilcharacter.pairComponent_eval`, `OAI.Erdos3.NativeMultidegreeNilcharacter.pairComponent_vertical`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_common_local_marked_family`, `OAI.Erdos3.NativeSampleCorrelation.AntisymmetricPairAlgebra`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairBudget_four_le`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairFrequencies`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairModels`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairNiltest`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairNiltest_bias`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairNiltest_complexity`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairNiltest_eval`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairNiltest_vertical`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairTests`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairTests_complexity`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairTests_eval`, `OAI.Erdos3.NativeSampleCorrelation.antisymmetricPairTests_vertical`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairNiltest`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairNiltest_bias`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairNiltest_complexity`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairNiltest_eval`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairNiltest_vertical`, `OAI.Erdos3.NativeSampleCorrelation.pairCoordinateNiltest`, `OAI.Erdos3.NativeSampleCorrelation.pairCoordinateNiltest_complexity`, `OAI.Erdos3.NativeSampleCorrelation.pairCoordinateNiltest_observable`, `OAI.Erdos3.NativeSampleCorrelation.pairCoordinateTests`, `OAI.Erdos3.NativeSampleCorrelation.pairCoordinateTests_complexity`, `OAI.Erdos3.NativeSampleModel.mono`, `OAI.Erdos3.OrdinaryPolynomialPhase.zeroLocalMajorSlice`, `OAI.Erdos3.PositiveShiftBasis.testingNiltest`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.eval_liftLong`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.liftLong`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.liftLong_complexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.liftLong_normBound`, `OAI.Erdos3.ResidueBoxSlice.expect_freezeShort`, `OAI.Erdos3.ResidueBoxSlice.freezeShort`, `OAI.Erdos3.ResidueBoxSlice.freezeShort_commonStrideIndex`, `OAI.Erdos3.ResidueBoxSlice.freezeShort_dense`, `OAI.Erdos3.ResidueBoxSlice.freezeShort_integerPoints`, `OAI.Erdos3.UniversalLocalMajorSliceTest.default`, `OAI.Erdos3.UniversalLocalMajorSliceTest.freezeShort`, `OAI.Erdos3.UniversalLocalMajorSliceTest.freezeShort_slice`, `OAI.Erdos3.UniversalLocalMajorSliceTest.freezeShort_stride`, `OAI.Erdos3.UniversalLocalMajorSliceTest.freezeShort_weight`, `OAI.Erdos3.UniversalLocalMajorSliceTest.nativeModel`, `OAI.Erdos3.UniversalLocalMajorSliceTest.nonempty`, `OAI.Erdos3.UniversalLocalMajorSliceTest.ofLocalMajorSliceTest`, `OAI.Erdos3.UniversalLocalMajorSliceTest.ofLocalMajorSliceTest_slice`, `OAI.Erdos3.UniversalLocalMajorSliceTest.ofLocalMajorSliceTest_weight`, `OAI.Erdos3.UniversalLocalMajorSliceTest.recOn`, `OAI.Erdos3.UniversalLocalMajorSliceTest.toLocalMajorSliceTest`, `OAI.Erdos3.UniversalLocalMajorSliceTest.toLocalMajorSliceTest_slice`, `OAI.Erdos3.UniversalLocalMajorSliceTest.toLocalMajorSliceTest_weight`, `OAI.Erdos3.UniversalLocalMajorSliceTest.value_eq_native_eval`, `OAI.Erdos3.UniversalLocalMajorSliceTest.weight`, `OAI.Erdos3.UniversalLocalMajorSliceTest.weight_eq_native_eval`, `OAI.Erdos3.UniversalLocalMajorSliceTest.weight_norm`, `OAI.Erdos3.VectorPolynomial.normalizedNativeSampleFunctions_mono`, `OAI.Erdos3.affineBasisCoefficient`, `OAI.Erdos3.affineBasisCoefficient_mem`, `OAI.Erdos3.affineBasisConstant`, `OAI.Erdos3.affineBasisConstant_mem`, `OAI.Erdos3.affine_basis_change`, `OAI.Erdos3.affine_basis_coordinate_sum`, `OAI.Erdos3.antisymmetricPairBudget`, `OAI.Erdos3.exists_antisymmetric_pair_correlation`, `OAI.Erdos3.exists_correlated_corner`, `OAI.Erdos3.exists_fourier_of_stepOne_cross_correlation`, `OAI.Erdos3.exists_local_affine_polynomial_family`, `OAI.Erdos3.exists_local_affine_scalar_chart`, `OAI.Erdos3.exists_phase_aligned_derivatives`, `OAI.Erdos3.exists_productive_localMajorSlice_coordinate_family`, `OAI.Erdos3.exists_quadratic_local_frequency`, `OAI.Erdos3.exists_reflected_corner_correlation`, `OAI.Erdos3.exists_stepOne_row_phase_budget`, `OAI.Erdos3.exists_stepOne_scalar_phase_budget`, `OAI.Erdos3.frozenLongExtension`, `OAI.Erdos3.frozenLongExtension_injective`, `OAI.Erdos3.frozenLongExtension_long`, `OAI.Erdos3.frozenLongExtension_shortStarts`, `OAI.Erdos3.frozenShortStarts`, `OAI.Erdos3.frozenShortStarts_inside`, `OAI.Erdos3.longCoordinateProjection`, `OAI.Erdos3.nativeMixedCubeResidual`, `OAI.Erdos3.nativeMixedCubeResidual_eq`, `OAI.Erdos3.nativeMixedCubeResidual_norm_le_one`, `OAI.Erdos3.nativeMixedResidual_norm_le_one`, `OAI.Erdos3.twistedNativeSampleFunctions_mono_of_twist`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B202

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticLocalFrequency
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {ι κ D V : Type} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V]

noncomputable def affineBasisCoefficient
    (B : Basis ι ℝ (κ → ℝ)) (β : κ → D → V) (i : ι) (d : D) : V :=
  ∑ j, B i j • β j d

noncomputable def affineBasisConstant
    (B : Basis ι ℝ (κ → ℝ)) (α : D → V) (β : κ → D → V) (c : ι → ℝ) (d : D) : V :=
  α d + ∑ i, c i • affineBasisCoefficient B β i d

theorem affine_basis_coordinate_sum
    (B : Basis ι ℝ (κ → ℝ)) (β : κ → D → V) (v : ι → ℝ) (d : D) :
    (∑ j, B.equivFun.symm v j • β j d) = ∑ i, v i • affineBasisCoefficient B β i d := by
  classical
  rw [Basis.equivFun_symm_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, affineBasisCoefficient,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem affine_basis_change
    (B : Basis ι ℝ (κ → ℝ)) (α : D → V) (β : κ → D → V)
    (c u : ι → ℝ) (d : D) :
    α d + ∑ j, B.equivFun.symm (c + u) j • β j d =
      affineBasisConstant B α β c d + ∑ i, u i • affineBasisCoefficient B β i d := by
  rw [affine_basis_coordinate_sum]
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, affineBasisConstant, add_assoc]

omit [Fintype ι] in
theorem affineBasisCoefficient_mem
    (B : Basis ι ℝ (κ → ℝ)) (β : κ → D → V) (U : D → Submodule ℝ V)
    (hβ : ∀ j d, β j d ∈ U d) (i : ι) (d : D) :
    affineBasisCoefficient B β i d ∈ U d :=
  Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hβ j d))

theorem affineBasisConstant_mem
    (B : Basis ι ℝ (κ → ℝ)) (α : D → V) (β : κ → D → V) (c : ι → ℝ)
    (U : D → Submodule ℝ V) (hα : ∀ d, α d ∈ U d) (hβ : ∀ j d, β j d ∈ U d) (d : D) :
    affineBasisConstant B α β c d ∈ U d :=
  Submodule.add_mem _ (hα d) (Submodule.sum_mem _
    (fun i _ => Submodule.smul_mem _ _ (affineBasisCoefficient_mem B β U hβ i d)))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem exists_local_affine_scalar_chart
    {r N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p)
    (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (hdense : Real.exp (-p) * N ≤ (J.card : ℝ)) (x : ZMod N → Fin r → ℤ)
    (hx : ∀ h ∈ J, ∀ i, |x h i| ≤ (R i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (x h)) (a : ℝ) (b : Fin r → ℝ) :
    ∃ K ⊆ J, K.Nonempty ∧ Real.exp (-((p + 4) ^ 7)) * N ≤ (K.card : ℝ) ∧
      ∃ (t c : Fin r → ℝ) (a' : ℝ) (b' : Fin r → ℝ),
        (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        (∀ i, |c i| ≤ properCyclicCoordinateBound r (Real.exp (-p)) + 1 / 16) ∧
        ∀ h ∈ K, (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ 1 / 16) ∧
          a + ∑ i, (x h i : ℝ) * b i =
            a' + ∑ i, affineCyclicTorusLocalLift t c h₀ h i * b' i := by
  obtain ⟨basis, _, t, ht, hperiod, K, hKJ, hK, hcard, c, hc, hdata⟩ :=
    exists_localized_cyclic_torus_chart η R hinj h₀ J hJ (Real.exp (-p))
      (Real.exp_pos _) hdense x hx hrep 8 (by norm_num)
  let B := basis.ofZLatticeBasis ℝ (cyclicIntegerKernel η)
  let a' := affineBasisConstant B (fun _ : Unit => a) (fun i _ => b i) c ()
  let b' (i : Fin r) := affineBasisCoefficient B (fun j (_ : Unit) => b j) i ()
  refine ⟨K, hKJ, hK, local_cyclic_torus_density hp hr J K hdense hcard,
    t, c, a', b', ht, hperiod, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, div_div, show (2 : ℝ) * 8 = 16 by norm_num] using hc
  · intro h hh
    obtain ⟨_, hsmall, hcoord⟩ := hdata h hh
    refine ⟨by norm_num at hsmall ⊢; exact hsmall, ?_⟩
    change a + ∑ i, integerVectorRealMap (x h) i * b i = _
    rw [hcoord]
    exact affine_basis_change B (fun _ : Unit => a) (fun i _ => b i) c
      (affineCyclicTorusLocalLift t c h₀ h) ()

theorem exists_quadratic_local_frequency :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ (r : ℕ) (t c b : Fin r → ℝ) (a : ℝ) (h₀ : ZMod N),
          (r : ℝ) ≤ (p + C) ^ C ∧
          (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
          (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
          (∀ i, |c i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∀ h ∈ H, (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ 1 / 16) ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (CircleFourier.character
                  (((n.val : ℝ) * (a + ∑ i, affineCyclicTorusLocalLift t c h₀ h i * b i) : ℝ) :
                    CircleFourier.Circle))‖ := by
  obtain ⟨A, _, hfrequencies⟩ := exists_quadratic_affine_frequency_coordinates_budget
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + 4) ^ 7 + (P + 4) ^ 5 + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  classical
  obtain ⟨J, hJ, hdense, r, R, η, ξ, h₀, ξ₀, hrank, hproper, hselected⟩ :=
    hfrequencies hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : q + (q + 4) ^ 7 + (q + 4) ^ 5 + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by
    have h₇ : 0 ≤ (q + 4) ^ 7 := by positivity
    have h₅ : 0 ≤ (q + 4) ^ 5 := by positivity
    linarith
  have hchartC : (q + 4) ^ 7 ≤ (p + C) ^ C := by
    have h₅ : 0 ≤ (q + 4) ^ 5 := by positivity
    linarith
  have hcenterC : (q + 4) ^ 5 + 2 ≤ (p + C) ^ C := by
    have h₇ : 0 ≤ (q + 4) ^ 7 := by positivity
    linarith
  choose x hx hrep hlarge using fun h : {h // h ∈ J} => hselected h.val h.property
  let x' (h : ZMod N) : Fin r → ℤ := if hh : h ∈ J then x ⟨h, hh⟩ else 0
  have hx' (h : ZMod N) (hh : h ∈ J) : ∀ i, |x' h i| ≤ (R i : ℤ) := by
    simpa only [x', dif_pos hh] using hx ⟨h, hh⟩
  have hrep' (h : ZMod N) (hh : h ∈ J) : h = h₀ + η (x' h) := by
    simpa only [x', dif_pos hh] using hrep ⟨h, hh⟩
  have hlarge' (h : ZMod N) (hh : h ∈ J) : Real.exp (-q) ≤
      ‖finiteFourierCoeff (multiplicativeDerivative f h) (AddChar.zmodAddEquiv (ξ₀ + ξ (x' h)))‖ := by
    simpa only [x', dif_pos hh] using hlarge ⟨h, hh⟩
  have hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)} := by
    simpa only [Set.InjOn, Finset.mem_coe, mem_centeredIntegerBox, Set.mem_ofPred_eq] using hproper
  obtain ⟨a, b, hphase⟩ := exists_affine_cyclic_character_phase ξ ξ₀
  obtain ⟨K, hKJ, hK, hKsize, t, c, a', b', ht, hperiod, hc, hlocal⟩ :=
    exists_local_affine_scalar_chart hq hrank η R hinj h₀ J hJ hdense x' hx' hrep' a b
  refine ⟨K, hK, ?_, r, t, c, b', a', h₀, hrank.trans hqC, ht, hperiod, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hchartC))
      (Nat.cast_nonneg _)).trans hKsize
  · intro i
    have hcoord := properCyclicCoordinateBound_le_exp hq hrank
    have hE : 1 ≤ Real.exp ((q + 4) ^ 5) := Real.one_le_exp (by positivity)
    calc
      |c i| ≤ properCyclicCoordinateBound r (Real.exp (-q)) + 1 / 16 := hc i
      _ ≤ 2 * Real.exp ((q + 4) ^ 5) := by linarith
      _ ≤ Real.exp 2 * Real.exp ((q + 4) ^ 5) := by
        gcongr
        linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = Real.exp ((q + 4) ^ 5 + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hcenterC
  · intro h hh
    obtain ⟨hsmall, heq⟩ := hlocal h hh
    refine ⟨hsmall, ?_⟩
    have heval (n : ZMod N) : CircleFourier.character
        (((n.val : ℝ) * (a' + ∑ i, affineCyclicTorusLocalLift t c h₀ h i * b' i) : ℝ) :
          CircleFourier.Circle) = AddChar.zmodAddEquiv (ξ₀ + ξ (x' h)) n := by
      rw [← heq]
      exact hphase (x' h) n
    simp only [heval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hlarge' h (hKJ hh))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticCyclicAntisymmetric
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem exists_reflected_corner_correlation (F : G → G → ℂ) (b₁ b₂ b₃ : G → ℂ)
    (hb₁ : ∀ x, ‖b₁ x‖ ≤ 1) (hb₂ : ∀ y, ‖b₂ y‖ ≤ 1) (hb₃ : ∀ z, ‖b₃ z‖ ≤ 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcorr : ρ ≤ (𝔼 x, 𝔼 y, F y x * b₁ x * b₂ y * b₃ (x + y)).re) :
    ∃ (z : G) (b : G → ℂ), (∀ y, ‖b y‖ ≤ 1) ∧
      ρ ^ 2 ≤ (𝔼 y, 𝔼 y',
        F y (z - y - y') * star (F y' (z - y - y')) * b y * star (b y')).re := by
  let B (z y : G) := b₂ y * star (b₃ (z - y))
  have hnorm : ρ ≤ ‖𝔼 x, b₁ x * (𝔼 y, F y x * b₂ y * b₃ (x + y))‖ := by
    have heq : (𝔼 x, b₁ x * (𝔼 y, F y x * b₂ y * b₃ (x + y))) =
        𝔼 x, 𝔼 y, F y x * b₁ x * b₂ y * b₃ (x + y) := by
      simp_rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      ring
    rw [heq]
    exact hcorr.trans (Complex.re_le_norm _)
  have hcs := finite_family_cauchy_schwarz_re b₁
    (fun y x => F y x * b₂ y * b₃ (x + y)) hb₁
  simp only [one_pow, one_mul] at hcs
  have hchange : (𝔼 y, 𝔼 y', 𝔼 x,
      (F y x * b₂ y * b₃ (x + y)) * star (F y' x * b₂ y' * b₃ (x + y'))) =
      𝔼 z, 𝔼 y, 𝔼 y',
        F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y') := by
    calc
      _ = 𝔼 y, 𝔼 y', 𝔼 z,
          F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y') := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro y' _
        apply Fintype.expect_equiv (Equiv.addRight (y + y'))
        intro x
        have h₁ : x + (y + y') - y = x + y' := by abel
        have h₂ : x + (y + y') - y' = x + y := by abel
        simp only [Equiv.coe_addRight, B, h₁, h₂, add_sub_cancel_right, star_mul, star_star]
        ring
      _ = 𝔼 y, 𝔼 z, 𝔼 y',
          F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y') := by
        apply Finset.expect_congr rfl
        intro y _
        exact Finset.expect_comm _ _ _
      _ = _ := Finset.expect_comm _ _ _
  have hmean := (pow_le_pow_left₀ hρ hnorm 2).trans hcs
  rw [hchange, expect_re, Fintype.expect_eq_sum_div_card] at hmean
  have hsum : (∑ _z : G, ρ ^ 2) ≤ ∑ z : G, (𝔼 y, 𝔼 y',
      F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y')).re := by
    have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using
      (le_div_iff₀ hcard).mp hmean
  obtain ⟨z, _, hz⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨z, B z, ?_, hz⟩
  intro y
  simp only [B, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hb₂ _)).trans (hb₃ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem exists_phase_aligned_derivatives (f : G → ℂ) (g : G → G → ℂ) :
    ∃ c : G → ℂ, (∀ h, ‖c h‖ = 1) ∧
      (𝔼 h, 𝔼 n, multiplicativeDerivative f h n * star (star (c h) * g h n)) =
        ((𝔼 h, ‖𝔼 n, multiplicativeDerivative f h n * star (g h n)‖ : ℝ) : ℂ) := by
  choose c hc hphase using fun h =>
    exists_complex_unit_phase (𝔼 n, multiplicativeDerivative f h n * star (g h n))
  refine ⟨c, hc, ?_⟩
  have heq (h : G) : (𝔼 n, multiplicativeDerivative f h n * star (star (c h) * g h n)) =
      (‖𝔼 n, multiplicativeDerivative f h n * star (g h n)‖ : ℂ) := by
    rw [← hphase h, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    simp only [star_mul, star_star]
    ring
  simp_rw [heq]
  simp [Fintype.expect_eq_sum_div_card]

theorem exists_correlated_corner (f : G → ℂ) (g : G → G → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {ρ : ℝ}
    (hcorr : ρ ≤ 𝔼 h, ‖𝔼 n, multiplicativeDerivative f h n * star (g h n)‖) :
    ∃ b₁ b₂ b₃ : G → ℂ,
      (∀ x, ‖b₁ x‖ ≤ 1) ∧ (∀ y, ‖b₂ y‖ ≤ 1) ∧ (∀ z, ‖b₃ z‖ ≤ 1) ∧
      ρ ≤ (𝔼 x, 𝔼 y, g y x * b₁ x * b₂ y * b₃ (x + y)).re := by
  obtain ⟨c, hc, hphase⟩ := exists_phase_aligned_derivatives f g
  refine ⟨(fun x => star (f x)), (fun y => star (c y)), f, ?_, ?_, hf, ?_⟩
  · intro x
    simpa only [norm_star] using hf x
  · intro y
    simp only [norm_star, hc, le_refl]
  · have heq : (𝔼 x, 𝔼 y, g y x * star (f x) * star (c y) * f (x + y)) =
        star (𝔼 h, 𝔼 n, multiplicativeDerivative f h n * star (star (c h) * g h n)) := by
      calc
        _ = 𝔼 y, 𝔼 x, star (multiplicativeDerivative f y x * star (star (c y) * g y x)) := by
          rw [Finset.expect_comm]
          apply Finset.expect_congr rfl
          intro y _
          apply Finset.expect_congr rfl
          intro x _
          simp only [multiplicativeDerivative, star_mul, star_star]
          ring
        _ = _ := by simp only [expect_star]
    rw [heq, hphase]
    simpa only [Complex.star_def, Complex.conj_re, Complex.ofReal_re] using hcorr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairCorrelator
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_antisymmetric_anchor_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (i j : Fin W.outputDim) (a : Fin 2 → ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        (boxAnchorFactor (W.antisymmetricKernel i j) a)) := by
  obtain ⟨A, _, hslice⟩ := exists_antisymmetric_coordinate_slice
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let R := Q + (Q + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j a
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A
  let r := q + (q + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : q ≤ r := le_add_of_nonneg_right (by positivity)
  have hbr : (q + B) ^ B ≤ r := le_add_of_nonneg_left hq
  obtain ⟨Ex⟩ := hslice W i j 0 (a 1)
  obtain ⟨Ey⟩ := hslice W i j 1 (a 0)
  change NativeIntegerExpansion (fun _ : Unit => 1) 1 q
    (fun x => W.antisymmetricKernel i j (x ()) (a 1)) at Ex
  change NativeIntegerExpansion (fun _ : Unit => 1) 1 q
    (fun x => W.antisymmetricKernel i j (a 0) (x ())) at Ey
  let Ex' := Ex.linearPullbackHom (fun _ : Unit =>
    ({ toFun := fun z : Fin 2 → ℤ => z 0, map_zero' := rfl, map_add' := fun _ _ => rfl }))
  let Ey' := Ey.linearPullbackHom (fun _ : Unit =>
    ({ toFun := fun z : Fin 2 → ℤ => z 1, map_zero' := rfl, map_add' := fun _ _ => rfl }))
  have Ec : NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q
      (fun _ => W.antisymmetricKernel i j (a 0) (a 1)) := by
    simpa [integerAffineMap] using Ex.affinePullback
      (fun (_ : Unit) (_ : Fin 2) => (0 : ℤ)) (fun _ => a 0)
  obtain ⟨E⟩ := hmul hq Ey'.conjugate Ex'.conjugate
  obtain ⟨F⟩ := hmul hr (E.mono hbr) (Ec.mono hqr)
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [R, Q, X, r, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_antisymmetric_pair_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
        {N : ℕ} [NeZero N] (i j : Fin W.outputDim),
      Real.exp (-p) ≤ (finiteBoxCorrelation (fun x y : ZMod N =>
        star (W.evalCyclic N i (correlationInput x y)) *
          W.evalCyclic N j (correlationInput y x))).re →
      Nonempty (NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))) := by
  obtain ⟨A, _, hanchor⟩ := NativeMultidegreeNilcharacter.exists_antisymmetric_anchor_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p hp W N _ i j hbox
  let K (x y : ZMod N) := W.antisymmetricKernel i j (x.val : ℤ) (y.val : ℤ)
  have hbias : Real.exp (-p) ≤ (finiteBoxCorrelation K).re := by
    simpa only [K, W.antisymmetricKernel_cyclic] using hbox
  obtain ⟨a, ha⟩ := exists_box_anchor_correlation K
  obtain ⟨E⟩ := hanchor W i j (fun k => ((a k).val : ℤ))
  have hcorr : Real.exp (-p) ≤ ‖𝔼 z : Fin 2 → ZMod N,
      W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ) *
        star (star (boxAnchorFactor (W.antisymmetricKernel i j)
          (fun k => ((a k).val : ℤ)) (fun k => ((z k).val : ℤ))))‖ := by
    simpa only [K, boxAnchorFactor, star_star] using hbias.trans ha
  obtain ⟨V⟩ := NativeSampleCorrelation.exists_of_expansion E.conjugate hp hcorr
  have hcost : p + (p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨V.mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def pairComponent (out : Fin W.outputDim) (a b : Fin 2) :
    W.model.Niltest (fun _ : Fin 2 => 1) :=
  (W.component out).linearPullbackHom
    ![{ toFun := fun n => n a, map_zero' := rfl, map_add' := fun _ _ => rfl },
      { toFun := fun n => n b, map_zero' := rfl, map_add' := fun _ _ => rfl }]

theorem pairComponent_eval (out : Fin W.outputDim) (a b : Fin 2) (n : Fin 2 → ℤ) :
    (W.pairComponent out a b).eval n = W.eval out (correlationInput (n a) (n b)) := by
  rw [pairComponent, Niltest.eval_linearPullbackHom, component_eval]
  apply congrArg (W.eval out)
  funext k
  fin_cases k <;> rfl

theorem pairComponent_vertical (out : Fin W.outputDim) (a b : Fin 2)
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ k, mixedCorrelationDegree 1 k))
    (x : W.model.Space) :
    (W.pairComponent out a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (W.pairComponent out a b).observable x :=
  W.vertical.vertical out z (by rwa [W.multi.realSubgroup_top]) x

end NativeMultidegreeNilcharacter

def antisymmetricPairBudget (p q : ℝ) : ℝ := p + q + raisedNiltestBudget (p + q) + 4

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

abbrev AntisymmetricPairAlgebra :=
  ∀ k : Option (Fin 2), optionLieSpace V.L (fun _ : Fin 2 => W.L) k

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

theorem antisymmetricPairTests_eval (n : Fin 2 → ℤ) :
    (∏ k, (V.antisymmetricPairTests k).eval n) =
      W.antisymmetricKernel i j (n 0) (n 1) * star (V.test.eval n) := by
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change (V.test.raiseStep (by decide : 1 ≤ ∑ l, mixedCorrelationDegree 1 l)).conjugate.eval n *
    ((W.pairComponent i 0 1).conjugate.eval n * (W.pairComponent j 1 0).eval n) = _
  rw [Niltest.eval_conjugate, Niltest.raiseStep_eval, Niltest.eval_conjugate,
    W.pairComponent_eval, W.pairComponent_eval]
  unfold NativeMultidegreeNilcharacter.antisymmetricKernel
  ring

theorem antisymmetricPairTests_vertical (k : Option (Fin 2))
    (z : (V.antisymmetricPairModels k).RealGroup)
    (hz : z ∈ (V.antisymmetricPairModels k).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l))
    (x : (V.antisymmetricPairModels k).Space) :
    (V.antisymmetricPairTests k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.antisymmetricPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.antisymmetricPairTests k).observable x := by
  cases k with
  | none =>
    exact V.test.conjugate.raiseStep_top_vertical
      (by decide : 1 < ∑ l, mixedCorrelationDegree 1 l) z hz x
  | some k =>
    fin_cases k
    · exact Niltest.conjugate_vertical _ _ (W.pairComponent_vertical i 0 1) z hz x
    · exact W.pairComponent_vertical j 1 0 z hz x

include V in
theorem antisymmetricPairBudget_four_le : 4 ≤ antisymmetricPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  unfold antisymmetricPairBudget raisedNiltestBudget
  nlinarith [sq_nonneg (p + q + 2)]

theorem antisymmetricPairTests_complexity (k : Option (Fin 2)) :
    (V.antisymmetricPairTests k).ComplexityLE (antisymmetricPairBudget p q) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpq : 0 ≤ p + q := add_nonneg hp hq
  have hr : 0 ≤ raisedNiltestBudget (p + q) := hpq.trans (le_raisedNiltestBudget _)
  cases k with
  | none =>
    exact (V.test.raiseStep_complexity (by decide) hpq
      (V.complexity.mono (le_add_of_nonneg_left hp))).mono
        (by unfold antisymmetricPairBudget; linarith)
  | some k =>
    have hcost : p + 4 ≤ antisymmetricPairBudget p q := by
      unfold antisymmetricPairBudget
      linarith
    fin_cases k
    · exact (W.component_complexity i).mono hcost
    · exact (W.component_complexity j).mono hcost

end NativeSampleCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AntisymmetricPairNiltest
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

noncomputable def antisymmetricPairNiltest :
    (pi V.antisymmetricPairModels).Niltest (fun _ : Fin 2 => 1) :=
  piNiltest V.antisymmetricPairModels V.antisymmetricPairTests
    ((by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
    (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
    V.antisymmetricPairTests_complexity

theorem antisymmetricPairNiltest_complexity :
    V.antisymmetricPairNiltest.ComplexityLE (productNiltestBudget (antisymmetricPairBudget p q)) :=
  piNiltest_complexity V.antisymmetricPairModels V.antisymmetricPairTests _ _ _

theorem antisymmetricPairNiltest_eval (n : Fin 2 → ℤ) :
    V.antisymmetricPairNiltest.eval n =
      W.antisymmetricKernel i j (n 0) (n 1) * star (V.test.eval n) := by
  rw [antisymmetricPairNiltest, piNiltest_eval]
  exact V.antisymmetricPairTests_eval n

theorem antisymmetricPairNiltest_vertical
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z ∈ (pi V.antisymmetricPairModels).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l)) (x : (pi V.antisymmetricPairModels).Space) :
    V.antisymmetricPairNiltest.observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.antisymmetricPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * V.antisymmetricPairNiltest.observable x :=
  piNiltest_vertical V.antisymmetricPairModels V.antisymmetricPairTests
    V.antisymmetricPairFrequencies _ _ _ V.antisymmetricPairTests_vertical z hz x

theorem antisymmetricPairNiltest_bias :
    Real.exp (-q) ≤ ‖𝔼 n ∈ integerBox (fun _ : Fin 2 => N), V.antisymmetricPairNiltest.eval n‖ := by
  rw [integerBox_expect_eq_zmod]
  simp_rw [V.antisymmetricPairNiltest_eval]
  exact V.correlation

end Erdos3.NativeSampleCorrelation

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeMixedPairNiltest
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))
  [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

noncomputable def mixedPairNiltest : (pi V.mixedPairModels).Niltest (fun _ : Fin (n + 2) => 1) :=
  piNiltest V.mixedPairModels V.mixedPairTests
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ mixedPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
    V.mixedPairTests_complexity

theorem mixedPairNiltest_complexity :
    V.mixedPairNiltest.ComplexityLE (productNiltestBudget (mixedPairBudget p q)) :=
  piNiltest_complexity V.mixedPairModels V.mixedPairTests _ _ _

theorem mixedPairNiltest_eval (x : Fin (n + 2) → ℤ) :
    V.mixedPairNiltest.eval x =
      W.mixedAntisymmetric i j x * star (V.test.eval x) := by
  rw [mixedPairNiltest, piNiltest_eval]
  exact V.mixedPairTests_eval x

theorem mixedPairNiltest_vertical (z : (pi V.mixedPairModels).RealGroup)
    (hz : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : (pi V.mixedPairModels).Space) :
    V.mixedPairNiltest.observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.mixedPairFrequencies) z.coord : ℝ) : CircleFourier.Circle) *
          V.mixedPairNiltest.observable x :=
  piNiltest_vertical V.mixedPairModels V.mixedPairTests V.mixedPairFrequencies _ _ _
    V.mixedPairTests_vertical z hz x

theorem mixedPairNiltest_bias :
    Real.exp (-q) ≤ ‖𝔼 x ∈ integerBox (fun _ : Fin (n + 2) => N), V.mixedPairNiltest.eval x‖ := by
  rw [integerBox_expect_eq_zmod]
  simp_rw [V.mixedPairNiltest_eval]
  exact V.correlation

end Erdos3.NativeSampleCorrelation

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonLocalAffineFamily
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

theorem exists_local_affine_polynomial_family
    {V : Type} [AddCommGroup V] [Module ℝ V] [Module ℚ V]
    {s r N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p)
    (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (hdense : Real.exp (-p) * N ≤ (J.card : ℝ)) (x : ZMod N → Fin r → ℤ)
    (hx : ∀ h ∈ J, ∀ i, |x h i| ≤ (R i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (x h))
    (P : ZMod N → VectorPolynomial Unit ℚ V) (Γ : VectorPolynomial Unit ℚ V)
    (α : Fin s → V) (β : Fin r → Fin s → V) (U : Fin s → Submodule ℝ V)
    (hα : ∀ d, α d ∈ U d) (hβ : ∀ i d, β i d ∈ U d)
    (hP : ∀ h ∈ J, P h = Γ + positiveUnivariate (fun d => α d + ∑ i, (x h i : ℝ) • β i d)) :
    ∃ K ⊆ J, K.Nonempty ∧ Real.exp (-((p + 4) ^ 7)) * N ≤ (K.card : ℝ) ∧
      ∃ b : Basis (Fin r) ℤ (cyclicIntegerKernel η),
        (∀ i j, |(b i : Fin r → ℝ) j| ≤
          properCyclicKernelBasisBound r (Real.exp (-p)) * ((R j : ℝ) + 1)) ∧
        ∃ (t c : Fin r → ℝ) (α' : Fin s → V) (β' : Fin r → Fin s → V),
          (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
          (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
          (∀ i, |c i| ≤ properCyclicCoordinateBound r (Real.exp (-p)) + 1 / 16) ∧
          (∀ d, α' d ∈ U d) ∧ (∀ i d, β' i d ∈ U d) ∧
          ∀ h ∈ K,
            (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ 1 / 16) ∧
            P h = Γ + positiveUnivariate (fun d => α' d +
              ∑ i, affineCyclicTorusLocalLift t c h₀ h i • β' i d) := by
  obtain ⟨b, hb, t, ht, hperiod, K, hKJ, hK, hcard, c, hc, hdata⟩ :=
    exists_localized_cyclic_torus_chart η R hinj h₀ J hJ (Real.exp (-p))
      (Real.exp_pos (-p)) hdense x hx hrep 8 (by norm_num)
  let B := b.ofZLatticeBasis ℝ (cyclicIntegerKernel η)
  let α' := affineBasisConstant B α β c
  let β' := affineBasisCoefficient B β
  refine ⟨K, hKJ, hK, local_cyclic_torus_density hp hr J K hdense hcard,
    b, hb, t, c, α', β', ht, hperiod, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, div_div, show (2 : ℝ) * 8 = 16 by norm_num] using hc
  · exact affineBasisConstant_mem B α β c U hα hβ
  · exact affineBasisCoefficient_mem B β U hβ
  · intro h hh
    obtain ⟨_, hsmall, hcoord⟩ := hdata h hh
    refine ⟨?_, ?_⟩
    · norm_num at hsmall ⊢
      exact hsmall
    · rw [hP h (hKJ hh)]
      have he : (fun d => α d + ∑ i, (x h i : ℝ) • β i d) =
          fun d => α' d + ∑ i, affineCyclicTorusLocalLift t c h₀ h i • β' i d := by
        funext d
        change α d + ∑ i, integerVectorRealMap (x h) i • β i d = _
        rw [hcoord]
        exact affine_basis_change B α β c (affineCyclicTorusLocalLift t c h₀ h) d
      rw [he]

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_common_local_marked_family
    {t : ℕ} {B : ℝ} (hB : 0 ≤ B) (ht : (t : ℝ) ≤ B)
    (η : (Fin t → ℤ) →+ ZMod N) (radius : Fin t → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (radius i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (hdense : Real.exp (-B) * N ≤ (J.card : ℝ))
    (v : ZMod N → Fin t → ℤ) (hv : ∀ h ∈ J, ∀ i, |v h i| ≤ (radius i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (v h))
    (A : ZMod N → VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (Γ : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (hΓdeg : DegreeLE (fun _ : Unit => 1) s Γ) (hΓzero : coefficients Γ 0 = 0)
    (hΓ : ∀ j : Fin s, coefficients Γ (Finsupp.single () (j.val + 1)) ∈
      (D.coefficientFreeSpan j).baseChange ℝ)
    (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (β : Fin t → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hα : ∀ j, α j ∈ (D.dependentFreeSpan j).baseChange ℝ)
    (hβ : ∀ i j, β i j ∈ (D.dependentFreeSpan j).baseChange ℝ)
    (hA : ∀ h ∈ J, A h = Γ + positiveUnivariate (fun j => α j + ∑ i, (v h i : ℝ) • β i j)) :
    ∃ K ⊆ J, K.Nonempty ∧ Real.exp (-((B + 4) ^ 7)) * N ≤ (K.card : ℝ) ∧
      ∃ (u c : Fin t → ℝ)
        (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ),
        (∀ i, u i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * u i = (k : ℝ)) ∧
        (∀ i, |c i| ≤ properCyclicCoordinateBound t (Real.exp (-B)) + 1 / 16) ∧
        ∀ h ∈ K, (∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 16) ∧
          A h = positiveUnivariate (fun j => (x j).val +
            ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) ∧
          ∀ n : ℤ,
            (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
              D.coefficientWeight D.coefficientIsDependent t
                (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
                  (D.localAffineMarkedLift t x y u c h₀ h n) = eval (fun _ => (n : ℚ)) (A h) := by
  obtain ⟨K, hKJ, hK, hcard, _, _, u, c, α', β', hu, hperiod, hc, hα', hβ', hlocal⟩ :=
    exists_local_affine_polynomial_family hB ht η radius hinj h₀ J hJ hdense v hv hrep
      A Γ α β (fun j => (D.dependentFreeSpan j).baseChange ℝ) hα hβ hA
  let x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ := fun j =>
    ⟨coefficients Γ (Finsupp.single () (j.val + 1)) + α' j,
      Submodule.add_mem _ (hΓ j) (Submodule.baseChange_mono ℝ
        (D.dependentFreeSpan_le_coefficientFreeSpan j) (hα' j))⟩
  let y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ :=
    fun j i => ⟨β' i j, hβ' i j⟩
  refine ⟨K, hKJ, hK, hcard, u, c, x, y, hu, hperiod, hc, ?_⟩
  intro h hh
  obtain ⟨hsmall, hpoly⟩ := hlocal h hh
  have he : A h = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
    rw [hpoly, ← positiveUnivariate_reconstruct Γ hΓdeg hΓzero]
    simp only [x, y, positiveUnivariate, monomial, TensorProduct.tmul_add,
      Finset.sum_add_distrib, add_assoc]
  exact ⟨hsmall, he, fun n => D.localAffineMarkedLift_eq_polynomial_eval t x y u c h₀ A h he n⟩

end Erdos3.NativeRankRelation.CommonData

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

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

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

theorem pairCoordinateTests_complexity (k : Fin 2) (out : Fin W.outputDim) (l : Option (Fin 2)) :
    (V.pairCoordinateTests k out l).ComplexityLE (antisymmetricPairBudget p q) := by
  have htwo : 2 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (2 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  cases l with
  | none => exact Niltest.oneOnOrbit_complexity _ htwo (V.antisymmetricPairTests_complexity none).1
  | some l =>
    fin_cases k <;> fin_cases l
    · exact V.antisymmetricPairTests_complexity (some 0)
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.antisymmetricPairTests_complexity (some 1)).1
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.antisymmetricPairTests_complexity (some 0)).1
    · exact V.antisymmetricPairTests_complexity (some 1)

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

noncomputable def pairCoordinateNiltest (k : Fin 2) (out : Fin W.outputDim) :
    (pi V.antisymmetricPairModels).Niltest (fun _ : Fin 2 => 1) :=
  piNiltest V.antisymmetricPairModels (V.pairCoordinateTests k out)
    ((by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
    (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
    (V.pairCoordinateTests_complexity k out)

theorem pairCoordinateNiltest_complexity (k : Fin 2) (out : Fin W.outputDim) :
    (V.pairCoordinateNiltest k out).ComplexityLE
      (productNiltestBudget (antisymmetricPairBudget p q)) :=
  piNiltest_complexity V.antisymmetricPairModels (V.pairCoordinateTests k out) _ _ _

theorem pairCoordinateNiltest_observable (k : Fin 2) (out : Fin W.outputDim)
    (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairCoordinateNiltest k out).observable x =
      W.vertical.observable out (productProjection V.antisymmetricPairModels (some k) x) := by
  change (∏ l, (V.pairCoordinateTests k out l).observable
    (productProjection V.antisymmetricPairModels l x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * (W.vertical.observable out
      (productProjection V.antisymmetricPairModels (some 0) x) * 1) = _
    simp only [one_mul, mul_one]
    rfl
  · change 1 * (1 * W.vertical.observable out
      (productProjection V.antisymmetricPairModels (some 1) x)) = _
    simp only [one_mul]
    rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.QuadraticPrimitiveNiltest
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quadratic_primitive_niltest_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p,
      ∀ i : Fin W.outputDim, ∀ χ : AddChar (ZMod N) ℂ,
      (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * χ n) ∈
        nativeCyclicFunctions 2 N ((p + C) ^ C) := by
  obtain ⟨A, _, hproduct⟩ := exists_productNiltestBudget_bound
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 216 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp W i χ
  obtain ⟨T, hTnorm, hT, hTeval⟩ := W.exists_quadratic_diagonal_niltest i
  obtain ⟨U, hUnorm, hU, hUeval⟩ := exists_cyclic_character_niltest χ
  let hdegree : 1 ≤ 2 := by omega
  let r := p + 216
  have hr : 0 ≤ r := by dsimp [r]; linarith
  let K : Bool → Type := BoolLieFamily W.L (RationalTorus.Algebra 1)
  let dims : Bool → ℕ := fun b => Bool.rec 1 W.dim b
  let models : ∀ b, RationalFilteredNilmanifold (K b) 2 (dims b) := fun b => by
    cases b
    · exact (RationalTorus.nilmanifold 1).raiseStep hdegree
    · exact W.model
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact U.raiseStep hdegree
    · exact T.conjugate
  have htests : ∀ b, (tests b).ComplexityLE r := by
    intro b
    cases b
    · apply (U.raiseStep_complexity hdegree (by norm_num) hU).mono
      dsimp [raisedNiltestBudget, r]
      linarith
    · exact hT.mono (by dsimp [r]; linarith)
  have hcap : ∀ b, (tests b).normBound ≤ 1 := by
    intro b
    cases b
    · exact hUnorm
    · exact hTnorm.le
  have hcard : (Fintype.card Bool : ℝ) ≤ r := by
    simp only [Fintype.card_bool, Nat.cast_ofNat]
    dsimp [r]
    linarith
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.unitBoundedPiNiltest models tests hr hcard htests hcap
  have hcost : productNiltestBudget r ≤ (p + C) ^ C := by
    apply (hproduct r hr).trans
    simpa [r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨{
    L := ∀ b, K b
    dim := _
    model := RationalFilteredNilmanifold.pi models
    test := S
    norm := le_rfl
    complexity := (RationalFilteredNilmanifold.unitBoundedPiNiltest_complexity
      models tests hr hcard htests hcap).mono hcost
    eval := ?_ }⟩
  intro n
  change _ = S.eval (fun _ => (n.val : ℤ))
  rw [RationalFilteredNilmanifold.unitBoundedPiNiltest_eval, Fintype.prod_bool]
  change _ = star (T.eval (fun _ => (n.val : ℤ))) *
    (U.raiseStep hdegree).eval (fun _ => (n.val : ℤ))
  rw [hTeval, RationalFilteredNilmanifold.Niltest.raiseStep_eval]
  change _ = star (W.eval i (fun _ => (n.val : ℤ))) * U.evalCyclic N (fun _ => n)
  rw [hUeval]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.StepOneScalarPhase
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_stepOne_row_phase_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d N : ℕ} [NeZero N]
      (D : RationalFilteredNilmanifold L 1 d) {p : ℝ}, 0 ≤ p →
      ∀ T : D.Niltest (fun _ : Fin 2 => 1), T.ComplexityLE p →
      ∀ F : ZMod N → ZMod N → ℂ, (∀ h n, ‖F h n‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ α β : ℝ, Real.exp (-((p + C) ^ C)) ≤
        (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n *
          star (character ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))‖) := by
  obtain ⟨A, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (2 * X + 2 + Polynomial.C A) ^ A + (2 * X + 2) + 2)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d N _ D p hp T hT F hF hmass
  let r := 2 * p + 2
  let δ := Real.exp (-(p + 2))
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hδ : 0 < δ := Real.exp_pos _
  have hδr : δ⁻¹ ≤ Real.exp r := by
    dsimp [δ]
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (by dsimp [r]; linarith)
  obtain ⟨J, inst, η, U, hcard, _, hU, hchar, _, _, _, herr⟩ :=
    T.exists_controlled_vertical_decomposition hr (hT.mono hpr) δ hδ hδr
  let := inst
  have hrow (h : ZMod N) :
      ‖𝔼 n : ZMod N, F h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖ ≤
        (∑ j : J, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖) + δ := by
    apply (norm_correlation_partition_bound (F h)
      (fun n => T.eval ![(h.val : ℤ), (n.val : ℤ)])
      (fun j n => (U j).eval ![(h.val : ℤ), (n.val : ℤ)]) (hF h)).trans
    apply add_le_add le_rfl
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    simpa only [norm_sub_rev] using herr ![(h.val : ℤ), (n.val : ℤ)]
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hrow h)
  simp only [Finset.expect_add_distrib, Finset.expect_sum_comm, Fintype.expect_const] at hm
  have htwo : 2 * δ ≤ Real.exp (-p) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hs : δ ≤ ∑ j : J, (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    linarith
  obtain ⟨j, hj⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ))
    (fun j => 𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖)
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hs)
  let θ (k : Fin 2) := realifyFunctional (η j) (VectorPolynomial.coefficients (U j).orbit.log (Finsupp.single k 1))
  let γ := realifyFunctional (η j) (VectorPolynomial.coefficients (U j).orbit.log 0)
  let a := (U j).observable (QuotientGroup.mk (1 : D.RealGroup)) * character (γ : CircleFourier.Circle)
  let P (h n : ZMod N) := character ((((h.val : ℝ) * θ 0 + (n.val : ℝ) * θ 1) : ℝ) : CircleFourier.Circle)
  have heval (h n : ZMod N) : (U j).eval ![(h.val : ℤ), (n.val : ℤ)] = a * P h n := by
    rw [D.stepOne_niltest_eval_affine (U j) (η j) (hchar j)]
    simp only [a, P, γ, θ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Int.cast_natCast, AddCircle.coe_add, character_add]
    ring
  have ha : ‖a‖ ≤ Real.exp r := by
    dsimp [a]
    rw [norm_mul, norm_character, mul_one]
    apply ((U j).norm_le _).trans
    have h := (U j).observable_budget (hU j).1
    have hl := (U j).lipBound.coe_nonneg
    linarith
  have hmean (h : ZMod N) :
      (𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])) =
        star a * (𝔼 n : ZMod N, F h n * star (P h n)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    rw [heval, star_mul]
    ring
  have hupper : (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖) ≤
      Real.exp r * (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := by
    simp only [hmean, norm_mul, norm_star, ← Finset.mul_expect]
    exact mul_le_mul_of_nonneg_right ha (Finset.expect_nonneg (fun _ _ => norm_nonneg _))
  have hchosen : Real.exp (-(p + 2 + verticalDecompositionBudget r)) ≤
      Real.exp r * (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := by
    have hexp : δ / Real.exp (verticalDecompositionBudget r) = Real.exp (-(p + 2 + verticalDecompositionBudget r)) := by
      dsimp [δ]
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [hexp] at hj
    exact hj.trans hupper
  have hlower : Real.exp (-(p + verticalDecompositionBudget r + r + 2)) ≤
      (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos r)).mp
    calc
      Real.exp r * Real.exp (-(p + verticalDecompositionBudget r + r + 2)) =
          Real.exp (-(p + 2 + verticalDecompositionBudget r)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp r * (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := hchosen
  have hcost : p + verticalDecompositionBudget r + r + 2 ≤ (p + C) ^ C := by
    have hh : p + (r + A) ^ A + r + 2 ≤ (p + C) ^ C := by
      simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
    linarith [hvertical r hr]
  exact ⟨θ 0, θ 1, (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hlower⟩

theorem exists_fourier_of_stepOne_cross_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d N : ℕ} [NeZero N]
      (D : RationalFilteredNilmanifold L 1 d) {p : ℝ}, 0 ≤ p →
      ∀ T : D.Niltest (fun _ : Fin 2 => 1), T.ComplexityLE p →
      ∀ f g : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → (∀ x, ‖g x‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, (f n * star (g (n + h))) *
        star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ χ : AddChar (ZMod N) ℂ, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff g χ‖ := by
  obtain ⟨C, hC, hphase⟩ := exists_stepOne_row_phase_budget
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d N _ D p hp T hT f g hf hg hmass
  obtain ⟨α, β, hcorr⟩ := hphase D hp T hT (fun h n => f n * star (g (n + h)))
    (fun shift point => by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf point)).trans (hg _)) hmass
  let u (n : ZMod N) := f n * star (character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))
  have hu (n : ZMod N) : ‖u n‖ ≤ 1 := by
    simpa only [u, norm_mul, norm_star, norm_character, mul_one] using hf n
  have hrow (h : ZMod N) :
      ‖𝔼 n : ZMod N, (f n * star (g (n + h))) *
        star (character ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))‖ =
      ‖𝔼 n : ZMod N, u n * star (g (n + h))‖ := by
    have heq : (𝔼 n : ZMod N, (f n * star (g (n + h))) *
        star (character ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))) =
        star (character (((h.val : ℝ) * α : ℝ) : CircleFourier.Circle)) *
          (𝔼 n : ZMod N, u n * star (g (n + h))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      simp only [u, AddCircle.coe_add, character_add, star_mul]
      ring
    rw [heq, norm_mul, norm_star, norm_character, one_mul]
  simp only [hrow] at hcorr
  obtain ⟨χ, hχ⟩ := exists_large_fourier_of_mean_cross_correlation u g hu
  exact ⟨χ, hcorr.trans hχ⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_stepOne_scalar_phase_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d N : ℕ} [NeZero N]
      (D : RationalFilteredNilmanifold L 1 d) {p : ℝ}, 0 ≤ p →
      ∀ T : D.Niltest (fun _ : Unit => 1), T.ComplexityLE p →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 n, f n * star (T.evalCyclic N (fun _ => n))‖ →
      ∃ β : ℝ, Real.exp (-((p + C) ^ C)) ≤
        ‖𝔼 n : ZMod N, f n * star (character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))‖ := by
  obtain ⟨C, hC, hphase⟩ := exists_stepOne_row_phase_budget
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d N _ D p hp T hT f hf hcorr
  let projection : Unit → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let U := T.linearPullbackHom projection
  have hU (h n : ZMod N) : U.eval ![(h.val : ℤ), (n.val : ℤ)] =
      T.evalCyclic N (fun _ => n) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
    rfl
  have hmass : Real.exp (-p) ≤ 𝔼 h : ZMod N,
      ‖𝔼 n : ZMod N, f n * star (U.eval ![(h.val : ℤ), (n.val : ℤ)])‖ := by
    simpa only [hU, Fintype.expect_const] using hcorr
  obtain ⟨α, β, hresult⟩ := hphase D hp U hT (fun _ n => f n) (fun _ => hf) hmass
  have hrow (h : ZMod N) :
      ‖𝔼 n : ZMod N, f n * star (character
        ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))‖ =
      ‖𝔼 n : ZMod N, f n * star (character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))‖ := by
    have heq : (𝔼 n : ZMod N, f n * star (character
        ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))) =
        star (character (((h.val : ℝ) * α : ℝ) : CircleFourier.Circle)) *
          (𝔼 n : ZMod N, f n * star (character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      simp only [AddCircle.coe_add, character_add, star_mul]
      ring
    rw [heq, norm_mul, norm_star, norm_character, one_mul]
  exact ⟨β, by simpa only [hrow, Fintype.expect_const] using hresult⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedCubeResiduals
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem nativeMixedResidual_norm_le_one {s N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (h : ZMod N) (i : Fin M.outputDim) (x : ZMod N) :
    ‖nativeMixedResidual f M h i x‖ ≤ 1 := by
  rw [nativeMixedResidual, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (multiplicativeDerivative_norm_le_one f hf h x)).trans (M.norm_eval _ _)

noncomputable def nativeMixedCubeResidual {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
    (i : Fin M.outputDim) (u : Fin (d + 1) → ZMod N) : ZMod N → ℂ :=
  cubeProduct (nativeMixedResidual f M (u 0) i) (List.ofFn (Fin.tail u))

theorem nativeMixedCubeResidual_norm_le_one {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
    (i : Fin M.outputDim) (u : Fin (d + 1) → ZMod N) (x : ZMod N) :
    ‖nativeMixedCubeResidual f M i u x‖ ≤ 1 :=
  cubeProduct_norm_le_one _ (nativeMixedResidual_norm_le_one f hf M (u 0) i) _ x

theorem nativeMixedCubeResidual_eq {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
    (i : Fin M.outputDim) (u : Fin (d + 1) → ZMod N) (x : ZMod N) :
    nativeMixedCubeResidual f M i u x =
      cubeProduct f (List.ofFn u) x *
        star (cubeProduct (fun y => M.evalCyclic N i (correlationInput (u 0) y))
          (List.ofFn (Fin.tail u)) x) := by
  change cubeProduct (fun y => multiplicativeDerivative f (u 0) y *
    star (M.evalCyclic N i (correlationInput (u 0) y))) (List.ofFn (Fin.tail u)) x = _
  rw [cubeProduct_mul, cubeProduct_star, List.ofFn_succ, cubeProduct_cons_eq_derivative]
  rfl

namespace NativeMixedCorrelation

theorem exists_degree_one_cube_residuals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim, ∃ Q : Finset (Fin (d + 1) → ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 1) ≤ (Q.card : ℝ) ∧
        ∀ u ∈ Q, u 0 ∈ M.shifts ∧
          Nonempty (NativeVectorCorrelation 1 N ((p + C) ^ C)
            (fun _ : Unit => nativeMixedCubeResidual f M.mixed i u)) := by
  obtain ⟨a, _, hiter⟩ := exists_iterated_native_derivative_correlations 1 d (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * X + P)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  classical
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsum : 2 * p + q ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨i, H, hsub, hH, hHdense, hHcorr⟩ := M.exists_fixed_residual_coordinate
  have hdata (h : H) := hiter hp ((Real.exp_le_exp.mpr hqC).trans hN)
    (nativeMixedResidual f M.mixed h.val i)
    (nativeMixedResidual_norm_le_one f hf M.mixed h.val i)
    (by simpa only [show d + 2 - 1 = 1 + d by omega] using hHcorr h.val h.property)
  choose K _hK hKdense hKcorr using hdata
  obtain ⟨Q, hQdense, hQmem⟩ := dense_tuple_fibers d H K (Real.exp_nonneg (-q))
    (by simpa only [ZMod.card] using hHdense)
    (fun h => by simpa only [ZMod.card] using hKdense h)
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le
      (by positivity : 0 < Real.exp (-(2 * p)) * Real.exp (-q) *
        (Fintype.card (ZMod N) : ℝ) ^ (d + 1)) hQdense
  refine ⟨i, Q, hQ, ?_, ?_⟩
  · have heq : Real.exp (-(2 * p + q)) = Real.exp (-(2 * p)) * Real.exp (-q) := by
      rw [neg_add, Real.exp_add]
    have hsmall := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hsum))
      (pow_nonneg (Nat.cast_nonneg N) (d + 1))
    rw [heq] at hsmall
    exact hsmall.trans (by simpa only [ZMod.card] using hQdense)
  · intro u hu
    obtain ⟨h, hh, htail⟩ := (hQmem u).mp hu
    refine ⟨hsub (hh ▸ h.property), ?_⟩
    obtain ⟨V⟩ := hKcorr h (Fin.tail u) htail
    change Nonempty (NativeVectorCorrelation 1 N ((p + C) ^ C)
      (fun _ : Unit => cubeProduct (nativeMixedResidual f M.mixed (u 0) i)
        (List.ofFn (Fin.tail u))))
    rw [← hh]
    exact ⟨V.mono hqC⟩

end NativeMixedCorrelation
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedSeparatedFamily
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_separated_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x) →
      ∀ {G Ω : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset Ω), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → Ω → Fin (s + 1) → ℤ) (f : G → Ω → ℂ),
      (∀ h ∈ H, ∀ u ∈ S h, ‖f h u‖ ≤ 1) →
      ∀ (j : Fin W.outputDim) (A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
      (∀ i x, ‖A i x‖ ≤ 1) →
      (∀ i x y, (∀ l, l ≠ i → x l = y l) → A i x = A i y) →
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 u ∈ S h, f h u * star (W.eval j
        (mixedReplicatedInput (sample h u 0) (fun _ : Fin s => ∑ l : Fin s, sample h u l.succ))) *
          ∏ i, A i (sample h u)‖) →
      ∃ (a : Equiv.Perm (Fin s) → Fin W.outputDim)
        (B : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
        (∀ i x, ‖B i x‖ ≤ 1) ∧
        (∀ i x y, (∀ l, l ≠ i → x l = y l) → B i x = B i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 u ∈ S h, f h u * star (mixedPermutationProduct W.eval a (sample h u)) *
              ∏ i, B i (sample h u)‖ := by
  obtain ⟨a, _, hexpand⟩ := exists_mixed_permutation_partition_expansion s hs
  obtain ⟨b, _, htransfer⟩ := exists_separated_family_correlation s
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Q + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W hsym G Ω H hH S hS sample f hf j A hA hAind hcorr
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have E : NativeIntegerVectorEquivalence s q
      (fun i (x : Fin (s + 1) → ℤ) => W.eval i
        (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ l : Fin s, x l.succ)))
      (mixedAssignmentPartitionVector W.eval) := hexpand W hsym
  obtain ⟨k, B, hB, hBind, H', hsub, hH', hsize, hBcorr⟩ := htransfer hr (E.mono hqr)
    (mixedAssignmentPartitionVector_unit W.eval W.unit_eval) H hH S hS sample f hf j A hA hAind
    (fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans (hcorr h hh))
  obtain ⟨D, hD, hDind, hDprod⟩ := W.exists_mixed_missing_factors (fun v => k (Sum.inr v))
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨(fun e => k (Sum.inl e)), (fun i x => B i x * star (D i x)),
    ?_, ?_, H', hsub, hH', ?_, ?_⟩
  · intro i x
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hB i x)).trans (hD i x)
  · intro i x y hxy
    change B i x * star (D i x) = B i y * star (D i y)
    rw [hBind i x y hxy, hDind i x y hxy]
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg _)).trans hsize
  · intro h hh
    simp only [Finset.prod_mul_distrib, ← star_prod, hDprod]
    simpa only [mixedAssignmentPartitionVector, star_mul, mul_comm, mul_left_comm, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hBcorr h hh)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedNativeFamilyMonotone
namespace OAI

section

namespace Erdos3

variable {σ Ω : Type*} {w : σ → ℕ} {degree : ℕ} {p q : ℝ}
  {sample : Ω → σ → ℤ} {f : Ω → ℂ}

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable def NativeSampleModel.mono (F : NativeSampleModel w degree p sample f)
    (hpq : p ≤ q) : NativeSampleModel w degree q sample f where
  L := F.L
  dim := F.dim
  model := F.model
  test := F.test
  norm := F.norm
  complexity := F.complexity.mono hpq
  eval := F.eval

theorem twistedNativeSampleFunctions_mono_of_twist
    {I I' : Type*} (twist : I → Ω → ℂ) (twist' : I' → Ω → ℂ)
    (hpq : p ≤ q) (lift : I → I') (hlift : ∀ i x, twist' (lift i) x = twist i x) :
    twistedNativeSampleFunctions w degree p sample twist ⊆
      twistedNativeSampleFunctions w degree q sample twist' := by
  rintro f (rfl | ⟨i, g, ⟨G⟩, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨lift i, g, ⟨G.mono hpq⟩, by simp only [hlift]⟩

namespace VectorPolynomial
open scoped NNReal

theorem normalizedNativeSampleFunctions_mono
    {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (w : X → ℕ) (degree : ℕ) (sample : Ω → X → ℤ)
    {p q : ℝ} (hpq : p ≤ q) :
    twistedNativeSampleFunctions w degree p sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp p) (Real.exp p)
        ⟨Real.exp p, Real.exp_nonneg _⟩) t => W.eval N poly (sample t)) ⊆
    twistedNativeSampleFunctions w degree q sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp q) (Real.exp q)
        ⟨Real.exp q, Real.exp_nonneg _⟩) t => W.eval N poly (sample t)) := by
  apply twistedNativeSampleFunctions_mono_of_twist _ _ hpq
    (fun W => W.mono (Real.exp_le_exp.mpr hpq) (Real.exp_le_exp.mpr hpq)
      (show (⟨Real.exp p, Real.exp_nonneg _⟩ : ℝ≥0) ≤ ⟨Real.exp q, Real.exp_nonneg _⟩ from
        Real.exp_le_exp.mpr hpq))
  intro W t
  rfl

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PositiveShiftTestingNiltests
namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open scoped TensorProduct NNReal

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}

noncomputable def testingNiltest (B : PositiveShiftBasis s N q a J)
    (hk : ZMod N × Fin B.count) : B.model.Niltest (fun _ : Fin 1 => 1) := by
  classical
  exact if hk.1 ∈ B.shifts then
    (B.mode hk.1 hk.2).linearPullbackHom (fun _ : Unit =>
      { toFun := fun x => x 0, map_zero' := rfl, map_add' := fun _ _ => rfl })
  else RationalFilteredNilmanifold.Niltest.const B.model (fun _ : Fin 1 => 1) 0

end Erdos3.PositiveShiftBasis

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.MixedPrimitiveNiltest
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_mixed_diagonal_niltest {d : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p) (i : Fin W.outputDim) :
    ∃ T : W.model.Niltest (fun _ : Unit => 1), T.normBound = 1 ∧ T.ComplexityLE (p + 4) ∧
      ∀ n : ℤ, T.eval (fun _ => n) = W.eval i (fun _ => n) := by
  obtain ⟨T, hT, hcomplexity, heval⟩ := W.exists_linear_niltest i
    (fun _ => { toFun := fun x : Unit → ℤ => x (), map_zero' := rfl, map_add' := fun _ _ => rfl })
  exact ⟨T, hT, hcomplexity, fun n => heval (fun _ => n)⟩

theorem exists_mixed_primitive_niltest_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p,
      ∀ i : Fin W.outputDim, ∀ g ∈ nativeCyclicFunctions (d + 2) N p,
      (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * g n) ∈
        nativeCyclicFunctions (d + 3) N ((p + C) ^ C) := by
  obtain ⟨A, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let R := 2 * X + (X + 2) ^ 2 + 7
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp W i g ⟨G⟩
  have hdegree : (∑ _ : MixedReplicatedIndex (d + 2), (1 : ℕ)) = d + 3 := mixedReplicated_totalDegree (d + 1)
  have hraise : d + 2 ≤ ∑ _ : MixedReplicatedIndex (d + 2), (1 : ℕ) := by omega
  obtain ⟨T, hTnorm, hT, hTeval⟩ := W.exists_mixed_diagonal_niltest i
  let r := 2 * p + (p + 2) ^ 2 + 7
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p + 4 ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 2)]
  have hGr : raisedNiltestBudget p ≤ r := by dsimp [raisedNiltestBudget, r]; linarith
  let K : Bool → Type := BoolLieFamily W.L G.L
  let dims : Bool → ℕ := fun b => Bool.rec G.dim W.dim b
  let models : ∀ b, RationalFilteredNilmanifold (K b) (∑ _ : MixedReplicatedIndex (d + 2), 1) (dims b) := fun b => by
    cases b
    · exact G.model.raiseStep hraise
    · exact W.model
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact G.test.raiseStep hraise
    · exact T.conjugate
  have htests : ∀ b, (tests b).ComplexityLE r := by
    intro b
    cases b
    · exact (G.test.raiseStep_complexity hraise hp G.complexity).mono hGr
    · exact hT.mono hpr
  have hcap : ∀ b, (tests b).normBound ≤ 1 := by
    intro b
    cases b
    · exact G.norm
    · exact hTnorm.le
  have hcard : (Fintype.card Bool : ℝ) ≤ r := by
    simp only [Fintype.card_bool, Nat.cast_ofNat]
    linarith
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.unitBoundedPiNiltest models tests hr hcard htests hcap
  have hcost : productNiltestBudget r ≤ (p + C) ^ C := by
    apply (hproduct r hr).trans
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have H : Nonempty (NativeCyclicModel (∑ _ : MixedReplicatedIndex (d + 2), 1) N ((p + C) ^ C)
      (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * g n)) := by
    refine ⟨{
      L := ∀ b, K b
      dim := _
      model := RationalFilteredNilmanifold.pi models
      test := S
      norm := le_rfl
      complexity := (RationalFilteredNilmanifold.unitBoundedPiNiltest_complexity
        models tests hr hcard htests hcap).mono hcost
      eval := ?_ }⟩
    intro n
    change _ = S.eval (fun _ => (n.val : ℤ))
    rw [RationalFilteredNilmanifold.unitBoundedPiNiltest_eval, Fintype.prod_bool]
    change _ = star (T.eval (fun _ => (n.val : ℤ))) *
      (G.test.raiseStep hraise).eval (fun _ => (n.val : ℤ))
    rw [hTeval, RationalFilteredNilmanifold.Niltest.raiseStep_eval, G.eval n]
    rfl
  change Nonempty (NativeCyclicModel (d + 3) N ((p + C) ^ C) _)
  simpa only [hdegree] using H

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3
open scoped TensorProduct BigOperators
variable {I L : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure LocalMajorSliceTest (D : RationalFilteredNilmanifold L s d)
    (N : I → ℕ) (cost budget : ℝ) where
  stride : ℕ
  stride_pos : 0 < stride
  slice : ResidueBoxSlice N stride
  dense : IsDenseCommonStrideBox N cost slice.integerPoints
  test : D.Niltest (fun _ : I => 1)
  norm : (test.normBound : ℝ) ≤ 1
  complexity : test.ComplexityLE budget

namespace LocalMajorSliceTest
variable {D : RationalFilteredNilmanifold L s d} {N : I → ℕ} {cost budget : ℝ}
noncomputable def weight (A : LocalMajorSliceTest D N cost budget) (x : I → ℤ) : ℂ :=
  star (A.test.eval (commonStrideIndex (fun i => (A.slice.start i : ℤ)) A.stride x))
theorem weight_norm (A : LocalMajorSliceTest D N cost budget) (x : I → ℤ) :
    ‖A.weight x‖ ≤ 1 := by
  simpa only [weight, norm_star] using
    (A.test.norm_eval_le (commonStrideIndex (fun i => (A.slice.start i : ℤ))
      A.stride x)).trans A.norm

noncomputable def full (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (cost budget : ℝ) (hcost : 0 ≤ cost)
    (T : D.Niltest (fun _ : I => 1)) (hT : (T.normBound : ℝ) ≤ 1)
    (hcomplexity : T.ComplexityLE budget) : LocalMajorSliceTest D N cost budget := by
  let A : ResidueBoxSlice N 1 :=
    { start := fun _ => 0
      length := N
      inside := fun i j hj => by simpa using hj }
  refine ⟨1, Nat.zero_lt_one, A, ?_, T, hT, hcomplexity⟩
  have hA := A.isDenseCommonStrideBox Nat.zero_lt_one (ρ := 4) (by norm_num)
    hN (fun i => by dsimp [A]; norm_num)
  have hzero : IsDenseCommonStrideBox N 0 A.integerPoints := by simpa using hA
  exact hzero.mono hcost
end LocalMajorSliceTest

theorem exists_productive_localMajorSlice_coordinate_family
    {Ω X η : Type*} [Fintype Ω]
    (D : RationalFilteredNilmanifold L s d)
    (law : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (cost budget δ : ℝ)
    (fallback : LocalMajorSliceTest D N cost budget)
    (physical : Ω → (I → ℤ) → X) (signal : η → X → ℂ)
    (hlocal : ∀ j z, z ∈ good j → ∃ A : LocalMajorSliceTest D N cost budget,
      δ ≤ ‖𝔼 x ∈ A.slice.integerPoints, signal j (physical z x) * A.weight x‖) :
    ∃ chosen : Ω → Option η → LocalMajorSliceTest D N cost budget,
      (∀ j z, z ∈ good j → δ ≤ ‖𝔼 x ∈ (chosen z (some j)).slice.integerPoints,
        signal j (physical z x) * (chosen z (some j)).weight x‖) ∧
      ∀ j, δ * law.mass (good j) ≤ sampledSliceSeminorm law
        (fun z (x : integerBox N) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox N) => (chosen z a).weight x.val) (signal j) := by
  classical
  let chosen (z : Ω) : Option η → LocalMajorSliceTest D N cost budget
    | none => fallback
    | some j => if hz : z ∈ good j then Classical.choose (hlocal j z hz) else fallback
  have hchosen (j : η) (z : Ω) (hz : z ∈ good j) :
      δ ≤ ‖𝔼 x ∈ (chosen z (some j)).slice.integerPoints,
        signal j (physical z x) * (chosen z (some j)).weight x‖ := by
    have he : chosen z (some j) = Classical.choose (hlocal j z hz) := by
      simp only [chosen, dif_pos hz]
    rw [he]
    exact Classical.choose_spec (hlocal j z hz)
  refine ⟨chosen, hchosen, ?_⟩
  intro j
  let : Nonempty (integerBox N) := ⟨⟨fun _ => 0,
    (mem_integerBox _ _).mpr (fun i => ⟨le_rfl, by exact_mod_cast hN i⟩)⟩⟩
  apply productive_mass_mul_le_sampledSliceSeminorm law (good j)
    (fun z (x : integerBox N) => physical z x.val)
    (fun z a => (chosen z a).slice.subtypeSites)
    (fun z a (x : integerBox N) => (chosen z a).weight x.val)
    (fun z a => (chosen z a).slice.subtypeSites_nonempty_of_integerPoints
      (chosen z a).dense.nonempty)
    (fun z a x => (chosen z a).weight_norm x.val) (signal j) δ
  intro z hz
  refine ⟨some j, ?_⟩
  rw [(chosen z (some j)).slice.expect_subtypeSites
    (fun x => signal j (physical z x) * (chosen z (some j)).weight x)]
  exact hchosen j z hz
namespace OrdinaryPolynomialPhase

variable {n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]

noncomputable def zeroLocalMajorSlice (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (cost : ℝ) (hcost : 0 ≤ cost) :
    LocalMajorSliceTest (nilmanifold n) N cost (budget n) := by
  let T := RationalFilteredNilmanifold.Niltest.const (nilmanifold n)
    (fun _ : I => 1) (0 : ℂ)
  apply LocalMajorSliceTest.full N hN cost (budget n) hcost T
  · change ‖(0 : ℂ)‖ ≤ 1
    simp
  · refine ⟨nilmanifold_geometry n, ?_⟩
    change Real.log (2 + ‖(0 : ℂ)‖ + 0) ≤ budget n
    simp only [norm_zero, add_zero]
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith [two_le_budget n]

end OrdinaryPolynomialPhase

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {V : Type*} (Long : V → Prop) [DecidablePred Long]

def frozenLongExtension (fixed : V → ℕ) (x : {i // Long i} → ℤ) : V → ℤ :=
  fun i => if hi : Long i then x ⟨i, hi⟩ else (fixed i : ℤ)

@[simp] theorem frozenLongExtension_long (fixed : V → ℕ)
    (x : {i // Long i} → ℤ) (i : {i // Long i}) :
    frozenLongExtension Long fixed x i.val = x i := by
  simp [frozenLongExtension, i.property]

theorem frozenLongExtension_injective (fixed : V → ℕ) :
    Function.Injective (frozenLongExtension Long fixed) := by
  intro x y h
  funext i
  simpa only [frozenLongExtension_long] using congrFun h i.val

namespace ResidueBoxSlice

variable {N : V → ℕ} {q : ℕ}

def freezeShort (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i) :
    ResidueBoxSlice N q where
  start i := if hi : Long i then A.start ⟨i, hi⟩ else fixed i
  length i := if hi : Long i then A.length ⟨i, hi⟩ else 1
  inside i j hj := by
    by_cases hi : Long i
    · simpa only [dif_pos hi] using
        A.inside ⟨i, hi⟩ j (by simpa only [dif_pos hi] using hj)
    · have hj0 : j = 0 := by simpa only [dif_neg hi, Nat.lt_one_iff] using hj
      simpa only [dif_neg hi, hj0, mul_zero, add_zero] using hfixed i hi

variable [Fintype V] [DecidableEq V]

theorem freezeShort_integerPoints
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i) :
    (A.freezeShort Long fixed hfixed).integerPoints =
      A.integerPoints.image (frozenLongExtension Long fixed) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    let t : ∀ i : {i // Long i}, Fin (A.length i) := fun i =>
      ⟨(j i.val).val, by simpa [freezeShort, i.property] using (j i.val).isLt⟩
    refine Finset.mem_image.mpr ⟨A.integerPoint t,
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, ?_⟩
    funext i
    by_cases hi : Long i
    · simp [frozenLongExtension, integerPoint, point, freezeShort, hi, t]
    · have hj0 : (j i).val = 0 := by
        have := (j i).isLt
        simpa only [freezeShort, dif_neg hi, Nat.lt_one_iff] using this
      simp [frozenLongExtension, integerPoint, point, freezeShort, hi, hj0]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
    let j : ∀ i, Fin ((A.freezeShort Long fixed hfixed).length i) := fun i =>
      if hi : Long i then
        ⟨(t ⟨i, hi⟩).val, by simp only [freezeShort, dif_pos hi]; exact (t ⟨i, hi⟩).isLt⟩
      else ⟨0, by simp [freezeShort, hi]⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    funext i
    by_cases hi : Long i <;>
      simp [frozenLongExtension, integerPoint, point, freezeShort, hi, j]

theorem expect_freezeShort
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    {W : Type*} [AddCommMonoid W] [Module ℚ≥0 W] (f : (V → ℤ) → W) :
    (𝔼 x ∈ (A.freezeShort Long fixed hfixed).integerPoints, f x) =
      (𝔼 x ∈ A.integerPoints, f (frozenLongExtension Long fixed x)) := by
  rw [freezeShort_integerPoints]
  exact Finset.expect_image (frozenLongExtension_injective Long fixed).injOn

omit [Fintype V] [DecidableEq V] in
theorem freezeShort_commonStrideIndex
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i) (x : V → ℤ) :
    (fun i : {i // Long i} =>
      commonStrideIndex (fun j => ((A.freezeShort Long fixed hfixed).start j : ℤ)) q x i.val) =
    commonStrideIndex (fun i => (A.start i : ℤ)) q (fun i => x i.val) := by
  funext i
  simp [commonStrideIndex, freezeShort, i.property]

theorem freezeShort_dense
    (A : ResidueBoxSlice (fun i : {i // Long i} => N i.val) q)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hq : 0 < q) {cost B : ℝ}
    (hA : IsDenseCommonStrideBox (fun i : {i // Long i} => N i.val) cost A.integerPoints)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    IsDenseCommonStrideBox N (max cost (Real.log B))
      (A.freezeShort Long fixed hfixed).integerPoints := by
  let A' := A.freezeShort Long fixed hfixed
  refine ⟨fun i => (A'.start i : ℤ), q, A'.length, hq, ?_,
    A'.progression_inside, ?_, A'.integerPoints_eq_commonStrideBox⟩
  · intro i
    by_cases hi : Long i
    · simpa only [A', freezeShort, dif_pos hi] using A.length_pos_of_dense hA ⟨i, hi⟩
    · simp [A', freezeShort, hi]
  · intro i
    by_cases hi : Long i
    · calc
        _ ≤ Real.exp (-cost) * (N i : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (neg_le_neg (le_max_left _ _))) (Nat.cast_nonneg _)
        _ ≤ A'.length i := by
          simpa only [A', freezeShort, dif_pos hi] using
            A.length_lower_of_dense hq hA ⟨i, hi⟩
    · have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
      have hexp : Real.exp (-max cost (Real.log B)) ≤ B⁻¹ := by
        calc
          _ ≤ Real.exp (-Real.log B) :=
            Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
          _ = B⁻¹ := by rw [Real.exp_neg, Real.exp_log hBpos]
      simp only [A', freezeShort, dif_neg hi, Nat.cast_one]
      calc
        _ ≤ B⁻¹ * (N i : ℝ) := mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg _)
        _ ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hshort i hi) (inv_nonneg.mpr hBpos.le)
        _ = 1 := inv_mul_cancel₀ hBpos.ne'

end ResidueBoxSlice

def longCoordinateProjection (i : {i // Long i}) : (V → ℤ) →+ ℤ where
  toFun x := x i.val
  map_zero' := rfl
  map_add' _ _ := rfl

namespace RationalFilteredNilmanifold.Niltest

variable [Fintype V] {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

noncomputable def liftLong (T : D.Niltest (fun _ : {i // Long i} => 1)) :
    D.Niltest (fun _ : V => 1) :=
  T.linearPullbackHom (longCoordinateProjection Long)

omit [DecidablePred Long] in
@[simp] theorem liftLong_normBound (T : D.Niltest (fun _ : {i // Long i} => 1)) :
    (T.liftLong Long).normBound = T.normBound := rfl

omit [DecidablePred Long] in
@[simp] theorem liftLong_complexityLE (T : D.Niltest (fun _ : {i // Long i} => 1))
    (p : ℝ) : (T.liftLong Long).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

omit [DecidablePred Long] in
theorem eval_liftLong (T : D.Niltest (fun _ : {i // Long i} => 1)) (x : V → ℤ) :
    (T.liftLong Long).eval x = T.eval (fun i => x i.val) :=
  T.eval_linearPullbackHom (longCoordinateProjection Long) x

end RationalFilteredNilmanifold.Niltest

namespace LocalMajorSliceTest

variable [Fintype V] [DecidableEq V] {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {N : V → ℕ} {cost budget B : ℝ}

noncomputable def freezeShort
    (A : LocalMajorSliceTest D (fun i : {i // Long i} => N i.val) cost budget)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    LocalMajorSliceTest D N (max cost (Real.log B)) budget where
  stride := A.stride
  stride_pos := A.stride_pos
  slice := A.slice.freezeShort Long fixed hfixed
  dense := A.slice.freezeShort_dense Long fixed hfixed A.stride_pos A.dense hB hshort
  test := A.test.liftLong Long
  norm := A.norm
  complexity := A.complexity

theorem freezeShort_weight
    (A : LocalMajorSliceTest D (fun i : {i // Long i} => N i.val) cost budget)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) (x : V → ℤ) :
    (A.freezeShort Long fixed hfixed hB hshort).weight x = A.weight (fun i => x i.val) := by
  change star ((A.test.liftLong Long).eval
    (commonStrideIndex (fun i => ((A.slice.freezeShort Long fixed hfixed).start i : ℤ))
      A.stride x)) = _
  rw [A.test.eval_liftLong, A.slice.freezeShort_commonStrideIndex]
  rfl

theorem expect_freezeShort
    (A : LocalMajorSliceTest D (fun i : {i // Long i} => N i.val) cost budget)
    (fixed : V → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B)
    (signal : (V → ℤ) → ℂ) :
    (𝔼 x ∈ (A.freezeShort Long fixed hfixed hB hshort).slice.integerPoints,
      signal x * (A.freezeShort Long fixed hfixed hB hshort).weight x) =
    (𝔼 x ∈ A.slice.integerPoints, signal (frozenLongExtension Long fixed x) * A.weight x) := by
  change (𝔼 x ∈ (A.slice.freezeShort Long fixed hfixed).integerPoints,
    signal x * (A.freezeShort Long fixed hfixed hB hshort).weight x) = _
  rw [A.slice.expect_freezeShort]
  apply Finset.expect_congr rfl
  intro x hx
  rw [A.freezeShort_weight]
  congr 2
  funext i
  exact frozenLongExtension_long Long fixed x i

end LocalMajorSliceTest

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {I L : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

namespace LocalMajorSliceTest

end LocalMajorSliceTest

end Erdos3

end

section

namespace Erdos3.LocalMajorSliceTest
open scoped TensorProduct

variable {I L : Type*} [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {N : I → ℕ}
    {cost budget cost' budget' : ℝ}

def mono (packet : LocalMajorSliceTest D N cost budget)
    (hcost : cost ≤ cost') (hbudget : budget ≤ budget') :
    LocalMajorSliceTest D N cost' budget' where
  stride := packet.stride
  stride_pos := packet.stride_pos
  slice := packet.slice
  dense := packet.dense.mono hcost
  test := packet.test
  norm := packet.norm
  complexity := packet.complexity.mono hbudget

@[simp] theorem mono_weight (packet : LocalMajorSliceTest D N cost budget)
    (hcost : cost ≤ cost') (hbudget : budget ≤ budget') (x : I → ℤ) :
    (packet.mono hcost hbudget).weight x = packet.weight x := rfl

end Erdos3.LocalMajorSliceTest

end

section

namespace Erdos3
open scoped TensorProduct BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

structure UniversalLocalMajorSliceTest (N : I → ℕ) (degree : ℕ)
    (cost budget : ℝ) where
  stride : ℕ
  stride_pos : 0 < stride
  slice : ResidueBoxSlice N stride
  dense : IsDenseCommonStrideBox N cost slice.integerPoints
  value : (I → ℤ) → ℂ
  native : Nonempty (NativeSampleModel (fun _ : I => 1) degree budget id value)

namespace UniversalLocalMajorSliceTest

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {N : I → ℕ} {degree : ℕ} {cost budget : ℝ}

noncomputable def nativeModel (packet : UniversalLocalMajorSliceTest N degree cost budget) :
    NativeSampleModel (fun _ : I => 1) degree budget id packet.value :=
  Classical.choice packet.native

theorem value_eq_native_eval (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) : packet.value x = packet.nativeModel.test.eval x :=
  packet.nativeModel.eval x

noncomputable def weight (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) : ℂ :=
  star (packet.value
    (commonStrideIndex (fun i => (packet.slice.start i : ℤ)) packet.stride x))

theorem weight_eq_native_eval (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) :
    packet.weight x = star (packet.nativeModel.test.eval
      (commonStrideIndex (fun i => (packet.slice.start i : ℤ)) packet.stride x)) := by
  rw [weight, packet.value_eq_native_eval]

theorem weight_norm (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) : ‖packet.weight x‖ ≤ 1 := by
  rw [weight, norm_star]
  exact packet.nativeModel.norm_le _

noncomputable def ofLocalMajorSliceTest
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L degree d}
    (packet : LocalMajorSliceTest D N cost budget) :
    UniversalLocalMajorSliceTest N degree cost budget where
  stride := packet.stride
  stride_pos := packet.stride_pos
  slice := packet.slice
  dense := packet.dense
  value := packet.test.eval
  native := ⟨{
    L := L
    dim := d
    model := D
    test := packet.test
    norm := by exact_mod_cast packet.norm
    complexity := packet.complexity
    eval := fun _ => rfl }⟩

@[simp] theorem ofLocalMajorSliceTest_weight
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L degree d}
    (packet : LocalMajorSliceTest D N cost budget) (x : I → ℤ) :
    (ofLocalMajorSliceTest packet).weight x = packet.weight x := rfl

@[simp] theorem ofLocalMajorSliceTest_slice
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L degree d}
    (packet : LocalMajorSliceTest D N cost budget) :
    (ofLocalMajorSliceTest packet).slice = packet.slice := rfl

noncomputable def default (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (degree : ℕ) (cost budget : ℝ) (hcost : 0 ≤ cost) (hbudget : 2 ≤ budget) :
    UniversalLocalMajorSliceTest N degree cost budget := by
  let model : NativeSampleModel (fun _ : I => 1) degree budget id (fun _ => 1) :=
    NativeSampleModel.constOne hbudget
  exact ofLocalMajorSliceTest (LocalMajorSliceTest.full N hN cost budget hcost
    model.test (by exact_mod_cast model.norm) model.complexity)

theorem nonempty (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (degree : ℕ) (cost budget : ℝ) (hcost : 0 ≤ cost) (hbudget : 2 ≤ budget) :
    Nonempty (UniversalLocalMajorSliceTest N degree cost budget) :=
  ⟨default N hN degree cost budget hcost hbudget⟩

end UniversalLocalMajorSliceTest
end Erdos3

end

section

namespace Erdos3.UniversalLocalMajorSliceTest
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra NativeSampleModel.topology NativeSampleModel.topologicalAdd NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {I : Type} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {degree : ℕ} {cost budget : ℝ}

noncomputable def toLocalMajorSliceTest
    (packet : UniversalLocalMajorSliceTest N degree cost budget) :
    LocalMajorSliceTest packet.nativeModel.model N cost budget where
  stride := packet.stride
  stride_pos := packet.stride_pos
  slice := packet.slice
  dense := packet.dense
  test := packet.nativeModel.test
  norm := by exact_mod_cast packet.nativeModel.norm
  complexity := packet.nativeModel.complexity

@[simp] theorem toLocalMajorSliceTest_slice
    (packet : UniversalLocalMajorSliceTest N degree cost budget) :
    packet.toLocalMajorSliceTest.slice = packet.slice := rfl

@[simp] theorem toLocalMajorSliceTest_weight
    (packet : UniversalLocalMajorSliceTest N degree cost budget) (x : I → ℤ) :
    packet.toLocalMajorSliceTest.weight x = packet.weight x :=
  (packet.weight_eq_native_eval x).symm

variable (Long : I → Prop) [DecidablePred Long] {B : ℝ}

noncomputable def freezeShort
    (packet : UniversalLocalMajorSliceTest (fun i : {i // Long i} => N i.val)
      degree cost budget)
    (fixed : I → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    UniversalLocalMajorSliceTest N degree (max cost (Real.log B)) budget :=
  ofLocalMajorSliceTest (packet.toLocalMajorSliceTest.freezeShort Long fixed hfixed hB hshort)

@[simp] theorem freezeShort_stride
    (packet : UniversalLocalMajorSliceTest (fun i : {i // Long i} => N i.val)
      degree cost budget)
    (fixed : I → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    (packet.freezeShort Long fixed hfixed hB hshort).stride = packet.stride := rfl

@[simp] theorem freezeShort_slice
    (packet : UniversalLocalMajorSliceTest (fun i : {i // Long i} => N i.val)
      degree cost budget)
    (fixed : I → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) :
    (packet.freezeShort Long fixed hfixed hB hshort).slice =
      packet.slice.freezeShort Long fixed hfixed := rfl

theorem freezeShort_weight
    (packet : UniversalLocalMajorSliceTest (fun i : {i // Long i} => N i.val)
      degree cost budget)
    (fixed : I → ℕ) (hfixed : ∀ i, ¬Long i → fixed i < N i)
    (hB : 1 ≤ B) (hshort : ∀ i, ¬Long i → (N i : ℝ) ≤ B) (x : I → ℤ) :
    (packet.freezeShort Long fixed hfixed hB hshort).weight x =
      packet.weight (fun i => x i.val) := by
  rw [freezeShort, ofLocalMajorSliceTest_weight,
    LocalMajorSliceTest.freezeShort_weight, toLocalMajorSliceTest_weight]

end Erdos3.UniversalLocalMajorSliceTest

end

section

namespace Erdos3
open scoped BigOperators TensorProduct Classical

variable {I : Type*} (keep : I → Prop)

noncomputable def frozenShortStarts (fixed : {i // ¬keep i} → ℤ) : I → ℕ :=
  fun i => if hi : keep i then 0 else (fixed ⟨i, hi⟩).toNat

theorem frozenShortStarts_inside {N : I → ℕ} (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < N i.val) :
    ∀ i, ¬keep i → frozenShortStarts keep fixed i < N i := by
  intro i hi
  simp only [frozenShortStarts, dif_neg hi]
  have h := hfixed ⟨i, hi⟩
  apply Int.ofNat_lt.mp
  simpa only [Int.toNat_of_nonneg h.1] using h.2

theorem frozenLongExtension_shortStarts (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i) (x : {i // keep i} → ℤ) :
    frozenLongExtension keep (frozenShortStarts keep fixed) x =
      finiteSplitPoint keep x fixed := by
  funext i
  by_cases hi : keep i
  · simp only [frozenLongExtension, finiteSplitPoint, dif_pos hi]
  · simp only [frozenLongExtension, frozenShortStarts, finiteSplitPoint, dif_neg hi]
    exact Int.toNat_of_nonneg (hfixed ⟨i, hi⟩)

variable [Fintype I] [DecidableEq I]

end Erdos3

end

end OAI

end


