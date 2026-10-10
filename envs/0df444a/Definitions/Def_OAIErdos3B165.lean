-- Prove2me | Definitions.Def_OAIErdos3B165
-- name    : OAIErdos3B165
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T03:00:05.532183+00:00
-- url     : https://prove2.me/theorems/593bfdf1-f9d1-4f56-8bbf-9a262f5ae43c
-- title:
--   OpenAI Erdős-3 split, definitions bundle 166 of 177
-- statement:
--   Definitions bundle 166 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B164`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 166 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.selectedJointFrameBoxMap`, `OAI.Erdos3.RationalFilteredNilmanifold.BoundedCellMarkedPolynomialFreezing`, `OAI.Erdos3.RationalFilteredNilmanifold.BoundedCellMarkedPolynomialFreezing.external_affine_slice`, `OAI.Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing`, `OAI.Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary`, `OAI.Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary.mono_slow`, `OAI.Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary.mono_slow_Q`, `OAI.Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary.mono_slow_denominator`, `OAI.Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary.mono_slow_grid`, `OAI.Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary.mono_slow_left`, `OAI.Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary.mono_slow_modulus`, `OAI.Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary.mono_slow_right`, `OAI.Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary.mono_slow_rightCount`, `OAI.Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.exists_dictionary`, `OAI.Erdos3.RationalFilteredNilmanifold.FiniteMarkedPolynomialFreezing`, `OAI.Erdos3.RationalFilteredNilmanifold.FiniteMarkedPolynomialFreezing.bounded_cells`, `OAI.Erdos3.RationalFilteredNilmanifold.NativeMarkedFreezingPhysicalData`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.markedFrozenValue`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_nativeMarkedFreezingPhysicalData`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_bounded_cell_marked_polynomial_freezing`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_external_marked_affine_slice_freezing`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_external_marked_affine_slice_freezing_dictionary`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_finite_marked_polynomial_freezing`, `OAI.Erdos3.RationalFilteredNilmanifold.finiteMarkedPolynomialFreezing_of_factors`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeMarkedFreezingExponent`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeMarkedFreezingPhysicalParameter`, `OAI.Erdos3.RationalFilteredNilmanifold.nativeMarkedFreezingPhysicalParameter_bounds`, `OAI.Erdos3.RationalFilteredNilmanifold.subdivisionCount_le_function_card`, `OAI.Erdos3.ResidueBoxSlice.affineIntegerPoint`, `OAI.Erdos3.ResidueBoxSlice.affineIntegerPoint_residue`, `OAI.Erdos3.ResidueBoxSlice.composeSlice_integerPoint`, `OAI.Erdos3.ResidueBoxSlice.composeSlice_integerPoint_affine`, `OAI.Erdos3.ResidueBoxSlice.composeSlice_integerPoints_eq_affine_image`, `OAI.Erdos3.ResidueBoxSlice.composeSlice_integerPoints_subset`, `OAI.Erdos3.ResidueBoxSlice.composeSlice_isDenseCommonStrideBox`, `OAI.Erdos3.ResidueBoxSlice.composeSlice_isDenseCommonStrideBox_of_fraction`, `OAI.Erdos3.ResidueBoxSlice.expect_composeSlice_integerPoints`, `OAI.Erdos3.affineParentIntegerPoint`, `OAI.Erdos3.exists_long_affine_residue_cell_frozen_score_with_cell`, `OAI.Erdos3.scalarCombinedLogThreshold`, `OAI.Erdos3.scalarInitialReferenceInput`, `OAI.Erdos3.scalarInitialThreshold`, `OAI.Erdos3.scalarTransferAccuracyLog`, `OAI.Erdos3.scalarTransferCapLog`, `OAI.Erdos3.scalarTransferCellLog`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B166

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UniformFiniteMarkedPolynomialFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def FiniteMarkedPolynomialFreezing
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  ∃ N Q M m n : ℕ, 0 < N ∧ 0 < Q ∧ 0 < M ∧ 0 < m ∧ 0 < n ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2 ∧
    ∃ (left : (Fin d → Fin (N + 1)) → D.RealGroup) (right : Fin n → D.RealGroup),
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
        ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B) ∧
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid m) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group)
        (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        ∃ (leftLabel : (σ → Fin (Q + 1)) → (Fin d → Fin (N + 1)))
          (rightLabel : (σ → ZMod M) → Fin n),
          (∀ i j,
            D.filtration.realPolynomialGroupMap F φ hφ w
              (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
            D.filtration.realPolynomialGroupMap F φ hφ w
              (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
          ∀ (test : D.Niltest w)
            (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
            E * P * R = g →
            ∀ j (x : σ → ℤ), (∀ i, |(x i : ℝ)| ≤ Tbox i) →
              (∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q j i| ≤ Tbox i * (2 / Q)) →
              ‖test.observable (QuotientGroup.mk
                  (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) g)) -
                test.observable (QuotientGroup.mk
                  (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
                    (D.filtration.frozenMarkedLeft F w S hS EF (left (leftLabel j)) * P *
                      D.filtration.frozenMarkedRight F w S hS RF
                        (right (rightLabel (fun i => (x i : ZMod M)))))))‖ ≤
                (test.lipBound : ℝ) * ε

theorem finiteMarkedPolynomialFreezing_of_factors
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse S φ)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ)
    (hrat : D.FiniteMarkedRationalFactorFreezing F c φ hφ w S hS l B)
    (hslow : D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox A ε B) :
    D.FiniteMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B := by
  obtain ⟨N, Q, hN, hQ, hNc, hQc, left, hlmark, hlcap, hl⟩ := hslow
  obtain ⟨M, m, n, hM, hm, hn, hMb, hmb, hnb, right, hr, hright⟩ := hrat
  have hB0 : 0 ≤ B := (Nat.cast_nonneg n).trans hnb
  have hpair : (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2 := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using
      mul_le_mul hNc hnb (Nat.cast_nonneg n) hB0
  refine ⟨N, Q, M, m, n, hN, hQ, hM, hm, hn, hNc, hQc, hMb, hmb, hnb, hpair,
    left, right, fun j => ⟨hlmark j, hlcap j⟩, hr, ?_⟩
  intro E EF R RF hE hEF hR hRF hEmark hRmark
  obtain ⟨leftLabel, hleftLabel⟩ := hl E EF hE hEF hEmark
  obtain ⟨rightLabel, hrightLabel⟩ := hright R RF hR hRF hRmark
  refine ⟨leftLabel, rightLabel, ?_, ?_⟩
  · intro i j
    exact D.filtration.frozenMarked_factors_mark F w φ hφ S hS hsection EF RF
      (left i) (right j) (hlmark i) (hr j).1
  · intro test g P hfac j x hx hj
    obtain ⟨γ, hγ, hKR, _⟩ := hrightLabel x
    have hcoset : (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
        (fun i => (x i : ℝ))
        ((D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R)) : D.Space) =
        QuotientGroup.mk (right (rightLabel (fun i => (x i : ZMod M)))) := by
      rw [hKR]
      exact QuotientGroup.mk_mul_of_mem _ hγ
    exact (test.observable_frozenMarked_polynomial_factors F φ S hS hsection g E P R hfac
      EF RF (left (leftLabel j)) (right (rightLabel (fun i => (x i : ZMod M))))
      (hlmark _) (hr _).1 (fun i => (x i : ℝ)) hcoset).trans
        (mul_le_mul_of_nonneg_left (hleftLabel j _ hx hj) (NNReal.coe_nonneg _))

theorem exists_uniform_finite_marked_polynomial_freezing (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.FiniteMarkedPolynomialFreezing F c φ hφ w S hS l Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hparams⟩ := exists_uniform_finite_marked_factor_parameters s a u
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hboth⟩ := hparams D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp Tbox hT
  obtain ⟨hrat, hslow⟩ := hboth l hl hlp Tbox hT
  exact D.finiteMarkedPolynomialFreezing_of_factors F c φ hφ w S hS hright l Tbox
    _ _ _ hrat hslow

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteMarkedFreezingCellBound
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def BoundedCellMarkedPolynomialFreezing
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  ∃ N Q M m n : ℕ, 0 < N ∧ 0 < Q ∧ (Q : ℝ) ≤ max 1 B ∧ 0 < M ∧ 0 < m ∧ 0 < n ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2 ∧
    ∃ (left : (Fin d → Fin (N + 1)) → D.RealGroup) (right : Fin n → D.RealGroup),
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
        ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B) ∧
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid m) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group)
        (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        ∃ (leftLabel : (σ → Fin (Q + 1)) → (Fin d → Fin (N + 1)))
          (rightLabel : (σ → ZMod M) → Fin n),
          (∀ i j,
            D.filtration.realPolynomialGroupMap F φ hφ w
              (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
            D.filtration.realPolynomialGroupMap F φ hφ w
              (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
          ∀ (test : D.Niltest w)
            (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
            E * P * R = g →
            ∀ j (x : σ → ℤ), (∀ i, |(x i : ℝ)| ≤ Tbox i) →
              (∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q j i| ≤ Tbox i * (2 / Q)) →
              ‖test.observable (QuotientGroup.mk
                  (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) g)) -
                test.observable (QuotientGroup.mk
                  (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
                    (D.filtration.frozenMarkedLeft F w S hS EF (left (leftLabel j)) * P *
                      D.filtration.frozenMarkedRight F w S hS RF
                        (right (rightLabel (fun i => (x i : ZMod M)))))))‖ ≤
                (test.lipBound : ℝ) * ε

theorem subdivisionCount_le_function_card {σ : Type*} [Fintype σ] [DecidableEq σ]
    [Nonempty σ] (Q : ℕ) : Q + 1 ≤ Fintype.card (σ → Fin (Q + 1)) := by
  classical
  have hinj : Function.Injective (fun a : Fin (Q + 1) => fun _ : σ => a) := by
    intro a b hab
    exact congrFun hab (Classical.choice inferInstance)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

theorem FiniteMarkedPolynomialFreezing.bounded_cells
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A ε B : ℝ}
    (h : D.FiniteMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B) :
    D.BoundedCellMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B := by
  obtain ⟨N, Q, M, m, n, hN, hQ, hM, hm, hn, hNc, hQc, hMb, hmb, hnb, hpair,
    left, right, hl, hr, hfreeze⟩ := h
  cases isEmpty_or_nonempty σ with
  | inr hne =>
    let : Nonempty σ := hne
    have hQb : (Q : ℝ) ≤ max 1 B := by
      have hQc' : ((Q + 1 : ℕ) : ℝ) ≤ B :=
        (Nat.cast_le.mpr (subdivisionCount_le_function_card (σ := σ) Q)).trans hQc
      exact (show (Q : ℝ) ≤ B by push_cast at hQc'; linarith).trans (le_max_right _ _)
    exact ⟨N, Q, M, m, n, hN, hQ, hQb, hM, hm, hn, hNc, hQc, hMb, hmb, hnb,
      hpair, left, right, hl, hr, hfreeze⟩
  | inl hempty =>
    let : IsEmpty σ := hempty
    have hone : (1 : ℝ) ≤ B :=
      (show (1 : ℝ) ≤ n by exact_mod_cast hn).trans hnb
    have hcard : (Fintype.card (σ → Fin (1 + 1)) : ℝ) ≤ B := by simpa using hone
    refine ⟨N, 1, M, m, n, hN, by omega, ?_, hM, hm, hn, hNc, hcard, hMb, hmb,
      hnb, hpair, left, right, hl, hr, ?_⟩
    · simpa only [Nat.cast_one] using le_max_left (1 : ℝ) B
    · intro E EF R RF hE hEF hR hRF hEproj hRproj
      obtain ⟨leftLabel, rightLabel, hmarks, herror⟩ := hfreeze E EF R RF
        hE hEF hR hRF hEproj hRproj
      let emptyCell : σ → Fin (Q + 1) := fun i => isEmptyElim i
      refine ⟨fun _ => leftLabel emptyCell, rightLabel, hmarks, ?_⟩
      intro test g P hfac j x hx hj
      exact herror test g P hfac emptyCell x hx (fun i => isEmptyElim i)

theorem exists_uniform_bounded_cell_marked_polynomial_freezing (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.BoundedCellMarkedPolynomialFreezing F c φ hφ w S hS l Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hbase⟩ := exists_uniform_finite_marked_polynomial_freezing s a u
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hfreeze⟩ := hbase D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  exact ⟨S, hS, hright, hSb, fun l hl hlp Tbox hT =>
    (hfreeze l hl hlp Tbox hT).bounded_cells⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

noncomputable def scalarTransferCapLog (b : ℕ) (Z : ℝ) : ℝ := (b : ℝ) * (Z + 2) + 1

noncomputable def scalarTransferAccuracyLog (b : ℕ) (p Z : ℝ) : ℝ :=
  3 * p + scalarTransferCapLog b Z + 10

noncomputable def scalarTransferCellLog (common : ℝ) (b : ℕ) (p Z U : ℝ) : ℝ :=
  65536 * (common + 3) ^ 4 + Z * b + scalarTransferAccuracyLog b p Z + U + 1

end Erdos3

end

section

namespace Erdos3

noncomputable def scalarInitialReferenceInput (m n d : ℕ) (p P0 : ℝ) : ℝ :=
  let Z := replacementCommonInputLog m n d P0
  let G := 2 * physicalPairCoefficientLog n d Z + 2
  G + Z + P0 + m + n + d + scalarTransferTail (3 * p) + p + 20

end Erdos3

end

section

namespace Erdos3

noncomputable def scalarCombinedLogThreshold (n d b : ℕ)
    (p P0 Z G refCost cellLog meshLog : ℝ) : ℝ :=
  refCost + p + scalarTransferTail (3 * p) + 2 * physicalReplacementThresholdLog n d b Z +
    G + P0 + 4 * meshLog + 2 * cellLog + 2 * Z + 100

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformExternalMarkedAffineSliceFreezingDictionary
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

variable {ι : Type*} {N : ι → ℕ} {q : ℕ}

def affineIntegerPoint (A : ResidueBoxSlice N q) (origin : ι → ℤ) (step : ℕ)
    (j : ∀ i, Fin (A.length i)) : ι → ℤ :=
  fun i => origin i + step * (A.point j i).val

theorem affineIntegerPoint_residue (A : ResidueBoxSlice N q)
    (origin : ι → ℤ) (step : ℕ) (j : ∀ i, Fin (A.length i)) :
    (fun i => (A.affineIntegerPoint origin step j i : ZMod q)) =
      fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q) := by
  funext i
  simp only [affineIntegerPoint, point, Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul,
    Int.cast_natCast]
  simp

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3
open scoped BigOperators

def affineParentIntegerPoint {ι : Type*} (N : ι → ℕ)
    (origin : ι → ℤ) (step : ℕ) (x : ∀ i, Fin (N i)) : ι → ℤ :=
  fun i => origin i + step * (x i).val

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

theorem exists_long_affine_residue_cell_frozen_score_with_cell
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (origin : ι → ℤ) (step : ℕ) (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |(origin i : ℝ) + step * n| ≤ T i)
    (hparentwidth : ∀ i, (step : ℝ) * N i ≤ 2 * T i)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ (1 / (Q : ℝ)) * N i)
    (score : (ι → ℤ) → ℝ) (f : (ι → ℤ) → ℂ)
    (frozen : I → J → (ι → ℤ) → ℂ)
    (leftLabel : (ι → Fin (Q + 1)) → I) (rightLabel : (ι → ZMod q) → J)
    {B τ ε θ S : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hθ : 0 < θ)
    (hscoreBound : ∀ x : ι → ℤ, (∀ i, |(x i : ℝ)| ≤ T i) → |score x| ≤ 1)
    (hcap : ∀ x : ι → ℤ, (∀ i, |(x i : ℝ)| ≤ T i) → score x * (f x).re ≤ B)
    (hfreeze : ∀ a (x : ι → ℤ), (∀ i, |(x i : ℝ)| ≤ T i) →
      (∀ i, |(x i : ℝ) - normalizedRealBoxGrid T Q a i| ≤ T i * (2 / Q)) →
      ‖f x - frozen (leftLabel a) (rightLabel (fun i => (x i : ZMod q))) x‖ ≤ ε)
    (hscore : S ≤ 𝔼 x : (∀ i, Fin (N i)),
      score (affineParentIntegerPoint N origin step x) *
        (f (affineParentIntegerPoint N origin step x)).re)
    (hbudget : τ + ε + B * θ < S) :
    ∃ A : ResidueBoxSlice N q, (∀ i, 0 < A.length i) ∧
      (∀ i, θ * N i / (4 * q * Q * (Fintype.card ι + 1 : ℝ)) ≤ A.length i) ∧
      ∃ z : ι → Fin (Q + 1),
        (∀ (j : ∀ i, Fin (A.length i)) i,
          |(A.affineIntegerPoint origin step j i : ℝ) -
            normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) ∧
        (∀ j : ∀ i, Fin (A.length i),
          ‖f (A.affineIntegerPoint origin step j) -
            frozen (leftLabel z)
              (rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q)))
              (A.affineIntegerPoint origin step j)‖ ≤ ε) ∧
        τ < 𝔼 j : (∀ i, Fin (A.length i)),
          score (A.affineIntegerPoint origin step j) *
            (frozen (leftLabel z)
              (rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q)))
              (A.affineIntegerPoint origin step j)).re := by
  classical
  let point := affineParentIntegerPoint N origin step
  let residue := fun r : ι → ZMod q => fun i => (origin i : ZMod q) + (step : ZMod q) * r i
  let V := fun r z x => (frozen (leftLabel z) (rightLabel (residue r)) (point x)).re
  have hbound (x : ∀ i, Fin (N i)) (i) : |(point x i : ℝ)| ≤ T i := by
    simpa only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
      Int.cast_natCast] using hparent i (x i).val (x i).isLt
  have hclose (r : ι → ZMod q) (z : ι → Fin (Q + 1)) (x : ∀ i, Fin (N i))
      (hr : ∀ i, ((x i).val : ZMod q) = r i)
      (hz : ∀ i, |(origin i : ℝ) + (step : ℝ) * (x i).val -
        normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) :
      dist (f (point x)).re (V r z x) ≤ ε := by
    have hres : (fun i => (point x i : ZMod q)) = residue r := by
      funext i
      simp only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast, hr, residue]
    have hcell (i) : |(point x i : ℝ) - normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
      simpa only [point, affineParentIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast] using hz i
    have hn := hfreeze z (point x) (hbound x) hcell
    rw [hres] at hn
    exact (show dist (f (point x)).re (V r z x) ≤
        ‖f (point x) - frozen (leftLabel z) (rightLabel (residue r)) (point x)‖ by
      simpa only [Real.dist_eq, V, Complex.sub_re] using
        Complex.abs_re_le_norm (f (point x) -
          frozen (leftLabel z) (rightLabel (residue r)) (point x))).trans hn
  obtain ⟨A, hlen, hlong, r, z, hr, hz, hs⟩ := exists_long_residue_cell_frozen_score
    N hN q Q hq hQ (fun i => (origin i : ℝ)) (step : ℝ) (Nat.cast_nonneg _)
    T hT hparent hparentwidth hlarge (fun x => score (point x)) (fun x => (f (point x)).re)
    V hB hτ hε hθ (fun x => hscoreBound (point x) (hbound x))
    (fun x => hcap (point x) (hbound x)) hclose hscore hbudget
  let jzero : ∀ i, Fin (A.length i) := fun i => ⟨0, hlen i⟩
  have hrstart : ∀ i, (A.start i : ZMod q) = r i := by
    intro i
    simpa only [ResidueBoxSlice.point, jzero, Nat.mul_zero, Nat.add_zero] using hr jzero i
  have hresidue : residue r =
      fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod q) := by
    funext i
    simp only [residue, Int.cast_add, Int.cast_mul, Int.cast_natCast, hrstart]
  have hcell (j : ∀ i, Fin (A.length i)) (i) :
      |(A.affineIntegerPoint origin step j i : ℝ) -
        normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q) := by
    simpa only [ResidueBoxSlice.affineIntegerPoint, Int.cast_add, Int.cast_mul,
      Int.cast_natCast] using hz j i
  refine ⟨A, hlen, hlong, z, hcell, ?_, ?_⟩
  · intro j
    have hn := hfreeze z (A.affineIntegerPoint origin step j) (hbound (A.point j)) (hcell j)
    simpa only [A.affineIntegerPoint_residue origin step j] using hn
  · dsimp only [V] at hs
    rw [hresidue] at hs
    exact hs

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} {N : I → ℕ} {q r : ℕ}

theorem composeSlice_integerPoint (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (j : ∀ i, Fin (T.length i)) :
    (S.composeSlice T).integerPoint j = S.integerPoint (T.point j) := by
  unfold integerPoint
  rw [S.composeSlice_point T]

theorem composeSlice_integerPoint_affine (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (j : ∀ i, Fin (T.length i)) :
    (S.composeSlice T).integerPoint j =
      T.affineIntegerPoint (fun i => (S.start i : ℤ)) q j := by
  rw [S.composeSlice_integerPoint T]
  funext i
  simp only [integerPoint, point, affineIntegerPoint, Nat.cast_add, Nat.cast_mul]

variable [Fintype I] [DecidableEq I]

theorem composeSlice_integerPoints_eq_affine_image (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) :
    (S.composeSlice T).integerPoints =
      Finset.univ.image (T.affineIntegerPoint (fun i => (S.start i : ℤ)) q) := by
  unfold integerPoints
  apply Finset.image_congr
  intro j _
  exact S.composeSlice_integerPoint_affine T j

theorem composeSlice_integerPoints_subset (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) :
    (S.composeSlice T).integerPoints ⊆ S.integerPoints := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr
    ⟨T.point j, Finset.mem_univ _, (S.composeSlice_integerPoint T j).symm⟩

theorem expect_composeSlice_integerPoints (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (hq : 0 < q) (hr : 0 < r)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : (I → ℤ) → V) :
    (𝔼 x ∈ (S.composeSlice T).integerPoints, f x) =
      𝔼 j : (∀ i, Fin (T.length i)),
        f (T.affineIntegerPoint (fun i => (S.start i : ℤ)) q j) := by
  rw [(S.composeSlice T).expect_integerPoints (Nat.mul_pos hq hr) f]
  apply Finset.expect_congr rfl
  intro j _
  exact congrArg f (S.composeSlice_integerPoint_affine T j)

theorem composeSlice_isDenseCommonStrideBox (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (hq : 0 < q) (hr : 0 < r)
    {cost loss : ℝ} (hS : IsDenseCommonStrideBox N cost S.integerPoints)
    (hT : ∀ i, (S.length i : ℝ) * Real.exp (-loss) ≤ (T.length i : ℝ)) :
    IsDenseCommonStrideBox N (cost + loss) (S.composeSlice T).integerPoints := by
  refine ⟨fun i => ((S.composeSlice T).start i : ℤ), q * r,
    (S.composeSlice T).length, Nat.mul_pos hq hr, ?_,
    (S.composeSlice T).progression_inside, ?_,
    (S.composeSlice T).integerPoints_eq_commonStrideBox⟩
  · intro i
    have hpos : (0 : ℝ) < T.length i :=
      (mul_pos (Nat.cast_pos.mpr (S.length_pos_of_dense hS i))
        (Real.exp_pos _)).trans_le (hT i)
    exact_mod_cast hpos
  · exact S.composeSlice_length_lower T (S.length_lower_of_dense hq hS) hT

theorem composeSlice_isDenseCommonStrideBox_of_fraction (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (hq : 0 < q) (hr : 0 < r)
    {cost θ denominator : ℝ} (hS : IsDenseCommonStrideBox N cost S.integerPoints)
    (hθ : 0 < θ) (hdenominator : 0 < denominator)
    (hT : ∀ i, θ * S.length i / denominator ≤ (T.length i : ℝ)) :
    IsDenseCommonStrideBox N (cost + Real.log (denominator / θ))
      (S.composeSlice T).integerPoints := by
  apply S.composeSlice_isDenseCommonStrideBox T hq hr hS
  intro i
  simpa only [Real.exp_neg, Real.exp_log (div_pos hdenominator hθ), inv_div,
    ← mul_div_assoc, mul_comm (S.length i : ℝ) θ] using hT i

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

noncomputable def Niltest.markedFrozenValue
    {σ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d} {v : σ → ℕ}
    (test : D.Niltest v) (F : NilpotentLieFiltration T t) (w : σ → ℕ)
    (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (EF RF : (F.realification.adaptedPolynomialFiltration w).Group)
    (P : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (kE kR : D.RealGroup) (x : σ → ℤ) : ℂ :=
  test.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
    (fun i => (x i : ℝ)) (D.filtration.frozenMarkedLeft F w S hS EF kE * P *
      D.filtration.frozenMarkedRight F w S hS RF kR)))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

def ExternalMarkedAffineSliceFreezing
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  ∃ N Q M m n : ℕ, 0 < N ∧ 0 < Q ∧ (Q : ℝ) ≤ max 1 B ∧ 0 < M ∧ 0 < m ∧ 0 < n ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2 ∧
    ∃ (left : (Fin d → Fin (N + 1)) → D.RealGroup) (right : Fin n → D.RealGroup),
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
        ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B) ∧
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid m) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group)
        (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        (∀ i j,
          D.filtration.realPolynomialGroupMap F φ hφ w
            (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
          D.filtration.realPolynomialGroupMap F φ hφ w
            (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
        ∀ (tests : X → D.Niltest w) (physical : (σ → ℤ) → X)
          (weight : (σ → ℤ) → ℂ) (Bweight Bobs Lip : ℝ),
          0 ≤ Bweight → 0 ≤ Bobs → 0 ≤ Lip →
          (∀ x : σ → ℤ, (∀ i, |(x i : ℝ)| ≤ Tbox i) → ‖weight x‖ ≤ Bweight) →
          (∀ z, ((tests z).normBound : ℝ) ≤ Bobs) →
          (∀ z, ((tests z).lipBound : ℝ) ≤ Lip) →
          ∀ (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
          E * P * R = g →
          ∀ Nparent : σ → ℕ, (∀ i, 0 < Nparent i) →
          ∀ (origin : σ → ℤ) (step : ℕ),
          (∀ i v, v < Nparent i → |(origin i : ℝ) + step * v| ≤ Tbox i) →
          (∀ i, (step : ℝ) * Nparent i ≤ 2 * Tbox i) →
          (∀ i, 2 * (M : ℝ) ≤ (1 / (Q : ℝ)) * Nparent i) →
          ∀ τ θ Sscore : ℝ, 0 ≤ τ → 0 < θ →
          (Sscore ≤ 𝔼 x : (∀ i, Fin (Nparent i)),
            (weight (affineParentIntegerPoint Nparent origin step x) *
              (tests (physical (affineParentIntegerPoint Nparent origin step x))).observable
                (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                  (fun i => (affineParentIntegerPoint Nparent origin step x i : ℝ)) g))).re) →
          τ + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < Sscore →
          ∃ A : ResidueBoxSlice Nparent M, (∀ i, 0 < A.length i) ∧
            (∀ i, θ * Nparent i / (4 * M * Q * (Fintype.card σ + 1 : ℝ)) ≤ A.length i) ∧
            ∃ i j,
              (∀ x : ∀ i, Fin (A.length i),
                ‖(tests (physical (A.affineIntegerPoint origin step x))).observable
                    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                      (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
                  (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                    F w S hS EF RF P (left i) (right j)
                    (A.affineIntegerPoint origin step x)‖ ≤ Lip * ε) ∧
              (∀ x : ∀ i, Fin (A.length i),
                ‖weight (A.affineIntegerPoint origin step x) *
                    (tests (physical (A.affineIntegerPoint origin step x))).observable
                      (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                        (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
                  weight (A.affineIntegerPoint origin step x) *
                    (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                      F w S hS EF RF P (left i) (right j)
                      (A.affineIntegerPoint origin step x)‖ ≤ Bweight * (Lip * ε)) ∧
              τ < 𝔼 x : (∀ i, Fin (A.length i)),
                (weight (A.affineIntegerPoint origin step x) *
                  (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                    F w S hS EF RF P (left i) (right j)
                    (A.affineIntegerPoint origin step x)).re

theorem BoundedCellMarkedPolynomialFreezing.external_affine_slice
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A ε B : ℝ}
    (hfreeze : D.BoundedCellMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B)
    (hT : ∀ i, 0 < Tbox i) (hε : 0 ≤ ε) :
    D.ExternalMarkedAffineSliceFreezing (X := X) F c φ hφ w S hS l Tbox A ε B := by
  obtain ⟨N, Q, M, m, n, hN, hQ, hQb, hM, hm, hn, hNc, hQc, hMb, hmb, hnb,
    hpair, left, right, hl, hr, hfreeze⟩ := hfreeze
  refine ⟨N, Q, M, m, n, hN, hQ, hQb, hM, hm, hn, hNc, hQc, hMb, hmb, hnb,
    hpair, left, right, hl, hr, ?_⟩
  intro E EF R RF hE hEF hR hRF hEproj hRproj
  obtain ⟨leftLabel, rightLabel, hmarks, herror⟩ := hfreeze E EF R RF hE hEF hR hRF hEproj hRproj
  refine ⟨hmarks, ?_⟩
  intro tests physical weight Bweight Bobs Lip hBw hBo hLip hweight hnorm hlip
    g P hfac Nparent hNp origin step hparent hwidth hlarge τ θ Sscore hτ hθ hscore hbudget
  let observed : (σ → ℤ) → ℂ := fun x => (tests (physical x)).observable
    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) g))
  let frozen := fun i j x => (tests (physical x)).markedFrozenValue
    F w S hS EF RF P (left i) (right j) x
  let weighted := fun x => weight x * observed x
  let weightedFrozen := fun i j x => weight x * frozen i j x
  have hcap (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ Tbox i) :
      (1 : ℝ) * (weighted x).re ≤ Bweight * Bobs := by
    have ho : ‖observed x‖ ≤ Bobs := ((tests (physical x)).norm_le _).trans (hnorm _)
    calc
      _ = (weighted x).re := one_mul _
      _ ≤ ‖weighted x‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ = ‖weight x‖ * ‖observed x‖ := norm_mul _ _
      _ ≤ Bweight * Bobs := mul_le_mul (hweight x hx) ho (norm_nonneg _) hBw
  have hpoint (a) (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ Tbox i)
      (ha : ∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q a i| ≤ Tbox i * (2 / Q)) :
      ‖observed x - frozen (leftLabel a) (rightLabel (fun i => (x i : ZMod M))) x‖ ≤
        Lip * ε :=
    (herror (tests (physical x)) g P hfac a x hx ha).trans
      (mul_le_mul_of_nonneg_right (hlip _) hε)
  have hclose (a) (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ Tbox i)
      (ha : ∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q a i| ≤ Tbox i * (2 / Q)) :
      ‖weighted x - weightedFrozen (leftLabel a)
        (rightLabel (fun i => (x i : ZMod M))) x‖ ≤ Bweight * (Lip * ε) := by
    change ‖weight x * observed x - weight x * frozen _ _ x‖ ≤ _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (hweight x hx) (hpoint a x hx ha) (norm_nonneg _) hBw
  obtain ⟨A, hlen, hlong, z, hcell, herr, hretained⟩ :=
    exists_long_affine_residue_cell_frozen_score_with_cell
      Nparent hNp M Q hM hQ origin step Tbox hT hparent hwidth hlarge
      (fun _ => (1 : ℝ)) weighted weightedFrozen leftLabel rightLabel
      (mul_nonneg hBw hBo) hτ (mul_nonneg hBw (mul_nonneg hLip hε)) hθ
      (fun _ _ => by norm_num) hcap hclose
      (by simpa only [one_mul] using hscore) hbudget
  refine ⟨A, hlen, hlong, leftLabel z,
    rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod M)), ?_, herr, ?_⟩
  · intro x
    have hx (i) : |(A.affineIntegerPoint origin step x i : ℝ)| ≤ Tbox i := by
      simpa only [ResidueBoxSlice.affineIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast] using hparent i (A.point x i).val (A.point x i).isLt
    have hp := hpoint z (A.affineIntegerPoint origin step x) hx (hcell x)
    simpa only [A.affineIntegerPoint_residue origin step x] using hp
  · simpa only [one_mul] using hretained

theorem exists_uniform_external_marked_affine_slice_freezing (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.ExternalMarkedAffineSliceFreezing (X := X) F c φ hφ w S hS l Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hbase⟩ := exists_uniform_bounded_cell_marked_polynomial_freezing s a u
  refine ⟨C, hC, ?_⟩
  intro X σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hfreeze⟩ := hbase D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  exact ⟨S, hS, hright, hSb, fun l hl hlp Tbox hT =>
    (hfreeze l hl hlp Tbox hT).external_affine_slice hT (Real.exp_nonneg _)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

namespace ExternalMarkedAffineSliceFreezing

structure Dictionary
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) where
  grid : ℕ
  Q : ℕ
  modulus : ℕ
  denominator : ℕ
  rightCount : ℕ
  grid_pos : 0 < grid
  Q_pos : 0 < Q
  modulus_pos : 0 < modulus
  denominator_pos : 0 < denominator
  rightCount_pos : 0 < rightCount
  Q_bound : (Q : ℝ) ≤ max 1 B
  gridCard_bound : (Fintype.card (Fin d → Fin (grid + 1)) : ℝ) ≤ B
  cellCard_bound : (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B
  modulus_bound : (modulus : ℝ) ≤ B
  denominator_bound : (denominator : ℝ) ≤ B
  rightCount_bound : (rightCount : ℝ) ≤ B
  pairCard_bound : (Fintype.card ((Fin d → Fin (grid + 1)) × Fin rightCount) : ℝ) ≤ B ^ 2
  left : (Fin d → Fin (grid + 1)) → D.RealGroup
  right : Fin rightCount → D.RealGroup
  left_bounds : ∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
    ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B
  right_bounds : ∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
    (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
    (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid denominator
  select : ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (EF : (F.realification.adaptedPolynomialFiltration w).Group)
    (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (RF : (F.realification.adaptedPolynomialFiltration w).Group),
    D.filtration.PolynomialSlowBound D.basis w Tbox A E →
    F.PolynomialSlowBound c w Tbox A EF →
    D.filtration.PolynomialRationalGrid D.basis w l R →
    F.PolynomialRationalGrid c w l RF →
    D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
    D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
    (∀ i j,
      D.filtration.realPolynomialGroupMap F φ hφ w
        (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
      D.filtration.realPolynomialGroupMap F φ hφ w
        (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
    ∀ (tests : X → D.Niltest w) (physical : (σ → ℤ) → X)
      (weight : (σ → ℤ) → ℂ) (Bweight Bobs Lip : ℝ),
      0 ≤ Bweight → 0 ≤ Bobs → 0 ≤ Lip →
      (∀ x : σ → ℤ, (∀ i, |(x i : ℝ)| ≤ Tbox i) → ‖weight x‖ ≤ Bweight) →
      (∀ z, ((tests z).normBound : ℝ) ≤ Bobs) →
      (∀ z, ((tests z).lipBound : ℝ) ≤ Lip) →
      ∀ (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
      E * P * R = g →
      ∀ Nparent : σ → ℕ, (∀ i, 0 < Nparent i) →
      ∀ (origin : σ → ℤ) (step : ℕ),
      (∀ i v, v < Nparent i → |(origin i : ℝ) + step * v| ≤ Tbox i) →
      (∀ i, (step : ℝ) * Nparent i ≤ 2 * Tbox i) →
      (∀ i, 2 * (modulus : ℝ) ≤ (1 / (Q : ℝ)) * Nparent i) →
      ∀ τ θ Sscore : ℝ, 0 ≤ τ → 0 < θ →
      (Sscore ≤ 𝔼 x : (∀ i, Fin (Nparent i)),
        (weight (affineParentIntegerPoint Nparent origin step x) *
          (tests (physical (affineParentIntegerPoint Nparent origin step x))).observable
            (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
              (fun i => (affineParentIntegerPoint Nparent origin step x i : ℝ)) g))).re) →
      τ + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < Sscore →
      ∃ A : ResidueBoxSlice Nparent modulus, (∀ i, 0 < A.length i) ∧
        (∀ i, θ * Nparent i / (4 * modulus * Q * (Fintype.card σ + 1 : ℝ)) ≤ A.length i) ∧
        ∃ i j,
          (∀ x : ∀ i, Fin (A.length i),
            ‖(tests (physical (A.affineIntegerPoint origin step x))).observable
                (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                  (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
              (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                F w S hS EF RF P (left i) (right j)
                (A.affineIntegerPoint origin step x)‖ ≤ Lip * ε) ∧
          (∀ x : ∀ i, Fin (A.length i),
            ‖weight (A.affineIntegerPoint origin step x) *
                (tests (physical (A.affineIntegerPoint origin step x))).observable
                  (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                    (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
              weight (A.affineIntegerPoint origin step x) *
                (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                  F w S hS EF RF P (left i) (right j)
                  (A.affineIntegerPoint origin step x)‖ ≤ Bweight * (Lip * ε)) ∧
          τ < 𝔼 x : (∀ i, Fin (A.length i)),
            (weight (A.affineIntegerPoint origin step x) *
              (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                F w S hS EF RF P (left i) (right j)
                (A.affineIntegerPoint origin step x)).re

theorem exists_dictionary
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A ε B : ℝ}
    (hfreeze : D.ExternalMarkedAffineSliceFreezing (X := X) F c φ hφ w S hS l Tbox A ε B) :
    Nonempty (Dictionary (X := X) D F c φ hφ w S hS l Tbox A ε B) := by
  obtain ⟨grid, Q, modulus, denominator, rightCount, hgrid, hQ, hQbound,
    hmodulus, hdenominator, hrightCount, hgridCard, hcellCard, hmodulusBound,
    hdenominatorBound, hrightCountBound, hpairCard, left, right, hleft, hright,
    hselect⟩ := hfreeze
  exact ⟨⟨grid, Q, modulus, denominator, rightCount, hgrid, hQ, hmodulus,
    hdenominator, hrightCount, hQbound, hgridCard, hcellCard, hmodulusBound,
    hdenominatorBound, hrightCountBound, hpairCard, left, right, hleft, hright,
    hselect⟩⟩

end ExternalMarkedAffineSliceFreezing

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary

open Module
open scoped TensorProduct

variable {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A A' ε B : ℝ}
    (dictionary : Dictionary (X := X) D F c φ hφ w S hS l Tbox A ε B)

def mono_slow (hT : ∀ i, 0 < Tbox i) (hslow : A' ≤ A) :
    Dictionary (X := X) D F c φ hφ w S hS l Tbox A' ε B where
  grid := dictionary.grid
  Q := dictionary.Q
  modulus := dictionary.modulus
  denominator := dictionary.denominator
  rightCount := dictionary.rightCount
  grid_pos := dictionary.grid_pos
  Q_pos := dictionary.Q_pos
  modulus_pos := dictionary.modulus_pos
  denominator_pos := dictionary.denominator_pos
  rightCount_pos := dictionary.rightCount_pos
  Q_bound := dictionary.Q_bound
  gridCard_bound := dictionary.gridCard_bound
  cellCard_bound := dictionary.cellCard_bound
  modulus_bound := dictionary.modulus_bound
  denominator_bound := dictionary.denominator_bound
  rightCount_bound := dictionary.rightCount_bound
  pairCard_bound := dictionary.pairCard_bound
  left := dictionary.left
  right := dictionary.right
  left_bounds := dictionary.left_bounds
  right_bounds := dictionary.right_bounds
  select := by
    intro E EF R RF hE hEF
    exact dictionary.select E EF R RF
      (D.filtration.polynomialSlowBound_mono D.basis w Tbox hT hslow E hE)
      (F.polynomialSlowBound_mono c w Tbox hT hslow EF hEF)

variable (hT : ∀ i, 0 < Tbox i) (hslow : A' ≤ A)

@[simp] theorem mono_slow_grid :
    (dictionary.mono_slow hT hslow).grid = dictionary.grid := rfl

@[simp] theorem mono_slow_Q :
    (dictionary.mono_slow hT hslow).Q = dictionary.Q := rfl

@[simp] theorem mono_slow_modulus :
    (dictionary.mono_slow hT hslow).modulus = dictionary.modulus := rfl

@[simp] theorem mono_slow_denominator :
    (dictionary.mono_slow hT hslow).denominator = dictionary.denominator := rfl

@[simp] theorem mono_slow_rightCount :
    (dictionary.mono_slow hT hslow).rightCount = dictionary.rightCount := rfl

@[simp] theorem mono_slow_left :
    (dictionary.mono_slow hT hslow).left = dictionary.left := rfl

@[simp] theorem mono_slow_right :
    (dictionary.mono_slow hT hslow).right = dictionary.right := rfl

end Erdos3.RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_external_marked_affine_slice_freezing_dictionary (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            ∀ slow : ℝ, slow ≤ Real.exp ((p + 2) ^ a) →
              Nonempty (ExternalMarkedAffineSliceFreezing.Dictionary (X := X)
                D F c φ hφ w S hS l Tbox slow (Real.exp (-((p + 2) ^ u)))
                (Real.exp ((p + C) ^ C))) := by
  obtain ⟨C, hC, hbase⟩ := exists_uniform_external_marked_affine_slice_freezing s a u
  refine ⟨C, hC, ?_⟩
  intro X σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hfreeze⟩ := hbase D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp Tbox hT slow hslow
  obtain ⟨dictionary⟩ := (hfreeze l hl hlp Tbox hT).exists_dictionary
  exact ⟨dictionary.mono_slow hT hslow⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedFreezingPhysicalData
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

noncomputable def nativeMarkedFreezingExponent (s a : ℕ) : ℕ :=
  Classical.choose
    (exists_uniform_external_marked_affine_slice_freezing_dictionary.{0, 0, 0, 0, 0} s a 3)

def nativeMarkedFreezingPhysicalParameter (p : ℝ) (C : ℕ) : ℝ :=
  (p + 3) ^ 36 + (p + C) ^ C

theorem nativeMarkedFreezingPhysicalParameter_bounds {p : ℝ} (hp : 0 ≤ p) (C : ℕ) :
    p ≤ nativeMarkedFreezingPhysicalParameter p C ∧
      (p + C) ^ C ≤ nativeMarkedFreezingPhysicalParameter p C ∧
      (p + 3) ^ 7 ≤ nativeMarkedFreezingPhysicalParameter p C ∧
      p + 1 ≤ nativeMarkedFreezingPhysicalParameter p C := by
  have hbase : 1 ≤ p + 3 := by linarith
  have hpow : (p + 3) ^ 7 ≤ (p + 3) ^ 36 := pow_le_pow_right₀ hbase (by decide)
  have hinput : p + 1 ≤ (p + 3) ^ 36 := by
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      (le_power_budget (show 0 ≤ p + 1 by linarith) (by decide : 1 ≤ 36))
  have hbudget : 0 ≤ (p + C) ^ C := by positivity
  have hfirst : (p + 3) ^ 36 ≤ nativeMarkedFreezingPhysicalParameter p C :=
    le_add_of_nonneg_right hbudget
  refine ⟨(by linarith [hinput.trans hfirst]), ?_, hpow.trans hfirst, hinput.trans hfirst⟩
  exact le_add_of_nonneg_left (by positivity)

variable {X σ κ L T : Type} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
    (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (l : ℕ) (Tbox : σ → ℝ) (slow p : ℝ) (C : ℕ)

structure NativeMarkedFreezingPhysicalData where
  sectionMap : T →ₗ[ℚ] L
  section_filtered : ∀ j, ∀ y ∈ F.layer j, sectionMap y ∈ D.filtration.layer j
  section_rightInverse : Function.RightInverse sectionMap φ
  section_height : ∀ i j, RationalHeightLE
    (LinearMap.toMatrix c D.basis sectionMap i j)
    (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)
  section_height_bound :
    (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (nativeMarkedFreezingPhysicalParameter p C)
  dictionary : ExternalMarkedAffineSliceFreezing.Dictionary (X := X)
    D F c φ hφ w sectionMap section_filtered l Tbox slow
    (Real.exp (-((p + 2) ^ 3))) (Real.exp ((p + C) ^ C))
  denominator_bound :
    ((matrixDenominator (LinearMap.toMatrix c D.basis sectionMap) * l *
      dictionary.denominator : ℕ) : ℝ) ≤
        Real.exp (nativeMarkedFreezingPhysicalParameter p C)

omit C in

theorem exists_nativeMarkedFreezingPhysicalData
    (a : ℕ)
    (ω : Fin d → ℕ)
    (hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (τ : κ → ℕ)
    (hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (hsurj : ∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hw : ∀ i, 0 < w i) (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hmap : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p)
    (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p)
    (hT : ∀ i, 0 < Tbox i) (hslow : slow ≤ Real.exp ((p + 2) ^ a)) :
    Nonempty (NativeMarkedFreezingPhysicalData (X := X) D F c φ hφ w l Tbox slow p
      (nativeMarkedFreezingExponent s a)) := by
  let C := nativeMarkedFreezingExponent s a
  obtain ⟨sectionMap, hsection, hright, hheight, hdict⟩ :=
    (Classical.choose_spec
      (exists_uniform_external_marked_affine_slice_freezing_dictionary.{0, 0, 0, 0, 0} s a 3)).2
      (X := X) D F c ω hDlayers τ hFlayers φ hφ hsurj w hw p hp hD hσ hκ hmap
  obtain ⟨dictionary⟩ := hdict l hl hlp Tbox hT slow hslow
  have hp1 : 0 ≤ p + 1 := by linarith
  have hp_le : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have hceil : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hmatrix : ∀ i j, RationalHeightLE (LinearMap.toMatrix c D.basis sectionMap i j)
      (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊) := by
    simpa only [LinearMap.toMatrix_apply] using hheight
  have hsectionBound := rationalKernelHeight_le_budget (Fintype.card κ) ⌈Real.exp p⌉₊
    hp1 (hκ.trans hp_le) hceil
  have hden := real_image_section_denominator_bound
    (LinearMap.toMatrix c D.basis sectionMap) ⌈Real.exp p⌉₊ l hmatrix hp1
    (hκ.trans hp_le) (by simpa only [Fintype.card_fin] using hD.1.trans hp_le)
    hceil (hlp.trans (Real.exp_le_exp.mpr hp_le))
  have hb := nativeMarkedFreezingPhysicalParameter_bounds hp C
  refine ⟨⟨sectionMap, hsection, hright, hmatrix, ?_, dictionary, ?_⟩⟩
  · exact hsectionBound.trans (Real.exp_le_exp.mpr (by
      simpa only [show p + 1 + 2 = p + 3 by ring] using hb.2.2.1))
  · calc
      _ = ((matrixDenominator (LinearMap.toMatrix c D.basis sectionMap) * l : ℕ) : ℝ) *
          dictionary.denominator := by rw [Nat.cast_mul]
      _ ≤ Real.exp ((p + 1 + 2) ^ 36) * Real.exp ((p + C) ^ C) :=
        mul_le_mul hden dictionary.denominator_bound (Nat.cast_nonneg _)
          (Real.exp_nonneg _)
      _ = Real.exp (nativeMarkedFreezingPhysicalParameter p C) := by
        rw [← Real.exp_add]
        congr 1
        simp only [nativeMarkedFreezingPhysicalParameter, show p + 1 + 2 = p + 3 by ring]

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarInitialThreshold
namespace OAI

section

namespace Erdos3

noncomputable def scalarInitialThreshold (E m n d : ℕ) (epsilon p P0 : ℝ) : ℝ :=
  let Z := replacementCommonInputLog m n d P0
  let G := 2 * physicalPairCoefficientLog n d Z + 2
  let U := scalarInitialReferenceInput m n d p P0
  let pref := affineReferenceInput epsilon U
  let common := affineCommonReferenceBudget E epsilon U
  let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
    (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
  scalarCombinedLogThreshold n d b p P0 Z G ((pref + 2) ^ E)
    (scalarTransferCellLog common b p Z U)
    (scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.UnconditionedJointFrameDomination
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open FiniteProbabilityWeights
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

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


