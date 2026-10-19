-- Prove2me | Definitions.Def_OAIE3v2B231
-- name    : OAIE3v2B231
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:37:48.214159+00:00
-- url     : https://prove2.me/theorems/ada4c6cc-a162-4038-a35a-12459bd4b6f1
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 236 of 311
-- statement:
--   Definitions bundle 236 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199`, `OAIE3v2B204`, `OAIE3v2B205`, `OAIE3v2B206`, `OAIE3v2B207`, `OAIE3v2B210`, `OAIE3v2B211`, `OAIE3v2B212`, `OAIE3v2B214` of this split.
--
--   Modules: `Estimates/FiniteMarkedFreezingCellBound.lean`, `Estimates/NativeIteratedDifferencing.lean`, `Estimates/NativeOptionPivotQuotientStrong.lean`, `Estimates/NativeProductVerticalization.lean`, `Estimates/NativeResidualCrossInduction.lean`, `Geometry/NativePairChartSymbol.lean`, `Lattices/AllocatedModularRankAffineFullWitness.lean`, `Lattices/CertifiedFullChartAffineTerminal.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/ControlledProjectionUniformBudget.lean`, `Polynomial/PolynomialSymbolBasisIndependence.lean`, `Polynomial/StepOneScalarPhase.lean`, `Polynomial/UniformFiniteMarkedPolynomialFreezing.lean`, `Sampling/SamplerSeparatedVariables.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B204
import Definitions.Def_OAIE3v2B205
import Definitions.Def_OAIE3v2B206
import Definitions.Def_OAIE3v2B207
import Definitions.Def_OAIE3v2B210
import Definitions.Def_OAIE3v2B211
import Definitions.Def_OAIE3v2B212
import Definitions.Def_OAIE3v2B214

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UniformFiniteMarkedPolynomialFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeIteratedDifferencing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_differenced_rows_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ZMod N → ℂ, (∀ h n, ‖f h n‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        f h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ K : ZMod N → (Fin 2 → ℤ) → ℂ,
        (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + C) ^ C) (K k))) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
          multiplicativeDerivative (f h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
  obtain ⟨A, _, hunit⟩ := exists_unit_vertical_mean_row_model (s + 1)
  obtain ⟨B, _, hcyclic⟩ := UnitVerticalObservable.exists_cyclic_second_difference_models_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * Q + 2 + Polynomial.C B) ^ B + 3 * Q + 20)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f hf hcorr
  classical
  let q := (p + A) ^ A
  let e := 2 * q + 2
  let r := (3 * q + 2 + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : r + 3 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  have heC : e ≤ (p + C) ^ C := by dsimp [e]; linarith
  have hN' : Real.exp (e + 16) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by dsimp [e]; linarith)).trans hN
  obtain ⟨m, _, hmcard, V, hD, hVcorr⟩ := hunit D T hp hT
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)]) f hf hcorr
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  have hmodels (k : ZMod N) : ∃ K : (Fin 2 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r K) ∧
      ∀ h : ℤ, (𝔼 n : ZMod N,
        ‖cyclicSecondDifference (V.test T.orbit 0).eval (V.test T.orbit 0).eval k h n -
          K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
    have hh := hcyclic D V T.orbit hq hD hcard he hN' 0 0 k
    have hbudgeteq : ((p + A) ^ A + e + B) ^ B = r := by
      change (q + e + B) ^ B = (3 * q + 2 + B) ^ B
      congr 1
      dsimp [e]
      ring
    simpa only [hbudgeteq] using hh
  choose K hK herror using hmodels
  let g (h n : ZMod N) := (V.test T.orbit 0).eval ![(h.val : ℤ), (n.val : ℤ)]
  have hd := mean_row_correlation_sq_le_approximated_derivatives f g
    (fun k h n => K k ![(h.val : ℤ), (n.val : ℤ)]) hf
    (ε := Real.exp (-e)) (by
      intro k h
      simpa only [g, multiplicativeDerivative, cyclicSecondDifference] using herror k h.val)
  have hlarge : Real.exp (-(2 * q)) ≤
      (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        multiplicativeDerivative (f h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) +
          Real.exp (-e) := by
    have hsquare := (pow_le_pow_left₀ (Real.exp_nonneg (-q)) hVcorr 2).trans hd
    have hexp : Real.exp (-q) ^ 2 = Real.exp (-(2 * q)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rwa [hexp] at hsquare
  have htwo : 2 * Real.exp (-e) ≤ Real.exp (-(2 * q)) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-e) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
  refine ⟨K, fun k => ⟨(Classical.choice (hK k)).mono hrC⟩, ?_⟩
  apply (Real.exp_le_exp.mpr (neg_le_neg heC)).trans
  linarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductVerticalization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

theorem exists_common_unit_vertical_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
              (Fin (n + 1)) ((p + C) ^ C),
            ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 x, weight h x * star (V.observable 0 (QuotientGroup.mk
                (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                  (fun _ => (x.val : ℤ)) (T h).orbit)))‖ := by
  obtain ⟨a, _, hvertical⟩ := exists_common_vertical_correlators
  obtain ⟨b, _, hcomplete⟩ := exists_native_unit_vertical_completion s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + Q + (Q + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hT hnorm hsame N _ weight hweight hcorr
  let q := (p + a) ^ a
  let q₂ := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq₂ : 0 ≤ q₂ := by dsimp [q₂]; positivity
  have htotal : p + q + q₂ + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, q₂, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hq₂C : q₂ ≤ (p + C) ^ C := by linarith
  obtain ⟨H', S, eta, hsub, hH', hdense, hheight, hS, hSsame, hvert, hint, hScorr⟩ :=
    hvertical D T H hH hp hT hnorm hsame weight hweight hcorr
  obtain ⟨h₀, hh₀⟩ := hH'
  have hmean : Real.exp (-q) ≤ 𝔼 x, ‖(S h₀).evalCyclic N (fun _ => x)‖ := by
    apply (hScorr h₀ hh₀).trans
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le_expect
    intro x _
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (hweight h₀ (hsub hh₀) x)
  obtain ⟨x₀, _, hx₀⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  let y : D.Space := QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
    (fun _ => (x₀.val : ℤ)) (S h₀).orbit)
  obtain ⟨n, hn, hnq, K, hK, v, hv0, hvunit, hvnorm, hvLip, hvvertical⟩ :=
    hcomplete D (S h₀) hq (hS h₀).2.2 (hS h₀).2.1 eta (hvert h₀) y hx₀
  let V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
      (Fin (n + 1)) ((p + C) ^ C) := {
    observable := v
    unit := hvunit
    norm := hvnorm
    lipBound := K
    lip_bound := hK.trans (Real.exp_le_exp.mpr hq₂C)
    lipschitz := hvLip
    frequency := eta
    height := fun i => (hheight i).trans hqC
    vertical := hvvertical
    integral := hint
  }
  refine ⟨H', hsub, ⟨h₀, hh₀⟩,
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC)) (Nat.cast_nonneg _)).trans hdense,
    n, hn, hnq.trans (Real.exp_le_exp.mpr hq₂C), V, ?_⟩
  intro h hh
  have hvalue (x : ZMod N) : V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)) = (S h).evalCyclic N (fun _ => x) / 2 := by
    change v 0 _ = _
    rw [hv0, hSsame h₀ h]
    change (S h).observable _ / 2 = (S h).observable _ / 2
    rw [(hS h).1]
  have heq : (𝔼 x, weight h x * star (V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)))) =
      (𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))) / 2 := by
    simp only [hvalue, star_div₀, star_ofNat, ← mul_div_assoc, ← Finset.expect_div]
  rw [heq, norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  apply le_trans _ (div_le_div_of_nonneg_right (hScorr h hh) (by norm_num : (0 : ℝ) ≤ 2))
  apply le_trans _ (exp_sub_one_le_half_exp (-q))
  apply Real.exp_le_exp.mpr
  linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_native_unit_factor_replacement (s degree : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      ∀ {N : ℕ} [NeZero N] (f : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation degree N p
        (fun _ : Unit => fun x => f h x * star ((T h).evalCyclic N (fun _ => x))))) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
              (Fin (n + 1)) ((p + C) ^ C),
            ∀ h ∈ H', Nonempty (NativeVectorCorrelation degree N ((p + C) ^ C)
              (fun _ : Unit => fun x => f h x * star (V.observable 0 (QuotientGroup.mk
                (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                  (fun _ => (x.val : ℤ)) (T h).orbit))))) := by
  classical
  obtain ⟨a, _, hselect⟩ := exists_common_unit_vertical_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (2 * X + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hT hnorm hsame N _ f hf hcorr
  let W (h : {h // h ∈ H}) := Classical.choice (hcorr h.val h.property)
  let weight (h : G) (x : ZMod N) : ℂ :=
    if hh : h ∈ H then
      f h x * star (((W ⟨h, hh⟩).test.expNormalize p).evalCyclic N (fun _ => x)) else 0
  have hweight (h : G) (hh : h ∈ H) (x : ZMod N) : ‖weight h x‖ ≤ 1 := by
    simp only [weight, dif_pos hh, norm_mul, norm_star]
    have hn : ‖((W ⟨h, hh⟩).test.expNormalize p).evalCyclic N (fun _ => x)‖ ≤ 1 := by
      apply (((W ⟨h, hh⟩).test.expNormalize p).norm_evalCyclic_le N (fun _ => x)).trans
      exact_mod_cast (W ⟨h, hh⟩).test.expNormalize_norm (W ⟨h, hh⟩).complexity
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h hh x)).trans hn
  have hweightcorr (h : G) (hh : h ∈ H) : Real.exp (-(2 * p + 2)) ≤
      ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖ := by
    let Wh := W ⟨h, hh⟩
    have hscale (x : ZMod N) : (Wh.test.expNormalize p).evalCyclic N (fun _ => x) =
        (Real.exp (-p) : ℂ) * Wh.test.evalCyclic N (fun _ => x) := rfl
    have heq : (𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))) =
        (Real.exp (-p) : ℂ) * (𝔼 x, (f h x * star ((T h).evalCyclic N (fun _ => x))) *
          star (Wh.test.evalCyclic N (fun _ => x))) := by
      simp only [weight, dif_pos hh]
      change (𝔼 x, (f h x * star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x))) *
        star ((T h).evalCyclic N (fun _ => x))) = _
      simp only [hscale, star_mul, Complex.star_def, Complex.conj_ofReal, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    rw [heq, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))]
    calc
      _ ≤ Real.exp (-p) * Real.exp (-p) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left Wh.correlation (Real.exp_nonneg _)
  obtain ⟨H', hsub, hH', hdense, n, hn, hnq, V, hVc⟩ :=
    hselect D T H hH (by linarith : 0 ≤ 2 * p + 2)
      (fun h hh => (hT h hh).mono (by linarith : p ≤ 2 * p + 2)) hnorm hsame
      weight hweight hweightcorr
  let q := (2 * p + 2 + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  refine ⟨H', hsub, hH',
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC)) (Nat.cast_nonneg _)).trans hdense,
    n, hn, hnq.trans (Real.exp_le_exp.mpr hqC), V.mono hqC, ?_⟩
  intro h hh
  let Wh := W ⟨h, hsub hh⟩
  refine ⟨{
    L := Wh.L
    dim := Wh.dim
    model := Wh.model
    test := Wh.test.expNormalize p
    complexity := (Wh.test.expNormalize_complexity Wh.complexity).mono hpC
    coordinate := ()
    correlation := ?_
  }⟩
  have hc := (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hVc h hh)
  have hweightval (x : ZMod N) : weight h x =
      f h x * star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x)) := by
    simp only [weight, dif_pos (hsub hh), Wh]
  change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x,
    (f h x * star (V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)))) *
      star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x))‖
  have heq : (𝔼 x, (f h x * star (V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)))) *
        star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x))) =
      (𝔼 x, weight h x * star (V.observable 0 (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (T h).orbit)))) := by
    simp only [hweightval]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [heq]
  exact hc

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_native_two_factor_unit_replacement (s t degree : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra ℚ L₁]
      [LieRing L₂] [LieAlgebra ℚ L₂]
      [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₂)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₂)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₂)] [T2Space (ℝ ⊗[ℚ] L₂)] {d₁ d₂ : ℕ}
      (D₁ : RationalFilteredNilmanifold L₁ s d₁) (D₂ : RationalFilteredNilmanifold L₂ t d₂)
      (T : G → D₁.Niltest (fun _ : Unit => 1)) (S : G → D₂.Niltest (fun _ : Unit => 1))
      (H : Finset G), H.Nonempty → ∀ {p : ℝ}, 0 ≤ p →
      (∀ h ∈ H, (T h).ComplexityLE p) → (∀ h ∈ H, (S h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) → (∀ h ∈ H, (S h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      (∀ h k, (S h).observable = (S k).observable) →
      ∀ {N : ℕ} [NeZero N] (f : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation degree N p (fun _ : Unit => fun x =>
        f h x * star ((S h).evalCyclic N (fun _ => x)) * star ((T h).evalCyclic N (fun _ => x))))) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n₁ : ℕ, 0 < n₁ ∧ (n₁ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V₁ : D₁.UnitVerticalObservable (D₁.filtration.realification.subgroup s)
              (Fin (n₁ + 1)) ((p + C) ^ C),
            ∃ n₂ : ℕ, 0 < n₂ ∧ (n₂ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∃ V₂ : D₂.UnitVerticalObservable (D₂.filtration.realification.subgroup t)
                  (Fin (n₂ + 1)) ((p + C) ^ C),
                ∀ h ∈ H', Nonempty (NativeVectorCorrelation degree N ((p + C) ^ C)
                  (fun _ : Unit => fun x => f h x *
                    star (V₂.observable 0 (QuotientGroup.mk
                      (D₂.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) (S h).orbit))) *
                    star (V₁.observable 0 (QuotientGroup.mk
                      (D₁.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) (T h).orbit))))) := by
  obtain ⟨a, _, hfirst⟩ := exists_native_unit_factor_replacement s degree
  obtain ⟨b, _, hsecond⟩ := exists_native_unit_factor_replacement t degree
  let X : Polynomial ℕ := Polynomial.X
  let Q₁ : Polynomial ℕ := (X + Polynomial.C a) ^ a
  let P₂ : Polynomial ℕ := X + Q₁ + 2
  let Q₂ : Polynomial ℕ := (P₂ + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q₁ + Q₂ + 2)
  refine ⟨C, hC, ?_⟩
  intro G L₁ L₂ _ _ _ _ _ _ _ _ _ _ _ _ d₁ d₂ D₁ D₂ T S H hH p hp
    hT hS hnT hnS hcT hcS N _ f hf hcorr
  have hfS (h : G) (hh : h ∈ H) (x : ZMod N) :
      ‖f h x * star ((S h).evalCyclic N (fun _ => x))‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    have hn : ‖(S h).evalCyclic N (fun _ => x)‖ ≤ 1 := by
      apply ((S h).norm_evalCyclic_le N (fun _ => x)).trans
      exact_mod_cast hnS h hh
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h hh x)).trans hn
  obtain ⟨H₁, hH₁H, hH₁, hdense₁, n₁, hn₁, hcount₁, V₁, hcorr₁⟩ :=
    hfirst D₁ T H hH hp hT hnT hcT
      (fun h x => f h x * star ((S h).evalCyclic N (fun _ => x))) hfS hcorr
  let q₁ := (p + a) ^ a
  let p₂ := p + q₁ + 2
  let q₂ := (p₂ + b) ^ b
  have hq₁ : 0 ≤ q₁ := by dsimp [q₁]; positivity
  have hp₂ : 0 ≤ p₂ := by dsimp [p₂]; positivity
  have hq₂ : 0 ≤ q₂ := by dsimp [q₂]; positivity
  have hpp₂ : p ≤ p₂ := by dsimp [p₂]; linarith
  have hq₁p₂ : q₁ ≤ p₂ := by dsimp [p₂]; linarith
  let f₂ (h : G) (x : ZMod N) := f h x * star (V₁.observable 0 (QuotientGroup.mk
    (D₁.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
      (fun _ => (x.val : ℤ)) (T h).orbit)))
  have hf₂ (h : G) (hh : h ∈ H₁) (x : ZMod N) : ‖f₂ h x‖ ≤ 1 := by
    change ‖f h x * star (V₁.observable 0 _)‖ ≤ 1
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h (hH₁H hh) x)).trans (V₁.norm 0 _)
  have hcorr₂ (h : G) (hh : h ∈ H₁) : Nonempty (NativeVectorCorrelation degree N p₂
      (fun _ : Unit => fun x => f₂ h x * star ((S h).evalCyclic N (fun _ => x)))) := by
    obtain ⟨Wh⟩ := hcorr₁ h hh
    refine ⟨(Wh.mono hq₁p₂).mapCoordinates _ id ?_⟩
    intro i x
    dsimp only [id_eq, f₂]
    ring
  obtain ⟨H₂, hH₂H₁, hH₂, hdense₂, n₂, hn₂, hcount₂, V₂, hfinal⟩ :=
    hsecond D₂ S H₁ hH₁ hp₂ (fun h hh => (hS h (hH₁H hh)).mono hpp₂)
      (fun h hh => hnS h (hH₁H hh)) hcS f₂ hf₂ hcorr₂
  have htotal : p + q₁ + q₂ + 2 ≤ (p + C) ^ C := by
    simpa [X, Q₁, P₂, Q₂, q₁, p₂, q₂, Polynomial.eval₂_pow] using hbudget p hp
  have hq₁C : q₁ ≤ (p + C) ^ C := by linarith
  have hq₂C : q₂ ≤ (p + C) ^ C := by linarith
  refine ⟨H₂, hH₂H₁.trans hH₁H, hH₂, ?_, n₁, hn₁,
    hcount₁.trans (Real.exp_le_exp.mpr hq₁C), V₁.mono hq₁C, n₂, hn₂,
    hcount₂.trans (Real.exp_le_exp.mpr hq₂C), V₂.mono hq₂C, ?_⟩
  · calc
      _ ≤ Real.exp (-(q₁ + q₂)) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-q₂) * (Real.exp (-q₁) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q₂) * H₁.card := mul_le_mul_of_nonneg_left hdense₁ (Real.exp_nonneg _)
      _ ≤ _ := hdense₂
  · intro h hh
    obtain ⟨Wh⟩ := hfinal h hh
    refine ⟨(Wh.mono hq₂C).mapCoordinates _ id ?_⟩
    intro i x
    change f h x * star (V₂.observable 0 _) * star (V₁.observable 0 _) =
      f₂ h x * star (V₂.observable 0 _)
    dsimp only [f₂]
    ring

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

universe v

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]

variable [Fintype ι] {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (j : ι)

theorem optionPairProjection_layers (k : ℕ)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i)
    (hx : x ∈ (optionProduct D₀ D).filtration.layer k) :
    optionPairProjection j x ∈ (pi (pairModels D₀ (D j))).filtration.layer k := by
  apply (mem_pi_layer (fun b => (pairModels D₀ (D j) b).filtration) k _).mpr
  intro b
  cases b
  · exact (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k x).mp hx (some j)
  · exact (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k x).mp hx none

theorem optionPairProjection_piRealOrbit_log {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w) :
    VectorPolynomial.map
      ((realificationLieHom (optionPairProjection j)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log =
        (pairOrbit D₀ (D j) (g none) (g (some j))).log := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  apply ((Pi.basis (fun b => (pairModels D₀ (D j) b).basis)).baseChange ℝ).repr.injective
  ext ⟨b, k⟩
  rw [realification_pi_basis_repr, realification_pi_basis_repr]
  change ((pairModels D₀ (D j) b).basis.baseChange ℝ).repr
    (realificationLieHom (liePiEval b) (realificationLieHom (optionPairProjection j)
      (coefficients (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g).log α))) k =
    ((pairModels D₀ (D j) b).basis.baseChange ℝ).repr
      (realificationLieHom (liePiEval b)
        (coefficients (pairOrbit D₀ (D j) (g none) (g (some j))).log α)) k
  have hpair := piRealOrbit_coefficient (fun b => (pairModels D₀ (D j) b).filtration)
    (fun b => by cases b; exact g (some j); exact g none) α b
  change realificationLieHom (liePiEval b)
    (coefficients (pairOrbit D₀ (D j) (g none) (g (some j))).log α) = _ at hpair
  rw [hpair]
  cases b
  · rw [realification_optionPairProjection_false]
    exact congrArg (fun x => ((D j).basis.baseChange ℝ).repr x k)
      (piRealOrbit_coefficient (fun i => (optionFactors D₀ D i).filtration) g α (some j))
  · rw [realification_optionPairProjection_true]
    exact congrArg (fun x => (D₀.basis.baseChange ℝ).repr x k)
      (piRealOrbit_coefficient (fun i => (optionFactors D₀ D i).filtration) g α none)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionPivotQuotientStrong
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} [Fintype J] {L Y : Type u} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal π eta js, π x = 0)
  (U : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
  (theta : ∀ j, M j →ₗ[ℚ] ℚ)
  (hzero : ∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer U s →
    realifyFunctional ((pairFrequency (eta j) (theta j)).comp
      (optionPairProjection j).toLinearMap) x = 0)

include hzero in

theorem optionNativeCommonFastTop_quotient_kernel_eq_zero
    (y : ∀ i : Option J,
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i)
    (hy : y ∈ ((optionProduct D E).filtration.gradedRefiltrationLayer U s).map
      (optionMarkedLieMap (L := M)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js))).toLinearMap)
    (hmark : optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker) y = 0) :
    y = 0 := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hπ : π (x none) = 0 := congrFun hmark none
  have hpartner (j : J) : x (some j) = 0 := congrFun hmark (some j)
  have hmem : x none ∈ D.filtration.pivotAnnihilatorIdeal π eta js := by
    apply (D.filtration.mem_pivotAnnihilatorIdeal π eta js (x none)).mpr
    refine ⟨?_, hπ, ?_⟩
    · exact (mem_pi_layer (fun i => (optionFactors D E i).filtration) s x).mp
        ((optionProduct D E).filtration.gradedRefiltrationLayer_le U s hx) none
    · intro j _
      have hz := (optionProduct D E).filtration.frequency_zero_on_refilteredLayer_of_real
        U ((pairFrequency (eta j) (theta j)).comp (optionPairProjection j).toLinearMap)
        s (hzero j) x hx
      simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap, pairFrequency_apply,
        optionPairProjection_true, optionPairProjection_false] at hz
      have hp : (x (some j) : M j) = (0 : M j) := hpartner j
      rw [hp, map_zero, add_zero] at hz
      exact hz
  funext i
  cases i with
  | none => exact (lieQuotientMap_eq_zero
      (D.filtration.pivotAnnihilatorIdeal π eta js) (x none)).mpr hmem
  | some j => exact hpartner j

variable {dQ : ℕ}
  (Q : RationalFilteredNilmanifold
    (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) s dQ)
  (hQ : Q.filtration = D.filtration.pivotQuotientFiltration π eta js)
  {κ κQ : Type*}
  (e : Basis κ ℚ (∀ i : Option J, optionLieSpace L M i)) (μ : κ → ℕ)
  (hSource : ∀ k, (optionProduct D E).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (c : Basis κQ ℚ (∀ i : Option J,
    optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i))
  (ν : κQ → ℕ)
  (hTarget : ∀ k, (optionProduct Q E).filtration.layer k =
    Submodule.span ℚ (c '' {i | k ≤ ν i}))
  (hU : BasisGradedSubmodule
    ((optionProduct D E).filtration.associatedGradedBasis e μ hSource) μ U.toSubmodule)

include hzero e μ hSource c ν hTarget hU in

theorem optionNativeCommonPivotQuotientFast_top_kernel_eq_zero
    (y : ∀ i : Option J,
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i)
    (hy : y ∈ (optionProduct Q E).filtration.gradedRefiltrationLayer
      (optionNativeCommonPivotQuotientFast D E π eta js Q hQ U) s)
    (hmark : optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker) y = 0) :
    y = 0 := by
  rw [optionNativeCommonPivotQuotientFast_layer_eq
    D E π eta js Q hQ U e μ hSource c ν hTarget hU s] at hy
  exact optionNativeCommonFastTop_quotient_kernel_eq_zero
    D E π eta js hker U theta hzero y hy hmark

include hzero e μ hSource c ν hTarget hU in

theorem optionNativeCommonPivotQuotientFast_graded_top_kernel
    (G : NilpotentLieFiltration (∀ i : Option J, optionLieSpace Y M i) s)
    (hmarked : ∀ k, ∀ y ∈ (optionProduct Q E).filtration.layer k,
      optionMarkedLieMap (L := M)
        (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker) y ∈
          G.layer k) :
    ∀ a ∈ optionNativeCommonPivotQuotientFast D E π eta js Q hQ U,
      basisGradeProjection
        ((optionProduct Q E).filtration.associatedGradedBasis c ν hTarget) ν s a = a →
      (optionProduct Q E).filtration.associatedGradedMap G
        (optionMarkedLieMap (L := M)
          (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker))
        hmarked a = 0 → a = 0 := by
  apply ((optionProduct Q E).filtration.graded_top_kernel_iff_refiltered_top_kernel
    G c ν hTarget
    (optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker))
    hmarked (optionNativeCommonPivotQuotientFast D E π eta js Q hQ U)).mpr
  exact optionNativeCommonPivotQuotientFast_top_kernel_eq_zero
    D E π eta js hker U theta hzero Q hQ e μ hSource c ν hTarget hU

end Erdos3.RationalFilteredNilmanifold

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_cross_row_detection_one :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCrossRowDetection 1 C := by
  obtain ⟨C, hC, hfourier⟩ := exists_fourier_of_stepOne_cross_correlation
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ _hN f g hf hg hcorr
  obtain ⟨χ, hχ⟩ := hfourier D hp T hT f g hf hg hcorr
  exact hχ.trans (norm_fourierCoeff_le_gowers_two g χ)

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_gowers_of_native_cross_family {s A : ℕ} (hdetect : NativeCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] [Nonempty I] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (a b : I → ZMod N → ℂ) (K : I → (Fin 2 → ℤ) → ℂ),
      (∀ i n, ‖a i n‖ ≤ 1) → (∀ i n, ‖b i n‖ ≤ 1) →
      (∀ i, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p (K i))) →
      Real.exp (-p) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        (a i n * star (b i (n + h))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ 𝔼 i, gowersNorm (s + 1) (b i) := by
  let X : Polynomial ℕ := Polynomial.X
  let T := 3 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (T + X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro I _ _ N _ p hp hN a b K ha hb hK hcorr
  classical
  let c (i : I) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    (a i n * star (b i (n + h))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖
  let z (i : I) := Real.exp (-(2 * p)) * c i
  let t := 3 * p + 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hc0 (i : I) : 0 ≤ c i := Finset.expect_nonneg (fun _ _ => norm_nonneg _)
  have hcap (i : I) : c i ≤ Real.exp (2 * p) := by
    apply Finset.expect_le Finset.univ_nonempty
    intro h _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      ((Classical.choice (hK i)).norm_eval_le _)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha i n)).trans (hb i (n + h))
  have hzcap (i : I) : z i ≤ 1 := by
    calc
      _ ≤ Real.exp (-(2 * p)) * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_left (hcap i) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzmean : Real.exp (-(3 * p)) ≤ 𝔼 i, z i := by
    change Real.exp (-(3 * p)) ≤ 𝔼 i, Real.exp (-(2 * p)) * c i
    rw [← Finset.mul_expect]
    have heq : Real.exp (-(3 * p)) = Real.exp (-(2 * p)) * Real.exp (-p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set z (Real.exp_nonneg (-(3 * p))) hzcap hzmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(3 * p)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hzle (i : I) : z i ≤ c i := mul_le_of_le_one_left (hc0 i)
    (Real.exp_le_one_iff.mpr (by linarith))
  have hcost : t + (t + p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hN' : Real.exp ((t + p + A) ^ A) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN
  have hnorm (i : I) (hi : i ∈ S) :
      Real.exp (-((t + p + A) ^ A)) ≤ gowersNorm (s + 1) (b i) := by
    have hc : Real.exp (-t) ≤ c i := hhalf.trans ((hlarge i hi).trans (hzle i))
    obtain ⟨V⟩ := NativeMeanRowCorrelation.exists_of_expansion
      (Classical.choice (hK i)) ht hc
    exact hdetect V.model V.test (by linarith : 0 ≤ t + p) V.complexity hN'
      (a i) (b i) (ha i) (hb i) V.correlation
  have hmass := dense_set_mean_lower_bound S (fun i => gowersNorm (s + 1) (b i))
    (fun i => gowersNorm_nonneg s (b i)) (Real.exp_nonneg (-((t + p + A) ^ A)))
    ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS) hnorm
  apply (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans
  have heq : Real.exp (-(t + (t + p + A) ^ A)) =
      Real.exp (-t) * Real.exp (-((t + p + A) ^ A)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [heq]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_characters_of_stepOne_rows :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {H : Type*} [Fintype H] [Nonempty H] {N : ℕ} [NeZero N] {p : ℝ},
      0 ≤ p → ∀ (F : H → ZMod N → ℂ) (g : H → (Unit → ℤ) → ℂ),
      (∀ h n, ‖F h n‖ ≤ Real.exp p) →
      (∀ h (n : ZMod N), ‖g h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 p (g h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖) →
      ∃ χ : H → AddChar (ZMod N) ℂ,
        Real.exp (-((p + C) ^ C)) ≤ 𝔼 h, ‖finiteFourierCoeff (F h) (χ h)‖ := by
  obtain ⟨A, _, hfourier⟩ := exists_fourier_of_stepOne_expansion
  let X : Polynomial ℕ := Polynomial.X
  let T := 2 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro H _ _ N _ p hp F g hF hg hE hcorr
  classical
  let F' : H → ZMod N → ℂ := fun h n => (Real.exp (-p) : ℂ) * F h n
  let t := 2 * p + 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hF' (h : H) (n : ZMod N) : ‖F' h n‖ ≤ 1 := by
    simp only [F', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-p) * Real.exp p := mul_le_mul_of_nonneg_left (hF h n) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hscale (h : H) :
      ‖𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))‖ =
        Real.exp (-p) * ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖ := by
    have heq : (𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))) =
        (Real.exp (-p) : ℂ) * (𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      dsimp [F']
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmean : Real.exp (-(2 * p)) ≤
      𝔼 h, ‖𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))‖ := by
    simp only [hscale, ← Finset.mul_expect]
    have heq : Real.exp (-(2 * p)) = Real.exp (-p) * Real.exp (-p) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  have hcap (h : H) : ‖𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hF' h n)).trans (hg h n)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set _ (Real.exp_nonneg (-(2 * p))) hcap hmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(2 * p)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hcharacter (h : H) (hh : h ∈ S) : ∃ χ : AddChar (ZMod N) ℂ,
      Real.exp (-((t + A) ^ A)) ≤ ‖finiteFourierCoeff (F' h) χ‖ :=
    hfourier ht ((Classical.choice (hE h)).mono hpt) (F' h) (hF' h) (hhalf.trans (hlarge h hh))
  let χ (h : H) : AddChar (ZMod N) ℂ := if hh : h ∈ S then Classical.choose (hcharacter h hh) else 1
  have hmass := dense_set_mean_lower_bound S (fun h => ‖finiteFourierCoeff (F' h) (χ h)‖)
    (fun _ => norm_nonneg _) (Real.exp_nonneg (-((t + A) ^ A)))
    ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS)
    (fun h hh => by simpa only [χ, dif_pos hh] using Classical.choose_spec (hcharacter h hh))
  have hmono (h : H) : ‖finiteFourierCoeff (F' h) (χ h)‖ ≤ ‖finiteFourierCoeff (F h) (χ h)‖ := by
    have heq : finiteFourierCoeff (F' h) (χ h) = (Real.exp (-p) : ℂ) * finiteFourierCoeff (F h) (χ h) := by
      unfold finiteFourierCoeff
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      dsimp [F']
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp))
  have hcost : t + (t + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨χ, (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans ?_⟩
  have heq : Real.exp (-(t + (t + A) ^ A)) = Real.exp (-t) * Real.exp (-((t + A) ^ A)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [heq]
  exact hmass.trans (Finset.expect_le_expect (fun h _ => hmono h))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_gowers_of_bounded_native_residual_cross_family {s A : ℕ}
    (hdetect : NativeResidualCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] [Nonempty I] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (a b : I → ZMod N → ℂ) (K : I → (Fin 2 → ℤ) → ℂ)
        (R : I → ZMod N → (Unit → ℤ) → ℂ),
      (∀ i n, ‖a i n‖ ≤ 1) → (∀ i n, ‖b i n‖ ≤ 1) →
      (∀ i h (n : ZMod N), ‖R i h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ i, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) p (K i))) →
      (∀ i h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R i h))) →
      Real.exp (-p) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        ((a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))) *
          star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ 𝔼 i, gowersNorm (s + 3) (b i) := by
  let X : Polynomial ℕ := Polynomial.X
  let T := 3 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (T + X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro I _ _ N _ p hp hN a b K R ha hb hR hK hRE hcorr
  classical
  let c (i : I) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    ((a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))) *
      star (K i ![(h.val : ℤ), (n.val : ℤ)])‖
  let z (i : I) := Real.exp (-(2 * p)) * c i
  let t := 3 * p + 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hc0 (i : I) : 0 ≤ c i := Finset.expect_nonneg (fun _ _ => norm_nonneg _)
  have hunit (i : I) (h n : ZMod N) :
      ‖(a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hR i h n)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha i n)).trans (hb i (n + h))
  have hcap (i : I) : c i ≤ Real.exp (2 * p) := by
    apply Finset.expect_le Finset.univ_nonempty
    intro h _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hunit i h n)).trans
      ((Classical.choice (hK i)).norm_eval_le _)
  have hzcap (i : I) : z i ≤ 1 := by
    calc
      _ ≤ Real.exp (-(2 * p)) * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_left (hcap i) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzmean : Real.exp (-(3 * p)) ≤ 𝔼 i, z i := by
    change Real.exp (-(3 * p)) ≤ 𝔼 i, Real.exp (-(2 * p)) * c i
    rw [← Finset.mul_expect]
    have heq : Real.exp (-(3 * p)) = Real.exp (-(2 * p)) * Real.exp (-p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set z (Real.exp_nonneg (-(3 * p))) hzcap hzmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(3 * p)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hzle (i : I) : z i ≤ c i := mul_le_of_le_one_left (hc0 i)
    (Real.exp_le_one_iff.mpr (by linarith))
  have hcost : t + (t + p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hN' : Real.exp ((t + p + A) ^ A) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN
  have hnorm (i : I) (hi : i ∈ S) :
      Real.exp (-((t + p + A) ^ A)) ≤ gowersNorm (s + 3) (b i) := by
    have hc : Real.exp (-t) ≤ c i := hhalf.trans ((hlarge i hi).trans (hzle i))
    obtain ⟨V⟩ := NativeMeanRowCorrelation.exists_of_expansion
      (Classical.choice (hK i)) ht hc
    exact hdetect V.model V.test (by linarith : 0 ≤ t + p) V.complexity hN'
      (a i) (b i) (R i) (ha i) (hb i) (hR i)
      (fun h => ⟨(Classical.choice (hRE i h)).mono (by linarith)⟩) V.correlation
  have hmass := dense_set_mean_lower_bound S (fun i => gowersNorm (s + 3) (b i))
    (fun i => gowersNorm_nonneg (s + 2) (b i)) (Real.exp_nonneg (-((t + p + A) ^ A)))
    ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS) hnorm
  apply (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans
  have heq : Real.exp (-(t + (t + p + A) ^ A)) =
      Real.exp (-t) * Real.exp (-((t + p + A) ^ A)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [heq]

theorem exists_gowers_of_native_residual_cross_family {s A : ℕ}
    (hdetect : NativeResidualCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] [Nonempty I] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (a b : I → ZMod N → ℂ) (K : I → (Fin 2 → ℤ) → ℂ)
        (R : I → ZMod N → (Unit → ℤ) → ℂ),
      (∀ i n, ‖a i n‖ ≤ 1) → (∀ i n, ‖b i n‖ ≤ 1) →
      (∀ i, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) p (K i))) →
      (∀ i h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R i h))) →
      Real.exp (-p) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        ((a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))) *
          star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ 𝔼 i, gowersNorm (s + 3) (b i) := by
  obtain ⟨B, _, hfamily⟩ := exists_gowers_of_bounded_native_residual_cross_family hdetect
  let X : Polynomial ℕ := Polynomial.X
  let Q := 3 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro I _ _ N _ p hp hN a b K R ha hb hK hRE hcorr
  classical
  let q := 3 * p + 2
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsum : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hresult : (q + B) ^ B ≤ (p + C) ^ C := by linarith
  let R₀ : I → ZMod N → (Unit → ℤ) → ℂ := fun i h x =>
    (Real.exp (-(2 * p)) : ℂ) * R i h x
  have hR₀ (i : I) (h n : ZMod N) : ‖R₀ i h (fun _ => (n.val : ℤ))‖ ≤ 1 := by
    simp only [R₀, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(2 * p)) * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_left ((Classical.choice (hRE i h)).norm_eval_le _)
          (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hR₀E (i : I) (h : ZMod N) :
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) q (R₀ i h)) := by
    apply Nonempty.intro
    apply NativeIntegerExpansion.mono _ hpq
    apply (Classical.choice (hRE i h)).scaleNormLeOne
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (Real.exp_le_one_iff.mpr (by linarith : -(2 * p) ≤ 0))
  have hscale (i : I) (h : ZMod N) :
      ‖𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R₀ i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖ =
      Real.exp (-(2 * p)) * ‖𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖ := by
    have heq : (𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R₀ i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])) =
      (Real.exp (-(2 * p)) : ℂ) * (𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      simp only [R₀, star_mul]
      rw [show star ((Real.exp (-(2 * p))) : ℂ) = (Real.exp (-(2 * p)) : ℂ) from
        Complex.conj_ofReal _]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hscaled : Real.exp (-q) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      ((a i n * star (b i (n + h))) * star (R₀ i h (fun _ => (n.val : ℤ)))) *
        star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    simp only [hscale, ← Finset.mul_expect]
    apply (Real.exp_le_exp.mpr (show -q ≤ -(3 * p) by dsimp [q]; linarith)).trans
    have heq : Real.exp (-(3 * p)) = Real.exp (-(2 * p)) * Real.exp (-p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  exact (Real.exp_le_exp.mpr (neg_le_neg hresult)).trans
    (hfamily hq ((Real.exp_le_exp.mpr hresult).trans hN) a b K R₀ ha hb hR₀
      (fun i => ⟨(Classical.choice (hK i)).mono hpq⟩) hR₀E hscaled)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativePairChartSymbol
namespace OAI

universe universeLevel

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] BoolLieFamily

variable {L M : Type universeLevel} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ τ ι : Type*} {w : σ → ℕ} {v : τ → ℕ}

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart
  weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom

theorem pairOrbit_polynomialOrbitRealChart_log
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    (pairOrbit D E (D.filtration.polynomialOrbitRealChart w v β hβ p)
      (E.filtration.polynomialOrbitRealChart w v β hβ q)).log =
        realChartSubstitute β (pairOrbit D E p q).log := by
  simp only [pairOrbit, piRealOrbit, PolynomialOrbit.log, polynomialOrbitOfLog, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases i
  · change VectorPolynomial.map
      ((realProductSingle (L := BoolLieFamily L M) false).restrictScalars ℚ)
      (E.filtration.polynomialOrbitRealChart w v β hβ q).log =
      realChartSubstitute β (VectorPolynomial.map
        ((realProductSingle (L := BoolLieFamily L M) false).restrictScalars ℚ) q.log)
    rw [polynomialOrbitRealChart_log]
    exact (realChartSubstitute_map β
      (realProductSingle (L := BoolLieFamily L M) false) q.log).symm
  · change VectorPolynomial.map
      ((realProductSingle (L := BoolLieFamily L M) true).restrictScalars ℚ)
      (D.filtration.polynomialOrbitRealChart w v β hβ p).log =
      realChartSubstitute β (VectorPolynomial.map
        ((realProductSingle (L := BoolLieFamily L M) true).restrictScalars ℚ) p.log)
    rw [polynomialOrbitRealChart_log]
    exact (realChartSubstitute_map β
      (realProductSingle (L := BoolLieFamily L M) true) p.log).symm

attribute [local irreducible] pairOrbit

theorem pairOrbitSymbol_polynomialOrbitRealChart
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    pairOrbitSymbol D E (D.filtration.polynomialOrbitRealChart w v β hβ p)
      (E.filtration.polynomialOrbitRealChart w v β hβ q) b ω hF =
        (pi (pairModels D E)).filtration.realPolynomialSymbolHom b ω hF v
          ((pi (pairModels D E)).filtration.weightedAdaptedRealChartHom w v β hβ
            ⟨⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩⟩) := by
  unfold pairOrbitSymbol
  apply congrArg ((pi (pairModels D E)).filtration.realPolynomialSymbolHom b ω hF v)
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact (pairOrbit_polynomialOrbitRealChart_log D E p q β hβ).trans
    ((pi (pairModels D E)).filtration.weightedAdaptedRealChartHom_coord
      w v β hβ ⟨⟨(pairOrbit D E p q).log, (pairOrbit D E p q).property⟩⟩).symm

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedRankComponentCoefficientIndex
    (G X : Type*) (I E : Fin m → Type*) (n : Fin m → ℕ)
    (B : LayerSamplerAxis I n → Type*) (inactive : LayerSamplerAxis I n → Prop) :=
  Σ t : (Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j),
    AllocatedRankComponentCoefficient (G := G) (B := B) inactive t.1 t.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

noncomputable local instance congruenceIndexFintype_rbe5f36_1 [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    Fintype (AllocatedCongruenceCoefficientIndex X E inactive L) := inferInstance
noncomputable local instance congruenceIndexDecidableEq
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :
    DecidableEq (AllocatedCongruenceCoefficientIndex X E inactive L) := Classical.decEq _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)

theorem allocatedActualPrimeBad_iff_modulusBad (p : P) (a : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p.val a f ↔
      allocatedActualModulusBad inactive spatial kernel block C (p.val ^ a) f := by
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨p.property, h⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedFullChartAffineTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedLinearMapChart_homogeneous
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (v : X ⊕ (Σ j, J j)) :
    (fullTaggedLinearMapChart J P v).IsWeightedHomogeneous
      (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v) := by
  cases v with
  | inl x => exact isWeightedHomogeneous_X (R := ℝ) _ _
  | inr v =>
    apply (weightedHomogeneousSubmodule ℝ _ _).sum_mem
    intro a _
    exact (weightedHomogeneousSubmodule ℝ _ _).smul_mem _
      (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr ⟨v.1, a⟩))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolBasisIndependence
namespace OAI

universe u

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d e : ℕ} {σ ι κ : Type*} {w : σ → ℕ}

theorem pairOrbitSymbol_basis_independent
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (c : Basis κ ℚ (PairAlgebra L M)) (ν : κ → ℕ)
    (hC : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (c '' {i | k ≤ ν i})) :
    pairOrbitSymbol D E p q b ω hF = pairOrbitSymbol D E p q c ν hC :=
  (pi (pairModels D E)).filtration.realPolynomialSymbolHom_basis_independent
    b ω hF c ν hC w _

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplerSeparatedVariables
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {D G : Type*} {B : D → Type*}

def samplerFrozenRaw {R : Type*} [Zero R] (h : D → ℕ)
    (raw : PrincipalTupleIndex B h × Option Empty → R) :
    SamplerTupleIndex G B h → R :=
  fun
    | .inl _ => 0
    | .inr k => raw (k, none)

end Erdos3

end

end OAI
end


