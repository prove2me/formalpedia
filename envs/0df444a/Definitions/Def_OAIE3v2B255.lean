-- Prove2me | Definitions.Def_OAIE3v2B255
-- name    : OAIE3v2B255
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:40:15.823625+00:00
-- url     : https://prove2.me/theorems/d2594503-4099-4782-b4e0-76d7682ee484
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 261 of 311
-- statement:
--   Definitions bundle 261 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B248`, `OAIE3v2B249` of this split.
--
--   Modules: `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/MarkedUnitOrbit.lean`, `Estimates/NativeCoveredCommonFactorization.lean`, `Estimates/NativeSharedFreeFamily.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Lattices/NativeCorrelatedAffineExistence.lean`, `Linear/NativeSharedFreeRankRelation.lean`, `Polynomial/CommonAnchorPolynomialCorrections.lean`, `Polynomial/LocalPhaseMarkedObservable.lean`, `Polynomial/PolynomialPatchTaggedBufferedScore.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B248
import Definitions.Def_OAIE3v2B249

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CommonAnchorPolynomialCorrections
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependent_polynomial_corrections (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors) (h₀ : ZMod N),
            h₀ ∈ A.shifts ∧ A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∀ h ∈ A.shifts, ∃ E Q : W.family.rank.filtration.realification.associatedDegree.adaptedLieSubalgebra
                  (fun _ : Unit => 1),
                coefficients E.val 0 = 0 ∧ coefficients Q.val 0 = 0 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) E.val ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n Q.val ∧
                ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  ∃ e u : (W.family.rank.filtration.layer
                      (Finsupp.weight (fun _ : Unit => 1) (α d)) 1).baseChange ℝ,
                    coefficients E.val (α d) = e.val ∧ coefficients Q.val (α d) = u.val ∧
                    W.family.horizontalCoefficient hs c τ hG (α d) h -
                        W.family.horizontalCoefficient hs c τ hG (α d) h₀ -
                        W.family.rank.filtration.realHorizontalMap
                          (Finsupp.weight (fun _ : Unit => 1) (α d)) e -
                        W.family.rank.filtration.realHorizontalMap
                          (Finsupp.weight (fun _ : Unit => 1) (α d)) u ∈
                      (fourDependentProjection (D.horizontal
                        ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  obtain ⟨C, hC, hfamily⟩ := exists_native_dependent_representative_family s hs
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPC, R, D, A, h₀,
      hh₀, hAW, hdensity, n, hn, hnC, hproj, hrep⟩ := hfamily W hF c τ hG hN
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPC, R, D, A, h₀,
    hh₀, hAW, hdensity, n, hn, hnC, hproj, ?_⟩
  intro h hh
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  choose e u he hu hres using (fun d => hrep d (hd d) h hh)
  let E := positiveUnivariate (fun d => (e d).val)
  let Q := positiveUnivariate (fun d => (u d).val)
  refine ⟨⟨E, W.family.rank.filtration.positiveUnivariate_horizontal_mem e⟩,
    ⟨Q, W.family.rank.filtration.positiveUnivariate_horizontal_mem u⟩,
    positiveUnivariate_zero _, positiveUnivariate_zero _, ?_, ?_, ?_⟩
  · exact positiveUnivariate_coefficientBound (W.family.model.basis.baseChange ℝ)
      (fun d => (e d).val) (fun _ : Unit => (N : ℝ))
      (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_nonneg _) he
  · exact positiveUnivariate_coefficientGrid (W.family.model.basis.baseChange ℝ)
      (fun d => (u d).val) n hu
  · intro d hd'
    exact ⟨e d, u d, positiveUnivariate_coefficient _ d, positiveUnivariate_coefficient _ d, hres d⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCoveredCommonFactorization
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_common_dependent_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                  (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    hs c τ hG (fun _ : Unit => 1) (α d) ξ) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                ∀ h ∈ A.shifts, ∃ ε γ v : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit
                    (fun _ : Unit => 1),
                  W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                    (fun _ : Unit => 1) 0 ε = 1 ∧
                  W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                    (fun _ : Unit => 1) 0 γ = 1 ∧
                  W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                    (fun _ : Unit => 1) 0 v = 1 ∧
                  CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                    (Real.exp ((p + C) ^ C)) ε.log ∧
                  CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                  ε * ξ * v * γ = W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h) ∧
                  ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                    Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                      hs c τ hG (fun _ : Unit => 1) (α d) v) ∈
                      (fourDependentProjection (D.horizontal
                        ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  obtain ⟨a, _, hfamily⟩ := exists_native_dependent_polynomial_corrections s hs
  obtain ⟨C, hC, hbudget⟩ := exists_common_reference_correction_budget s a
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hBC, hcost⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A, h₀,
      hh₀, hAW, hdensity, n, hn, hnB, hproj, hcorrection⟩ :=
    hfamily W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hq : 0 ≤ q := hp.trans hpq
  have hP : 0 ≤ P := hq.trans hqP
  let S := (P + 3) ^ 2 + (s : ℝ) * q
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hSB : S ≤ (B + 3) ^ 2 + s * B :=
    add_le_add (pow_le_pow_left₀ (by linarith) (add_le_add hPB (le_refl 3)) 2)
      (mul_le_mul_of_nonneg_left (hqP.trans hPB) (Nat.cast_nonneg s))
  have hsum : Real.exp B + Real.exp S ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp B + Real.exp B + Real.exp S := by linarith [Real.exp_nonneg B]
      _ ≤ Real.exp (B + S + 2) := exp_repeated_add_le hB hS
      _ ≤ _ := Real.exp_le_exp.mpr ((add_le_add (add_le_add (le_refl B) hSB) (le_refl 2)).trans hcost)
  obtain ⟨E₀, Q₀, hE₀zero, hQ₀zero, hE₀, hQ₀, href⟩ :=
    A.exists_anchor_polynomial_corrections h₀ hh₀ hs hq hP c τ hG n hproj
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  choose e₀ u₀ he₀ hu₀ hfirst using (fun d => href d (hd d))
  let ε₀ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
    ⟨⟨E₀.val⟩, E₀.property⟩
  let γ₀ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
    ⟨⟨Q₀.val⟩, Q₀.property⟩
  let g₀ := W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h₀)
  let ξ := ε₀⁻¹ * g₀ * γ₀⁻¹
  have hε₀zero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 ε₀ = 1 :=
    (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ ε₀).mpr hE₀zero
  have hγ₀zero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 γ₀ = 1 :=
    (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ γ₀).mpr hQ₀zero
  have hg₀ : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 g₀ = 1 := W.family.orbit_rank_normalized h₀
  have hξzero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 ξ = 1 := by
    simp only [ξ, map_mul, map_inv, hε₀zero, hγ₀zero, hg₀, inv_one, one_mul]
  have hξvalue (d : Fin s) :
      Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
        hs c τ hG (fun _ : Unit => 1) (α d) ξ) =
      W.family.horizontalCoefficient hs c τ hG (α d) h₀ -
        W.family.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) (e₀ d) -
        W.family.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) (u₀ d) := by
    have he := W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
      hs c τ hG (fun _ : Unit => 1) (α d) ε₀ (e₀ d) (he₀ d).symm
    have hu := W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
      hs c τ hG (fun _ : Unit => 1) (α d) γ₀ (u₀ d) (hu₀ d).symm
    have h := toAdd_hom_corrected_reference
      (W.family.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ : Unit => 1) (α d)) ε₀ g₀ γ₀
    rw [he, hu] at h
    exact h
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hproj, ξ, hξzero, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro d hd'
    rw [hξvalue]
    exact hfirst d
  · intro h hh
    obtain ⟨E, Q, hEzero, hQzero, hE, hQ, hres⟩ := hcorrection h hh
    let ε : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
      ⟨⟨(E + E₀).val⟩, (E + E₀).property⟩
    let γ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
      ⟨⟨(Q + Q₀).val⟩, (Q + Q₀).property⟩
    let g := W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h)
    let v := ξ⁻¹ * ε⁻¹ * g * γ⁻¹
    have hεzero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
        (fun _ : Unit => 1) 0 ε = 1 := by
      apply (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ ε).mpr
      change coefficients (E.val + E₀.val) 0 = 0
      simp only [map_add, Finsupp.add_apply, hEzero, hE₀zero, add_zero]
    have hγzero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
        (fun _ : Unit => 1) 0 γ = 1 := by
      apply (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ γ).mpr
      change coefficients (Q.val + Q₀.val) 0 = 0
      simp only [map_add, Finsupp.add_apply, hQzero, hQ₀zero, add_zero]
    have hg : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
        (fun _ : Unit => 1) 0 g = 1 := W.family.orbit_rank_normalized h
    refine ⟨ε, γ, v, hεzero, hγzero, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [v, map_mul, map_inv, hξzero, hεzero, hg, hγzero, inv_one, one_mul]
    · exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N)
        (CoefficientBound.add _ _ hE hE₀) hsum
    · exact CoefficientGrid.add _ _ hQ hQ₀
    · change ε * ξ * v * γ = g
      dsimp only [v]
      group
    · intro d hd'
      obtain ⟨e, u, he, hu, hdep⟩ := hres d hd'
      let π := W.family.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d))
      have hεvalue : Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
          hs c τ hG (fun _ : Unit => 1) (α d) ε) = π e + π (e₀ d) := by
        apply (W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
          hs c τ hG (fun _ : Unit => 1) (α d) ε (e + e₀ d) ?_).trans (map_add π e (e₀ d))
        change e.val + (e₀ d).val = coefficients (E.val + E₀.val) (α d)
        rw [map_add, Finsupp.add_apply, he, he₀]
      have hγvalue : Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
          hs c τ hG (fun _ : Unit => 1) (α d) γ) = π u + π (u₀ d) := by
        apply (W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
          hs c τ hG (fun _ : Unit => 1) (α d) γ (u + u₀ d) ?_).trans (map_add π u (u₀ d))
        change u.val + (u₀ d).val = coefficients (Q.val + Q₀.val) (α d)
        rw [map_add, Finsupp.add_apply, hu, hu₀]
      have hv := toAdd_hom_corrected_factor
        (W.family.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ : Unit => 1) (α d)) ξ ε g γ
      rw [hξvalue d, hεvalue, hγvalue] at hv
      have hv' := hv.trans (sub_corrected_reference_add_errors
        (W.family.horizontalCoefficient hs c τ hG (α d) h)
        (W.family.horizontalCoefficient hs c τ hG (α d) h₀) (π e) (π u) (π (e₀ d)) (π (u₀ d)))
      exact (congrArg (fun z => z ∈ (fourDependentProjection (D.horizontal
        ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd'⟩)).baseChange ℝ) hv').mpr hdep

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_periodic_common_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n M : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    hs c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) ξ)) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
              ∀ h ∈ A.shifts, ∃ ε γ v : W.family.model.filtration.realification.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * ξ * v * γ = W.family.orbit h ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    hs c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) v)) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ) : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)) ∧
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ)⁻¹ : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)⁻¹) := by
  obtain ⟨a, _, hfactor⟩ := exists_native_common_dependent_factorization s hs
  obtain ⟨b, _, hperiod⟩ := exists_native_orbit_rational_period s
  obtain ⟨C, hC, hbudget⟩ := exists_native_periodic_factorization_budget a b
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hBC, hperiodC⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A,
      hAW, hdensity, n, hn, hnB, hproj, ξ, hξ₀, hfirst, hsplit⟩ :=
    hfactor W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B + 1 := (hpq.trans (hqP.trans hPB)).trans (by linarith)
  obtain ⟨M, hM, hMB, hMsolve⟩ := hperiod W.family.model (fun _ : Unit => 1)
    (fun _ => Nat.zero_lt_one) (B + 1) (by linarith)
    (RationalFilteredNilmanifold.GeometryComplexityLE.mono W.family.model W.family.complexity.1 hpB)
    (by simpa only [Fintype.card_unit, Nat.cast_one] using (show (1 : ℝ) ≤ B + 1 by linarith))
    n hn (hnB.trans (Real.exp_le_exp.mpr (by linarith)))
  have hlog (g : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1)) :
      ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g).log = g.log := by
    simpa only [MulEquiv.apply_symm_apply] using
      (W.family.rank.orbitEquiv_log (fun _ : Unit => 1)
        ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g)).symm
  have heval (g : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1))
      (x : Unit → ℤ) :
      W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x
          ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g) =
        W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval (fun _ : Unit => 1) x g := by
    simpa only [MulEquiv.apply_symm_apply] using
      (W.family.rank.orbitEquiv_eval (fun _ : Unit => 1)
        ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g) x).symm
  let ξ' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm ξ
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, M, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hM,
    hMB.trans (Real.exp_le_exp.mpr hperiodC), hproj, ξ', (heval ξ 0).trans hξ₀, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro d hd
    simpa only [ξ', MulEquiv.apply_symm_apply] using hfirst d hd
  · intro h hh
    obtain ⟨ε, γ, v, hε₀, hγ₀, hv₀, hε, hγ, heq, hdep⟩ := hsplit h hh
    let ε' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm ε
    let γ' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm γ
    let v' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm v
    have hgrid : CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ'.log := by
      simpa only [γ', hlog] using hγ
    refine ⟨ε', γ', v', (heval ε 0).trans hε₀, (heval γ 0).trans hγ₀,
      (heval v 0).trans hv₀, ?_, hgrid, ?_, ?_, hMsolve γ' hgrid⟩
    · apply CoefficientBound.mono (W.family.model.basis.baseChange ℝ)
        (fun _ : Unit => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N)
        (M := Real.exp B) _ (Real.exp_le_exp.mpr hBC)
      simpa only [ε', hlog] using hε
    · have hf := congrArg (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm heq
      simpa only [map_mul, MulEquiv.symm_apply_apply] using hf
    · intro d hd
      simpa only [v', MulEquiv.apply_symm_apply] using hdep d hd

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_frozen_common_factorization (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n M : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) ξ)) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
              ∀ h ∈ A.shifts, ∃ ε γ v : W.family.model.filtration.realification.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * ξ * v * γ = W.family.orbit h ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) v)) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                (∃ y : ZMod N,
                  (∀ x, ∑ i, ‖W.family.model.frozenCyclicOrbitValue
                    (W.family.vertical.observable i) ε (ξ * v) γ y x‖ ^ 2 = 1) ∧
                  Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                    (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
                      (W.family.vertical.observable i) ε (ξ * v) γ y x)))) ∧
                ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ) : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)) ∧
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ)⁻¹ : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)⁻¹) := by
  obtain ⟨a, _, hfactor⟩ := exists_native_periodic_common_factorization s (by omega)
  obtain ⟨b, _, hfreeze⟩ := exists_native_frozen_rank_correlation s 1 hs
  obtain ⟨C, hC, hbudget⟩ := exists_frozen_common_factorization_budget a b
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hBC, hFC⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A,
      hAW, hdensity, n, M, hn, hnB, hM, hMB, hproj, ξ, hξ₀, hfirst, hsplit⟩ :=
    hfactor W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B + 2 := (hpq.trans (hqP.trans hPB)).trans (by linarith)
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, M, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hM,
    hMB.trans (Real.exp_le_exp.mpr hBC), hproj, ξ, hξ₀, hfirst, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro h hh
    obtain ⟨ε, γ, v, hε₀, hγ₀, hv₀, hε, hγ, heq, hdep, hperiod⟩ := hsplit h hh
    have hε' : CoefficientBound (W.family.model.basis.baseChange ℝ)
        (fun _ : Unit => (N : ℝ)) (Real.exp (((B + 2) + 2) ^ 1)) ε.log :=
      CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) hε
        (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
    obtain ⟨y, hunit, V⟩ := hfreeze W hF ⟨h, hAW hh⟩ (B + 2) (by linarith) hpB M hM
      (hMB.trans (Real.exp_le_exp.mpr (by linarith))) ε ξ v γ heq hε'
      (fun x y hxy => (hperiod x y hxy).1) ((Real.exp_le_exp.mpr hFC).trans hN)
    refine ⟨ε, γ, v, hε₀, hγ₀, hv₀, ?_, hγ, heq, hdep,
      ⟨y, hunit, ⟨(Classical.choice V).mono hFC⟩⟩, hperiod⟩
    exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) hε
      (Real.exp_le_exp.mpr hBC)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSharedFreeFamily
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_shared_common_factorization (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n M : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) ξ)) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
              ∃ H' : Finset (ZMod N), H' ⊆ A.shifts ∧ H'.Nonempty ∧
                Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
              ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
                (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
                (Λ.subgroupOf W.family.model.lattice).Normal ∧
                (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
                (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                ∃ (K : ℕ) (hK : 0 < K)
                  (hin : scaledIntegerGrid K ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
                  (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid K),
                  (W.family.rank.withLattice Λ K hK hin hout).ComplexityLE ((p + C) ^ C) ∧
              ∃ U : (W.family.model.withLattice Λ K hK hin hout).UnitVerticalObservable
                  ((W.family.rank.withLattice Λ K hK hin hout).realSubgroup s r)
                  (Fin W.family.outputDim) ((p + C) ^ C),
                U.frequency = W.family.vertical.frequency ∧
              ∀ h ∈ H', ∃ ε γ v : W.family.model.filtration.realification.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * ξ * v * γ = W.family.orbit h ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) v)) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                  (W.replacedRankResidual h (fun i x => U.observable i (QuotientGroup.mk
                    (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v)))))) ∧
                ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ) : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)) ∧
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ)⁻¹ : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)⁻¹) := by
  obtain ⟨a, _, hfactor⟩ := exists_native_frozen_common_factorization s hs
  obtain ⟨b, _, hshared⟩ := exists_native_shared_frozen_orbit_correlations s 1
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B₀ + (B₀ + 2 + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  let T := (B + 2 + b) ^ b
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hcost : B + T + 2 ≤ (p + C) ^ C := by
    simpa [B₀, B, T, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : B ≤ (p + C) ^ C := by linarith
  have hTC : T ≤ (p + C) ^ C := by linarith
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A,
      hAW, hdensity, n, M, hn, hnB, hM, hMB, hproj, ξ, hξ₀, hfirst, hsplit⟩ :=
    hfactor W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B + 2 := (hpq.trans (hqP.trans hPB)).trans (by linarith)
  have hA : A.shifts.Nonempty := by
    have hcard : (0 : ℝ) < Fintype.card (ZMod N) := by exact_mod_cast Fintype.card_pos
    have hpos := (mul_pos (Real.exp_pos (-B)) hcard).trans_le hdensity
    exact Finset.card_pos.mp (by exact_mod_cast hpos)
  have hdata (h : {h // h ∈ A.shifts}) := hsplit h h.property
  choose ε γ v hε₀ hγ₀ hv₀ hε hγ heq hdep hy hperiod using hdata
  choose y _hunit V using hy
  let ε' (h : ZMod N) := if hh : h ∈ A.shifts then ε ⟨h, hh⟩ else 1
  let γ' (h : ZMod N) := if hh : h ∈ A.shifts then γ ⟨h, hh⟩ else 1
  let v' (h : ZMod N) := if hh : h ∈ A.shifts then v ⟨h, hh⟩ else 1
  let y' (h : ZMod N) := if hh : h ∈ A.shifts then y ⟨h, hh⟩ else 0
  have hε' (h : ZMod N) (hh : h ∈ A.shifts) :
      CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp (((B + 2) + 2) ^ 1)) (ε' h).log := by
    simp only [ε', dif_pos hh]
    exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) (hε ⟨h, hh⟩)
      (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hγ' (h : ZMod N) (hh : h ∈ A.shifts) :
      CoefficientGrid (W.family.model.basis.baseChange ℝ) n (γ' h).log := by
    simpa only [γ', dif_pos hh] using hγ ⟨h, hh⟩
  have hcorr (h : ZMod N) (hh : h ∈ A.shifts) :
      Nonempty (NativeVectorCorrelation (s - 1) N (B + 2)
        (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε' h) (ξ * v' h) (γ' h) (y' h) x))) := by
    simpa only [ε', γ', v', y', dif_pos hh] using
      (show Nonempty _ from ⟨(Classical.choice (V ⟨h, hh⟩)).mono (show B ≤ B + 2 by linarith)⟩)
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, K, hK, hin, hout,
      hRank, H', hsub, hnonempty, hdense, U, hfreq, hU⟩ :=
    hshared W hF (show 0 ≤ B + 2 by linarith) hpB n hn
      (hnB.trans (Real.exp_le_exp.mpr (by linarith)))
      A.shifts ε' γ' (fun h => ξ * v' h) y' hA hε' hγ' hcorr
  have hdense' : Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(B + T)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-T) * (Real.exp (-B) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-T) * A.shifts.card := mul_le_mul_of_nonneg_left hdensity (Real.exp_pos _).le
      _ ≤ _ := hdense
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, M, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hM,
    hMB.trans (Real.exp_le_exp.mpr hBC), hproj, ξ, hξ₀, hfirst,
    H', hsub, hnonempty, hdense', Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hTC), K, hK, hin, hout, hRank.mono _ hTC,
    U.mono hTC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro h hh
    let h' : {h // h ∈ A.shifts} := ⟨h, hsub hh⟩
    refine ⟨ε h', γ h', v h', hε₀ h', hγ₀ h', hv₀ h', ?_, hγ h', heq h', hdep h', ?_, hperiod h'⟩
    · exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) (hε h')
        (Real.exp_le_exp.mpr hBC)
    · simpa only [v', dif_pos (hsub hh), h', UnitVerticalObservable.mono] using
        (show Nonempty _ from ⟨(Classical.choice (hU h hh)).mono hTC⟩)

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_shared_free_family (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
        Real.exp ((p + C) ^ C) ≤ N →
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (B : D.CoefficientBases ((p + C) ^ C))
            (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
              (finrank ℚ D.CoefficientFreeLieAlgebra))
            (T : E.DegreeRankStructure r),
            T.filtration = D.coefficientFreeFiltration ∧
            T.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
            Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
               IsModuleTopology.topologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 E.basis
             ∃ V : E.UnitVerticalObservable (T.realSubgroup s r)
                 (Fin W.family.outputDim) ((p + C) ^ C),
               V.frequency = B.freeFrequency D ∧
               ∃ ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                 E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                 (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
                   (D.commonFreeSpan d).baseChange ℝ) ∧
                 ∃ H' : Finset (ZMod N), H' ⊆ H ∧ H' ⊆ W.shifts ∧ H'.Nonempty ∧
                   CyclicShortShiftSet H' ∧
                   Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                   ∀ h ∈ H', ∃ v : E.filtration.realification.PolynomialOrbit
                       (fun _ : Unit => 1),
                     E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                     (∀ d : Fin s, coefficients v.log (Finsupp.single () (d.val + 1)) ∈
                       (D.dependentFreeSpan d).baseChange ℝ) ∧
                     Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                       (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
                         (E.filtration.realification.polynomialOrbitEval
                           (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))))))) := by
  obtain ⟨a, _, hshared⟩ := exists_native_shared_common_factorization s hs
  obtain ⟨b, _, hbases⟩ := NativeRankRelation.CommonData.exists_controlled_coefficient_bases
  obtain ⟨e, _, hfree⟩ := NativeRankRelation.CommonData.exists_native_common_free_model s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let M₀ : Polynomial ℕ := A₀ + (A₀ + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (M₀ + (M₀ + Polynomial.C e) ^ e)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  obtain ⟨c, τ, _, _, _, hLayers, _⟩ :=
    W.family.model.exists_controlled_adapted_basis hp W.family.complexity.1
  have hG (j : ℕ) : W.family.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}) := by
    rw [W.family.rank.associated]
    exact hLayers j
  let A := (p + a) ^ a
  let M := A + (A + b) ^ b
  let Q := (M + e) ^ e
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hAB : 0 ≤ (A + b) ^ b := by positivity
  have hM : 0 ≤ M := add_nonneg hA hAB
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hAM : A ≤ M := le_add_of_nonneg_right hAB
  have hMC : M ≤ (p + C) ^ C := by
    have h : M + Q ≤ (p + C) ^ C := by
      simpa [A₀, M₀, A, M, Q, Polynomial.eval₂_pow] using hbudget p hp
    exact (le_add_of_nonneg_right hQ).trans h
  have hQC : Q ≤ (p + C) ^ C := by
    have h : M + Q ≤ (p + C) ^ C := by
      simpa [A₀, M₀, A, M, Q, Polynomial.eval₂_pow] using hbudget p hp
    exact (le_add_of_nonneg_left hM).trans h
  have hAC := hAM.trans hMC
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA, R, D, anchors,
      hanchors, _hdensity, n, m, _hn, _hnA, _hm, _hmA, _hproj, ξ, hξ0, hcommon,
      H', hsub, hnonempty, hdense, Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex,
      k, hk, hin, hout, hRank, U, hfreq, hfactor⟩ :=
    hshared W hf c τ hG ((Real.exp_le_exp.mpr hAC).trans hN)
  have hP : 0 ≤ P := hp.trans (hpq.trans hqP)
  obtain ⟨B₀⟩ := hbases D hP (hpq.trans hqP)
  have hBM : (P + b) ^ b ≤ M := by
    calc
      (P + b) ^ b ≤ (A + b) ^ b :=
        pow_le_pow_left₀ (by positivity) (by change P + (b : ℝ) ≤ A + b; linarith) b
      _ ≤ M := le_add_of_nonneg_left hA
  let B := B₀.mono D hBM
  obtain ⟨E, T, hT, hTc, hcentral, ⟨frame⟩, _hmatrix, _hlattice, hV⟩ :=
    hfree D B (W.family.model.withLattice Λ k hk hin hout)
      (W.family.rank.withLattice Λ k hk hin hout) rfl rfl hM
      (hRank.mono _ hAM) (Fin W.family.outputDim) (U.mono hAM)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hVfreq, hVobs⟩ := hV
  have hdegree (d : Fin s) :
      Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) ≤ s := by
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  have hξcoeff (d : Fin s) : coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ := by
    have h := (D.native_coefficient_mem_common (by omega) c τ hG (fun _ : Unit => 1)
      (Finsupp.single () (d.val + 1)) (hdegree d) ξ).mpr (hcommon d (hdegree d))
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using h
  obtain ⟨ξ', hξ'0, hξ'coeff, _hξ'log, hξ'eval⟩ :=
    B.exists_native_commonFreePolynomialOrbit D E T hT ξ hξ0 hξcoeff
  have hH'H : H' ⊆ H := hsub.trans anchors.shifts_subset
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA.trans hAC, R, D,
    B.mono D hMC, E, T, hT, hTc.mono T hQC, hcentral, ⟨frame.mono hQC⟩, V.mono hQC, ?_, ξ', hξ'0,
    hξ'coeff, H', hH'H, hsub.trans hanchors, hnonempty,
    (fun x hx y hy => hshort x (hH'H hx) y (hH'H hy)), ?_, ?_⟩
  · change V.frequency = W.family.vertical.frequency.comp (B.freeEvaluation D).toLinearMap
    change V.frequency = U.frequency.comp (B.freeEvaluation D).toLinearMap at hVfreq
    rw [hfreq] at hVfreq
    exact hVfreq
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hAC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    obtain ⟨ε, γ, v, _hε0, _hγ0, hv0, _hε, _hγ, _heq, hdep, hcorr, _hperiod⟩ := hfactor h hh
    have hvcoeff (d : Fin s) : coefficients v.log (Finsupp.single () (d.val + 1)) ∈
        (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ := by
      have h := (D.native_coefficient_mem_dependent (by omega) c τ hG (fun _ : Unit => 1)
        (Finsupp.single () (d.val + 1)) (hdegree d) v).mpr (hdep d (hdegree d))
      simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using h
    obtain ⟨v', hv'0, hv'coeff, _hv'log, hv'eval⟩ :=
      B.exists_native_dependentFreePolynomialOrbit D E T hT v hv0 hvcoeff
    refine ⟨v', hv'0, hv'coeff, ?_⟩
    have hvalue (i : Fin W.family.outputDim) (x : ZMod N) :
        (V.mono hQC).observable i (QuotientGroup.mk
          (E.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ' * v'))) =
        U.observable i (QuotientGroup.mk
          (W.family.model.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))) := by
      change V.observable i _ = _
      rw [hVobs]
      change U.observable i _ = U.observable i _
      congr 2
      rw [map_mul, map_mul, hξ'eval, hv'eval, map_mul]
    have heq : (fun (i : Fin W.family.outputDim) (x : ZMod N) =>
        (V.mono hQC).observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ' * v')))) =
        (fun (i : Fin W.family.outputDim) (x : ZMod N) => U.observable i (QuotientGroup.mk
          (W.family.model.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v)))) :=
      funext fun i => funext (hvalue i)
    rw [heq]
    exact ⟨(Classical.choice hcorr).mono hAC⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeSharedFreeRankRelation
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_shared_free_rank_relation (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ N →
      ∃ (A : ℝ) (hpA : p ≤ A), A ≤ (p + C) ^ C ∧
      ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
        H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
        p ≤ q ∧ q ≤ P ∧ P ≤ A ∧
        ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
          (B : D.CoefficientBases A)
          (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
            (finrank ℚ D.CoefficientFreeLieAlgebra))
          (T : E.DegreeRankStructure r) (hT : T.ComplexityLE A),
          T.filtration = D.coefficientFreeFiltration ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis A) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) A,
             V.frequency = B.freeFrequency D ∧
             ∃ (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
               (hξ : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1),
               (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
                 (D.commonFreeSpan d).baseChange ℝ) ∧
               ∃ H' : Finset (ZMod N), H' ⊆ H ∧ H' ⊆ W.shifts ∧ H'.Nonempty ∧
                 CyclicShortShiftSet H' ∧
                 Real.exp (-A) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                 ∃ (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
                   (hv : ∀ h, E.filtration.realification.polynomialOrbitEval
                     (fun _ : Unit => 1) 0 (v h) = 1),
                   (∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
                     (D.dependentFreeSpan d).baseChange ℝ) ∧
                   (∀ h ∈ H', Nonempty (NativeVectorCorrelation (s - 1) N A
                     (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
                       (E.filtration.realification.polynomialOrbitEval
                         (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v h))))))) ∧
                   (let U := W.replacementFamily E T hpA hT V (fun h => ξ * v h)
                     (fun h => by rw [map_mul, hξ, hv h, one_mul])
                    ∃ (out' : Fin U.outputDim) (H'' : Finset (ZMod N)) (q' : ℝ),
                      H'' ⊆ H' ∧ H''.Nonempty ∧ CyclicShortShiftSet H'' ∧
                      Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H''.card : ℝ) ∧
                      A ≤ q' ∧ q' ≤ (p + C) ^ C ∧
                      ∃ R' : NativeRankRelation U out' H'' q' q',
                        Nonempty (R'.CommonData ((p + C) ^ C)))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_shared_free_family s hs
  obtain ⟨c, _, hrelation⟩ := exists_native_common_rank_relation s (by omega)
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_eval_budget (A₀ + (A₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let A := (p + a) ^ a
  let Z := (A + c) ^ c
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hAZ : A + Z ≤ (p + C) ^ C := by
    simpa [A₀, A, Z, Polynomial.eval₂_pow] using hbudget p hp
  have hAC : A ≤ (p + C) ^ C := (le_add_of_nonneg_right hZ).trans hAZ
  have hZC : Z ≤ (p + C) ^ C := (le_add_of_nonneg_left hA).trans hAZ
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA, R, D, B, E, T,
    hfiltration, hT, hcentral, hframe, hdata⟩ :=
    hfree W hf ((Real.exp_le_exp.mpr hAC).trans hN)
  have hpA : p ≤ A := hpq.trans (hqP.trans hPA)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, H', hH'H, hH'W, hH', hshort', hdense, hfactor⟩ := hdata
  have hall (h : ZMod N) :
      ∃ v : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
        (∀ d : Fin s, coefficients v.log (Finsupp.single () (d.val + 1)) ∈
          (D.dependentFreeSpan d).baseChange ℝ) ∧
        (h ∈ H' → Nonempty (NativeVectorCorrelation (s - 1) N A
          (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
            (E.filtration.realification.polynomialOrbitEval
              (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))))))) := by
    by_cases hh : h ∈ H'
    · obtain ⟨v, hv, hcoeff, hc⟩ := hfactor h hh
      exact ⟨v, hv, hcoeff, fun _ => hc⟩
    · refine ⟨1, map_one _, ?_, fun hh' => (hh hh').elim⟩
      intro d
      change (0 : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) ∈ _
      exact Submodule.zero_mem _
  choose v hv hcoeff hcorr using hall
  let X := W.replaceRank E T hpA hT V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) H' hH' hdense hcorr
  obtain ⟨out', H'', q', hsub, hnonempty, hshort'', hdense'', hAq, hqZ, R', ⟨D'⟩⟩ :=
    hrelation X hf ((Real.exp_le_exp.mpr hZC).trans hN)
  refine ⟨A, hpA, hAC, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hfiltration, hcentral, hframe, V, hfreq, ξ, hξ, hcommon,
    H', hH'H, hH'W, hH', hshort', hdense, v, hv, hcoeff, hcorr,
    out', H'', q', hsub, hnonempty, hshort'', ?_, hAq, hqZ.trans hZC, R', ⟨D'.mono hZC⟩⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hZC))
    (Nat.cast_nonneg _)).trans hdense''

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ) (u : Fin t → ℝ)

noncomputable def commonAffineMarkedLift (h n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
    (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j) +
    (h : ℚ) • realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y u j))

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedUnitOrbit
namespace OAI


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N)

noncomputable def localAffineMarkedLift (h : ZMod N) (n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  D.commonAffineMarkedLift t (D.localAffineMarkedBase t x y u c h₀) y u h.val n

end Erdos3.NativeRankRelation.CommonData


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalPhaseMarkedObservable
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def localPhaseMarkedOrbit :
    (D.markedQuotientMultidegree t).realification.PolynomialOrbit :=
  Mul.mul (α := (D.markedQuotientMultidegree t).realification.PolynomialOrbit)
    (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)
    (realMarkedParameterOrbit D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t
        (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i) :
      (D.markedQuotientMultidegree t).realification.PolynomialOrbit)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)

variable (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def localPhaseMarkedLift (h : ZMod N) (n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  realMarkedAffineShift D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t
      (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)
      (D.commonAffineMarkedLift t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def HasCommonInducedCorrelationFamily
    {τ K I J : Type*} [Fintype I] [Fintype J]
    {s k r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T J Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (f : τ → K → ZMod N → ℂ) (B : ℝ) : Prop :=
    ∃ (m : ℕ) (_hm : 0 < m), (m : ℝ) ≤ Real.exp B ∧
            ∃ d : ℕ, d ≤ n * (s + 1) * (t + 1) ^ s + t ∧
              ∃ E : RationalFilteredNilmanifold
                (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
                  D.coefficientWeight D.coefficientIsDependent t) (s + 1) d,
                ∃ M : E.MultidegreeStructure (mixedCorrelationDegree s),
                  M.filtration = D.markedQuotientMultidegree t ∧ M.ComplexityLE B ∧
                  (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
                     D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
                   letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
                     D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
                       IsModuleTopology.topologicalAddGroup ℝ _
                   letI := realification_moduleTopology_t2 E.basis
                   letI := E.metricSpace
                   ∃ G : J → E.Space → ℂ,
                     (∀ j z, ‖G j z‖ ≤ 2) ∧
                     (∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) ∧
                     ∀ z, Nonempty (NativeVectorCorrelation degree N B
                       (fun ij : K × ((I × I) × (I × J)) => fun n =>
                         f z ij.1 n * star (G ij.2.2.2 (QuotientGroup.mk
                           ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
                             (correlationInput ((h z).val : ℤ) (n.val : ℤ))
                             (D.localPhaseMarkedOrbit t x y u c h₀ m)))) *
                         star (V.observable ij.2.1.1 (QuotientGroup.mk
                             (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                               (fun _ => (n.val : ℤ)) (v z))) *
                           star (V.observable ij.2.1.2 (QuotientGroup.mk
                             (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                               (fun _ => (n.val : ℤ)) (a z))))) *
                         star (mapDifferenceObservable V U D.dependentQuotientMap hφ ij.2.2 (QuotientGroup.mk
                           (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                             (fun _ => (n.val : ℤ)) (a z)))))))

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem HasCommonInducedCorrelationFamily.mono
    {τ K I J : Type*} [Fintype I] [Fintype J]
    {s k r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T J Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (f : τ → K → ZMod N → ℂ) {B C : ℝ}
    (hfamily : D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ x y u c h₀ h a v f B)
    (hBC : B ≤ C) :
    D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ x y u c h₀ h a v f C := by
  obtain ⟨m, hm, hmp, d, hdim, E, M, hMF, hM, hobs⟩ := hfamily
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hBC), d, hdim, E, M, hMF,
    hM.mono M hBC, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let := E.metricSpace
  obtain ⟨G, hGn, hGL, hcorr⟩ := hobs
  refine ⟨G, hGn, ?_, ?_⟩
  · intro j
    exact (hGL j).weaken (show (⟨Real.exp B, Real.exp_nonneg _⟩ : ℝ≥0) ≤
      ⟨Real.exp C, Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hBC)
  · intro z
    exact (hcorr z).map (fun W => W.mono hBC)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {τ K I : Type} [Fintype I] {s r N n degree : ℕ} [NeZero N]
  {b p q P Z : ℝ} {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b}
  {out : Fin W.outputDim} {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
  (D : R.CommonData P) (t : ℕ)
  (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : A.DegreeRankStructure (r + 1))
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : A.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Z)
  (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
  (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (f : τ → K → ZMod N → ℂ)

def HasCoveredInducedCorrelationFamily (B : ℝ) : Prop :=
  ∃ Λ : Subgroup A.filtration.Group, Λ ≤ A.lattice ∧
    ∃ (m : ℕ) (hm : 0 < m)
      (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates A.basis Λ)
      (hout : bchSubgroupCoordinates A.basis Λ ⊆ denominatorGrid m),
      let A₀ := A.withLattice Λ m hm hin hout
      let T₀ := T.withLattice Λ m hm hin hout
      T₀.ComplexityLE B ∧
      ∃ e : ℕ, e ≤ n ∧ ∃ Q : RationalFilteredNilmanifold D.DependentQuotient s e,
        ∃ S : Q.DegreeRankStructure (r + 1),
          S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE B ∧
          ∃ hφ : A₀.lattice ≤ Q.lattice.comap (mapOfSteps
            (hL := A₀.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap),
            ∃ V₀ : A₀.UnitVerticalObservable (T₀.realSubgroup s (r + 1)) I B,
              V₀.frequency = V.frequency ∧
              (∀ i z, V₀.observable i (QuotientGroup.mk z) = V.observable i (QuotientGroup.mk z)) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 Q.basis
               ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp B ∧
                 ∃ U : Q.UnitVerticalObservable (S.realSubgroup s (r + 1)) (Fin k) B,
                   D.HasCommonInducedCorrelationFamily (degree := degree)
                     t A₀ Q V₀ U hφ x y u c h₀ h a v f B ∧
                   A₀.HasLowerRankOrbitFamily T₀ (fun _ : Unit => 1)
                     (fun z ij w => mapDifferenceObservable V₀ U D.dependentQuotientMap hφ ij
                       (QuotientGroup.mk (A₀.filtration.realification.polynomialOrbitEval
                         (fun _ : Unit => 1) w (a z)))) B)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeCorrelatedAffineExistence
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def nativeSharedFreeRelationConstant (s : ℕ) (hs : 2 ≤ s) : ℕ :=
  (exists_native_shared_free_rank_relation s hs).choose

def NativeCorrelationStructure.HasCorrelatedAffineComparison
    {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s (r + 1) N p f) (hs : 2 ≤ s) (C : ℕ) : Prop :=
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  ∃ (A : ℝ) (hpA : p ≤ A), A ≤ Z ∧
  ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
    H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧ p ≤ q ∧ q ≤ P ∧ P ≤ A ∧
    ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
      (B : D.CoefficientBases A)
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
        (finrank ℚ D.CoefficientFreeLieAlgebra))
      (T : E.DegreeRankStructure (r + 1)) (hT : T.ComplexityLE A),
      T.filtration = D.coefficientFreeFiltration ∧ IsCentralLieBasis E.basis ∧
      Nonempty (FreeCoordinateFrame E.basis A) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 E.basis
       ∃ V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) A,
         V.frequency = B.freeFrequency D ∧
         ∃ (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
           (hξ : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1),
           (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
             (D.commonFreeSpan d).baseChange ℝ) ∧
           ∃ (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
             (hv : ∀ h, E.filtration.realification.polynomialOrbitEval
               (fun _ : Unit => 1) 0 (v h) = 1),
             (∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
               (D.dependentFreeSpan d).baseChange ℝ) ∧
             (let U := W.replacementFamily E T hpA hT V (fun h => ξ * v h)
                (fun h => by rw [map_mul, hξ, hv h, one_mul])
              ∃ (out' : Fin U.outputDim) (H' : Finset (ZMod N)) (q' : ℝ),
                H' ⊆ W.shifts ∧ H'.Nonempty ∧ CyclicShortShiftSet H' ∧
                Real.exp (-Z) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                A ≤ q' ∧ q' ≤ Z ∧
                ∃ (R' : NativeRankRelation U out' H' q' q') (D' : R'.CommonData Z),
                  D.CorrelatedAffineComparison E T hpA hT V (fun h => ξ * v h)
                    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs ∧
                  Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
                    sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C ∧
                  ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
                    nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
                  nativeLowerPairModelBudget s
                    (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
                    (p + C) ^ C))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchTaggedBufferedScore
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {τ : Type*} (p : τ → ℕ) {d s : ℕ} {w : Fin d → ℕ}
variable [Fintype (PolynomialShearIndex w)]

noncomputable def weightedPolynomialShearOrbitSymbolicHom (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit p) :
    MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ :=
  polynomialShearExpHom (polynomialSymbolicShearDerivation w
    (weightedPolynomialShearOrbitParameterCoordinates s hw p g))

end Erdos3

end

end OAI
end


