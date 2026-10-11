-- Prove2me | Definitions.Def_OAIErdos3B201
-- name    : OAIErdos3B201
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T15:38:31.443349+00:00
-- url     : https://prove2.me/theorems/5f559956-a30a-430a-b918-f45ae50d0504
-- title:
--   OpenAI Erdős-3 split, definitions bundle 202 of 207
-- statement:
--   Definitions bundle 202 of 207 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B200`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 202 available.
--
--   Modules: `OAI.Erdos3.NativeDegreeRankDerivativeData`, `OAI.Erdos3.NativeDegreeRankDerivativeData.mono`, `OAI.Erdos3.NativeDegreeRankDerivativeData.rank_integral`, `OAI.Erdos3.NativeDegreeRankDerivativeData.rank_vertical`, `OAI.Erdos3.NativeDegreeRankDerivativeData.toFamily`, `OAI.Erdos3.NativeDegreeRankDerivativeData.toFamily_correlation`, `OAI.Erdos3.NativeDegreeRankDerivativeData.toFamily_evalCyclic`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_common_induced_correlation_family`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_covered_induced_correlation_family`, `OAI.Erdos3.NativeUnitVerticalData`, `OAI.Erdos3.NativeUnitVerticalData.mono`, `OAI.Erdos3.NativeUnitVerticalData.test`, `OAI.Erdos3.NativeUnitVerticalData.test_complexity`, `OAI.Erdos3.NativeUnitVerticalData.test_zero_correlation`, `OAI.Erdos3.NativeUnitVerticalData.test_zero_evalCyclic`, `OAI.Erdos3.QuadraticMarked.exists_model`, `OAI.Erdos3.QuadraticMarked.exists_model_from_seed`, `OAI.Erdos3.exists_compatible_marked_evaluation_model`, `OAI.Erdos3.exists_degree_rank_native_inverse_models`, `OAI.Erdos3.exists_induced_marked_model`, `OAI.Erdos3.exists_markedShift_evaluation_model_with_budget`, `OAI.Erdos3.exists_native_induced_marked_model`, `OAI.Erdos3.exists_native_unit_vertical_data`, `OAI.Erdos3.exists_normalized_marked_model`, `OAI.Erdos3.exists_quadratic_antisymmetric_box`, `OAI.Erdos3.exists_quadratic_bounded_family`, `OAI.Erdos3.exists_quadratic_bounded_mixed_correlation`, `OAI.Erdos3.exists_quadratic_corner_model`, `OAI.Erdos3.exists_quadratic_cyclic_antisymmetric`, `OAI.Erdos3.exists_quadratic_fixed_mixed_correlation`, `OAI.Erdos3.exists_quadratic_native_mixed_correlation`, `OAI.Erdos3.exists_quadratic_pair_correlator`, `OAI.Erdos3.exists_quadratic_reflected_model`, `OAI.Erdos3.exists_unit_vertical_native_inverse_models`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B192
import Definitions.Def_OAIErdos3B204

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3

open Module

variable {I ι ν L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hH hc hgen in
theorem exists_markedShift_evaluation_model_with_budget (t : ℕ)
    (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
    (c : Basis ν ℚ (L ⧸ J)) {K : ℕ}
    (hcoef : ∀ i j, RationalHeightLE (c.repr (lieQuotientMap J (b j)) i) K)
    (l : ℕ) (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card ι : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hKp : (K : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
      ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
        ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
          M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
          M.ComplexityLE (markedShiftModelBudget s p) ∧ l ∣ D.grid ∧
          bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
          (∀ i j, rationalLogHeight
            (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤
              markedShiftModelBudget s p) ∧
          (∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤
            markedShiftModelBudget s p) ∧
          ∀ i j, rationalLogHeight (c.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤
            markedShiftModelBudget s p := by
  classical
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  have ha : a ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t :=
    F.associatedDegree.polynomialShift_finrank_le b ω hF hω t
  have hd : d ≤ a := (markedShiftSubalgebra F v w marked t).toSubmodule.finrank_le
  have hi : finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ≤ d :=
    (markedShiftSecondIdeal F v w marked t).toSubmodule.finrank_le
  let R := markedShiftInputBudget s p
  let Q := markedShiftHeightBudget s p
  have hpR : p ≤ R := le_markedShiftInputBudget s hp
  have hR : 0 ≤ R := markedShiftInputBudget_nonneg s hp
  have hRQ : R ≤ Q := markedShiftInputBudget_le_height s hp
  have hQS : Q ≤ markedShiftModelBudget s p := markedShiftHeightBudget_le_model s hp
  have haR : (a : ℝ) ≤ R := (Nat.cast_le.mpr ha).trans
    (markedShift_dimension_budget s (Fintype.card ι) t hp hn ht)
  have hdR : (d : ℝ) ≤ R := (Nat.cast_le.mpr hd).trans haR
  obtain ⟨m, hm, q, hq, f, hstructure, hlayers, hdirection, hphase, heval⟩ :=
    exists_markedShiftQuotient_bounded_evaluation_data F b ω hF hω v w marked hw hv hH hc hgen
      t J hJ c hcoef
  choose c' hc' using hlayers
  let M₀ := markedShiftMultidegree F v w marked hw hv t
  obtain ⟨B, hB, hdiv, hbound, D, M, hMF, hDf, hgrid, hcoords, hcomplex⟩ :=
    M₀.exists_bounded_integral_model f c' hc' hstructure l hl
  have hmR : (m : ℝ) ≤ R := (Nat.cast_le.mpr (hm.trans hi)).trans hdR
  have hqR : (q : ℝ) ≤ R := (Nat.cast_le.mpr hq).trans hdR
  have hheight : (markedEvaluationHeight s (Fintype.card ι) a d m q H K : ℝ) ≤ Real.exp Q :=
    markedEvaluationHeight_le_exp s (Fintype.card ι) a d m q H K hR
      (step_le_markedShiftInputBudget s hp) (hn.trans hpR) haR hdR hmR hqR
      (hHp.trans (Real.exp_le_exp.mpr hpR)) (hKp.trans (Real.exp_le_exp.mpr hpR))
  have hgridS : (B : ℝ) ≤ Real.exp (markedShiftModelBudget s p) := by
    have hb := integral_grid_allowance_le_exp (bchIntegralDenominatorBound (s + 1)) q
      (markedEvaluationHeight s (Fintype.card ι) a d m q H K) l
      (hR.trans hRQ) (hqR.trans hRQ) hheight
      (hlp.trans (Real.exp_le_exp.mpr (hpR.trans hRQ)))
    exact (Nat.cast_le.mpr hbound).trans (hb.trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left (hR.trans hRQ))))
  refine ⟨q, hq.trans (hd.trans ha), D, M, hMF,
    hcomplex _ (hqR.trans (hRQ.trans hQS)) hgridS
      (hheight.trans (Real.exp_le_exp.mpr hQS)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgrid]
    exact hdiv
  · simpa only [hgrid] using hcoords
  · intro i j
    rw [hDf]
    exact (rationalLogHeight_le_of_height (hdirection i j) hheight).trans hQS
  · intro i j
    rw [hDf]
    exact (rationalLogHeight_le_of_height (hphase i j) hheight).trans hQS
  · intro i j
    rw [hDf]
    exact (rationalLogHeight_le_of_height (heval i j) hheight).trans hQS

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_compatible_marked_evaluation_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I ι L : Type*} [Fintype I] [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] {r t e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (_hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      (E : RationalFilteredNilmanifold (L ⧸ J) u e) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (t : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      (∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap J (b j)) i) ≤ p) →
      ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
        ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
          ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
            M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
            M.ComplexityLE ((p + C) ^ C) ∧
            bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
            (∀ i j, rationalLogHeight
              (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤
                (p + C) ^ C) ∧
            (∀ i j, rationalLogHeight (markedQuotientPhase F v w marked t (D.basis j) i) ≤
              (p + C) ^ C) ∧
            (∀ i j, rationalLogHeight
              (E.basis.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤
                (p + C) ^ C) ∧
            (∀ z : D.filtration.Group, z ∈ D.lattice →
              (⟨markedBaseEvaluation F v w marked t J hJ 0 z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
            (∀ z : D.filtration.Group, z ∈ D.lattice →
              IntegralVector (markedQuotientPhase F v w marked t z.coord)) ∧
            (∀ z : D.RealGroup, z ∈ D.realLattice →
              (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈
                E.realLattice) ∧
            ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∀ a : Fin t → ℤ,
                (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                  D.filtration.Group) ∈ D.lattice := by
  obtain ⟨a, ha, hmodelbudget⟩ := exists_markedShiftModel_budget s
  obtain ⟨c, hcoverC, hcover⟩ := exists_marked_evaluation_lattice s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + 1 + Polynomial.C a) ^ a
  let Q₀ := (P₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + Q₀ + (Q₀ + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro I ι L _ _ _ _ r t e u F b ω hF hω v w marked hw hv J hJ E p hp hn ht hc hgen hE hcoef
  let P := (p + 1 + a) ^ a
  let Q := (P + c) ^ c
  have hp1 : p ≤ p + 1 := by linarith
  have hp1P : p + 1 ≤ P := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    calc
      p + 1 ≤ p + 1 + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + 1 + a) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ a)
  have hpP : p ≤ P := hp1.trans hp1P
  have hP : 0 ≤ P := hp.trans hpP
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hPQ : P ≤ Q := by
    have hc1 : 1 ≤ c := by omega
    have hc1' : (1 : ℝ) ≤ c := by exact_mod_cast hc1
    calc
      P ≤ P + c := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (P + c) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hc1
  have htotal : P + Q + (Q + 3) ^ 3 ≤ (p + C) ^ C := by
    simpa [X, P₀, Q₀, P, Q, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C := by
    have hn3 : 0 ≤ (Q + 3) ^ 3 := by positivity
    linarith
  have hQC : Q ≤ (p + C) ^ C := by
    have hn3 : 0 ≤ (Q + 3) ^ 3 := by positivity
    linarith
  have hmC : (Q + 3) ^ 3 ≤ (p + C) ^ C := by linarith
  have hS : markedShiftModelBudget s (p + 1) ≤ P := hmodelbudget (p + 1) (by linarith)
  obtain ⟨q, hqdim, D, M, hMF, hM, _, hcoords, hdir, hphase, heval⟩ :=
    exists_markedShift_evaluation_model_with_budget F b ω hF hω v w marked hw hv
      (one_le_ceil_exp p) (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
      (fun i j => rationalHeightLE_ceil_exp (hgen i j)) t J hJ E.basis
      (fun i j => rationalHeightLE_ceil_exp (hcoef i j)) 1 (by decide)
      (by linarith : 0 ≤ p + 1) (hn.trans hp1) (ht.trans hp1)
      (ceil_exp_le_exp_add_one hp) (ceil_exp_le_exp_add_one hp)
      (by exact_mod_cast Real.one_le_exp (by linarith : 0 ≤ p + 1))
  have hMP : M.ComplexityLE P := hM.mono M hS
  have hdirP (i j) := (hdir i j).trans hS
  have hphaseP (i j) := (hphase i j).trans hS
  have hevalP (i j) := (heval i j).trans hS
  obtain ⟨B, Λ, hB, hin, hout, _, _, hgrid, hMQ, hmap, hintegral, hrealmap⟩ :=
    hcover F v w marked D M J hJ E hP hMP (hE.mono E hpP) (ht.trans hpP) hevalP hphaseP
  let D' := D.withLattice Λ B hB hin hout
  let M' := M.withLattice Λ B hB hin hout
  have hdirQ : ∀ i j, rationalLogHeight
      (D'.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ Q :=
    fun i j => (hdirP i j).trans hPQ
  have htQ : (t : ℝ) ≤ Q := (ht.trans hpP).trans hPQ
  obtain ⟨m, hm, hmb, hmlattice⟩ := exists_marked_direction_lattice_scale F v w marked t D'
    hQ hMQ.1.1 htQ hMQ.1.2.1 hdirQ
  refine ⟨q, hqdim, D', M', hMF, hMQ.mono M' hQC, hgrid,
    (fun i j => (hdirP i j).trans hPC), (fun i j => (hphaseP i j).trans hPC),
    (fun i j => (hevalP i j).trans hPC), hmap, hintegral, hrealmap,
    m, hm, hmb.trans (Real.exp_le_exp.mpr hmC), hmlattice⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_normalized_marked_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I ι L : Type*} [Fintype I] [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] {r t e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (_hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      (E : RationalFilteredNilmanifold (L ⧸ J) u e) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (t : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      (∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap J (b j)) i) ≤ p) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
          ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
            ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
              M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
              M.ComplexityLE ((p + C) ^ C) ∧
              (∀ i j, rationalLogHeight
                (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤
                  (p + C) ^ C) ∧
              (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤
                (p + C) ^ C) ∧
              (∀ i j, rationalLogHeight
                (E.basis.repr (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤
                  (p + C) ^ C) ∧
              (∀ z : D.filtration.Group, z ∈ D.lattice →
                (⟨markedBaseEvaluation F v w marked t J hJ 0 z.coord⟩ : E.filtration.Group) ∈ E.lattice) ∧
              (∀ z : D.RealGroup, z ∈ D.realLattice →
                (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈
                  E.realLattice) ∧
              (∀ z : D.filtration.Group, z ∈ D.lattice →
                IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) ∧
              ∀ a : Fin t → ℤ,
                (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                  D.filtration.Group) ∈ D.lattice := by
  obtain ⟨a, ha, hmodel⟩ := exists_compatible_marked_evaluation_model s
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (2 * P₀ + 3) ^ 5)
  refine ⟨C, hC, ?_⟩
  intro I ι L _ _ _ _ r t e u F b ω hF hω v w marked hw hv J hJ E p hp hn ht hc hgen hE hcoef
  let P := (p + a) ^ a
  let Q := (2 * P + 3) ^ 5
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hpP : p ≤ P := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    calc
      p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (p + a) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ a)
  have hTQ : 2 * P + 1 ≤ Q := by
    simpa only [show 2 * P + 1 + 2 = 2 * P + 3 by ring] using
      le_power_budget (by linarith : 0 ≤ 2 * P + 1) (by decide : 1 ≤ 5)
  have htotal : P + Q ≤ (p + C) ^ C := by
    simpa [X, P₀, P, Q, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C := (le_add_of_nonneg_right hQ).trans htotal
  have hQC : Q ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  obtain ⟨q, hqdim, D, M, hMF, hM, _, hdir, hphase, heval, hmap, _, hrealmap,
      m, hm, hmb, hmlattice⟩ := hmodel F b ω hF hω v w marked hw hv J hJ E hp hn ht hc hgen hE hcoef
  obtain ⟨N, hN, hin, hout, _, hM'⟩ := exists_normalizedMarkedLattice_model F v w marked t D m M
    hP hM (ht.trans hpP) hm hmb hphase
  let Λ := normalizedMarkedLattice F v w marked t D m
  let D' := D.withLattice Λ N hN hin hout
  let M' := M.withLattice Λ N hN hin hout
  have hlatR : D'.realLattice ≤ D.realLattice :=
    Subgroup.map_mono (normalizedMarkedLattice_le F v w marked t D m)
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hPC), q, hqdim, D', M', hMF,
    hM'.mono M' hQC, (fun i j => (hdir i j).trans hPC), ?_,
    (fun i j => (heval i j).trans hPC), ?_, ?_, ?_, ?_⟩
  · intro i j
    exact (normalizedMarkedPhase_height F v w marked t m hm hP hmb (D.basis j) i
      (hphase i j)).trans (hTQ.trans hQC)
  · intro z hz
    exact hmap z hz.1
  · intro z hz
    exact hrealmap z (hlatR hz)
  · exact normalizedMarkedLattice_integral F v w marked t D m
  · exact fun a => normalizedMarkedLattice_direction F v w marked t D m hm a (hmlattice a)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_induced_marked_model (s u : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I ι J L : Type*} [Fintype I] [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] {r t e : ℕ}
      (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (_hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (Q : LieIdeal ℚ L) (hQ : markedLieSpan v w marked 0 2 0 ≤ Q.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ Q))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ Q))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ Q))] [T2Space (ℝ ⊗[ℚ] (L ⧸ Q))]
      (E : RationalFilteredNilmanifold (L ⧸ Q) u e) (V : J → E.Space → ℂ) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (t : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) →
      (∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap Q (b j)) i) ≤ p) →
      (∀ i x, ‖V i x‖ ≤ 1) →
      (letI := E.metricSpace; ∀ i, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i)) →
      ∃ (m : ℕ) (hm : 0 < m), (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ d : ℕ, d ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
          ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d,
            ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
              M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
              M.ComplexityLE ((p + C) ^ C) ∧
              ∃ hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
                  (⟨(markedBaseEvaluation F v w marked t Q hQ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice,
                (∀ z : D.filtration.Group, z ∈ D.lattice →
                  IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) ∧
                (∀ a : Fin t → ℤ,
                  (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                    D.filtration.Group) ∈ D.lattice) ∧
                (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
                 letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
                   IsModuleTopology.topologicalAddGroup ℝ _
                 letI := realification_moduleTopology_t2 D.basis
                 letI := D.metricSpace
                 ∃ G : J → D.Space → ℂ,
                   (∀ i x, ‖G i x‖ ≤ 2) ∧
                   (∀ i, LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ (G i)) ∧
                   ∀ i (g : D.RealGroup),
                     (∀ j, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord j| ≤ 1 / 4) →
                     G i (QuotientGroup.mk g) =
                       markedLocalCoefficientValue F v w marked hw hv t m hm D Q hQ E hmap (V i) g) := by
  classical
  obtain ⟨A, hA, hmodel⟩ := exists_normalized_marked_model s
  obtain ⟨B, _, hext⟩ := exists_induced_marked_observable s u hs
  let P₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro I ι J L _ _ _ _ r t e F b ω hF hω v w marked hw hv Q hQ _ _ _ _ E V p hp hd ht hc hgen hE hproj hVnorm hV
  let P := (p + A) ^ A
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpP : p ≤ P := by
    apply (le_power_budget hp (a := A) (by omega)).trans
    change (p + 2) ^ A ≤ (p + A) ^ A
    exact pow_le_pow_left₀ (by linarith) (add_le_add le_rfl (by exact_mod_cast hA)) A
  have htotal : P + (P + B) ^ B ≤ (p + C) ^ C := by
    simpa [P₀, P, Polynomial.eval₂_pow] using hbudget p hp
  have hPC : P ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans htotal
  have hEC : (P + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  obtain ⟨m, hm, hmp, d, hdim, D, M, hMF, hM, hdir, hphase, heval, _, hmap, hint, hlat⟩ :=
    hmodel F b ω hF hω v w marked hw hv Q hQ E hp hd ht hc hgen hE hproj
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hPC), d, hdim, D, M, hMF,
    hM.mono M hPC, hmap, hint, hlat, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 D.basis
  let := D.metricSpace
  let := E.metricSpace
  have hchoose (i : J) := hext F v w marked hw hv hm D Q hQ E hmap hP hM.1
    (hE.mono E hpP) (ht.trans hpP) hmp hdir hphase heval hint hlat (V i) (hVnorm i)
    ((hV i).weaken (show (⟨Real.exp p, Real.exp_nonneg p⟩ : ℝ≥0) ≤
      ⟨Real.exp P, Real.exp_nonneg P⟩ from Real.exp_le_exp.mpr hpP))
  choose G hG hGeq hGnorm using hchoose
  refine ⟨G, hGnorm, ?_, hGeq⟩
  intro i
  exact (hG i).weaken (show (⟨Real.exp ((P + B) ^ B), Real.exp_nonneg _⟩ : ℝ≥0) ≤
    ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hEC)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_induced_marked_model (s u : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I J L : Type*} [Fintype I]
      [LieRing L] [LieAlgebra ℚ L] {r t e n : ℕ}
      (F : DegreeRankLieFiltration L s r) (A : RationalFilteredNilmanifold L s n)
      (_hFA : F.associatedDegree = A.filtration) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
      (Q : LieIdeal ℚ L) (hQ : markedLieSpan v w marked 0 2 0 ≤ Q.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ Q))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ Q))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ Q))] [T2Space (ℝ ⊗[ℚ] (L ⧸ Q))]
      (E : RationalFilteredNilmanifold (L ⧸ Q) u e) (V : J → E.Space → ℂ) {p : ℝ},
      0 ≤ p → A.GeometryComplexityLE p → (t : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (A.basis.repr (v i) j) ≤ p) → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap Q (A.basis j)) i) ≤ p) →
      (∀ i x, ‖V i x‖ ≤ 1) →
      (letI := E.metricSpace; ∀ i, LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ (V i)) →
      ∃ (m : ℕ) (hm : 0 < m), (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ d : ℕ, d ≤ n * (s + 1) * (t + 1) ^ s + t ∧
          ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d,
            ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
              M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
              M.ComplexityLE ((p + C) ^ C) ∧
              ∃ hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
                  (⟨(markedBaseEvaluation F v w marked t Q hQ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice,
                (∀ z : D.filtration.Group, z ∈ D.lattice →
                  IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) ∧
                (∀ a : Fin t → ℤ,
                  (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
                    D.filtration.Group) ∈ D.lattice) ∧
                (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
                 letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
                   IsModuleTopology.topologicalAddGroup ℝ _
                 letI := realification_moduleTopology_t2 D.basis
                 letI := D.metricSpace
                 ∃ G : J → D.Space → ℂ,
                   (∀ i x, ‖G i x‖ ≤ 2) ∧
                   (∀ i, LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ (G i)) ∧
                   ∀ i (g : D.RealGroup),
                     (∀ j, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord j| ≤ 1 / 4) →
                     G i (QuotientGroup.mk g) =
                       markedLocalCoefficientValue F v w marked hw hv t m hm D Q hQ E hmap (V i) g) := by
  obtain ⟨B, _, hmodel⟩ := exists_induced_marked_model s u hs
  let X : Polynomial ℕ := Polynomial.X + (Polynomial.X + 3) ^ 11 + 1
  let P₀ := X + (X + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + (P₀ + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro I J L _ _ _ r t e n F A hFA v w marked hw hv Q hQ _ _ _ _ E V p hp hA ht hgen hE hproj hVnorm hV
  obtain ⟨b, ω, N, _, _, hfil, hb, hbinv, hbc, _, _, _, _⟩ := A.exists_controlled_adapted_basis hp hA
  have hFb : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}) := by
    simpa only [hFA] using hfil
  have hω := F.associatedDegree.adaptedBasis_weight_le_step b ω hFb
  let x := p + (p + 3) ^ 11 + 1
  let P := x + (x + 2) ^ 4
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpx : p ≤ x := by dsimp [x]; linarith [pow_nonneg (by linarith : 0 ≤ p + 3) 11]
  have hpx1 : p + 1 ≤ x := by dsimp [x]; linarith [pow_nonneg (by linarith : 0 ≤ p + 3) 11]
  have hxP : x ≤ P := le_add_of_nonneg_right (by positivity)
  have hpP : p ≤ P := hpx.trans hxP
  have hpowP : (x + 2) ^ 4 ≤ P := by dsimp [P]; linarith
  have h5x : (p + 3) ^ 5 ≤ x := by
    have hh := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 5 ≤ 11)
    dsimp [x]
    linarith
  have h11P : (p + 3) ^ 11 ≤ P := by
    apply le_trans ?_ hxP
    dsimp [x]
    linarith
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ P := by
    rw [Fintype.card_fin, finrank_eq_card_basis A.basis, Fintype.card_fin]
    exact hA.1.trans hpP
  have hdimx : (Fintype.card (Fin n) : ℝ) ≤ x := by simpa only [Fintype.card_fin] using hA.1.trans hpx
  have hgenb (i j) : rationalLogHeight (b.repr (v i) j) ≤ P := by
    have hh := linearMap_coordinate_logHeight A.basis b (LinearMap.id : L →ₗ[ℚ] L) hx hdimx
      (fun a c => (hbinv a c).trans h5x) (v i) (fun a => (hgen i a).trans hpx) j
    exact hh.trans hpowP
  have hprojb (i j) : rationalLogHeight (E.basis.repr (lieQuotientMap Q (b j)) i) ≤ P := by
    exact (linearMap_coordinate_logHeight A.basis E.basis (lieQuotientMap Q).toLinearMap hx hdimx
      (fun a c => (hproj c a).trans hpx) (b j) (fun a => (hb j a).trans hpx1) i).trans hpowP
  have htotal : P + (P + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, P₀, P, x, Polynomial.eval₂_pow] using hbudget p hp
  have hbound : (P + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  let := E.metricSpace
  obtain ⟨m, hm, hmp, d, hdimd, D, M, hMF, hM, hmap, hint, hlat, hobs⟩ :=
    hmodel F b ω hFb hω v w marked hw hv Q hQ E V hP hdim (ht.trans hpP)
      (fun i j k => (hbc i j k).trans h11P) hgenb (hE.mono E hpP) hprojb hVnorm
      (fun i => (hV i).weaken (show (⟨Real.exp p, Real.exp_nonneg p⟩ : ℝ≥0) ≤
        ⟨Real.exp P, Real.exp_nonneg P⟩ from Real.exp_le_exp.mpr hpP))
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hbound), d, ?_, D, M, hMF,
    hM.mono M hbound, hmap, hint, hlat, ?_⟩
  · simpa only [Fintype.card_fin, finrank_eq_card_basis A.basis] using hdimd
  · let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    let := realification_moduleTopology_t2 D.basis
    let := D.metricSpace
    obtain ⟨G, hGn, hGL, hGe⟩ := hobs
    refine ⟨G, hGn, ?_, hGe⟩
    intro i
    exact (hGL i).weaken (show (⟨Real.exp ((P + B) ^ B), Real.exp_nonneg _⟩ : ℝ≥0) ≤
      ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hbound)

end Erdos3

end

section

namespace Erdos3.QuadraticMarked

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_model_from_seed :
    ∃ C : ℕ, 2 ≤ C ∧ ∀
      [TopologicalSpace (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)]
      [T2Space (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)] {e : ℕ}
      (E : RationalFilteredNilmanifold (RationalTorus.BottomQuotient 1) 1 e)
      (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) (V : E.Space → ℂ)
      {p : ℝ}, 1 ≤ p → ∀ t : ℕ, (t : ℝ) ≤ p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (lieQuotientMap (⊥ : LieIdeal ℚ Seed)
        (RationalTorus.basis 1 j)) i) ≤ p) →
      (∀ x, ‖V x‖ ≤ 1) →
      (letI := E.metricSpace; LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ V) →
      (∀ z : E.RealGroup, V (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z) →
      Model t η ((p + C) ^ C) := by
  obtain ⟨C, hC, hmodel⟩ := exists_induced_marked_model 1 1 (by decide)
  refine ⟨C, hC, ?_⟩
  intro _ _ _ _ e E η V p hp t ht hE hproj hVnorm hVLip hVeq
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  obtain ⟨m, hm, hmp, d, hdim, D, M, hMF, hM, hmap, hint, hlat, hG⟩ :=
    hmodel (t := t) filtration (RationalTorus.basis 1) weights filtration_layers (fun _ => le_rfl)
      generators weights marked weight_pos generator_mem (⊥ : LieIdeal ℚ Seed) second_marked_span
      E (fun _ : Unit => V) hp0 (by simpa only [Fintype.card_fin, Nat.cast_one] using hp)
      ht (structure_height hp0) (generator_height hp0) hE hproj
      (fun _ => hVnorm) (fun _ => hVLip)
  refine ⟨m, hm, hmp, d, D, ?_, M, hMF, hM, hint, hlat, ?_⟩
  · norm_num only [Fintype.card_fin, Nat.reduceAdd, pow_one, one_mul] at hdim
    omega
  · let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra t)
    let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra t) := IsModuleTopology.topologicalAddGroup ℝ _
    let := realification_moduleTopology_t2 D.basis
    let := D.metricSpace
    obtain ⟨G, hGnorm, hGLip, hGeq⟩ := hG
    refine ⟨G (), hGnorm (), hGLip (), ?_⟩
    intro g hg
    rw [hGeq () g hg, markedLocalCoefficientValue_apply, hVeq]
    rfl

theorem exists_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 1 ≤ p → ∀ t : ℕ, (t : ℝ) ≤ p →
      ∃ η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ,
        (∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0) ∧
        Model t η ((p + C) ^ C) := by
  obtain ⟨A, hA, hseed⟩ := RationalTorus.exists_bottom_quotient_character
  obtain ⟨B, _, hmodel⟩ := exists_model_from_seed
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p hp t ht
  classical
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (le_power_budget hp0 (a := A) (by omega)).trans
    change (p + 2) ^ A ≤ (p + A) ^ A
    exact pow_le_pow_left₀ (by linarith) (add_le_add le_rfl (by exact_mod_cast hA)) A
  have htotal : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp0
  have hBC : (q + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans htotal
  have hspan : (⊥ : LieIdeal ℚ Seed).toSubmodule =
      Submodule.span ℚ (RationalTorus.basis 1 '' (∅ : Set (Fin 1))) := by simp
  let qb := NilpotentLieFiltration.quotientFinBasis (RationalTorus.basis 1)
    (⊥ : LieIdeal ℚ Seed) ∅ hspan
  let := moduleTopology ℝ (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] RationalTorus.BottomQuotient 1) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 qb
  obtain ⟨e, E, hE, hproj, η, V, hη, hVLip, hVnorm, hVeq⟩ := hseed 1 0 hp0 (by simpa using hp)
  have hm : Model t η ((q + B) ^ B) := hmodel E η V (hp.trans hpq) t (ht.trans hpq)
    (hE.mono E hpq) (fun i j => (hproj i j).trans hpq) (fun x => (hVnorm x).le) hVLip hVeq
  exact ⟨η, hη, hm.mono hBC⟩

end Erdos3.QuadraticMarked

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_common_induced_correlation_family (s k : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {τ K I J : Type*} [Fintype I] [Fintype J]
      {r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (t : ℕ)
      (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (_hFA : D.coefficientFreeFiltration.associatedDegree = A.filtration)
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
        (hL := A.filtration.lowerCentralSeries_eq_bot) (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap)),
      0 ≤ Z → A.GeometryComplexityLE Z → Q.GeometryComplexityLE Z → (t : ℝ) ≤ Z →
      (∀ i j, rationalLogHeight (A.basis.repr (D.coefficientFreeGenerator i) j) ≤ Z) →
      (∀ i j, rationalLogHeight (Q.basis.repr (D.dependentQuotientMap (A.basis j)) i) ≤ Z) →
      (Fintype.card I : ℝ) ≤ Real.exp Z → (Fintype.card J : ℝ) ≤ Real.exp Z →
      ∀ (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
        (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
        (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
        (∀ z i, |affineCyclicTorusLocalLift u c h₀ (h z) i| ≤ 1 / 4) →
        (∀ z, (a z).log = positiveUnivariate (fun j => (x j).val +
          ∑ i, affineCyclicTorusLocalLift u c h₀ (h z) i • (y j i).val)) →
        ∀ f : τ → K → ZMod N → ℂ,
          (∀ z, Nonempty (NativeVectorCorrelation degree N Z (fun ij : K × I => fun n =>
            f z ij.1 n * star (V.observable ij.2 (QuotientGroup.mk
              (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) (v z))))))) →
          D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ
            x y u c h₀ h a v f ((Z + C) ^ C) := by
  obtain ⟨B, _, hmodel⟩ := exists_native_induced_marked_model s k hs
  let P₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * Polynomial.X + P₀)
  refine ⟨C, hC, ?_⟩
  intro τ K I J _ _ r N n e degree _ b p q P Z W out H R D t A hFA Q _ _ _ _ _ _ _ _ S T V U hφ
    hZ hA hQ ht hgen hproj hI hJ x y u c h₀ h a v hsmall ha f hcorr
  let Q₀ := (Z + B) ^ B
  have hQ₀ : 0 ≤ Q₀ := by dsimp [Q₀]; positivity
  have htotal : 3 * Z + Q₀ ≤ (Z + C) ^ C := by
    simpa [P₀, Q₀, Polynomial.eval₂_pow] using hbudget Z hZ
  have hQC : Q₀ ≤ (Z + C) ^ C := by linarith
  have hthree : Z + Z + Z ≤ (Z + C) ^ C := by linarith
  let := Q.metricSpace
  obtain ⟨m, hm, hmp, d, hdim, E, M, hMF, hM, hmap, hint, hlat, hobs⟩ :=
    hmodel D.coefficientFreeFiltration A hFA D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
      D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer (D.dependentWordIdeal 0 2 0) le_rfl Q U.observable
      hZ hA ht hgen hQ hproj U.norm
      (fun j => (U.lipschitz j).weaken (show U.lipBound ≤ ⟨Real.exp Z, Real.exp_nonneg _⟩ from U.lip_bound))
  exact D.hasCommonInducedCorrelationFamily_of_model t A Q V U hφ x y u c h₀ h a v f
    Q₀ ((Z + C) ^ C) hs hZ hI hJ hsmall ha hcorr m hm hmp d hdim E M hMF hM hmap hlat hobs hQC hthree

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

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

theorem exists_covered_induced_correlation_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {τ K I : Type} [Fintype I]
      {r N n degree : ℕ} [NeZero N] {b p q P Q₀ Z : ℝ}
      {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (J : D.CoefficientBases Q₀) (t : ℕ)
      (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : A.DegreeRankStructure (r + 1))
      [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      (V : A.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Z),
      T.filtration = D.coefficientFreeFiltration →
      V.frequency = J.freeFrequency D →
      0 ≤ Z → T.ComplexityLE Z → (t : ℝ) ≤ Z →
      (∀ i j, rationalLogHeight (A.basis.repr (D.coefficientFreeGenerator i) j) ≤ Z) →
      (Fintype.card I : ℝ) ≤ Real.exp Z →
      ∀ (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
        (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
        (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
        (∀ z i, |affineCyclicTorusLocalLift u c h₀ (h z) i| ≤ 1 / 4) →
        (∀ z, (a z).log = positiveUnivariate (fun j => (x j).val +
          ∑ i, affineCyclicTorusLocalLift u c h₀ (h z) i • (y j i).val)) →
        (∀ z, A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (a z) = 1) →
        ∀ f : τ → K → ZMod N → ℂ,
          (∀ z, Nonempty (NativeVectorCorrelation degree N Z (fun ij : K × I => fun w =>
            f z ij.1 w * star (V.observable ij.2 (QuotientGroup.mk
              (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                (fun _ => (w.val : ℤ)) (v z))))))) →
          D.HasCoveredInducedCorrelationFamily (degree := degree)
            t A T V x y u c h₀ h a v f ((Z + C) ^ C) := by
  obtain ⟨a₀, _, hcover⟩ := exists_covered_dependentQuotient_comparison s
  obtain ⟨b₀, _, hinduce⟩ := exists_common_induced_correlation_family s s hs
  let Y₀ : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a₀) ^ a₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Y₀ + (Y₀ + Polynomial.C b₀) ^ b₀)
  refine ⟨C, hC, ?_⟩
  intro τ K I _ r N n degree _ b p q P Q₀ Z W out H R D J t A T _ _ _ _ V
    hTF hV hZ hT ht hgen hI x y u c h₀ h a v hsmall ha ha0 f hcorr
  let B := (Z + a₀) ^ a₀
  let Y := Z + B
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hY : 0 ≤ Y := add_nonneg hZ hB
  have hZY : Z ≤ Y := le_add_of_nonneg_right hB
  have hBY : B ≤ Y := le_add_of_nonneg_left hZ
  have htotal : Y + (Y + b₀) ^ b₀ ≤ (Z + C) ^ C := by
    simpa [Y₀, Y, B, Polynomial.eval₂_pow] using hbudget Z hZ
  have hYC : Y ≤ (Z + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans htotal
  have hBC : B ≤ (Z + C) ^ C := hBY.trans hYC
  have hindC : (Y + b₀) ^ b₀ ≤ (Z + C) ^ C := (le_add_of_nonneg_left hY).trans htotal
  obtain ⟨e, he, Q, S, hSF, hS, _, _, hproj, Λ, hΛ, _, _, _, _,
    m, hm, hin, hout, hT₀, hφ, V₀, hVfreq, _, hVobs, hcoeff⟩ :=
    hcover D J A T V hTF hZ hT hgen hV 1 (by decide) (by simpa using Real.one_le_exp hZ)
  let A₀ := A.withLattice Λ m hm hin hout
  let T₀ := T.withLattice Λ m hm hin hout
  refine ⟨Λ, hΛ, m, hm, hin, hout, hT₀.mono T₀ hBC, e, he, Q, S, hSF,
    hS.mono S hBC, hφ, V₀.mono hBC, hVfreq, hVobs, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨k, hk, hkB, U, _, _, hcomparison⟩ := hcoeff
  refine ⟨k, hk, hkB.trans (Real.exp_le_exp.mpr hBC), U.mono hBC, ?_, ?_⟩
  · have hFA : D.coefficientFreeFiltration.associatedDegree = A₀.filtration := by
      rw [← hTF]
      exact T.associated
    have hcorrY (z : τ) : Nonempty (NativeVectorCorrelation degree N Y
        (fun ij : K × I => fun w => f z ij.1 w *
          star ((V₀.mono hBY).observable ij.2 (QuotientGroup.mk
            (A₀.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (w.val : ℤ)) (v z)))))) := by
      obtain ⟨Bz⟩ := hcorr z
      have hvalue (i : I) (w : ZMod N) :
          (V₀.mono hBY).observable i (QuotientGroup.mk
            (A₀.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (w.val : ℤ)) (v z))) =
          V.observable i (QuotientGroup.mk
            (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (w.val : ℤ)) (v z))) := hVobs i _
      simpa only [hvalue] using
        (show Nonempty (NativeVectorCorrelation degree N Y _) from ⟨Bz.mono hZY⟩)
    have hfamily := hinduce D t A₀ hFA Q (V₀.mono hBY) (U.mono hBY) hφ
      hY (hT₀.1.mono A₀ hBY) (hS.1.mono Q hBY) (ht.trans hZY)
      (fun i j => (hgen i j).trans hZY) (fun i j => (hproj i j).trans hBY)
      (hI.trans (Real.exp_le_exp.mpr hZY))
      (by simpa only [Fintype.card_fin] using hkB.trans (Real.exp_le_exp.mpr hBY))
      x y u c h₀ h a v hsmall ha f hcorrY
    exact HasCommonInducedCorrelationFamily.mono D t A₀ Q (V₀.mono hBY) (U.mono hBY)
      hφ x y u c h₀ h a v f hfamily hindC
  · apply ((hcomparison Unit (fun _ => 1)).mono hBC).realizeFamily
    intro z
    exact ⟨a z, ha0 z, fun _ _ => rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ} {bound : σ → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (M : ∀ i, (D i).MultidegreeStructure bound)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

namespace NativeBoundedMultidegreeFamily

variable {σ I : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (F : NativeBoundedMultidegreeFamily bound I p)

end NativeBoundedMultidegreeFamily

namespace NativeMultidegreeNilcharacter

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeBoundedMultidegreeFamily

open scoped TensorProduct

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

end Erdos3.NativeBoundedMultidegreeFamily

namespace Erdos3.NativeUnitRankFamily

open scoped TensorProduct

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

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

end NativeUnitRankFamily

namespace NativeBoundedMultidegreeFamily

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

variable {σ I : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (M : NativeBoundedMultidegreeFamily bound I p) (hpq : p ≤ q)
  {n : ℕ} (hn : (n + 1 : ℝ) ≤ Real.exp q)
  (V : M.model.UnitVerticalObservable
    (M.model.filtration.realification.subgroup (∑ i, bound i)) (Fin (n + 1)) q)

end NativeBoundedMultidegreeFamily

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

end Erdos3

end

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

end Erdos3.QuadraticMarked

end

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped BigOperators

end Erdos3.QuadraticMarked

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_quadratic_bounded_family :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 1 ≤ p → ∀ t : ℕ, (t : ℝ) ≤ p →
      ∀ {N : ℕ} (a : ℝ) (b u c : Fin t → ℝ) (h₀ : ZMod N),
      ∃ F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree 1) (Fin 1 × Unit) ((p + C) ^ C),
        ∀ h : ZMod N, (∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4) → ∀ n : ℤ,
          F.eval (0, ()) (correlationInput (h.val : ℤ) n) =
            CircleFourier.character (((n : ℝ) *
              (a + ∑ i, affineCyclicTorusLocalLift u c h₀ h i * b i) : ℝ) : CircleFourier.Circle) / 2 := by
  obtain ⟨A, _, hmodel⟩ := QuadraticMarked.exists_model
  obtain ⟨B, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + 6 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p hp t ht N a b u c h₀
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : productNiltestBudget (q + 6) ≤ (p + C) ^ C := by
    apply (hproduct (q + 6) (by positivity)).trans
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp0
  obtain ⟨η, hη, m, hm, _, d, D, _, M, hMF, hM, _, hlat, hG⟩ := hmodel hp t ht
  let := moduleTopology ℝ (ℝ ⊗[ℚ] QuadraticMarked.Algebra t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] QuadraticMarked.Algebra t) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 D.basis
  let := D.metricSpace
  obtain ⟨G, hGn, hGL, hGe⟩ := hG
  let W := NativeMultidegreeNilcharacter.constOne (mixedCorrelationDegree 1) (p := 0) (by positivity)
  have hreal : (QuadraticMarked.multidegree t).realification = M.filtration.realification :=
    congrArg MultidegreeLieFiltration.realification hMF.symm
  let g := (QuadraticMarked.multidegree t).realification.orbitEquivOfEq hreal
    (QuadraticMarked.localOrbit t m a b u c h₀)
  have hstep : 2 = ∑ i, mixedCorrelationDegree 1 i := (mixedCorrelationDegree_sum 1).symm
  obtain ⟨F, hF⟩ := W.exists_product_with_bounded_family D M hstep g (fun _ : Unit => G)
    hq hM (fun _ => hGn) (fun _ => hGL)
  have hcost' : productNiltestBudget (0 + q + 2 + 4) ≤ (p + C) ^ C := by
    rw [show 0 + q + 2 + 4 = q + 6 by ring]
    exact hcost
  refine ⟨F.mono hcost', ?_⟩
  intro h hsmall n
  change F.eval ((0 : Fin 1), ()) (correlationInput (h.val : ℤ) n) = _
  apply (hF ((0 : Fin 1), ()) (correlationInput (h.val : ℤ) n)).trans
  change 1 * G (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n) g)) / 2 = _
  rw [one_mul]
  congr 1
  have he := (QuadraticMarked.multidegree t).realification.orbitEquivOfEq_eval hreal
    (QuadraticMarked.localOrbit t m a b u c h₀) (correlationInput (h.val : ℤ) n)
  change G (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval _ g)) = _
  rw [he]
  exact QuadraticMarked.localOrbit_observable D η hη m hm hlat G hGe a b u c h₀ h hsmall n

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_bounded_mixed_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree 1) (Fin 1 × Unit) ((p + C) ^ C),
          ∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
              star (F.eval (0, ()) (correlationInput (h.val : ℤ) (n.val : ℤ)))‖ := by
  obtain ⟨A, _, hfrequency⟩ := exists_quadratic_local_frequency
  obtain ⟨B, _, hfamily⟩ := exists_quadratic_bounded_family
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + 1 + (Q + 1 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : q + 1 + (q + 1 + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q + 1 ≤ (p + C) ^ C := by
    have : 0 ≤ (q + 1 + B) ^ B := by positivity
    linarith
  have hfamilyC : (q + 1 + B) ^ B ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, r, u, c, b, a, h₀, hr, _, _, _, hcorr⟩ := hfrequency hp f hf hG
  obtain ⟨F, hF⟩ := hfamily (show 1 ≤ q + 1 by linarith) r (by linarith : (r : ℝ) ≤ q + 1)
    a b u c h₀
  refine ⟨H, hH, ?_, F.mono hfamilyC, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -q))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    obtain ⟨hsmall, hc⟩ := hcorr h hh
    have hvalue (n : ZMod N) : F.eval (0, ()) (correlationInput (h.val : ℤ) (n.val : ℤ)) =
        CircleFourier.character (((n.val : ℝ) *
          (a + ∑ i, affineCyclicTorusLocalLift u c h₀ h i * b i) : ℝ) : CircleFourier.Circle) / 2 := by
      simpa only [Int.cast_natCast] using
        hF h (fun i => (hsmall i).trans (by norm_num)) (n.val : ℤ)
    simp only [NativeBoundedMultidegreeFamily.mono_eval, hvalue, star_div₀, star_ofNat,
      ← mul_div_assoc, ← Finset.expect_div, norm_div, Complex.norm_ofNat]
    exact (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -q - 1)).trans
      ((exp_sub_one_le_half_exp (-q)).trans (div_le_div_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 2)))

end Erdos3

end

section

namespace Erdos3

theorem exists_quadratic_native_mixed_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
        Nonempty (NativeMixedCorrelation 1 N ((p + C) ^ C) f) := by
  obtain ⟨A, _, hbounded⟩ := exists_quadratic_bounded_mixed_correlation
  obtain ⟨B, _, hconvert⟩ := exists_native_mixed_of_bounded 1
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbound : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨H, hH, hdense, F, hcorr⟩ := hbounded hp f hf hG
  obtain ⟨W⟩ := hconvert hq f hf H hH hdense F (0, ()) hcorr
  exact ⟨W.mono hbound⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_fixed_mixed_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim, ∀ h ∈ H,
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 x, multiplicativeDerivative f h x * star (M.evalCyclic N i (correlationInput h x))‖ := by
  obtain ⟨A, _, hMixed⟩ := exists_quadratic_native_mixed_correlation
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * Q)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbound : 2 * q ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨W⟩ := hMixed hp f hf hG
  obtain ⟨i, H, _, hH, hdense, hcorr⟩ := W.exists_fixed_quadratic_coordinate
  refine ⟨H, hH, ?_, W.mixed.mono hqC, i, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbound))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hbound)).trans (hcorr h hh)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_corner_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ b₁ b₂ b₃ : ZMod N → ℂ,
              (∀ x, ‖b₁ x‖ ≤ 1) ∧ (∀ y, ‖b₂ y‖ ≤ 1) ∧ (∀ z, ‖b₃ z‖ ≤ 1) ∧
              Real.exp (-((p + C) ^ C)) ≤
                (𝔼 x : ZMod N, 𝔼 y : ZMod N,
                  M.evalCyclic N i (correlationInput y x) *
                    b₁ x * b₂ y * b₃ (x + y)).re := by
  obtain ⟨A, _, hfixed⟩ := exists_quadratic_fixed_mixed_correlation
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  classical
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 2 * q ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr⟩ := hfixed hp f hf hG
  let g (h n : ZMod N) := M.evalCyclic N i (correlationInput h n)
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hindicator : (𝔼 h : ZMod N, if h ∈ H then Real.exp (-q) else 0) =
      (H.card : ℝ) * Real.exp (-q) / N := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : Real.exp (-(2 * q)) ≤
      𝔼 h : ZMod N, ‖𝔼 n : ZMod N, multiplicativeDerivative f h n * star (g h n)‖ := by
    calc
      _ = Real.exp (-q) * Real.exp (-q) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (H.card : ℝ) * Real.exp (-q) / N := by
        apply (le_div_iff₀ hN).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense (Real.exp_nonneg (-q))]
      _ = _ := hindicator.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact hcorr h hh
        · exact norm_nonneg _
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, hcorner⟩ :=
    exists_correlated_corner f g hf hmean
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, b₁, b₂, b₃, hb₁, hb₂, hb₃, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg htotal)).trans hcorner

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

theorem exists_quadratic_reflected_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ (n₀ : ZMod N) (b : ZMod N → ℂ), (∀ y, ‖b y‖ ≤ 1) ∧
              Real.exp (-((p + C) ^ C)) ≤
                (𝔼 y : ZMod N, 𝔼 y' : ZMod N,
                  M.evalCyclic N i (correlationInput y (n₀ - y - y')) *
                    star (M.evalCyclic N i (correlationInput y' (n₀ - y - y'))) *
                    b y * star (b y')).re := by
  obtain ⟨A, _, hcorner⟩ := exists_quadratic_corner_model
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 2 * q ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr, b₁, b₂, b₃, hb₁, hb₂, hb₃, hc⟩ := hcorner hp f hf hG
  obtain ⟨z, b, hb, hreflected⟩ := exists_reflected_corner_correlation
    (fun y x => M.evalCyclic N i (correlationInput y x))
    b₁ b₂ b₃ hb₁ hb₂ hb₃ (Real.exp_nonneg (-q)) hc
  have hpower : Real.exp (-q) ^ 2 = Real.exp (-(2 * q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [hpower] at hreflected
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, z, b, hb, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg htotal)).trans hreflected

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_cyclic_antisymmetric :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ (i' j' : Fin M.outputDim) (a b : ZMod N → ℂ),
              (∀ x, ‖a x‖ ≤ 1) ∧ (∀ y, ‖b y‖ ≤ 1) ∧
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
                  star (M.evalCyclic N i' (correlationInput x y)) *
                    M.evalCyclic N j' (correlationInput y x) * a x * b y‖ := by
  obtain ⟨A, _, hreflect⟩ := exists_quadratic_reflected_model
  obtain ⟨B, _, hanti⟩ := exists_integer_antisymmetric_correlation
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let R := 2 * Q + 10
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  let r := 2 * q + 10
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hcost : r + (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hr : 0 ≤ r := hq.trans hqr
  have hqC : q ≤ (p + C) ^ C := by have := pow_nonneg (by positivity : 0 ≤ r + B) B; linarith
  have hfinal : (r + B) ^ B ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr, z, b, hb, hreflected⟩ := hreflect hp f hf hG
  have heval (k : Fin M.outputDim) (x n : ZMod N) :
      M.eval k (correlationInput (x.val : ℤ) (n.val : ℤ)) = M.evalCyclic N k (correlationInput x n) := by
    apply congrArg (M.eval k)
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  let F (x n : ℤ) := M.eval i (correlationInput x n)
  have hc : Real.exp (-q) ≤ ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F x.val (z - x - y).val * star (F y.val (z - x - y).val) * b x * star (b y)‖ := by
    simpa only [F, heval] using hreflected.trans (Complex.re_le_norm _)
  obtain ⟨k, a₀, b₀, ha₀, hb₀, hunwrapped⟩ := exists_unwrapped_reflected_correlation
    hq F F (fun _ _ => M.norm_eval i _) (fun _ _ => M.norm_eval i _) z b hb hc
  have hpairMean (g : ZMod N → ZMod N → ℂ) :
      (𝔼 u : ZMod N × ZMod N, g u.1 u.2) = 𝔼 x : ZMod N, 𝔼 y : ZMod N, g x y := by
    rw [← Finset.univ_product_univ, Finset.expect_product]
  obtain ⟨i', j', a₁, b₁, ha₁, hb₁, hantisymmetric⟩ := hanti (M.mono hqr)
    ((z.val : ℤ) + (k.val : ℤ) * N) i i (Finset.univ : Finset (ZMod N × ZMod N))
    Finset.univ_nonempty (fun u => (u.1.val : ℤ)) (fun u => (u.2.val : ℤ))
    a₀ b₀ ha₀ hb₀ (by
      simpa only [← Finset.univ_product_univ, Finset.expect_product,
        NativeMultidegreeNilcharacter.mono_eval, r, F] using hunwrapped)
  change Fin M.outputDim at i' j'
  change Real.exp (-((r + B) ^ B)) ≤
    ‖𝔼 u : ZMod N × ZMod N,
      star (M.eval i' (correlationInput (u.1.val : ℤ) (u.2.val : ℤ))) *
        M.eval j' (correlationInput (u.2.val : ℤ) (u.1.val : ℤ)) *
        a₁ u.1.val * b₁ u.2.val‖ at hantisymmetric
  rw [hpairMean (fun x y =>
    star (M.eval i' (correlationInput (x.val : ℤ) (y.val : ℤ))) *
      M.eval j' (correlationInput (y.val : ℤ) (x.val : ℤ)) *
      a₁ x.val * b₁ y.val)] at hantisymmetric
  simp_rw [heval] at hantisymmetric
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, i', j', (fun x => a₁ x.val), (fun y => b₁ y.val),
    (fun x => ha₁ _), (fun y => hb₁ _), ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg hfinal)).trans hantisymmetric

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuadraticAntisymmetricBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_antisymmetric_box :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ i' j' : Fin M.outputDim,
              Real.exp (-((p + C) ^ C)) ≤
                (finiteBoxCorrelation (fun x y : ZMod N =>
                  star (M.evalCyclic N i' (correlationInput x y)) *
                    M.evalCyclic N j' (correlationInput y x))).re := by
  obtain ⟨A, _, hanti⟩ := exists_quadratic_cyclic_antisymmetric
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * Q)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 4 * q ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr, i', j', a, b, ha, hb, hpair⟩ := hanti hp f hf hG
  let K (x y : ZMod N) :=
    star (M.evalCyclic N i' (correlationInput x y)) * M.evalCyclic N j' (correlationInput y x)
  have hbox : Real.exp (-q) ^ 4 ≤ (finiteBoxCorrelation K).re :=
    (pow_le_pow_left₀ (Real.exp_nonneg _) hpair 4).trans
      (norm_weighted_pair_mean_pow_four_le_box K a b ha hb)
  have hpower : Real.exp (-q) ^ 4 = Real.exp (-(4 * q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [hpower] at hbox
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, i', j', ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hbox

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairCorrelator
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

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

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

end NativeMultidegreeNilcharacter

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

end NativeSampleCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_pair_correlator :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ i' j' : Fin M.outputDim,
                Nonempty (NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
                  Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
                  (fun z => M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ))) := by
  obtain ⟨A, _, hbox⟩ := exists_quadratic_antisymmetric_box
  obtain ⟨B, _, hpair⟩ := exists_antisymmetric_pair_correlation
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (q + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hcost
  obtain ⟨H, hH, hdense, M, i, hcorr, i', j', hbias⟩ := hbox hp f hf hG
  obtain ⟨V⟩ := hpair hq M i' j' hbias
  exact ⟨q, hq, hqC, H, hH, hdense, M, i, hcorr, i', j', ⟨V.mono hBC⟩⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

structure NativeUnitVerticalData {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (B : NativeCommonDerivativeModels s N p f) (V : NativeVerticalDerivativeData B) (q : ℝ) where
  tailDim : ℕ
  dimension : (tailDim + 1 : ℝ) ≤ Real.exp q
  observable : Fin (tailDim + 1) → B.model.Space → ℂ
  lipBound : ℝ≥0
  lip_bound : (lipBound : ℝ) ≤ Real.exp q
  unit : ∀ x, ∑ i, ‖observable i x‖ ^ 2 = 1
  norm : ∀ i x, ‖observable i x‖ ≤ 1
  lipschitz : letI := B.model.metricSpace; ∀ i, LipschitzWith lipBound (observable i)
  scalar : ∀ h x, observable 0 x = (B.test h).observable x / 2
  vertical : ∀ i z, z ∈ B.model.filtration.realification.subgroup s → ∀ x,
    observable i (z • x) =
      CircleFourier.character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle) *
        observable i x

namespace NativeUnitVerticalData

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} {V : NativeVerticalDerivativeData B}
  (U : NativeUnitVerticalData B V q)

noncomputable def mono {p' q' : ℝ} (hp : p ≤ p') (hq : q ≤ q') :
    NativeUnitVerticalData (B.mono hp) (V.mono hp) q' where
  tailDim := U.tailDim
  dimension := U.dimension.trans (Real.exp_le_exp.mpr hq)
  observable := U.observable
  lipBound := U.lipBound
  lip_bound := U.lip_bound.trans (Real.exp_le_exp.mpr hq)
  unit := U.unit
  norm := U.norm
  lipschitz := U.lipschitz
  scalar := U.scalar
  vertical := U.vertical

noncomputable def test (i : Fin (U.tailDim + 1)) (h : ZMod N) :
    B.model.Niltest (fun _ : Unit => 1) where
  orbit := (B.test h).orbit
  observable := U.observable i
  normBound := 1
  lipBound := U.lipBound
  norm_le := U.norm i
  lipschitz := U.lipschitz i

theorem test_zero_evalCyclic (h x : ZMod N) :
    (U.test 0 h).evalCyclic N (fun _ => x) = (B.test h).evalCyclic N (fun _ => x) / 2 :=
  U.scalar h _

theorem test_complexity (hpq : p ≤ q) (hq : 0 ≤ q)
    (i : Fin (U.tailDim + 1)) (h : ZMod N) : (U.test i h).ComplexityLE (q + 4) := by
  refine ⟨B.geometry.mono B.model (by linarith), ?_⟩
  have ht := niltest_log_bound_of_exp (1 : ℝ≥0) U.lipBound (a := 0) (b := q)
    (by norm_num) hq (by simp) U.lip_bound
  simpa only [test, zero_add] using ht

theorem test_zero_correlation (h : ZMod N) (hh : h ∈ B.shifts) :
    Real.exp (-(p + 1)) ≤
      ‖𝔼 x, multiplicativeDerivative f h x * star ((U.test 0 h).evalCyclic N (fun _ => x))‖ := by
  have heq :
      (𝔼 x, multiplicativeDerivative f h x * star ((U.test 0 h).evalCyclic N (fun _ => x))) =
      (𝔼 x, multiplicativeDerivative f h x * star ((B.test h).evalCyclic N (fun _ => x))) / 2 := by
    simp only [U.test_zero_evalCyclic, star_div₀, star_ofNat, ← mul_div_assoc, ← Finset.expect_div]
  rw [heq, norm_div]
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [htwo]
  have hsmall : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-p)
  exact hsmall.trans (div_le_div_of_nonneg_right (B.correlation h hh) (by norm_num))

end NativeUnitVerticalData

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_native_unit_vertical_data (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (B : NativeCommonDerivativeModels s N p f) (V : NativeVerticalDerivativeData B),
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeUnitVerticalData B V ((p + C) ^ C)) := by
  obtain ⟨C, hC, hcomplete⟩ := RationalFilteredNilmanifold.exists_native_unit_vertical_completion s
  refine ⟨C, hC, ?_⟩
  intro N _ p f B V hp hf
  obtain ⟨y, hy⟩ := B.exists_large_common_observable hf
  obtain ⟨n, _, hn, K, hK, v, hv0, hvunit, hvnorm, hvLip, hvvertical⟩ :=
    hcomplete B.model (B.test 0) hp (B.complexity 0) (B.norm 0) V.frequency
      (V.vertical 0) y hy
  refine ⟨{
    tailDim := n
    dimension := hn
    observable := v
    lipBound := K
    lip_bound := hK
    unit := hvunit
    norm := hvnorm
    lipschitz := hvLip
    scalar := ?_
    vertical := hvvertical
  }⟩
  intro h x
  rw [hv0, B.common_observable 0 h]

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem exists_unit_vertical_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ R : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
      ∃ V : NativeVerticalDerivativeData R,
        Nonempty (NativeUnitVerticalData R V ((p + D) ^ D)) := by
  obtain ⟨a, _, hmodels⟩ := exists_vertical_native_inverse_models hI
  obtain ⟨b, _, hunit⟩ := exists_native_unit_vertical_data s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hp0 : 0 ≤ (p + a) ^ a := by positivity
  have hp1 : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have htotal : (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have h0 : (p + a) ^ a ≤ (p + D) ^ D := by linarith
  have h1 : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by linarith
  obtain ⟨B, ⟨V⟩⟩ := hmodels hp f hf hG
  obtain ⟨U⟩ := hunit B V hp0 hf
  exact ⟨B.mono h0, V.mono h0, ⟨U.mono h0 h1⟩⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

structure NativeDegreeRankDerivativeData {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (B : NativeCommonDerivativeModels s N p f) (r : ℕ) (q : ℝ) where
  vertical : NativeVerticalDerivativeData B
  unit : NativeUnitVerticalData B vertical q
  rank : B.model.DegreeRankStructure r
  complexity : rank.ComplexityLE q

namespace NativeDegreeRankDerivativeData

variable {s N r : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} (W : NativeDegreeRankDerivativeData B r q)

noncomputable def mono {p' q' : ℝ} (hp : p ≤ p') (hq : q ≤ q') :
    NativeDegreeRankDerivativeData (B.mono hp) r q' where
  vertical := W.vertical.mono hp
  unit := W.unit.mono hp hq
  rank := W.rank
  complexity := W.complexity.mono W.rank hq

theorem rank_vertical (i : Fin (W.unit.tailDim + 1)) (z : B.model.RealGroup)
    (hz : z ∈ W.rank.realSubgroup s r) (x : B.model.Space) :
    W.unit.observable i (z • x) =
      CircleFourier.character ((realifyFunctional W.vertical.frequency z.coord : ℝ) :
        CircleFourier.Circle) * W.unit.observable i x :=
  W.unit.vertical i z (W.rank.realSubgroup_le_degree s r hz) x

theorem rank_integral (z : B.model.RealGroup) (hz : z ∈ W.rank.realSubgroup s r)
    (hΓ : z ∈ B.model.realLattice) : ∃ n : ℤ, realifyFunctional W.vertical.frequency z.coord = n :=
  W.vertical.integral z (W.rank.realSubgroup_le_degree s r hz) hΓ

end NativeDegreeRankDerivativeData

end Erdos3

end

section

namespace Erdos3

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_degree_rank_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ B : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
        Nonempty (NativeDegreeRankDerivativeData B s ((p + D) ^ D)) := by
  obtain ⟨a, _, hmodels⟩ := exists_unit_vertical_native_inverse_models hI
  obtain ⟨b, _, hrank⟩ := RationalFilteredNilmanifold.exists_native_degree_rank_structure s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have ht : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have hcost : (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hqD : (p + a) ^ a ≤ (p + D) ^ D := by linarith
  have htD : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by linarith
  obtain ⟨B, V, ⟨U⟩⟩ := hmodels hp f hf hG
  obtain ⟨R, _, hR⟩ := hrank B.model hq B.geometry
  refine ⟨B.mono hqD, ⟨{
    vertical := V.mono hqD
    unit := U.mono hqD hqD
    rank := R
    complexity := hR.mono R htD
  }⟩⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankFamilyConstruction
namespace OAI

section

namespace Erdos3.NativeDegreeRankDerivativeData

open scoped BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} (W : NativeDegreeRankDerivativeData B r q)

noncomputable def toFamily (hpq : p ≤ q) : NativeDegreeRankFamily s r (ZMod N) q where
  L := B.L
  dim := B.dim
  model := B.model
  rank := W.rank
  complexity := W.complexity
  orbit h := (B.test h).orbit
  normalized := W.vertical.normalized
  outputDim := W.unit.tailDim + 1
  output_pos := by omega
  output_bound := by simpa only [Nat.cast_add, Nat.cast_one] using W.unit.dimension
  vertical := {
    observable := W.unit.observable
    unit := W.unit.unit
    norm := W.unit.norm
    lipBound := W.unit.lipBound
    lip_bound := W.unit.lip_bound
    lipschitz := W.unit.lipschitz
    frequency := W.vertical.frequency
    height := fun i => (W.vertical.height i).trans hpq
    vertical := W.rank_vertical
    integral := W.rank_integral
  }

theorem toFamily_evalCyclic (hpq : p ≤ q) (i : Fin (W.unit.tailDim + 1)) (h x : ZMod N) :
    (W.toFamily hpq).evalCyclic N i h x = (W.unit.test i h).evalCyclic N (fun _ => x) := rfl

theorem toFamily_correlation (hpq : p ≤ q) (h : ZMod N) (hh : h ∈ B.shifts) :
    Real.exp (-(p + 1)) ≤
      ‖𝔼 x, multiplicativeDerivative f h x *
        star ((W.toFamily hpq).evalCyclic N (0 : Fin (W.unit.tailDim + 1)) h x)‖ := by
  simp only [W.toFamily_evalCyclic]
  exact W.unit.test_zero_correlation h hh

end Erdos3.NativeDegreeRankDerivativeData

end

end OAI

end


