-- Prove2me | Definitions.Def_OAIE3v2B209
-- name    : OAIE3v2B209
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:10:55.656418+00:00
-- url     : https://prove2.me/theorems/3dc4fa2c-db85-46ca-979b-aaaa713d67e9
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 213 of 311
-- statement:
--   Definitions bundle 213 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B299`, `OAIE3v2B189`, `OAIE3v2B190`, `OAIE3v2B193` of this split.
--
--   Modules: `Estimates/ControlledPrescribedMarkedNativeFactorization.lean`, `Estimates/HomogeneousQuotientSymbolLiftBounds.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Geometry/CertifiedFullChartRecoveredTerminal.lean`, `Geometry/RestrictedChartPrefixControl.lean`, `Linear/ControlledProjectionUniformBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B189
import Definitions.Def_OAIE3v2B190
import Definitions.Def_OAIE3v2B193

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

theorem filteredSymbolMapDenominator_le {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H) :
    F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w ≤
      H ^ (Fintype.card (SymbolBasisIndex w ν) * Fintype.card (SymbolBasisIndex w ω)) := by
  apply matrixDenominator_le
  intro i j
  exact F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w hH hentries j i

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousQuotientSymbolLiftBounds
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators TensorProduct

namespace NilpotentLieFiltration

variable {σ ι κ L Q : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousQuotientGradedPolynomial_coefficientBound [Fintype κ]
    (eQ : Basis κ ℝ Q) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded))
    (p : VectorPolynomial σ ℚ Q) (T : σ → ℝ) (hT : ∀ j, 0 < T j)
    {M B : ℝ} (hM : 0 ≤ M)
    (hS : ∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (S (eQ j)) i| ≤ B)
    (hp : ∀ α j, |eQ.repr (coefficients p α) j| ≤ M / monomialScale T α) :
    CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T
      ((Fintype.card κ : ℝ) * B * M)
      (F.homogeneousQuotientGradedPolynomial b ω hF k S p) := by
  intro α i
  rw [F.homogeneousQuotientGradedPolynomial_coefficient]
  apply (basisCoordinateProjection_abs_repr_le
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) {i | ω i = k}
    (S (coefficients p α)) i).trans
  exact (linearMap_abs_repr_le eQ _ S
    (div_nonneg hM (monomialScale_pos T hT α).le) hS
    (coefficients p α) (hp α) i).trans_eq (by ring)

theorem homogeneousQuotientGradedPolynomial_coefficientGrid [Fintype κ] [Fintype ι]
    (eQ : Basis κ ℝ Q) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded))
    (p : VectorPolynomial σ ℚ Q) (qS qP : ℕ)
    (hS : ∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (S (eQ j)) i) ∈ realDenominatorGrid qS)
    (hp : ∀ α, (fun j => eQ.repr (coefficients p α) j) ∈ realDenominatorGrid qP) :
    CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) (qS * qP)
      (F.homogeneousQuotientGradedPolynomial b ω hF k S p) := by
  intro α
  rw [F.homogeneousQuotientGradedPolynomial_coefficient]
  apply basisCoordinateProjection_real_grid _ {i | ω i = k}
  have h := linear_lift_grid_of_coefficients
    ((((F.associatedGradedBasis b ω hF).baseChange ℝ).equivFun.toLinearMap).comp S)
    eQ (fun j => eQ.repr (coefficients p α) j) qP qS (hp α) hS
  simpa only [Basis.sum_repr, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Basis.equivFun_apply] using h

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RestrictedChartPrefixControl
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute realPolynomialChartSubstitution

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)
  (U : Submodule ℚ F.AssociatedGraded)
  (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

theorem restrictedMajorChartCorrection_graded (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w := by
  rw [F.restrictedMajorChartCorrection_coord]
  apply F.homogeneousQuotientGradedPolynomial_graded
  exact weightedHomogeneousPart_homogeneous w k p

theorem restrictedMajorChartCorrection_adapted (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord ∈
      F.associatedGradedFiltration.realification.adaptedLieSubalgebra w :=
  F.associatedGradedFiltration.gradedPolynomial_mem_adapted
    (F.associatedGradedBasis b ω hF) ω (F.associatedGradedFiltration_layer b ω hF) w _
    (F.restrictedMajorChartCorrection_graded b ω hF w U S k p)

theorem restrictedMajorChartCorrection_adapted_one (hw : ∀ i, 0 < w i) (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord ∈
      F.associatedGradedFiltration.realification.adaptedLieSubalgebra (fun _ => 1) := by
  have ha := F.restrictedMajorChartCorrection_adapted b ω hF w U S k p
  intro α
  apply F.associatedGradedFiltration.realification.antitone
    (show Finsupp.weight (fun _ : σ => 1) α ≤ Finsupp.weight w α from ?_) (ha α)
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, mul_one]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right (α i) (hw i))

theorem realGradedSymbolPolynomialHom_restrictedMajorCorrection (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.realGradedSymbolPolynomialHom b ω hF w
        (F.restrictedMajorCorrection b ω hF w U S k p) =
      F.restrictedMajorChartCorrection b ω hF w U S k p := by
  apply NilpotentLieBCHGroup.ext
  exact F.realGradedSymbolPolynomial_homogeneousQuotientSymbolLift b ω hF w k
    (S.baseChange ℝ) _ (weightedHomogeneousPart_homogeneous w k p)

theorem restrictedMajorChartCorrection_substitute
    (f : σ → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i)) (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.restrictedMajorChartCorrection b ω hF w U S k (realChartSubstitute f p) =
      realPolynomialChartSubstitution
        F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f
        (F.restrictedMajorChartCorrection b ω hF w U S k p) := by
  apply NilpotentLieBCHGroup.ext
  rw [F.restrictedMajorChartCorrection_coord, realPolynomialChartSubstitution_coord,
    F.restrictedMajorChartCorrection_coord]
  rw [← realChartSubstitute_weightedHomogeneousPart w w f hf]
  simp only [homogeneousQuotientGradedPolynomial, realChartSubstitute_map]

theorem realGradedSymbolPolynomialHom_restrictedMajorCorrection_chart
    (f : σ → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i)) (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.realGradedSymbolPolynomialHom b ω hF w
        (F.restrictedMajorCorrection b ω hF w U S k (realChartSubstitute f p)) =
      realPolynomialChartSubstitution
        F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f
        (F.restrictedMajorChartCorrection b ω hF w U S k p) := by
  rw [F.realGradedSymbolPolynomialHom_restrictedMajorCorrection,
    F.restrictedMajorChartCorrection_substitute b ω hF w U S f hf]

theorem restrictedMajorOuterFactors_chart_representation
    (f : σ → MvPolynomial σ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i))
    (qS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) (n : ℕ) :
    let outer := F.restrictedMajorOuterFactors b ω hF w U S
      (fun j => realChartSubstitute f (qS j)) pR n
    (F.realGradedSymbolPolynomialHom b ω hF w outer.1,
      F.realGradedSymbolPolynomialHom b ω hF w outer.2) =
      F.associatedGradedFiltration.polynomialChartOuterIteration f
        (fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (qS j))
        (fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (pR j)) n := by
  induction n with
  | zero => simp only [restrictedMajorOuterFactors, polynomialChartOuterIteration, map_one]
  | succ n ih =>
    have hleft := congrArg Prod.fst ih
    have hright := congrArg Prod.snd ih
    dsimp only at hleft hright ⊢
    simp only [restrictedMajorOuterFactors, polynomialChartOuterIteration, map_mul,
      F.realGradedSymbolPolynomialHom_restrictedMajorCorrection_chart b ω hF w U S f hf,
      F.realGradedSymbolPolynomialHom_restrictedMajorCorrection, hleft, hright]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_restricted_chart_iteration_bounds (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
        ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) H) →
      ∀ (U : Submodule ℚ F.AssociatedGraded)
        (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
        (eQ : Basis κ ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) (B M : ℝ)
        (qS qP : ℕ), 0 ≤ M → 0 < qS * qP → ((qS * qP : ℕ) : ℝ) ≤ Real.exp p →
      (Fintype.card κ : ℝ) * B * M ≤ Real.exp ((p + 2) ^ a) →
      (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i| ≤ B) →
      (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i) ∈ realDenominatorGrid qS) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ qS * qP ∣ m ∧
        ∀ (f : σ → MvPolynomial σ ℝ),
        (∀ i, (f i).IsWeightedHomogeneous w (w i)) →
        ∀ pS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)),
        (∀ j < s, ∀ α i, |eQ.repr (coefficients (pS j) α) i| ≤ M) →
        (∀ j < s, ∀ α, (fun i => eQ.repr (coefficients (pR j) α) i) ∈ realDenominatorGrid qP) →
        ∀ n ≤ s,
        let outer := F.restrictedMajorOuterFactors b ω hF w U S
          (fun j => realChartSubstitute f (pS j)) pR n
        ∃ Echart : PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
          F.realGradedSymbolPolynomialHom b ω hF w outer.1 =
            realPolynomialChartSubstitution
              F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f Echart ∧
          CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
            (Real.exp ((p + C) ^ C)) Echart.coord ∧
          CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) m
            (F.realGradedSymbolPolynomialHom b ω hF w outer.2).coord := by
  obtain ⟨C, hC, hiteration⟩ := exists_polynomial_chart_outer_iteration_bounds s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hstructure
    U S eQ B M qS qP hM hqpos hqp hcost hSbound hSgrid
  obtain ⟨m, hm, hmp, hqm, hbound⟩ := hiteration F.associatedGradedFiltration
    (F.associatedGradedBasis b ω hF) ω (F.associatedGradedFiltration_layer b ω hF)
    H p hH hp hι hσ hHp hstructure (qS * qP) hqpos hqp
  refine ⟨m, hm, hmp, hqm, ?_⟩
  intro f hf pS pR hpS hpR n hn
  let q := fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (pS j)
  let r := fun j => F.restrictedMajorChartCorrection b ω hF w U S (j + 1) (pR j)
  have hslow : ∀ j < s, CoefficientBound
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
        (Real.exp ((p + 2) ^ a)) (q j).coord := by
    intro j hj
    dsimp only [q]
    rw [F.restrictedMajorChartCorrection_coord]
    have hpbase : ∀ α i, |eQ.repr (coefficients (pS j) α) i| ≤
        M / monomialScale (fun _ => 1) α := by
      simpa [monomialScale] using hpS j hj
    have hc := F.homogeneousQuotientGradedPolynomial_coefficientBound b ω hF eQ
      (j + 1) (S.baseChange ℝ) (weightedHomogeneousPart w (j + 1) (pS j))
      (fun _ => 1) (fun _ => zero_lt_one) hM hSbound
      (weightedHomogeneousPart_coordinateBound eQ (fun _ => 1) (fun _ => zero_lt_one)
        hM (pS j) hpbase w (j + 1))
    intro α i
    exact (hc α i).trans (div_le_div_of_nonneg_right hcost
      (monomialScale_pos (fun _ => 1) (fun _ => zero_lt_one) α).le)
  have hgrid : ∀ j < s, CoefficientGrid
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) (qS * qP) (r j).coord := by
    intro j hj
    dsimp only [r]
    rw [F.restrictedMajorChartCorrection_coord]
    apply F.homogeneousQuotientGradedPolynomial_coefficientGrid b ω hF eQ (j + 1)
      (S.baseChange ℝ) (weightedHomogeneousPart w (j + 1) (pR j)) qS qP hSgrid
    exact weightedHomogeneousPart_coordinateGrid eQ (pR j) qP (hpR j hj) w (j + 1)
  obtain ⟨Echart, hE, hEb, hRg⟩ := hbound f q r
    (fun j _ => F.restrictedMajorChartCorrection_adapted_one b ω hF w U S hw (j + 1) (pS j))
    (fun j _ => F.restrictedMajorChartCorrection_adapted_one b ω hF w U S hw (j + 1) (pR j))
    hslow hgrid n hn
  have hrep := F.restrictedMajorOuterFactors_chart_representation b ω hF w U S f hf pS pR n
  have hleft := congrArg Prod.fst hrep
  have hright := congrArg Prod.snd hrep
  dsimp only at hleft hright ⊢
  refine ⟨Echart, hleft.trans hE, hEb, ?_⟩
  rw [hright]
  exact hRg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_restricted_chart_prefix_control (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
        ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) H) →
      ∀ (U : Submodule ℚ F.AssociatedGraded)
        (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
        (eQ : Basis κ ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
        (B Bphase : ℝ) (qS : ℕ), 0 ≤ Bphase → 0 < qS →
      (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card κ : ℝ) * Bphase) ≤ Real.exp p →
      (Fintype.card κ : ℝ) * B * Real.exp Bphase ≤ Real.exp ((p + 2) ^ a) →
      (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i| ≤ B) →
      (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (S.baseChange ℝ (eQ j)) i) ∈ realDenominatorGrid qS) →
      ∀ (f : σ → MvPolynomial σ ℝ),
      (∀ i, (f i).IsWeightedHomogeneous w (w i)) →
      ∀ (pS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
        (q : ℕ → ℕ) (n : ℕ), n ≤ s →
      (∀ j < n, 0 < q j) →
      (∀ j < n, (q j : ℝ) ≤ Real.exp ((Fintype.card κ : ℝ) * Bphase)) →
      (∀ j < n, ∀ α i, |eQ.repr (coefficients (pS j) α) i| ≤ Real.exp Bphase) →
      (∀ j < n, ∀ α, (fun i => eQ.repr (coefficients (pR j) α) i) ∈
        realDenominatorGrid (q j)) →
      let outer := F.restrictedMajorOuterFactors b ω hF w U S
        (fun j => realChartSubstitute f (pS j)) pR n
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        qS * (∏ j : Fin n, q j.val) ∣ m ∧
        ∃ Echart : PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
          F.realGradedSymbolPolynomialHom b ω hF w outer.1 =
            realPolynomialChartSubstitution
              F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot f Echart ∧
          CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
            (Real.exp ((p + C) ^ C)) Echart.coord ∧
          CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) m
            (F.realGradedSymbolPolynomialHom b ω hF w outer.2).coord := by
  obtain ⟨C, hC, hiteration⟩ := exists_restricted_chart_iteration_bounds s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hstructure
    U S eQ B Bphase qS hBphase hqS hdenbudget hcost hSbound hSgrid f hf
    pS pR q n hn hqpos hqbound hpS hpR
  classical
  let Q : ℕ := ∏ j : Fin n, q j.val
  have hQpos : 0 < Q := majorPhaseCoordinateDenominator_pos
    (fun j : Fin n => q j.val) (fun j => hqpos j.val j.isLt)
  have hQbound : (Q : ℝ) ≤ Real.exp ((s : ℝ) * (Fintype.card κ : ℝ) * Bphase) := by
    have hbase : (Q : ℝ) ≤ Real.exp ((n : ℝ) * (Fintype.card κ : ℝ) * Bphase) := by
      simpa only [Fintype.card_fin, mul_assoc] using
        majorPhaseCoordinateDenominator_le_exp (fun j : Fin n => q j.val)
          ((Fintype.card κ : ℝ) * Bphase) (fun j => hqbound j.val j.isLt)
    apply hbase.trans (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) (Nat.cast_nonneg _)) hBphase
  have hqQ (j : ℕ) (hj : j < n) : q j ∣ Q :=
    Finset.dvd_prod_of_mem (fun j : Fin n => q j.val) (Finset.mem_univ (⟨j, hj⟩ : Fin n))
  have htotal : ((qS * Q : ℕ) : ℝ) ≤ Real.exp p := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hQbound (Nat.cast_nonneg qS)).trans hdenbudget
  obtain ⟨m, hm, hmp, hdiv, hbound⟩ := hiteration F b ω hF w hw H p hH hp hι hσ hHp
    hstructure U S eQ B (Real.exp Bphase) qS Q (Real.exp_nonneg _)
    (Nat.mul_pos hqS hQpos) htotal hcost hSbound hSgrid
  let pS' := fun j => if j < n then pS j else 0
  let pR' := fun j => if j < n then pR j else 0
  have hpS' : ∀ j < s, ∀ α i, |eQ.repr (coefficients (pS' j) α) i| ≤ Real.exp Bphase := by
    intro j _ α i
    by_cases hj : j < n
    · simpa only [pS', if_pos hj] using hpS j hj α i
    · simpa only [pS', if_neg hj, map_zero, Finsupp.zero_apply, abs_zero] using
        Real.exp_nonneg Bphase
  have hpR' : ∀ j < s, ∀ α,
      (fun i => eQ.repr (coefficients (pR' j) α) i) ∈ realDenominatorGrid Q := by
    intro j _ α
    by_cases hj : j < n
    · simpa only [pR', if_pos hj] using
        realDenominatorGrid_subset_of_dvd (hqpos j hj) (hqQ j hj) (hpR j hj α)
    · refine ⟨0, ?_⟩
      funext i
      simp [pR', hj]
  have hprefix : F.restrictedMajorOuterFactors b ω hF w U S
      (fun j => realChartSubstitute f (pS' j)) pR' n =
      F.restrictedMajorOuterFactors b ω hF w U S
        (fun j => realChartSubstitute f (pS j)) pR n := by
    apply F.restrictedMajorOuterFactors_congr
    · intro j hj
      simp only [pS', if_pos hj]
    · intro j hj
      simp only [pR', if_pos hj]
  have hout := hbound f hf pS' pR' hpS' hpR' n hn
  dsimp only at hout ⊢
  rw [hprefix] at hout
  exact ⟨m, hm, hmp, hdiv, hout⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3
open scoped TensorProduct BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

namespace UniversalLocalMajorSliceTest

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {N : I → ℕ} {degree : ℕ} {cost budget : ℝ}

theorem weight_norm (packet : UniversalLocalMajorSliceTest N degree cost budget)
    (x : I → ℤ) : ‖packet.weight x‖ ≤ 1 := by
  rw [weight, norm_star]
  exact packet.nativeModel.norm_le _

end UniversalLocalMajorSliceTest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartRecoveredTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientSample_floor_coeff_sum
    (sample : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o sample = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) :
    (fun i => mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (sample j) d i) +
      (fun i => (((coefficientIntegerFloorPolynomial U b o sample c j i).coeff d.val : ℤ) : ℝ)) =
      (c ⟨j, d⟩).val := by
  funext i
  have h := congrArg (fun polynomial : MvPolynomial K ℝ => polynomial.coeff d.val)
    (canonicalCoefficientSample_floor_polynomial_remainder U b hb o sample c hc j i).1
  simp only [coefficientRowPolynomial, monomialArrayPolynomial_coeff _ Subtype.val_injective,
    MvPolynomial.coeff_add,
    mixedLiftPolynomial_coeff _ _ _ _ Subtype.val_injective, coeff_map,
    Int.coe_castRingHom] at h
  exact h.symm

theorem canonicalCoefficientSample_floor_coeff_separate
    (sample : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o sample = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1))
    {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ))
    (hQU : U j ≤ LinearMap.ker Q) {D : ℝ} (hD : 0 < D)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hsmall : ∀ t, |Q (fun i => mixedLiftCoefficient (euclideanSubspace (U j))
      (b j) (o j) (sample j) d i) t| < 1 / D) :
    Q (fun i => (((coefficientIntegerFloorPolynomial U b o sample c j i).coeff d.val : ℤ) : ℝ)) = 0 := by
  apply (separate_kernel Q _ _ hD ?_ (hgrid _) hsmall).2
  rw [canonicalCoefficientSample_floor_coeff_sum U b hb o sample c hc j d]
  exact hQU (c ⟨j, d⟩).property

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (f : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

noncomputable def realSymbolProjection (w : σ → ℕ) :
    F.RealPolynomialSymbolGroup w →* G.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.filteredPolynomialSymbolMap G φ hφ w)

theorem exists_symbolFactorizationIn_projection_pullback
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hfactor : G.SymbolFactorizationIn f ν hG T
      (F.realSymbolProjection G φ hφ (fun _ => 1) X) p l U) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (((p + 2) ^ 10 + 2) ^ 36) ∧ l ∣ m ∧
      F.SymbolFactorizationIn e ω hF T X (((p + 2) ^ 10 + 2) ^ 18 + p) m
        (U.comap (F.associatedGradedMap G φ hφ)) := by
  classical
  let w : σ → ℕ := fun _ => 1
  let B := F.polynomialSymbolBasis e ω hF w
  let C := G.polynomialSymbolBasis f ν hG w
  let ψ := F.filteredPolynomialSymbolMap G φ hφ w
  have hψ : Function.Surjective ψ :=
    F.filteredPolynomialSymbolMap_surjective G φ hφ w hsurj
  have himage : (⊤ : LieSubalgebra ℚ (F.PolynomialSymbol w)).map ψ = ⊤ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨x, rfl⟩ := hψ y
      exact ⟨x, trivial, rfl⟩
  have hb : ∀ j i, RationalHeightLE (B.repr (B j) i) H := by
    intro j i
    simp only [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact rationalHeightLE_one hH
    · exact rationalHeightLE_zero hH
  obtain ⟨S, m, hm, hmp, hlm, hsolve, hslow, hgrid⟩ :=
    NilpotentLieBCHGroup.exists_controlled_fast_lift
      (F.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (G.polynomialSymbol_lowerCentralSeries_eq_bot w) B C
      (fun z => z.val.1) (fun z => z.val.1) ⊤ B B.span_eq
      (fun _ _ _ => trivial) ψ
      (fun i j hij => F.filteredPolynomialSymbolMap_monomial_blocks
        G e ω hF f ν hG φ hφ w j i hij)
      hH hl hb
      (fun i j => F.filteredPolynomialSymbolMap_basis_height
        G e ω hF f ν hG φ hφ w hH hentries j i)
      hp hrows hcols hHp hlp
  simp only [Basis.equivFun_apply] at hslow hgrid
  let lift := NilpotentLieBCHGroup.realLinearCoordinateLift
    (hL := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w) S
  have hright (g : G.RealPolynomialSymbolGroup w) :
      F.realSymbolProjection G φ hφ w (lift g) = g := by
    apply (hsolve g ?_).2
    change g.coord ∈ ((⊤ : LieSubalgebra ℚ (F.PolynomialSymbol w)).map ψ).toSubmodule.baseChange ℝ
    rw [himage]
    simp
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := hfactor
  dsimp only [SymbolSlowBound, SymbolRationalGrid] at hE hR
  let middle := (lift E)⁻¹ * X * (lift R)⁻¹
  have hmiddle : F.realSymbolProjection G φ hφ w middle = P := by
    dsimp only [middle]
    rw [map_mul, map_mul, map_inv, map_inv, hright, hright, ← hprod]
    group
  refine ⟨m, hm, hmp, hlm, lift E, middle, lift R, ?_, ?_, ?_, ?_⟩
  · dsimp only [middle]; group
  · have h := hslow (monomialScale T) (monomialScale_pos T hT)
      (Real.exp p) (Real.exp_pos p).le E (by with_reducible exact hE)
    simp only [← Real.exp_add] at h
    dsimp only [SymbolSlowBound]
    with_reducible exact h
  · apply hgrid R
    with_reducible exact hR
  · rw [← F.symbolPointwiseSubalgebra_comap G e ω hF f ν hG φ hφ w U,
      realificationLieSubalgebra_comap]
    change (F.realSymbolProjection G φ hφ w middle).coord ∈
      realificationLieSubalgebra (G.symbolPointwiseSubalgebra f ν hG w U)
    rw [hmiddle]
    with_reducible exact hP

end NilpotentLieFiltration
end Erdos3

end

end OAI
end


