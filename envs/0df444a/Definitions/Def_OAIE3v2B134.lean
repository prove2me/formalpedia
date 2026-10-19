-- Prove2me | Definitions.Def_OAIE3v2B134
-- name    : OAIE3v2B134
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:03:05.372446+00:00
-- url     : https://prove2.me/theorems/2c7eaf03-3678-4524-a26e-07505353618b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 136 of 311
-- statement:
--   Definitions bundle 136 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115`, `OAIE3v2B116`, `OAIE3v2B117`, `OAIE3v2B120`, `OAIE3v2B121` of this split.
--
--   Modules: `Estimates/CurrentLayerPreservation.lean`, `Estimates/DerivativeHorizontalLifts.lean`, `Estimates/DerivativeIndexBounds.lean`, `Estimates/FullFastHorizontalNormalization.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/ReindexedFastCoefficientSection.lean`, `Estimates/ShiftedGradedCalculus.lean`, `Estimates/UnnormalizedCommonSymbolFactorization.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Geometry/WeightedCoordinateExtraction.lean`, `Lattices/UniformDerivativeLatticeExtraction.lean`, `Linear/RationalTagConstraintChartBasis.lean`, `Linear/RealDualRationalBounds.lean`, `Nilpotent/ControlledBracketToCurrentLayer.lean`, `Nilpotent/CurrentBracketInductionStep.lean`, `Nilpotent/PolynomialBCHRemoval.lean`, `Polynomial/FormalPolynomialCorrectionStep.lean`, `Polynomial/PolynomialKernelDirectionBudget.lean`, `Polynomial/PolynomialLiftMatching.lean`, `Polynomial/RealPolynomialChartSubstitution.lean`, `Polynomial/ScaledPolynomialDualBounds.lean`, `Polynomial/ShiftedGradedPolynomial.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B116
import Definitions.Def_OAIE3v2B117
import Definitions.Def_OAIE3v2B120
import Definitions.Def_OAIE3v2B121

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem PolynomialDerivativeSystem.real_evaluation (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (hsystem : PolynomialDerivativeSystem P small rational extra) (i : σ) (t : σ → ℝ) :
    dualLogDerivative (realPolynomialJet i t P) = eval₂ t (small i) +
      dualAdjoint (realPolynomialValueHom t P) (eval₂ t (rational i)) + eval₂ t (extra i) := by
  have h := congrArg (eval₂ t) (hsystem i)
  simpa only [eval₂_formalLogDerivative, map_add, eval₂_dualAdjoint] using h

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealDualRationalBounds
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem realDualBasis_structure (b : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ ℝ (c i j k) = b.repr ⁅b i, b j⁆ k)
    (i j k : ι ⊕ ι) :
    algebraMap ℚ ℝ (dualStructureConstants c i j k) =
      (realDualBasis b).repr ⁅realDualBasis b i, realDualBasis b j⁆ k := by
  cases i <;> cases j <;> cases k <;>
    simp [dualStructureConstants, dualBaseLinear_lie, dualTangentLinear_lie, ← hc]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem dual_basis_bound {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L] (e : Basis ι ℝ L)
    (z : DualLieAlgebra L) (M : ℝ)
    (hb : ∀ i, |e.repr (dualBaseLinear z) i| ≤ M)
    (ht : ∀ i, |e.repr (dualTangentLinear z) i| ≤ M) :
    ∀ i, |(realDualBasis e).repr z i| ≤ M := by
  intro i
  cases i with
  | inl i => simpa only [realDualBasis_repr_inl] using hb i
  | inr i => simpa only [realDualBasis_repr_inr] using ht i

theorem exists_dual_coordinate_operation_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L]
      [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      1 ≤ H → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ z : DualGroup hnil,
        (∀ i, |e.repr (dualBaseLinear z.coord) i| ≤ Real.exp ((p + 2) ^ a)) →
        (∀ i, |e.repr (dualTangentLinear z.coord) i| ≤ Real.exp ((p + 2) ^ a)) →
        ∀ i, |e.repr (dualLogDerivative z) i| ≤ Real.exp ((p + C) ^ C)) ∧
      (∀ (g : NilpotentLieBCHGroup L s hnil) (x : L),
        (∀ i, |e.repr g.coord i| ≤ Real.exp ((p + 2) ^ a)) →
        (∀ i, |e.repr x i| ≤ Real.exp ((p + 2) ^ a)) →
        ∀ i, |e.repr (dualAdjoint g x) i| ≤ Real.exp ((p + C) ^ C)) := by
  have hproductExists := exists_bch_fixed_product_exp_bound s a 3
  obtain ⟨K, _, hproduct⟩ := hproductExists
  let B : Polynomial ℕ := (2 * Polynomial.X + Polynomial.C K) ^ K
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil hstructure hH hp hd hHp hc
  have hfinal : (2 * p + K) ^ K ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbound p hp
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp ((2 * p + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a)
  have hdim : (Fintype.card (ι ⊕ ι) : ℝ) ≤ 2 * p := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith
  have hproducts (rs : List (DualGroup hnil)) (hlen : rs.length ≤ 3)
      (hrs : ∀ r ∈ rs, ∀ i,
        |(realDualBasis e).repr r.coord i| ≤ Real.exp ((p + 2) ^ a)) :
      ∀ i, |(realDualBasis e).repr rs.prod.coord i| ≤ Real.exp ((p + C) ^ C) := by
    have hb := hproduct (realDualBasis e) (dualStructureConstants c) H (2 * p)
      (dualLie_lowerCentralSeries_eq_bot hnil) rs (realDualBasis_structure e c hstructure)
      (by positivity) hdim hlen (hHp.trans (Real.exp_le_exp.mpr (by linarith)))
      (dualStructureConstants_height c hH hc) (fun r hr i => (hrs r hr i).trans hinput)
    exact fun i => (hb i).trans (Real.exp_le_exp.mpr hfinal)
  constructor
  · intro z hbase htangent i
    have hconst : ∀ j, |(realDualBasis e).repr
        ((dualConstantHom (dualBaseHom z))⁻¹).coord j| ≤ Real.exp ((p + 2) ^ a) := by
      apply dual_basis_bound
      · intro j
        change |e.repr (dualBaseLinear (-dualConstantLie (dualBaseLinear z.coord))) j| ≤ _
        simpa only [map_neg, dualBaseLinear_constant, Finsupp.neg_apply, abs_neg] using hbase j
      · intro j
        change |e.repr (dualTangentLinear (-dualConstantLie (dualBaseLinear z.coord))) j| ≤ _
        simp only [map_neg, dualTangentLinear_constant, neg_zero, map_zero, Finsupp.zero_apply, abs_zero]
        exact Real.exp_nonneg _
    have hinputs : ∀ r ∈ [z, (dualConstantHom (dualBaseHom z))⁻¹],
        ∀ j, |(realDualBasis e).repr r.coord j| ≤ Real.exp ((p + 2) ^ a) := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dual_basis_bound e _ _ hbase htangent
      · exact hconst
    have hh := hproducts [z, (dualConstantHom (dualBaseHom z))⁻¹] (by simp) hinputs (Sum.inr i)
    simpa only [List.prod_cons, List.prod_nil, mul_one, realDualBasis_repr_inr, dualLogDerivative] using hh
  · intro g x hg hx i
    have hleft : ∀ j, |(realDualBasis e).repr (dualConstantHom g).coord j| ≤
        Real.exp ((p + 2) ^ a) := by
      apply dual_basis_bound
      · intro j
        change |e.repr (dualBaseLinear (dualConstantLie g.coord)) j| ≤ _
        simpa only [dualBaseLinear_constant] using hg j
      · intro j
        change |e.repr (dualTangentLinear (dualConstantLie g.coord)) j| ≤ _
        simp only [dualTangentLinear_constant, map_zero, Finsupp.zero_apply, abs_zero]
        exact Real.exp_nonneg _
    have hmiddle : ∀ j, |(realDualBasis e).repr (dualTangentElement (hnil := hnil) x).coord j| ≤
        Real.exp ((p + 2) ^ a) := by
      apply dual_basis_bound
      · intro j
        change |e.repr (dualBaseLinear (dualInfinitesimal x)) j| ≤ _
        simp only [dualBaseLinear_infinitesimal, map_zero, Finsupp.zero_apply, abs_zero]
        exact Real.exp_nonneg _
      · intro j
        change |e.repr (dualTangentLinear (dualInfinitesimal x)) j| ≤ _
        simpa only [dualTangentLinear_infinitesimal] using hx j
    have hright : ∀ j, |(realDualBasis e).repr ((dualConstantHom g)⁻¹).coord j| ≤
        Real.exp ((p + 2) ^ a) := by
      intro j
      simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hleft j
    have hinputs : ∀ r ∈ [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹],
        ∀ j, |(realDualBasis e).repr r.coord j| ≤ Real.exp ((p + 2) ^ a) := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hleft
      · exact hmiddle
      · exact hright
    have hh := hproducts [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹]
      (by simp) hinputs (Sum.inr i)
    simpa only [List.prod_cons, List.prod_nil, mul_one, ← mul_assoc, realDualBasis_repr_inr, dualAdjoint] using hh

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rationalDualBasis_structure (b : Basis ι ℚ L) (i j k : ι ⊕ ι) :
    lieStructureConstants (L := DualLieAlgebra L) (rationalDualBasis b) i j k =
      dualStructureConstants (lieStructureConstants b) i j k := by
  cases i <;> cases j <;> cases k <;>
    simp [lieStructureConstants, dualStructureConstants, dualBaseLinear_lie, dualTangentLinear_lie]

theorem rationalDualBasis_structure_height (b : Basis ι ℚ L) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) (i j k : ι ⊕ ι) :
    RationalHeightLE (lieStructureConstants (L := DualLieAlgebra L) (rationalDualBasis b) i j k) H := by
  rw [rationalDualBasis_structure]
  exact dualStructureConstants_height _ hH hc i j k

theorem rationalDualBasis_grid_iff [Fintype ι] (b : Basis ι ℚ L) (l : ℕ) (x : DualLieAlgebra L) :
    (rationalDualBasis b).equivFun x ∈ denominatorGrid l ↔
      b.equivFun (dualBaseLinear x) ∈ denominatorGrid l ∧
      b.equivFun (dualTangentLinear x) ∈ denominatorGrid l := by
  constructor
  · rintro ⟨a, ha⟩
    constructor
    · exact ⟨fun i => a (Sum.inl i), fun i => by
        simpa only [Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inl] using ha (Sum.inl i)⟩
    · exact ⟨fun i => a (Sum.inr i), fun i => by
        simpa only [Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inr] using ha (Sum.inr i)⟩
  · rintro ⟨⟨a, ha⟩, ⟨b', hb'⟩⟩
    refine ⟨Sum.elim a b', ?_⟩
    intro i
    cases i with
    | inl i => simpa only [Sum.elim_inl, Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inl] using ha i
    | inr i => simpa only [Sum.elim_inr, Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inr] using hb' i

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem real_dual_log_grid_of_rational (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (hlog : ∀ z : DualGroup hnil,
      e.equivFun (dualBaseLinear z.coord) ∈ denominatorGrid l →
      e.equivFun (dualTangentLinear z.coord) ∈ denominatorGrid l →
      e.equivFun (dualLogDerivative z) ∈ denominatorGrid m)
    (z : DualGroup (realification_lowerCentralSeries_eq_bot hnil))
    (hb : (e.baseChange ℝ).equivFun (dualBaseLinear z.coord) ∈ realDenominatorGrid l)
    (ht : (e.baseChange ℝ).equivFun (dualTangentLinear z.coord) ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (dualLogDerivative z) ∈ realDenominatorGrid m := by
  obtain ⟨a, ha, hea⟩ := real_grid_exists_rationalLieInclusion e l hl _ hb
  obtain ⟨b, hb, heb⟩ := real_grid_exists_rationalLieInclusion e l hl _ ht
  let q : DualGroup hnil := ⟨dualConstantLie a + dualInfinitesimal b⟩
  have hqa : dualBaseLinear q.coord = a := by
    change dualBaseLinear (dualConstantLie a + dualInfinitesimal b) = a
    simp only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]
  have hqb : dualTangentLinear q.coord = b := by
    change dualTangentLinear (dualConstantLie a + dualInfinitesimal b) = b
    simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]
  have hq := hlog q (by rwa [hqa]) (by rwa [hqb])
  have he : rationalLieInclusion (dualLogDerivative q) = dualLogDerivative z := by
    apply dualLinearLift_logDerivative_eq (realification_lowerCentralSeries_eq_bot hnil)
      (⊤ : LieIdeal ℚ L) rationalLieInclusion rationalLieInclusion.toLinearMap
      (fun x y _ => rationalLieInclusion.map_lie x y) q (by trivial) z
    apply dual_ext
    · rw [dualLinearLift_base, hqa]
      exact hea
    · rw [dualLinearLift_tangent, hqb]
      exact heb
  change (fun i => (e.baseChange ℝ).repr (dualLogDerivative z) i) ∈ realDenominatorGrid m
  rw [← he]
  simp_rw [rationalLieInclusion_coordinates]
  exact (real_cast_mem_denominatorGrid_iff m _).mpr hq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realificationLieSubalgebra_toSubmodule (K : LieSubalgebra ℚ L) :
    (realificationLieSubalgebra K).toSubmodule = K.toSubmodule.baseChange ℝ := rfl

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem mem_real_symbolPointwiseSubalgebra_iff_coefficients
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w) :
    x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hlayers w U) ↔
      ∀ α, coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α ∈
        realificationLieSubalgebra U := by
  change x ∈ (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule.baseChange ℝ ↔ _
  rw [F.symbolPointwiseSubalgebra_eq_ker, real_baseChange_ker]
  change (F.symbolSubalgebraQuotientMap b ω hlayers w U).baseChange ℝ x = 0 ↔ _
  rw [VectorPolynomial.realificationLinearEquiv_eq_zero_iff]
  have hker : U.toSubmodule.baseChange ℝ = LinearMap.ker (U.toSubmodule.mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using real_baseChange_ker U.toSubmodule.mkQ
  constructor
  · intro hx α
    change coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α ∈ U.toSubmodule.baseChange ℝ
    rw [hker]
    change U.toSubmodule.mkQ.baseChange ℝ
      (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) = 0
    exact (F.symbolSubalgebraQuotientMap_real_coefficient b ω hlayers w U x α).symm.trans (hx α)
  · intro hx α
    have h := hx α
    change coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α ∈ U.toSubmodule.baseChange ℝ at h
    rw [hker] at h
    exact (F.symbolSubalgebraQuotientMap_real_coefficient b ω hlayers w U x α).trans h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScaledPolynomialDualBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_polynomial_slow_product_bound (s a k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∀ rs : List ((F.realification.adaptedPolynomialFiltration w).Group), rs.length ≤ k →
      (∀ r ∈ rs, F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) r) →
      F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C)) rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_bch_fixed_product_exp_bound s a k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT rs hlen hrs
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.adaptedMonomialBasis b ω hlayers w
  let E := F.scaledRealAdaptedMonomialBasis b ω hlayers w T hT
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (AdaptedBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (adaptedBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hstruct : ∀ i j z, algebraMap ℚ ℝ (lieStructureConstants B i j z) = E.repr ⁅E i, E j⁆ z :=
    fun i j z => (F.scaledRealAdaptedMonomialBasis_structure b ω hlayers w T hT i j z).symm
  have hheight : ∀ i j z, RationalHeightLE (lieStructureConstants B i j z) H :=
    F.adaptedMonomialBasis_bracket_height b ω hlayers w hH hb
  let ys := rs.map (F.realAdaptedPolynomialGroupLift w b ω hlayers)
  have hys : ys.map (F.realAdaptedPolynomialGroupHom w) = rs := by
    simp only [ys, List.map_map, Function.comp_def, F.realAdaptedPolynomialGroupHom_lift]
    simp
  have hinput : ∀ r ∈ ys, ∀ z, |E.repr r.coord z| ≤ Real.exp ((q + 2) ^ a) := by
    intro r hr z
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    have hslow : F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a))
        (F.realAdaptedPolynomialGroupHom w (F.realAdaptedPolynomialGroupLift w b ω hlayers u)) := by
      rw [F.realAdaptedPolynomialGroupHom_lift]
      exact hrs u hu
    have hz := (F.polynomialSlowBound_groupHom_iff b w ω hlayers T hT (Real.exp_nonneg _) _).mp hslow z
    have hscaled := (F.scaledRealAdaptedMonomialBasis_bound_iff b ω hlayers w T hT _ z _).mpr hz
    exact hscaled.trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity) (add_le_add hpq (le_refl 2)) a))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  have hout : F.PolynomialSlowBound b w T (Real.exp ((p + C) ^ C))
      (F.realAdaptedPolynomialGroupHom w ys.prod) := by
    apply (F.polynomialSlowBound_groupHom_iff b w ω hlayers T hT (Real.exp_nonneg _) _).mpr
    intro z
    apply (F.scaledRealAdaptedMonomialBasis_bound_iff b ω hlayers w T hT _ z _).mp
    exact (hK E (lieStructureConstants B) H q
      (F.adaptedPolynomialFiltration w).realification.lowerCentralSeries_eq_bot ys hstruct hq hdim
      (by simpa only [ys, List.length_map] using hlen) (hHp.trans (Real.exp_le_exp.mpr hpq))
      hheight hinput z).trans (Real.exp_le_exp.mpr hpoly)
  rwa [map_list_prod, hys] at hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realAdaptedCoefficientBound_scaled_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.RealAdaptedCoefficientBound b ω hF w T M x ↔
      ∀ z, |(F.scaledRealAdaptedMonomialBasis b ω hF w T hT).repr x z| ≤ M := by
  simp only [RealAdaptedCoefficientBound, F.scaledRealAdaptedMonomialBasis_bound_iff]

theorem exists_scaled_polynomial_dual_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      (∀ z : DualGroup (F.adaptedPolynomialFiltration w).realification.lowerCentralSeries_eq_bot,
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) (dualBaseLinear z.coord) →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) (dualTangentLinear z.coord) →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + C) ^ C)) (dualLogDerivative z)) ∧
      (∀ (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w),
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) g.coord →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) x →
        F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + C) ^ C)) (dualAdjoint g x)) := by
  have hdualExists := exists_dual_coordinate_operation_bound s a
  obtain ⟨D, _, hdual⟩ := hdualExists
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let B : Polynomial ℕ := (Q + Polynomial.C D) ^ D
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hc T hT
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hF)
  let q := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ (s + 2))).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (AdaptedBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (adaptedBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hF))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hfinal : (q + D) ^ D ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp ((q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (add_le_add hpq (le_refl (2 : ℝ))) a)
  let E := F.scaledRealAdaptedMonomialBasis b ω hF w T hT
  have hoperations := hdual E (lieStructureConstants (F.adaptedMonomialBasis b ω hF w)) H q
    (F.adaptedPolynomialFiltration w).realification.lowerCentralSeries_eq_bot
    (fun i j k => (F.scaledRealAdaptedMonomialBasis_structure b ω hF w T hT i j k).symm)
    hH hq hdim (hHp.trans (Real.exp_le_exp.mpr hpq))
    (F.adaptedMonomialBasis_bracket_height b ω hF w hH hc)
  have hin (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
      (hx : F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) x) :
      ∀ z, |E.repr x z| ≤ Real.exp ((q + 2) ^ a) :=
    fun z => ((F.realAdaptedCoefficientBound_scaled_iff b ω hF w T hT _ x).mp hx z).trans hinput
  have hout (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
      (hx : ∀ z, |E.repr x z| ≤ Real.exp ((q + D) ^ D)) :
      F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + C) ^ C)) x := by
    apply (F.realAdaptedCoefficientBound_scaled_iff b ω hF w T hT _ x).mpr
    exact fun z => (hx z).trans (Real.exp_le_exp.mpr hfinal)
  constructor
  · intro z hb ht
    exact hout _ (hoperations.1 z (hin _ hb) (hin _ ht))
  · intro g x hg hx
    exact hout _ (hoperations.2 g x (hin _ hg) (hin _ hx))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedGradedPolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem shiftedGradedPolynomial_monomial (k : ℕ) (α : σ →₀ ℕ) (v : L) :
    F.shiftedGradedPolynomial b ω hlayers w k (monomial α v) =
      monomial α (F.gradedPieceProjection b ω hlayers (Finsupp.weight w α + k) v) := by
  classical
  apply coefficients.injective
  apply Finsupp.ext
  intro β
  rw [F.shiftedGradedPolynomial_coefficient, coefficients_monomial, coefficients_monomial]
  by_cases h : α = β
  · subst β
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), Finsupp.single_eq_of_ne (Ne.symm h), map_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedGradedCalculus
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem shiftedGradedPolynomial_directionalDerivative [Fintype σ] (h : σ → ℚ)
    (k : ℕ) (p : VectorPolynomial σ ℚ L) :
    F.shiftedGradedPolynomial b ω hlayers (fun _ : σ => 1) (k + 1) (directionalDerivative h p) =
      directionalDerivative h (F.shiftedGradedPolynomial b ω hlayers (fun _ : σ => 1) k p) := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.shiftedGradedPolynomial_coefficient, coefficients_directionalDerivative,
    coefficients_directionalDerivative, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, F.shiftedGradedPolynomial_coefficient]
  simp only [map_add, Finsupp.weight_single, one_smul, Nat.add_right_comm, Nat.add_assoc]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CurrentLayerPreservation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem lie_mem_invariant_sup_layer_of_degree
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {i j : ℕ}
    {u v : L} (hu : u ∈ U) (hui : u ∈ F.layer i) (hv : v ∈ V ⊔ F.layer j) :
    ⁅u, v⁆ ∈ V ⊔ F.layer (i + j) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [lie_add]
  exact (V ⊔ F.layer (i + j)).add_mem
    (Submodule.mem_sup_left (hUV _ hu _ hx))
    (Submodule.mem_sup_right (F.lie_mem hui hy))

theorem correction_adjoint_sub_current_bracket_mem (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {j : ℕ} (hj : 2 ≤ j)
    (a : F.Group) (haU : a.coord ∈ U) (ha : a.coord ∈ F.layer (j - 1))
    (x k : L) (hx : x - k ∈ V ⊔ F.layer 2) :
    dualAdjoint a x - (x + ⁅a.coord, k⁆) ∈ V ⊔ F.layer (j + 1) := by
  have hx1 : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hrem := F.dualAdjoint_sub_first_bracket_mem_layer hs a ha x hx1
  have hrem' : dualAdjoint a x - (x + ⁅a.coord, x⁆) ∈ F.layer (j + 1) :=
    F.antitone (by omega) hrem
  have hbr : ⁅a.coord, x - k⁆ ∈ V ⊔ F.layer (j + 1) := by
    have h := F.lie_mem_invariant_sup_layer_of_degree U V hUV haU ha hx
    have he : j - 1 + 2 = j + 1 := by omega
    simpa only [he] using h
  have h := (V ⊔ F.layer (j + 1)).add_mem (Submodule.mem_sup_right hrem') hbr
  rw [lie_sub] at h
  convert h using 1; abel

theorem correction_removal_coord_sub_mem_layer {j : ℕ}
    (a g c : F.Group) (ha : a.coord ∈ F.layer (j - 1))
    (hc : c.coord ∈ F.layer (j - 1)) (hj : 1 ≤ j) :
    (a⁻¹ * g * c⁻¹).coord - (g.coord - a.coord - c.coord) ∈ F.layer j := by
  have hg1 : g.coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hag1 : (a⁻¹ * g).coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have ha' : -a.coord ∈ F.layer (j - 1) := (F.layer (j - 1)).neg_mem ha
  have hc' : -c.coord ∈ F.layer (j - 1) := (F.layer (j - 1)).neg_mem hc
  have hleft : ⁅-a.coord, g.coord⁆ ∈ F.layer j := by
    simpa only [Nat.sub_add_cancel hj] using F.lie_mem ha' hg1
  have hright : ⁅(a⁻¹ * g).coord, -c.coord⁆ ∈ F.layer j := by
    have he : 1 + (j - 1) = j := by omega
    simpa only [he] using F.lie_mem hag1 hc'
  have h1 := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot (F.layerIdeal j)
    (-a.coord) g.coord hleft
  have h2 := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot (F.layerIdeal j)
    (a⁻¹ * g).coord (-c.coord) hright
  change (a⁻¹ * g).coord - (-a.coord + g.coord) ∈ F.layer j at h1
  change (a⁻¹ * g * c⁻¹).coord - ((a⁻¹ * g).coord + -c.coord) ∈ F.layer j at h2
  convert (F.layer j).add_mem h2 h1 using 1; abel

theorem correction_removal_preserves_lower_layers {j : ℕ}
    (a g c : F.Group) (ha : a.coord ∈ F.layer (j - 1))
    (hc : c.coord ∈ F.layer (j - 1)) (hj : 1 ≤ j) :
    (a⁻¹ * g * c⁻¹).coord - g.coord ∈ F.layer (j - 1) := by
  have h := F.antitone (by omega : j - 1 ≤ j)
    (F.correction_removal_coord_sub_mem_layer a g c ha hc hj)
  have hneg := (F.layer (j - 1)).neg_mem ((F.layer (j - 1)).add_mem ha hc)
  convert (F.layer (j - 1)).add_mem h hneg using 1; abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem logDerivative_current_layer_of_lower_brackets (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (z : DualGroup F.lowerCentralSeries_eq_bot) (hz : dualBaseLinear z.coord ∈ U)
    (k : L) (ht : dualTangentLinear z.coord - k ∈ V ⊔ F.layer j)
    (hk : ⁅dualBaseLinear z.coord, k⁆ ∈ V ⊔ F.layer (j + 1)) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ V ⊔ F.layer (j + 1) := by
  apply F.logDerivative_current_layer_relation hs U V hUV j z hz
  have h := (V ⊔ F.layer (j + 1)).add_mem
    (F.lie_mem_invariant_sup_next_layer U V hUV j hz ht) hk
  simpa only [lie_sub, sub_add_cancel] using h

theorem adjoint_sub_mem_invariant_next_layer (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (g : F.Group) (hg : g.coord ∈ U) (r : L) (hr : r ∈ V ⊔ F.layer j) :
    dualAdjoint g r - r ∈ V ⊔ F.layer (j + 1) := by
  have hbr := F.lie_mem_invariant_sup_next_layer U V hUV j hg hr
  have hW := F.invariant_sup_layer U V hUV (j + 1)
  have hrem := dualAdjoint_sub_first_bracket_mem hs U (V ⊔ F.layer (j + 1))
    hW g hg r (hW _ hg _ hbr)
  convert (V ⊔ F.layer (j + 1)).add_mem hrem hbr using 1; abel

theorem current_layer_derivative_system (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (z : DualGroup F.lowerCentralSeries_eq_bot) (hz : dualBaseLinear z.coord ∈ U)
    (k small rational extra : L)
    (ht : dualTangentLinear z.coord - k ∈ V ⊔ F.layer j)
    (hk : ⁅dualBaseLinear z.coord, k⁆ ∈ V ⊔ F.layer (j + 1))
    (hr : rational ∈ V ⊔ F.layer j) (he : extra - k ∈ V ⊔ F.layer (j + 1))
    (hsystem : dualLogDerivative z = small + dualAdjoint (dualBaseHom z) rational + extra) :
    dualTangentLinear z.coord - k - (small + rational) ∈ V ⊔ F.layer (j + 1) := by
  have hY := F.logDerivative_current_layer_of_lower_brackets (by omega) U V hUV j z hz k ht hk
  have hA := F.adjoint_sub_mem_invariant_next_layer hs U V hUV j (dualBaseHom z) hz rational hr
  rw [hsystem] at hY
  convert (V ⊔ F.layer (j + 1)).add_mem
    ((V ⊔ F.layer (j + 1)).neg_mem hY) ((V ⊔ F.layer (j + 1)).add_mem hA he) using 1
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem realGradeProjection_mem_layer (k : ℕ) (x : ℝ ⊗[ℚ] L) :
    basisGradeProjection (b.baseChange ℝ) w k x ∈ F.realification.layer k := by
  change basisGradeProjection (b.baseChange ℝ) w k x ∈ (F.realLayer k).toSubmodule
  rw [F.realLayer_eq_span_basis b k _ (hlayers k)]
  apply Submodule.span_mono (Set.image_mono ?_)
    (basisCoordinateProjection_mem_span (b.baseChange ℝ) {i | w i = k} x)
  intro i hi
  exact (show w i = k from hi).ge

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem realGradeProjection_mem_of_mem_sup_next
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (j : ℕ) (x : ℝ ⊗[ℚ] L) (hx : x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    basisGradeProjection (b.baseChange ℝ) w j x ∈ V := by
  obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers j z hz, add_zero]
  exact hV j v hv

include hlayers in
theorem real_correction_preserves_grades_below (j : ℕ) (a g c : F.realification.Group)
    (ha : a.coord ∈ F.realification.layer j) (hc : c.coord ∈ F.realification.layer j) :
    ∀ d < j, basisGradeProjection (b.baseChange ℝ) w d (a⁻¹ * g * c⁻¹).coord =
      basisGradeProjection (b.baseChange ℝ) w d g.coord := by
  have hdiff : (a⁻¹ * g * c⁻¹).coord - g.coord ∈ F.realification.layer j := by
    have h := F.realification.correction_removal_preserves_lower_layers (j := j + 1)
      a g c (by simpa using ha) (by simpa using hc) (by omega)
    simpa only [Nat.add_sub_cancel] using h
  intro d hd
  have hz := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers d _
    (F.realification.antitone (Nat.succ_le_of_lt hd) hdiff)
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

include hlayers in
theorem real_correction_current_grade (j : ℕ) (a g c : F.realification.Group)
    (ha : a.coord ∈ F.realification.layer j) (hc : c.coord ∈ F.realification.layer j) :
    basisGradeProjection (b.baseChange ℝ) w j (a⁻¹ * g * c⁻¹).coord =
      basisGradeProjection (b.baseChange ℝ) w j g.coord -
        basisGradeProjection (b.baseChange ℝ) w j a.coord -
        basisGradeProjection (b.baseChange ℝ) w j c.coord := by
  have h := F.realGradeProjection_bch_triple b w hlayers j (-a.coord) g.coord (-c.coord)
    ((F.realification.layer j).neg_mem ha) ((F.realification.layer j).neg_mem hc)
  change basisGradeProjection (b.baseChange ℝ) w j (a⁻¹ * g * c⁻¹).coord = _ at h
  rw [h, map_neg, map_neg]
  abel

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

section Rational

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adjoint_correction_sub_mem_layer (hs : 2 ≤ s) (j : ℕ)
    (a : F.Group) (ha : a.coord ∈ F.layer j) (x : L) :
    dualAdjoint a x - x ∈ F.layer (j + 1) := by
  have hx : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hrem := F.dualAdjoint_sub_first_bracket_mem_layer hs a ha x hx
  have hsmall : dualAdjoint a x - (x + ⁅a.coord, x⁆) ∈ F.layer (j + 1) :=
    F.antitone (by omega) hrem
  have hbr : ⁅a.coord, x⁆ ∈ F.layer (j + 1) := F.lie_mem ha hx
  convert (F.layer (j + 1)).add_mem hsmall hbr using 1
  abel

end Rational

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeIndexBounds
namespace OAI

section

namespace Erdos3

theorem euclideanDerivative_index_graph_bounds
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let k := Module.finrank ℝ (LinearMap.ker π)
    let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup
    let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
    0 < I ∧ ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
        (MeasureTheory.volume (α := LinearMap.ker π)) ≤ C ∧
      (I : ℝ) ≤ C * (l : ℝ) ^ k ∧
      Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det ≤ C * (l : ℝ) ^ k := by
  let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
  let hspos : ∀ j, 0 < scale j := fun j => lt_of_lt_of_le zero_lt_one (hscale j)
  let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T hT0 scale (fun j => (hspos j).ne') Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
  let k := Module.finrank ℝ (LinearMap.ker π)
  have hresult := euclideanDerivative_covolume_product_bound
    T hT scale (fun j => (hspos j).ne') Y A l hl R δ hR hδ H r hr hnorm hdense hlarge
  obtain ⟨hI, G, hG, hsection, hprod⟩ := hresult
  refine ⟨hI, G, hG, hsection, ?_⟩
  obtain ⟨p, _, hp⟩ := euclideanDerivative_vertical_covolume_lower
    T hT0 scale hspos Y A hA hdiag l hl ρ
  have hden : 0 < (l : ℝ) ^ k := pow_pos (by exact_mod_cast hl) _
  have hweights : 1 ≤ ∏ i, scale (p i) := Finset.one_le_prod (fun i _ => hscale (p i))
  have hlower : 1 / (l : ℝ) ^ k ≤
      ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
        (MeasureTheory.volume (α := LinearMap.ker π)) := by
    calc
      1 / (l : ℝ) ^ k = 1 / (l : ℝ) ^ k * 1 := (mul_one _).symm
      _ ≤ 1 / (l : ℝ) ^ k * (∏ i, scale (p i)) :=
        mul_le_mul_of_nonneg_left hweights (one_div_pos.mpr hden).le
      _ ≤ _ := hp
  apply covolume_index_graph_bounds hden hlower
    (by exact_mod_cast Nat.succ_le_iff.mpr hI)
    (one_le_euclidean_section_gram_sqrt Z G hG)
  exact hprod

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem associatedGradedBasis_homogeneous_brackets :
    BasisHomogeneousBrackets (F.associatedGradedBasis b w hlayers) w := by
  intro i j k hk
  rw [F.associatedGradedBasis_bracket b w hlayers, if_neg (Ne.symm hk)]

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialBCHRemoval
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def bchRemove (s : ℕ) (A P B : VectorPolynomial σ ℚ L) :
    VectorPolynomial σ ℚ L := lieBCH s (lieBCH s (-A) P) (-B)

theorem eval₂_bchRemove [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    (s : ℕ) (A P B : VectorPolynomial σ ℚ L) (t : σ → ℝ) :
    eval₂ t (bchRemove s A P B) = lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B) := by
  have h₁ := map_lieBCH (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t) s (lieBCH s (-A) P) (-B)
  have h₂ := map_lieBCH (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t) s (-A) P
  rw [h₂] at h₁
  simp only [map_neg, eval₂Lie_apply] at h₁
  exact h₁

theorem bchRemove_coefficients_mem (U : LieSubalgebra ℚ L) (s : ℕ)
    (A P B : VectorPolynomial σ ℚ L)
    (hA : ∀ α, coefficients A α ∈ U) (hP : ∀ α, coefficients P α ∈ U)
    (hB : ∀ α, coefficients B α ∈ U) :
    ∀ α, coefficients (bchRemove s A P B) α ∈ U := by
  let W := coefficientLieSubalgebra (σ := σ) U
  have ha : A ∈ W := hA
  have hp : P ∈ W := hP
  have hb : B ∈ W := hB
  exact lieBCH_mem W s (lieBCH_mem W s (W.neg_mem ha) hp) (W.neg_mem hb)

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem polynomial_bchRemove_grades (E : Submodule ℝ (ℝ ⊗[ℚ] L)) (j : ℕ)
    (hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (A P B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hA : ∀ α, coefficients A α ∈ E) (hB : ∀ α, coefficients B α ∈ E) :
    map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (bchRemove s A P B) =
      map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P - A - B ∧
      ∀ d < j, map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) (bchRemove s A P B) =
        map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P := by
  have heq (X Y : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
      (h : ∀ t : σ → ℝ, eval₂ t X = eval₂ t Y) : X = Y := by
    apply sub_eq_zero.mp
    apply eq_zero_of_eval₂_zero (K := ℝ)
    intro t
    rw [map_sub, h t, sub_self]
  have hvalues (t : σ → ℝ) :
      basisGradeProjection (b.baseChange ℝ) w j
          (lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B)) =
        basisGradeProjection (b.baseChange ℝ) w j (eval₂ t P) - eval₂ t A - eval₂ t B ∧
      ∀ d < j, basisGradeProjection (b.baseChange ℝ) w d
          (lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B)) =
        basisGradeProjection (b.baseChange ℝ) w d (eval₂ t P) := by
    have ha := hE _ ((eval₂_mem_iff_coefficients E A).mpr hA t)
    have hc := hE _ ((eval₂_mem_iff_coefficients E B).mpr hB t)
    have hal : eval₂ t A ∈ F.realification.layer j := by
      simpa only [ha] using F.realGradeProjection_mem_layer b w hlayers j (eval₂ t A)
    have hcl : eval₂ t B ∈ F.realification.layer j := by
      simpa only [hc] using F.realGradeProjection_mem_layer b w hlayers j (eval₂ t B)
    have hcurrent := F.real_correction_current_grade b w hlayers j
      ⟨eval₂ t A⟩ ⟨eval₂ t P⟩ ⟨eval₂ t B⟩ hal hcl
    have hbelow := F.real_correction_preserves_grades_below b w hlayers j
      ⟨eval₂ t A⟩ ⟨eval₂ t P⟩ ⟨eval₂ t B⟩ hal hcl
    change basisGradeProjection (b.baseChange ℝ) w j
      (lieBCH s (lieBCH s (-eval₂ t A) (eval₂ t P)) (-eval₂ t B)) = _ at hcurrent
    rw [ha, hc] at hcurrent
    exact ⟨hcurrent, hbelow⟩
  constructor
  · apply heq
    intro t
    simp only [eval₂_map, eval₂_bchRemove, map_sub]
    exact (hvalues t).1
  · intro d hd
    apply heq
    intro t
    simp only [eval₂_map, eval₂_bchRemove]
    exact (hvalues t).2 d hd

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace VectorPolynomial

theorem pderiv_map {σ V W : Type*} [LieRing V] [LieAlgebra ℚ V]
    [LieRing W] [LieAlgebra ℚ W] (i : σ) (f : V →ₗ[ℚ] W) (P : VectorPolynomial σ ℚ V) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor W (map f P) =
      map f ((MvPolynomial.pderiv i).toLinearMap.rTensor V P) := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  simp only [coefficients_pderiv, coefficients_map, map_smul]

theorem pderiv_mem_submodule {σ V : Type*} [LieRing V] [LieAlgebra ℚ V]
    (W : Submodule ℚ V) (P : VectorPolynomial σ ℚ V)
    (hP : ∀ α, coefficients P α ∈ W) (i : σ) (α : σ →₀ ℕ) :
    coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor V P) α ∈ W := by
  rw [coefficients_pderiv]
  exact W.smul_mem _ (hP _)

end VectorPolynomial

namespace NilpotentLieFiltration

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem real_sub_horizontal_mem_of_lower_grades (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    {j : ℕ} (hj : 2 ≤ j) (x : ℝ ⊗[ℚ] L)
    (hlower : ∀ d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d x ∈ V) :
    x - basisGradeProjection (b.baseChange ℝ) w 1 x ∈ V ⊔ (F.realLayer j).toSubmodule := by
  classical
  have hzero : basisGradeProjection (b.baseChange ℝ) w 0 x = 0 :=
    F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers 0 x
      (by rw [show 0 + 1 = 1 from rfl, F.realification.one_eq_top]; trivial)
  have hlow : basisBelowProjection (b.baseChange ℝ) w j x -
      basisGradeProjection (b.baseChange ℝ) w 1 x ∈ V := by
    rw [basisBelowProjection_eq_sum_grades,
      ← Finset.sum_erase_add (Finset.range j) (fun d => basisGradeProjection (b.baseChange ℝ) w d x)
        (by simp only [Finset.mem_range]; omega : 1 ∈ Finset.range j), add_sub_cancel_right]
    apply V.sum_mem
    intro d hd
    obtain ⟨hd1, hdj⟩ := Finset.mem_erase.mp hd
    by_cases hd0 : d = 0
    · subst d
      rw [hzero]
      exact V.zero_mem
    · exact hlower d (by omega) (Finset.mem_range.mp hdj)
  have hhigh := F.sub_realGradeTruncation_mem b w hlayers j x
  have h := (V ⊔ (F.realLayer j).toSubmodule).add_mem
    (Submodule.mem_sup_right hhigh) (Submodule.mem_sup_left hlow)
  convert h using 1
  abel

include hlayers in
theorem real_polynomial_derivative_lower_layers (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    {j : ℕ} (hj : 2 ≤ j) (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P α) ∈ V)
    (i : σ) (t : σ → ℝ) :
    let D := eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P)
    D - basisGradeProjection (b.baseChange ℝ) w 1 D ∈ V ⊔ (F.realLayer j).toSubmodule ∧
      basisGradeProjection (b.baseChange ℝ) w 1 D ∈ K := by
  intro D
  let π := basisGradeProjection (b.baseChange ℝ) w 1
  let q := LinearMap.id - π
  let W := V ⊔ (F.realLayer j).toSubmodule
  have hq : ∀ α, coefficients (map (q.restrictScalars ℚ) P) α ∈ W := by
    intro α
    rw [coefficients_map]
    exact F.real_sub_horizontal_mem_of_lower_grades b w hlayers V hj _ (hlower α)
  have hπ : ∀ α, coefficients (map (π.restrictScalars ℚ) P) α ∈ K := by
    intro α
    rw [coefficients_map]
    exact hK α
  have hDq := (eval₂_mem_iff_coefficients W
    ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (map (q.restrictScalars ℚ) P))).mpr
      (pderiv_mem_submodule (W.restrictScalars ℚ) _ hq i) t
  have hDπ := (eval₂_mem_iff_coefficients K
    ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (map (π.restrictScalars ℚ) P))).mpr
      (pderiv_mem_submodule (K.restrictScalars ℚ) _ hπ i) t
  rw [pderiv_map, eval₂_map] at hDq hDπ
  exact ⟨hDq, hDπ⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem real_current_layer_polynomial_derivative_equation (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) {j : ℕ} (hj : 2 ≤ j)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hU : ∀ t : σ → ℝ, eval₂ t P ∈ U)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P α) ∈ V)
    (hbracket : ∀ (t : σ → ℝ) k, k ∈ K →
      ⁅eval₂ t P, k⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (extra : σ → (σ → ℝ) → ℝ ⊗[ℚ] L)
    (z : σ → (σ → ℝ) → DualGroup F.realification.lowerCentralSeries_eq_bot)
    (hbase : ∀ i t, dualBaseLinear (z i t).coord = eval₂ t P)
    (htangent : ∀ i t, dualTangentLinear (z i t).coord =
      eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P))
    (hextra : ∀ i t, extra i t - basisGradeProjection (b.baseChange ℝ) w 1
      (eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P)) ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : ∀ i t, dualLogDerivative (z i t) = eval₂ t (small i) +
      dualAdjoint (dualBaseHom (z i t)) (eval₂ t (rational i)) + extra i t) :
    ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P) -
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V := by
  have hW (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ V.restrictScalars ℚ ⊔ F.realification.layer d ↔
        x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  intro i
  apply (eval₂_mem_iff_coefficients V _).mp
  intro t
  let D := eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P)
  let k := basisGradeProjection (b.baseChange ℝ) w 1 D
  have hlow := F.real_polynomial_derivative_lower_layers b w hlayers V K hj P hK hlower i t
  have hzU : dualBaseLinear (z i t).coord ∈ U := by rw [hbase]; exact hU t
  have hzlow : dualTangentLinear (z i t).coord - k ∈ V.restrictScalars ℚ ⊔ F.realification.layer j := by
    rw [htangent]
    exact (hW j _).mpr hlow.1
  have hzbracket : ⁅dualBaseLinear (z i t).coord, k⁆ ∈
      V.restrictScalars ℚ ⊔ F.realification.layer (j + 1) := by
    rw [hbase]
    exact (hW (j + 1) _).mpr (hbracket t k hlow.2)
  have hr : eval₂ t (rational i) ∈ V.restrictScalars ℚ ⊔ F.realification.layer j :=
    (hW j _).mpr ((eval₂_mem_iff_coefficients _ _).mpr (hrational i) t)
  have he := (hW (j + 1) _).mpr (hextra i t)
  have hcurrent := F.realification.current_layer_derivative_system hs U (V.restrictScalars ℚ)
    hUV j (z i t) hzU k (eval₂ t (small i)) (eval₂ t (rational i)) (extra i t)
    hzlow hzbracket hr he (hsystem i t)
  have hproj := F.realGradeProjection_mem_of_mem_sup_next b w hlayers V hV j _
    ((hW (j + 1) _).mp hcurrent)
  have hkzero : basisGradeProjection (b.baseChange ℝ) w j k = 0 :=
    basisGradeProjection_other (b.baseChange ℝ) w (by omega : j ≠ 1) D
  rw [htangent, map_sub, map_sub, map_add, hkzero, sub_zero] at hproj
  simp only [map_sub, pderiv_map, eval₂_map]
  convert hproj using 1
  change _ = (basisGradeProjection (b.baseChange ℝ) w j D -
    (basisGradeProjection (b.baseChange ℝ) w j (eval₂ t (small i)) +
      basisGradeProjection (b.baseChange ℝ) w j (eval₂ t (rational i))))
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficientSubmodule_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P Q : VectorPolynomial σ ℚ L)
    (hP : P ∈ coefficientLieSubalgebra U) (hQ : Q ∈ coefficientSubmodule V) :
    ⁅P, Q⁆ ∈ coefficientSubmodule V := by
  classical
  rw [← sum_monomial_coefficients P, ← sum_monomial_coefficients Q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients P).support (coefficients Q).support
    (fun α => monomial (R := ℚ) α (coefficients P α))
    (fun β => monomial (R := ℚ) β (coefficients Q β))]
  apply (coefficientSubmodule V).sum_mem
  intro α _
  apply (coefficientSubmodule V).sum_mem
  intro β _
  rw [lie_monomial]
  exact monomial_mem_coefficientSubmodule V _ (hUV _ (hP α) _ (hQ β))

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem formalLogDerivative_mem_coefficientSubmodule
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (i : σ) (P : PolynomialGroup σ hnil)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hPV : ∀ α, coefficients P.coord α ∈ V) :
    ∀ α, coefficients (formalLogDerivative i P) α ∈ V :=
  formalLogDerivative_mem_of_invariant (coefficientLieSubalgebra U) (coefficientSubmodule V)
    (fun A hA B hB => coefficientSubmodule_invariant U V hUV A B hA hB)
    i P hPU (pderiv_mem_submodule V P.coord hPV i)

theorem dualAdjoint_mem_coefficientSubmodule
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P : PolynomialGroup σ hnil) (Q : VectorPolynomial σ ℚ L)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hQV : ∀ α, coefficients Q α ∈ V) :
    ∀ α, coefficients (dualAdjoint P Q) α ∈ V :=
  dualAdjoint_mem_of_invariant (coefficientLieSubalgebra U) (coefficientSubmodule V)
    (fun A hA B hB => coefficientSubmodule_invariant U V hUV A B hA hB) P hPU Q hQV

theorem polynomial_derivative_removal_preserves_coefficients
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (i : σ) (A B : PolynomialGroup σ hnil) (small rational : VectorPolynomial σ ℚ L)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hAV : ∀ α, coefficients A.coord α ∈ V) (hBV : ∀ α, coefficients B.coord α ∈ V)
    (hsmall : ∀ α, coefficients small α ∈ V)
    (hrational : ∀ α, coefficients rational α ∈ V) :
    (∀ α, coefficients (dualAdjoint A⁻¹ (small - formalLogDerivative i A)) α ∈ V) ∧
      ∀ α, coefficients (dualAdjoint B rational - formalLogDerivative i B) α ∈ V := by
  have hYA := formalLogDerivative_mem_coefficientSubmodule U V hUV i A hAU hAV
  have hYB := formalLogDerivative_mem_coefficientSubmodule U V hUV i B hBU hBV
  have hAinv : ∀ α, coefficients A⁻¹.coord α ∈ U := by
    intro α
    change coefficients (-A.coord) α ∈ U
    rw [map_neg, Finsupp.neg_apply]
    exact U.neg_mem (hAU α)
  constructor
  · exact dualAdjoint_mem_coefficientSubmodule U V hUV A⁻¹ _ hAinv
      ((coefficientSubmodule V).sub_mem hsmall hYA)
  · exact (coefficientSubmodule V).sub_mem
      (dualAdjoint_mem_coefficientSubmodule U V hUV B rational hBU hrational) hYB

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
open scoped Matrix

theorem controlled_weighted_quotient_coordinates
    {ι κ δ V W : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : Basis ι ℝ V) (f : Basis κ ℝ W) (q : V →ₗ[ℝ] W)
    (c : ι → δ) (r : κ → δ) (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ)
    (hD : LinearMap.toMatrix e f q = D.map (Rat.castHom ℝ)) (hDS : D * S = 1)
    (hDb : ∀ i j, r i ≠ c j → D i j = 0) (hSb : ∀ i j, c i ≠ r j → S i j = 0)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (hDh : ∀ i j, ((D i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a) ∧
      ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hSh : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ (a + 4)) ∧ l ∣ m ∧
      (∀ x : V, e.equivFun x ∈ realDenominatorGrid l →
        f.equivFun (q x) ∈ realDenominatorGrid m) ∧
      (∀ y : κ → ℝ, y ∈ realDenominatorGrid l →
        e.equivFun (rationalCoordinateSection e S y) ∈ realDenominatorGrid m) ∧
      (∀ y : κ → ℝ, q (rationalCoordinateSection e S y) = f.equivFun.symm y) ∧
      ∀ (scale : δ → ℝ), (∀ d, 0 < scale d) → ∀ M : ℝ, 0 ≤ M →
        (∀ x : V, (∀ j, |e.equivFun x j| ≤ M / scale (c j)) →
          ∀ i, |f.equivFun (q x) i| ≤ Real.exp ((p + 2) ^ (a + 4)) * M / scale (r i)) ∧
        (∀ y : κ → ℝ, (∀ j, |y j| ≤ M / scale (r j)) →
          ∀ i, |e.equivFun (rationalCoordinateSection e S y) i| ≤
            Real.exp ((p + 2) ^ (a + 4)) * M / scale (c i)) := by
  let m := matrixDenominator D * matrixDenominator S * l
  have hm : 0 < m := Nat.mul_pos (Nat.mul_pos (matrixDenominator_pos D) (matrixDenominator_pos S)) hl
  have hmD : matrixDenominator D * l ∣ m := ⟨matrixDenominator S, by dsimp [m]; ring⟩
  have hmS : matrixDenominator S * l ∣ m := ⟨matrixDenominator D, by dsimp [m]; ring⟩
  refine ⟨m, hm, matrix_pair_denominator_le_exp_power D S l hp a ha hι hκ
    (fun i j => (hDh i j).2) (fun i j => (hSh i j).2) hlp,
    ⟨matrixDenominator D * matrixDenominator S, by dsimp [m]; ring⟩, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact realDenominatorGrid_subset_of_dvd (Nat.mul_pos (matrixDenominator_pos D) hl) hmD
      (rational_coordinate_map_grid e f q D hD l x hx)
  · intro y hy
    exact realDenominatorGrid_subset_of_dvd (Nat.mul_pos (matrixDenominator_pos S) hl) hmS
      (rationalCoordinateSection_grid e S l y hy)
  · exact rationalCoordinateSection_rightInverse e S f q D hD hDS
  · intro scale hscale M hM
    have hbudget : Real.exp ((p + 2) ^ (a + 2)) ≤ Real.exp ((p + 2) ^ (a + 4)) :=
      Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by omega))
    constructor
    · intro x hx i
      have h := rational_coordinate_map_weighted_exp e f q D hD c r hDb hp hι a ha
        (fun i j => (hDh i j).1) scale hscale hM x hx i
      exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget hM) (hscale _).le)
    · intro y hy i
      have h := rationalCoordinateSection_weighted e S c r hSb hp hκ a ha
        (fun i j => (hSh i j).1) scale hscale hM y hy i
      exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget hM) (hscale _).le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintChartBasis
namespace OAI

section

namespace Erdos3

theorem exists_bounded_rational_projection_lift
    {E F α β : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype α] {k : ℕ}
    (b : Module.Basis (Fin k) ℝ E) (P : E →ₗ[ℝ] (α → ℝ))
    (hP : Function.Injective P) (g : E →ₗ[ℝ] (β → ℝ))
    (e : α → β) (hhor : ∀ v i, g v (e i) = P v i)
    (W : (β → ℝ) →ₗ[ℝ] F) (C : ℝ)
    (hbound : ∀ v, ‖W (g v)‖ ≤ C * ‖P v‖)
    (B : Matrix β (Fin k) ℝ) (hB : ∀ i j, B i j = g (b j) i)
    (p : Fin k → α) (hp : (B.submatrix (e ∘ p) id).det ≠ 0)
    (Q : Matrix β (Fin k) ℚ)
    (hQ : Q.map (Rat.castHom ℝ) = B * (B.submatrix (e ∘ p) id)⁻¹)
    (hQid : Q.submatrix (e ∘ p) id = 1) :
    let QH := Q.submatrix e id
    ∃ R : LinearMap.range P →ₗ[ℝ] (β → ℝ),
      (∀ x i, R x (e i) = x.val i) ∧
      (∀ x, ‖W (R x)‖ ≤ C * ‖x‖) ∧
      (∀ v, R ⟨P v, v, rfl⟩ = g v) ∧
      LinearMap.range P = Submodule.span ℝ (Set.range (QH.map (Rat.castHom ℝ)).col) ∧
      LinearIndependent ℝ (QH.map (Rat.castHom ℝ)).col ∧
      LinearIndependent ℚ QH.col ∧
      (∀ j, ∃ x : LinearMap.range P,
        x.val = (QH.map (Rat.castHom ℝ)).col j ∧ R x = (Q.map (Rat.castHom ℝ)).col j) := by
  let J := (LinearEquiv.ofInjective P hP).symm.toLinearMap
  have hJ (x : LinearMap.range P) : P (J x) = x.val :=
    congrArg Subtype.val ((LinearEquiv.ofInjective P hP).apply_symm_apply x)
  let R := g.comp J
  let H := B.submatrix e id
  let QH := Q.submatrix e id
  have hHcol : H.col = fun j => P (b j) := by
    funext j i
    exact (hB (e i) j).trans (hhor (b j) i)
  have hQH : QH.map (Rat.castHom ℝ) = H * (H.submatrix p id)⁻¹ := by
    ext i j
    exact congrArg (fun M : Matrix β (Fin k) ℝ => M (e i) j) hQ
  have hQHid : QH.submatrix p id = 1 := hQid
  have hrealid : (QH.map (Rat.castHom ℝ)).submatrix p id = 1 := by
    rw [hQH]
    exact row_normalization_submatrix H p hp
  refine ⟨R, ?_, ?_, ?_, ?_, independent_columns_of_identity_minor _ p hrealid,
    independent_columns_of_identity_minor QH p hQHid, ?_⟩
  · intro x i
    exact (hhor (J x) i).trans (congrFun (hJ x) i)
  · intro x
    have h := hbound (J x)
    rw [hJ x] at h
    exact h
  · intro v
    have h : J ⟨P v, v, rfl⟩ = v := hP (hJ ⟨P v, v, rfl⟩)
    change g (J ⟨P v, v, rfl⟩) = g v
    rw [h]
  · change LinearMap.range P = Submodule.span ℝ (Set.range (QH.map (Rat.castHom ℝ)).col)
    rw [hQH, row_normalization_col_span H p hp, hHcol]
    exact basis_projection_range_eq_span b P
  · intro j
    obtain ⟨v, hv⟩ := exists_normalized_basis_vector b g B hB
      (B.submatrix (e ∘ p) id)⁻¹ j
    have hv' : g v = (Q.map (Rat.castHom ℝ)).col j := by
      rw [hQ]
      exact hv
    let x : LinearMap.range P := ⟨P v, v, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · funext i
      exact (hhor v i).symm.trans (congrFun hv' (e i))
    · have hx : J x = v := hP (hJ x)
      change g (J x) = _
      rw [hx]
      exact hv'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeHorizontalLifts
namespace OAI

section

namespace Erdos3

theorem assemble_rational_horizontal_lift
    {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype σ]
    {m a k : ℕ} (b : Module.Basis (Fin k) ℝ E)
    (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m))
    (P : E →ₗ[ℝ] (Fin a → ℝ)) (hPinj : Function.Injective P) (ha : a ≤ m)
    (hP : ∀ v i, P v i = f v (Sum.inr (Fin.castLE ha i)))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hAhor : ∀ x i, A x (Fin.castLE ha i) = x (Fin.castLE ha i))
    (scale : Fin m → ℝ) (hs0 : ∀ j, scale j ≠ 0)
    (hscalehor : ∀ i : Fin a, scale (Fin.castLE ha i) = 1)
    (B : Matrix (Fin m) (Fin k) ℝ)
    (hrep : ∀ j, f (b j) = euclideanVerticalMap scale hs0 A (B.col j))
    (p : Fin k → Fin a) (hp : (B.submatrix (Fin.castLE ha ∘ p) id).det ≠ 0)
    (Q : Matrix (Fin m) (Fin k) ℚ)
    (hQ : Q.map (Rat.castHom ℝ) = B * (B.submatrix (Fin.castLE ha ∘ p) id)⁻¹)
    (hQid : Q.submatrix (Fin.castLE ha ∘ p) id = 1)
    (D H : ℕ) (hD : 0 < D) (hDH : D ≤ H)
    (hgrid : ∀ j, Q.col j ∈ denominatorGrid D)
    (hheight : ∀ i j, RationalHeightLE (Q (Fin.castLE ha i) j) H)
    (N : ℝ) (hnorm : ∀ v, ‖v‖ ≤ N * ‖P v‖) :
    ∃ lifts : RationalHorizontalLift k P ha A scale N H,
      ∀ v, euclideanVerticalMap scale hs0 A (lifts.rationalLift ⟨P v, v, rfl⟩) = f v := by
  let W := euclideanVerticalMap (σ := σ) scale hs0 A
  obtain ⟨g, hgb, hgf⟩ := exists_basis_linear_lift b f.toLinearMap W B.col hrep
  have hW (v) : W (g v) = f v := LinearMap.congr_fun hgf v
  have hhor (v) (i : Fin a) : g v (Fin.castLE ha i) = P v i := by
    calc
      _ = A (g v) (Fin.castLE ha i) := (hAhor (g v) i).symm
      _ = W (g v) (Sum.inr (Fin.castLE ha i)) := by
        change _ = scale (Fin.castLE ha i) * A (g v) (Fin.castLE ha i)
        rw [hscalehor, one_mul]
      _ = f v (Sum.inr (Fin.castLE ha i)) := congrArg (fun z => z (Sum.inr (Fin.castLE ha i))) (hW v)
      _ = P v i := (hP v i).symm
  have hbound (v) : ‖W (g v)‖ ≤ N * ‖P v‖ := by
    rw [hW, f.norm_map]
    exact hnorm v
  have hB (i j) : B i j = g (b j) i := (congrFun (hgb j) i).symm
  obtain ⟨R, hRhor, hRbound, hRsection, hspan, hLIreal, hLIrat, hRbasis⟩ :=
    exists_bounded_rational_projection_lift b P hPinj g (Fin.castLE ha) hhor W N hbound
      B hB p hp Q hQ hQid
  refine ⟨{
    denominator := D
    denominator_pos := hD
    denominator_le := hDH
    basisMatrix := Q.submatrix (Fin.castLE ha) id
    basis_height := hheight
    independent_rat := hLIrat
    independent_real := hLIreal
    span_eq := hspan
    rationalLift := R
    geometricLift := A.toLinearMap.comp R
    factorization := rfl
    rational_horizontal := hRhor
    geometric_horizontal := ?_
    norm_scaled := ?_
    rational_on_basis := ?_
  }, ?_⟩
  · intro x i
    change A (R x) (Fin.castLE ha i) = x.val i
    rw [hAhor, hRhor]
  · intro x
    have h := hRbound x
    change ‖euclideanVerticalMap (σ := σ) scale hs0 A (R x)‖ ≤ N * ‖x‖ at h
    rw [euclideanVerticalMap_norm_eq] at h
    exact h
  · intro j
    obtain ⟨x, hx, hrx⟩ := hRbasis j
    refine ⟨x, hx, ?_⟩
    rw [hrx]
    exact (real_cast_mem_denominatorGrid_iff D (Q.col j)).mpr (hgrid j)
  · intro v
    change W (R ⟨P v, v, rfl⟩) = f v
    rw [hRsection]
    exact hW v

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_lifts
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * (C * (l : ℝ) ^ k)
    let H := Nat.ceil (C * (l : ℝ) ^ k)
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      ∃ lifts : RationalHorizontalLift k P ha A scale N H,
        ∀ v : V, euclideanVerticalMap scale hs0 A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * (C * (l : ℝ) ^ k)
  let H := Nat.ceil (C * (l : ℝ) ^ k)
  change ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
    ∃ lifts : RationalHorizontalLift k P ha A scale N H,
      ∀ v : V, euclideanVerticalMap scale hs0 A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val
  intro hupper
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, p, _, hrep, hp, D, hD, hDH, Q, hgrid, hQ, hQid, hheight⟩ :=
    euclideanDerivative_rational_lift_matrix_data T hT scale hscale Y A hA hdiag
      l hl R a ha Tmin C hscalehor hblock hfar hlarge hupper
  let bR := b.ofZLatticeBasis ℝ L
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  have hbrep (j) : f (bR j) = euclideanVerticalMap scale hs0 A (B.col j) := by
    simp only [bR, Module.Basis.ofZLatticeBasis_apply]
    exact hrep j
  have hP : ∀ v i, P v i = f v (Sum.inr (Fin.castLE ha i)) := fun _ _ => rfl
  have hPinj : Function.Injective P := euclideanDerivative_horizontal_injective
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hscalehor hblock hfar hlarge hupper
  have hAhor (x) (i : Fin a) : A x (Fin.castLE ha i) = x (Fin.castLE ha i) := by
    have h := euclideanVerticalMap_horizontal (σ := σ) scale hs0 hscalehor A hA hblock
      x (Fin.castLE ha i) i.isLt
    rw [euclideanVerticalMap_apply_inr, hscalehor (Fin.castLE ha i) i.isLt, one_mul] at h
    exact h
  have hn : ∀ v : V, ‖v‖ ≤ N * ‖P v‖ := euclideanDerivative_horizontal_norm_bound
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hscalehor hblock hfar hlarge hupper
  exact assemble_rational_horizontal_lift (E := V) (σ := σ) (m := m) (a := a) (k := k)
    bR f P hPinj ha hP A hAhor scale hs0 (fun i => hscalehor _ i.isLt)
    B hbrep p hp Q hQ hQid D H hD hDH hgrid hheight N hn

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformDerivativeLatticeExtraction
namespace OAI

section

namespace Erdos3

theorem derivative_covolume_budget_le_exp (d n : ℕ) (R δ p : ℝ)
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hR0 : 0 ≤ R) (hR : R ≤ Real.exp p) (hδ : 0 < δ)
    (hδinv : δ⁻¹ ≤ Real.exp p) :
    (((d : ℝ) + 2) * ((n : ℝ) * R)) ^ d / δ ≤ Real.exp (3 * p ^ 2 + 2 * p) := by
  have hd2 : (d : ℝ) + 2 ≤ Real.exp (p + 1) := by
    exact (by linarith : (d : ℝ) + 2 ≤ (p + 1) + 1).trans (Real.add_one_le_exp (p + 1))
  have hnexp : (n : ℝ) ≤ Real.exp p :=
    hn.trans ((show p ≤ p + 1 by linarith).trans (Real.add_one_le_exp p))
  have hbase : ((d : ℝ) + 2) * ((n : ℝ) * R) ≤ Real.exp (3 * p + 1) := by
    calc
      _ ≤ Real.exp (p + 1) * (Real.exp p * Real.exp p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp (3 * p + 1) ^ d * Real.exp p := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase d) hδinv
        (inv_nonneg.mpr hδ.le) (by positivity)
    _ = Real.exp ((d : ℝ) * (3 * p + 1) + p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (3 * p ^ 2 + 2 * p) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hd (by positivity : 0 ≤ 3 * p + 1)]

theorem derivative_output_budgets_le_exp (n k l : ℕ) (B p : ℝ)
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp (4 * p ^ 2 + 2 * p)) :
    B ≤ Real.exp ((p + 2) ^ 3) ∧
      (n : ℝ) * k * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (l : ℝ) * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (Nat.ceil B : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  have hne : (n : ℝ) ≤ Real.exp p :=
    hn.trans ((show p ≤ p + 1 by linarith).trans (Real.add_one_le_exp p))
  have hke : (k : ℝ) ≤ Real.exp p :=
    hk.trans ((show p ≤ p + 1 by linarith).trans (Real.add_one_le_exp p))
  have hpoly := derivative_output_exponent_le hp
  have h0 : 4 * p ^ 2 + 2 * p ≤ (p + 2) ^ 3 := by linarith
  have h1 : 4 * p ^ 2 + 3 * p ≤ (p + 2) ^ 3 := by linarith
  have h2 : 4 * p ^ 2 + 4 * p ≤ (p + 2) ^ 3 := by linarith
  have h3 : 4 * p ^ 2 + 2 * p + 1 ≤ (p + 2) ^ 3 := by linarith
  refine ⟨hB.trans (Real.exp_le_exp.mpr h0), ?_, ?_, ?_⟩
  · calc
      _ ≤ (n : ℝ) * k * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ ≤ Real.exp p * Real.exp p * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ = Real.exp (4 * p ^ 2 + 4 * p) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h2
  · calc
      _ ≤ (l : ℝ) * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ ≤ Real.exp p * Real.exp (4 * p ^ 2 + 2 * p) := by gcongr
      _ = Real.exp (4 * p ^ 2 + 3 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h1
  · calc
      (Nat.ceil B : ℝ) ≤ Nat.ceil (Real.exp (4 * p ^ 2 + 2 * p)) := by
        exact_mod_cast Nat.ceil_mono hB
      _ ≤ Real.exp (4 * p ^ 2 + 2 * p + 1) := ceil_exp_le_exp_add_one (by positivity)
      _ ≤ _ := Real.exp_le_exp.mpr h3

end Erdos3

end

section

namespace Erdos3

theorem lattice_subspace_budgets_le_exp
    {σ : Type*} [Fintype σ] {m : ℕ}
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ Fin m))) (V : Submodule ℝ Z)
    (l : ℕ) (R δ p : ℝ) (hp : 0 ≤ p)
    (hdim : ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hR0 : 0 ≤ R) (hR : R ≤ Real.exp p)
    (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp p) :
    let n := Fintype.card σ + Fintype.card (Fin m)
    let d := Module.finrank ℝ Z
    let k := Module.finrank ℝ V
    let C := (((d : ℝ) + 2) * ((n : ℝ) * R)) ^ d / δ
    let B := C * (l : ℝ) ^ k
    C * (l : ℝ) ^ m ≤ Real.exp ((p + 2) ^ 3) ∧
      B ≤ Real.exp ((p + 2) ^ 3) ∧
      (n : ℝ) * k * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (l : ℝ) * B ≤ Real.exp ((p + 2) ^ 3) ∧
      (Nat.ceil B : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  let n := Fintype.card σ + Fintype.card (Fin m)
  let d := Module.finrank ℝ Z
  let k := Module.finrank ℝ V
  let C := (((d : ℝ) + 2) * ((n : ℝ) * R)) ^ d / δ
  let B := C * (l : ℝ) ^ k
  have hdn : d ≤ n := by
    simpa only [finrank_euclideanSpace, Fintype.card_sum] using Z.finrank_le
  have hdp : (d : ℝ) ≤ p := (Nat.cast_le.mpr hdn).trans hdim
  have hkp : (k : ℝ) ≤ p := (Nat.cast_le.mpr V.finrank_le).trans hdp
  have hmp : (m : ℝ) ≤ p := by
    have hmn : m ≤ n := by simp [n]
    exact (Nat.cast_le.mpr hmn).trans hdim
  have hC : C ≤ Real.exp (3 * p ^ 2 + 2 * p) :=
    derivative_covolume_budget_le_exp d n R δ p hp hdp hdim hR0 hR hδ hδinv
  have hB : B ≤ Real.exp (4 * p ^ 2 + 2 * p) :=
    derivative_extended_budget_le_exp k l C p hp hkp hl hC
  have hthreshold : C * (l : ℝ) ^ m ≤ Real.exp ((p + 2) ^ 3) := by
    apply (derivative_extended_budget_le_exp m l C p hp hmp hl hC).trans
    apply Real.exp_le_exp.mpr
    have he := derivative_output_exponent_le hp
    linarith
  exact ⟨hthreshold, derivative_output_budgets_le_exp n k l B p hp hdim hkp hl hB⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedCoordinateExtraction
namespace OAI

section

namespace Erdos3

theorem coordinateDerivativeSystem_of_lifts
    {σ E : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup E] [Module ℝ E]
    {m a k H : ℕ} (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (scale : Fin m → ℝ)
    (P : E →ₗ[ℝ] (Fin a → ℝ)) (ha : a ≤ m) (N bound : ℝ)
    (lifts : RationalHorizontalLift k P ha A scale N H)
    (hN : N ≤ bound) (hH : (H : ℝ) ≤ bound)
    (D : ℕ) (hD : 0 < D) (hDb : (D : ℝ) ≤ bound)
    (hderiv : ∀ i, ∃ (s r : Fin m → ℝ) (q : LinearMap.range P),
      Y (Pi.basisFun ℝ σ i) = s + A r + lifts.geometricLift q ∧
      r ∈ realDenominatorGrid D ∧
      ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ bound / T i) :
    Nonempty (CoordinateDerivativeSystem ha T Y A scale bound) := by
  choose s r q heq hgrid hsmall using hderiv
  exact ⟨{
    K := LinearMap.range P
    k := k
    heightBound := H
    height_le := hH
    basisMatrix := lifts.basisMatrix
    basis_height := lifts.basis_height
    independent_rat := lifts.independent_rat
    independent_real := lifts.independent_real
    span_eq := lifts.span_eq
    rationalLift := lifts.rationalLift
    geometricLift := lifts.geometricLift
    factorization := lifts.factorization
    rational_horizontal := lifts.rational_horizontal
    geometric_horizontal := lifts.geometric_horizontal
    norm_scaled := fun x => (lifts.norm_scaled x).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg x))
    liftDenominator := lifts.denominator
    liftDenominator_pos := lifts.denominator_pos
    liftDenominator_le := (Nat.cast_le.mpr lifts.denominator_le).trans hH
    rational_on_basis := lifts.rational_on_basis
    derivativeDenominator := D
    derivativeDenominator_pos := hD
    derivativeDenominator_le := hDb
    slow := s
    rational := r
    horizontal := q
    derivative_eq := heq
    derivative_grid := hgrid
    slow_bound := hsmall
  }⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FullFastHorizontalNormalization
namespace OAI

section

namespace Erdos3

theorem exists_controlled_derivative_absorption {H E V ι κ ν τ σ : Type*}
    [AddCommGroup H] [Module ℝ H] [AddCommGroup E] [Module ℝ E]
    [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] [Fintype κ] [Fintype ν]
    (e : H ≃ₗ[ℝ] (ι → ℝ)) (U K : Submodule ℝ H)
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U.map e.toLinearMap)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K.map e.toLinearMap)
    (b : ν → K) (hb : ∀ j, e (b j).val = (B.map (Rat.castHom ℝ)).col j)
    (P : E →ₗ[ℝ] H) (f : E →ₗ[ℝ] E) (hf : P.comp f = P)
    (S R : K →ₗ[ℝ] E) (hSR : S = f.comp R)
    (hS : P.comp S = K.subtype) (hR : P.comp R = K.subtype)
    (c : E →ₗ[ℝ] (τ → ℝ)) (N : E →ₗ[ℝ] V)
    (n rden : ℕ) (hRgrid : ∀ j, c (R (b j)) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) J) (hB : ∀ i j, RationalHeightLE (B i j) J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (M C : ℝ) (hC : 0 ≤ C) (hSbound : ∀ x, ‖N (S x)‖ ≤ C * ‖e x.val‖)
    (y small rational : σ → E) (k : σ → K)
    (hsystem : ∀ i, y i = small i + f (rational i) + S (k i))
    (hy : ∀ i, P (y i) ∈ U)
    (hsmall : ∀ i, ‖e (P (small i))‖ ≤ Real.exp p / T i)
    (hNsmall : ∀ i, ‖N (small i)‖ ≤ M / T i)
    (hrational : ∀ i, e (P (rational i)) ∈ realDenominatorGrid l)
    (hrgrid : ∀ i, c (rational i) ∈ realDenominatorGrid rden) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ ks kr : σ → K, ∀ i,
        P (small i - S (ks i)) ∈ U ∧
        P (rational i - R (kr i)) ∈ U ∧
        (k i + ks i + kr i).val ∈ U ∧
        y i = (small i - S (ks i)) + f (rational i - R (kr i)) + S (k i + ks i + kr i) ∧
        ‖e (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i ∧
        ‖N (small i - S (ks i))‖ ≤ (M + C * Real.exp ((p + 2) ^ 19) * Real.exp p) / T i ∧
        ‖e (P (small i - S (ks i)))‖ ≤ (1 + Real.exp ((p + 2) ^ 19)) * Real.exp p / T i ∧
        c (rational i - R (kr i)) ∈ realDenominatorGrid (rden * (n * m)) := by
  obtain ⟨m, hm, hmp, split, hsplit, hnorm, hgrid⟩ :=
    exists_controlled_kernel_split_equiv e U K A B hAspan hBspan b hb (c.comp R) n hRgrid
      hJ hl hA hB hp hι hcols hJp hlp
  let ks : σ → K := fun i => split (P (small i))
  let kr : σ → K := fun i => split (P (rational i))
  have hks (i : σ) : ‖e (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i := by
    calc
      _ ≤ Real.exp ((p + 2) ^ 19) * ‖e (P (small i))‖ := hnorm _
      _ ≤ Real.exp ((p + 2) ^ 19) * (Real.exp p / T i) :=
        mul_le_mul_of_nonneg_left (hsmall i) (Real.exp_nonneg _)
      _ = _ := by ring
  refine ⟨m, hm, hmp, ks, kr, fun i => ?_⟩
  have hproj : P (y i) = P (small i) + P (rational i) + (k i).val := by
    rw [hsystem i, map_add, map_add,
      show P (f (rational i)) = P (rational i) from DFunLike.congr_fun hf _,
      show P (S (k i)) = (k i).val from DFunLike.congr_fun hS _]
  have hparts := horizontal_parts_separation_equiv e U K A B hAspan hBspan
    hJ hl hA hB hp hι hcols hJp hlp T hT i
    (P (y i)) (P (small i)) (P (rational i)) (k i) hproj (hy i) (hsmall i) (hrational i)
  have habsorb := horizontal_absorption_with_split U K P f hf S R hSR hS hR split hsplit
    (y i) (small i) (rational i) (k i) (hsystem i) (hy i) hparts.1 hparts.2
  refine ⟨habsorb.1, habsorb.2.1, habsorb.2.2.1, habsorb.2.2.2, hks i, ?_, ?_, ?_⟩
  · calc
      _ ≤ ‖N (small i)‖ + ‖N (S (ks i))‖ := by rw [map_sub]; exact norm_sub_le _ _
      _ ≤ M / T i + C * (Real.exp ((p + 2) ^ 19) * Real.exp p / T i) :=
        add_le_add (hNsmall i) ((hSbound _).trans (mul_le_mul_of_nonneg_left (hks i) hC))
      _ = _ := by ring
  · rw [map_sub, map_sub, show P (S (ks i)) = (ks i).val from DFunLike.congr_fun hS _]
    calc
      _ ≤ ‖e (P (small i))‖ + ‖e (ks i).val‖ := norm_sub_le _ _
      _ ≤ Real.exp p / T i + Real.exp ((p + 2) ^ 19) * Real.exp p / T i :=
        add_le_add (hsmall i) (hks i)
      _ = _ := by ring
  · rw [map_sub]
    exact realDenominatorGrid_sub_product rden (n * m) _ _ (hrgrid i) (hgrid _ (hrational i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexedFastCoefficientSection
namespace OAI

section

namespace Erdos3

open Module

noncomputable def reindexCoordinateSection {ν E : Type*} [AddCommGroup E] [Module ℝ E]
    (R : (ν → ℝ) →ₗ[ℝ] E) (e : Equiv.Perm ν) : (ν → ℝ) →ₗ[ℝ] E where
  toFun y := R (fun i => y (e.symm i))
  map_add' _ _ := R.map_add _ _
  map_smul' r _ := R.map_smul r _

theorem reindexCoordinateSection_right_inverse {ν E Q : Type*} [Fintype ν]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup Q] [Module ℝ Q]
    (P : E →ₗ[ℝ] Q) (b : Basis ν ℝ Q) (R : (ν → ℝ) →ₗ[ℝ] E)
    (hR : ∀ y, P (R y) = b.equivFun.symm y) (e : Equiv.Perm ν) (y : ν → ℝ) :
    P (reindexCoordinateSection R e y) = (b.reindex e.symm).equivFun.symm y := by
  apply (b.reindex e.symm).equivFun.injective
  rw [LinearEquiv.apply_symm_apply, basis_reindex_equivFun]
  change (fun i => b.equivFun (P (R (fun j => y (e.symm j)))) (e i)) = y
  rw [hR, LinearEquiv.apply_symm_apply]
  funext i
  exact congrArg y (e.symm_apply_apply i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialLiftMatching
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem real_sub_grade_mem_sup_next (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : x ∈ V ⊔ (F.realLayer j).toSubmodule) :
    x - basisGradeProjection (b.baseChange ℝ) w j x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have ht : basisBelowProjection (b.baseChange ℝ) w j z = 0 := by
    have hz' : z - 0 ∈ F.realification.layer j := by rw [sub_zero]; exact hz
    have h := (F.realGradeTruncation_eq_iff b w hlayers j z 0).mpr hz'
    simpa only [map_zero] using h
  have hhigh := F.sub_realGradeTruncation_mem b w hlayers (j + 1) z
  rw [basisBelowProjection_succ, ht, zero_add] at hhigh
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem
    (Submodule.mem_sup_left (V.sub_mem hv (hV j v hv))) (Submodule.mem_sup_right hhigh)
  simpa only [map_add, add_sub_add_comm] using h

include hlayers in
theorem real_matching_grade_remainder (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ) (x y : ℝ ⊗[ℚ] L)
    (hx : x ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hmatch : basisGradeProjection (b.baseChange ℝ) w j x - y ∈ V) :
    x - y ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem
    (F.real_sub_grade_mem_sup_next b w hlayers V hV j x hx) (Submodule.mem_sup_left hmatch)
  simpa only [sub_add_sub_cancel] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelDirectionBudget
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem polynomial_kernel_direction_budget (n k H l : ℕ) {p M : ℝ}
    (hp : 0 ≤ p) (hM : 0 ≤ M) (hH : 1 ≤ H)
    (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) (hMp : M ≤ Real.exp p) :
    ((n : ℝ) + 1) * ((rationalSolveHeight k H : ℝ) + 1) * M ≤ Real.exp ((p + 2) ^ 8) ∧
      ((rationalSolveHeight k H ^ (k * n) * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
  let B := (p + 2) ^ 5
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := one_le_pow₀ (by linarith : (1 : ℝ) ≤ p + 2)
  have hpB : p ≤ B := le_power_budget hp (by decide : 1 ≤ 5)
  have hq : 0 ≤ p + B := add_nonneg hp hB
  have hheight : (rationalSolveHeight k H : ℝ) ≤ Real.exp (p + B) :=
    (rationalSolveHeight_le_budget k H hp hk hHp).trans
      (Real.exp_le_exp.mpr (by dsimp [B]; linarith))
  have hfactor := current_layer_coordinate_factor_bound hq n (rationalSolveHeight k H)
    (hn.trans (le_add_of_nonneg_right hB)) hheight
  have h8 : (8 : ℝ) ≤ (p + 2) ^ 3 := by
    calc
      (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (p + 2) ^ 3 :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ p + 2) 3
  have hlog : 2 * (p + B) + 1 + p ≤ (p + 2) ^ 8 := by
    calc
      _ ≤ 6 * B := by linarith
      _ ≤ (p + 2) ^ 3 * B := mul_le_mul_of_nonneg_right (by linarith) hB
      _ = _ := by dsimp [B]; ring
  constructor
  · calc
      _ ≤ Real.exp (2 * (p + B) + 1) * Real.exp p :=
        mul_le_mul hfactor hMp hM (Real.exp_nonneg _)
      _ = Real.exp (2 * (p + B) + 1 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  · have hHpow : (1 : ℕ) ≤ H ^ (n * k) := one_le_pow₀ hH
    have hnat := Nat.mul_le_mul_right (rationalSolveHeight k H ^ (k * n)) hHpow
    simp only [one_mul] at hnat
    have hK : ((rationalSolveHeight k H ^ (k * n) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 8) :=
      (Nat.cast_le.mpr hnat).trans (rational_grid_height_le_exp n k H hp hn hk hHp)
    have hd := grid_allowance_mul_le_exp hp hl hK
    simpa only [Nat.mul_comm] using hd

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.ControlledBracketToCurrentLayer
namespace OAI

section

namespace Erdos3

theorem bracket_transition_budget_bounds {p : ℝ} (hp : 0 ≤ p)
    (k m d : ℕ) (hk : (k : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hd : (d : ℝ) ≤ Real.exp ((p + 2) ^ 9)) :
    Real.exp p ≤ Real.exp (bracketTransitionBudget p) ∧
      Real.exp p + (k : ℝ) * Real.exp p * Real.exp ((p + 2) ^ 8) ≤
        Real.exp (bracketTransitionBudget p) ∧
      ((m * (m * d) : ℕ) : ℝ) ≤ Real.exp (bracketTransitionBudget p) := by
  have h8 : 0 ≤ (p + 2) ^ 8 := by positivity
  have h9 : 0 ≤ (p + 2) ^ 9 := by positivity
  have hpE : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hterm : (k : ℝ) * Real.exp p * Real.exp ((p + 2) ^ 8) ≤
      Real.exp (2 * p + (p + 2) ^ 8) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp ((p + 2) ^ 8) := by
        gcongr
        exact hk.trans hpE
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  refine ⟨Real.exp_le_exp.mpr (by unfold bracketTransitionBudget; linarith), ?_, ?_⟩
  · calc
      _ ≤ Real.exp (2 * p + (p + 2) ^ 8) + Real.exp (2 * p + (p + 2) ^ 8) :=
        add_le_add (Real.exp_le_exp.mpr (by linarith)) hterm
      _ = Real.exp (2 * p + (p + 2) ^ 8) * 2 := by ring
      _ ≤ Real.exp (2 * p + (p + 2) ^ 8) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + (p + 2) ^ 8 + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold bracketTransitionBudget; linarith)
  · calc
      _ = (m : ℝ) * ((m : ℝ) * (d : ℝ)) := by simp only [Nat.cast_mul]
      _ ≤ Real.exp p * (Real.exp p * Real.exp ((p + 2) ^ 9)) :=
        mul_le_mul hm (mul_le_mul hm hd (Nat.cast_nonneg _) (Real.exp_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + (p + 2) ^ 9) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold bracketTransitionBudget; linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnnormalizedCommonSymbolFactorization
namespace OAI

section

namespace Erdos3

theorem exists_derivative_difference_inputs
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ))
    (A : Matrix κ κ ℝ) (l : ℕ) (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (R : ℝ)
    (hinputs : ∀ h ∈ H, ∃ r : κ → ℝ, r ∈ realDenominatorGrid l ∧
      ‖derivativeGridPoint T scale Y A (h - h₀) r‖ ≤ R) :
    ∃ D : Finset (σ → ℤ), D.card = H.card ∧
      ∃ q : (σ → ℤ) → κ → ℝ, ∀ h ∈ D,
        q h ∈ realDenominatorGrid l ∧ ‖derivativeGridPoint T scale Y A h (q h)‖ ≤ R := by
  classical
  let D := H.image (fun h => h - h₀)
  let q : (σ → ℤ) → κ → ℝ := fun h =>
    if hh : h + h₀ ∈ H then (hinputs (h + h₀) hh).choose else 0
  refine ⟨D, ?_, q, ?_⟩
  · apply Finset.card_image_iff.mpr
    intro h _ k _ he
    simpa only [sub_add_cancel] using congrArg (fun x => x + h₀) he
  · intro h hh
    have hh' : h + h₀ ∈ H := by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
      simpa only [sub_add_cancel] using hk
    simpa only [q, dif_pos hh', add_sub_cancel_right] using
      (hinputs (h + h₀) hh').choose_spec

end Erdos3

end

end OAI
end


