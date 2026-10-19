-- Prove2me | Definitions.Def_OAIE3v2B145
-- name    : OAIE3v2B145
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:18:49.733874+00:00
-- url     : https://prove2.me/theorems/d9b863ba-eeaf-4033-b10c-42bbb6f19a00
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 147 of 311
-- statement:
--   Definitions bundle 147 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B128`, `OAIE3v2B129`, `OAIE3v2B133`, `OAIE3v2B134`, `OAIE3v2B135` of this split.
--
--   Modules: `Estimates/CurrentLayerPreservation.lean`, `Estimates/FastCoefficientImage.lean`, `Estimates/FormalInductionTerminal.lean`, `Estimates/RealFirstCoefficientHorizontal.lean`, `Estimates/ShiftedGradedCalculus.lean`, `Estimates/StepDropTerminalContainment.lean`, `Estimates/UniformFormalCurrentLayerStep.lean`, `Geometry/ReducedSquareCoefficientCoordinates.lean`, `Geometry/WeightedCoordinateExtraction.lean`, `Lattices/FirstCoefficientLatticeCoordinates.lean`, `Linear/AssociatedGradedBasisIndependence.lean`, `Linear/LayerOneProjectionMatrixBounds.lean`, `Linear/RankQuotientHeightBudget.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Nilpotent/PolynomialBCHRemoval.lean`, `Polynomial/CurrentPolynomialDerivativeRemoval.lean`, `Polynomial/FormalPolynomialCorrectionStep.lean`, `Polynomial/PolynomialLiftMatching.lean`, `Polynomial/QuantitativeOuterPolynomialProducts.lean`, `Polynomial/ScaledPolynomialDualBounds.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B129
import Definitions.Def_OAIE3v2B133
import Definitions.Def_OAIE3v2B134
import Definitions.Def_OAIE3v2B135

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScaledPolynomialDualBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem exists_polynomial_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (_hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List ((F.realification.adaptedPolynomialFiltration w).Group), rs.length ≤ k →
        (∀ r ∈ rs, F.PolynomialRationalGrid b w l r) → F.PolynomialRationalGrid b w m rs.prod := by
  obtain ⟨K, _, hK⟩ := exists_real_bch_rational_product_bound s k
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.adaptedMonomialBasis b ω hlayers w
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
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hK B H q (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    hq hdim (hHp.trans (Real.exp_le_exp.mpr hpq))
    (F.adaptedMonomialBasis_bracket_height b ω hlayers w hH hb) l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  have hpoly : (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpoly), hlm, ?_⟩
  intro rs hlen hrs
  let ys := rs.map (F.realAdaptedPolynomialGroupLift w b ω hlayers)
  have hys : ys.map (F.realAdaptedPolynomialGroupHom w) = rs := by
    simp only [ys, List.map_map, Function.comp_def, F.realAdaptedPolynomialGroupHom_lift]
    simp
  have hinput : ∀ r ∈ ys, (B.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid l := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    apply (F.polynomialRationalGrid_groupHom_iff b w ω hlayers l _).mp
    rw [F.realAdaptedPolynomialGroupHom_lift]
    exact hrs u hu
  have hout := (F.polynomialRationalGrid_groupHom_iff b w ω hlayers m ys.prod).mpr
    (hprod ys (by simpa only [ys, List.length_map] using hlen) hinput)
  rwa [map_list_prod, hys] at hout

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AssociatedGradedBasisIndependence
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem real_gradedPieceProjection_coordinate (j : ℕ) (v : ℝ ⊗[ℚ] L) (i : ι) :
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr
      ((F.gradedPieceProjection b ω hlayers j).baseChange ℝ v) i =
      if ω i = j then (b.baseChange ℝ).repr v i else 0 := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      F.gradedPieceProjection_coordinate, Basis.baseChange_repr_tmul]
    split_ifs <;> simp only [zero_smul]
  | add v z hv hz =>
    simp only [map_add, Finsupp.add_apply, hv, hz]
    split_ifs <;> simp only [add_zero]

theorem realGradedSymbolPolynomial_coefficient_of_polynomial
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realSymbolOfPolynomial b ω hlayers w p)) α =
        (F.gradedPieceProjection b ω hlayers (Finsupp.weight w α)).baseChange ℝ (coefficients p α) := by
  apply ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr.injective
  ext i
  rw [F.real_gradedPieceProjection_coordinate]
  by_cases h : Finsupp.weight w α = ω i
  · rw [if_pos h.symm]
    exact (F.realGradedSymbolPolynomial_coordinate b ω hlayers w _ ⟨(α, i), h⟩).trans
      (F.realSymbolOfPolynomial_coordinate b ω hlayers w p ⟨(α, i), h⟩)
  · rw [if_neg (Ne.symm h)]
    exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w _ α i h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedGradedCalculus
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

theorem adaptedLogDerivative_mul
    (P Q : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.adaptedLogDerivative h (P * Q).coord =
      F.adaptedLogDerivative h P.coord + dualAdjoint P (F.adaptedLogDerivative h Q.coord) := by
  change dualLogDerivative (F.adaptedPolynomialJetHom h (P * Q)) = _
  rw [map_mul, dualLogDerivative_mul, F.adaptedPolynomialJetHom_apply,
    F.adaptedPolynomialJet_baseHom]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedLogDerivative_constant (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hp : coefficients p.val 0 = 0) :
    coefficients (F.adaptedLogDerivative h p).val 0 =
      coefficients (directionalDerivative h p.val) 0 := by
  let φ : F.adaptedLieSubalgebra (fun _ : σ => 1) →ₗ⁅ℚ⁆ L :=
    (evalLie (0 : σ → ℚ)).comp (F.adaptedLieSubalgebra (fun _ => 1)).incl
  have hφ (q : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
      φ q = coefficients q.val 0 := eval_zero_eq_coefficient q.val
  have hjet : dualLinearLift φ φ.toLinearMap (F.adaptedPolynomialJet h p).coord =
      (dualTangentElement (hnil := F.lowerCentralSeries_eq_bot)
        (φ (F.adaptedDirectionalDerivative h p))).coord := by
    rw [dualLinearLift_apply, F.adaptedPolynomialJet_base, F.adaptedPolynomialJet_tangent]
    change dualConstantLie (φ p) + dualInfinitesimal (φ (F.adaptedDirectionalDerivative h p)) = _
    rw [hφ p, hp, map_zero, zero_add]
    rfl
  have he := dualLinearLift_logDerivative_eq F.lowerCentralSeries_eq_bot
    (⊤ : LieIdeal ℚ (F.adaptedLieSubalgebra (fun _ : σ => 1))) φ φ.toLinearMap
    (fun x y _ => φ.map_lie x y) (F.adaptedPolynomialJet h p) (by trivial)
    (dualTangentElement (φ (F.adaptedDirectionalDerivative h p))) hjet
  rw [dualLogDerivative_tangent] at he
  change φ (F.adaptedLogDerivative h p) = φ (F.adaptedDirectionalDerivative h p) at he
  simpa only [hφ, F.adaptedDirectionalDerivative_coe] using he

theorem adaptedLogDerivative_constant_unit [DecidableEq σ] (i : σ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hp : coefficients p.val 0 = 0) :
    coefficients (F.adaptedLogDerivative (Pi.single i 1) p).val 0 =
      coefficients p.val (Finsupp.single i 1) := by
  classical
  rw [F.adaptedLogDerivative_constant _ p hp, coefficients_directionalDerivative]
  simp [Pi.single_apply]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem gradedPieceProjection_lie {i j : ℕ} {u v : L}
    (hu : u ∈ F.layer i) (hv : v ∈ F.layer j) :
    F.gradedPieceProjection b ω hlayers (i + j) ⁅u, v⁆ =
      ⁅F.gradedPieceProjection b ω hlayers i u, F.gradedPieceProjection b ω hlayers j v⁆ := by
  have hi := F.gradedPieceProjection_eq_pieceMap b ω hlayers i ⟨u, hu⟩
  have hj := F.gradedPieceProjection_eq_pieceMap b ω hlayers j ⟨v, hv⟩
  have hij := F.gradedPieceProjection_eq_pieceMap b ω hlayers (i + j) ⟨⁅u, v⁆, F.lie_mem hu hv⟩
  change F.gradedPieceProjection b ω hlayers i u = _ at hi
  change F.gradedPieceProjection b ω hlayers j v = _ at hj
  change F.gradedPieceProjection b ω hlayers (i + j) ⁅u, v⁆ = _ at hij
  rw [hi, hj, hij, F.associatedGradedPieceMap_lie]

theorem shiftedGradedPolynomial_lie (w : σ → ℕ) {i j : ℕ} {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w i) (hq : q ∈ F.shiftedAdaptedSubmodule w j) :
    F.shiftedGradedPolynomial b ω hlayers w (i + j) ⁅p, q⁆ =
      ⁅F.shiftedGradedPolynomial b ω hlayers w i p, F.shiftedGradedPolynomial b ω hlayers w j q⁆ := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum, sum_lie_sum, map_sum, lie_monomial, F.shiftedGradedPolynomial_monomial]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  have hdeg : Finsupp.weight w (α + β) + (i + j) =
      (Finsupp.weight w α + i) + (Finsupp.weight w β + j) := by
    rw [map_add]
    omega
  rw [hdeg, F.gradedPieceProjection_lie b ω hlayers (hp α) (hq β)]

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

theorem correction_inverse_adjoint_sub_current_bracket_mem (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {j : ℕ} (hj : 2 ≤ j)
    (a : F.Group) (haU : a.coord ∈ U) (ha : a.coord ∈ F.layer (j - 1))
    (x k : L) (hx : x - k ∈ V ⊔ F.layer 2) :
    dualAdjoint a⁻¹ x - (x - ⁅a.coord, k⁆) ∈ V ⊔ F.layer (j + 1) := by
  have h := F.correction_adjoint_sub_current_bracket_mem hs U V hUV hj a⁻¹
    (U.neg_mem haU) ((F.layer (j - 1)).neg_mem ha) x k hx
  simpa only [coord_inv, neg_lie, ← sub_eq_add_neg] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem current_layer_normalization {κ : Type*} (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {j : ℕ} (hj : 2 ≤ j)
    (g a c : F.Group) (hg : g.coord ∈ U) (haU : a.coord ∈ U) (hcU : c.coord ∈ U)
    (ha : a.coord ∈ F.layer (j - 1)) (hc : c.coord ∈ F.layer (j - 1))
    (S R k : κ → L) (p : L) (hp : p ∈ F.layer (j - 1))
    (hSR : ∀ b, S b = dualAdjoint g (R b))
    (hR : ∀ b, R b - k b ∈ V ⊔ F.layer j)
    (hlower : ∀ b, ⁅g.coord - p, k b⁆ ∈ V ⊔ F.layer (j + 1))
    (hleft : ∀ b, S b - k b - ⁅a.coord, k b⁆ ∈ V ⊔ F.layer (j + 1))
    (hright : ∀ b, R b - k b + ⁅c.coord, k b⁆ ∈ V ⊔ F.layer (j + 1)) :
    let g' := a⁻¹ * g * c⁻¹
    let S' := fun b => dualAdjoint a⁻¹ (S b)
    let R' := fun b => dualAdjoint c (R b)
    let p' := p - a.coord - c.coord
    a * g' * c = g ∧ g'.coord ∈ U ∧ p' ∈ F.layer (j - 1) ∧
      g'.coord - (g.coord - a.coord - c.coord) ∈ F.layer j ∧
      (∀ b, S' b = dualAdjoint g' (R' b)) ∧
      ∀ b, S' b - k b ∈ V ⊔ F.layer (j + 1) ∧
        R' b - k b ∈ V ⊔ F.layer (j + 1) ∧
        ⁅p', k b⁆ ∈ V ⊔ F.layer (j + 1) := by
  intro g' S' R' p'
  have hj1 : 1 ≤ j := by omega
  have hdown : V ⊔ F.layer j ≤ V ⊔ F.layer 2 :=
    sup_le le_sup_left ((F.antitone hj).trans le_sup_right)
  have hR2 (b : κ) : R b - k b ∈ V ⊔ F.layer 2 := hdown (hR b)
  have hS2 (b : κ) : S b - k b ∈ V ⊔ F.layer 2 := by
    have hx : R b ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
    have h := F.dualAdjoint_sub_mem_next_layer 1 g (R b) hx
    rw [hSR b]
    convert (V ⊔ F.layer 2).add_mem (Submodule.mem_sup_right h) (hR2 b) using 1
    abel
  refine ⟨?_, ?_, (F.layer (j - 1)).sub_mem ((F.layer (j - 1)).sub_mem hp ha) hc,
    F.correction_removal_coord_sub_mem_layer a g c ha hc hj1,
    fun b => F.removal_adjoint_relation a g c (S b) (R b) (hSR b), ?_⟩
  · dsimp [g']
    group
  · exact lieBCH_mem U s (lieBCH_mem U s (U.neg_mem haU) hg) (U.neg_mem hcU)
  · intro b
    have hSa := F.correction_inverse_adjoint_sub_current_bracket_mem hs U V hUV hj
      a haU ha (S b) (k b) (hS2 b)
    have hRc := F.correction_adjoint_sub_current_bracket_mem hs U V hUV hj
      c hcU hc (R b) (k b) (hR2 b)
    have hk1 : k b ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
    have hbr := F.adjoint_current_layer_relation U V hUV hs hj1 g hg (R b) (k b)
      p hp hk1 (hR b) (hlower b)
    rw [← hSR b] at hbr
    refine ⟨?_, ?_, ?_⟩
    · convert (V ⊔ F.layer (j + 1)).add_mem hSa (hleft b) using 1; dsimp [S']; abel
    · convert (V ⊔ F.layer (j + 1)).add_mem hRc (hright b) using 1; dsimp [R']; abel
    · have h := (V ⊔ F.layer (j + 1)).sub_mem
        ((V ⊔ F.layer (j + 1)).add_mem hbr (hleft b)) (hright b)
      dsimp [p']
      rw [sub_lie, sub_lie]
      convert h using 1; abel

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
theorem real_mem_of_homogeneous_mem_sup_next
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (j : ℕ) (x : ℝ ⊗[ℚ] L) (hgrade : basisGradeProjection (b.baseChange ℝ) w j x = x)
    (hx : x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) : x ∈ V := by
  have h := F.realGradeProjection_mem_of_mem_sup_next b w hlayers V hV j x hx
  rwa [hgrade] at h

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastCoefficientImage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem firstCoefficientHorizontal_section (x : L ⧸ F.layer 2) :
    F.firstCoefficientHorizontal w (F.firstCoefficientHorizontalSection w x) = x := by
  obtain ⟨v, rfl⟩ := (F.layer 2).mkQ_surjective x
  rw [F.firstCoefficientHorizontalSection_mk, F.firstCoefficientHorizontal_constant]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

theorem firstCoefficientIndex_grade_pos {σ ι : Type*} (ω : ι → ℕ)
    (z : FirstCoefficientIndex (fun _ : σ => 1) ω) : 1 ≤ ω z.val.2 := by
  have h := z.property
  omega

theorem firstCoefficientIndex_zero_iff_grade_one {σ ι : Type*} (ω : ι → ℕ)
    (z : FirstCoefficientIndex (fun _ : σ => 1) ω) :
    z.val.1 = 0 ↔ ω z.val.2 = 1 := by
  constructor
  · intro hz
    have h := z.property
    simpa only [hz, map_zero, zero_add] using h.symm
  · intro hz
    apply Finsupp.ext
    intro i
    change z.val.1 i = 0
    by_contra hi
    have hw := Finsupp.le_weight_of_ne_zero' (fun _ : σ => (1 : ℕ)) hi
    have h := z.property
    omega

theorem exists_sorted_firstCoefficient_rows {σ ι : Type*} {d : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ), a ≤ d ∧
      Monotone (fun i => ω (rows (e i)).val.2) ∧
      ∀ i, i.val < a ↔ (rows (e i)).val.1 = 0 := by
  obtain ⟨e, a, ha, hm, hi⟩ := exists_sorted_positive_weights
    (fun i => ω (rows i).val.2) (fun i => firstCoefficientIndex_grade_pos ω (rows i))
  refine ⟨e, a, ha, hm, ?_⟩
  intro i
  exact (hi i).trans (firstCoefficientIndex_zero_iff_grade_one ω (rows (e i))).symm

theorem sorted_firstCoefficient_scale_bounds {σ ι : Type*} {d a : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (hzero : ∀ i, i.val < a ↔ (rows i).val.1 = 0)
    (T : σ → ℝ) (Tmin : ℝ) (hmin : 1 ≤ Tmin) (hT : ∀ i, Tmin ≤ T i) :
    (∀ i, i.val < a → monomialScale T (rows i).val.1 = 1) ∧
      (∀ i, a ≤ i.val → Tmin ≤ monomialScale T (rows i).val.1) := by
  constructor
  · intro i hi
    rw [(hzero i).mp hi, monomialScale_zero]
  · intro i hi
    apply le_monomialScale_of_ne_zero T hmin hT
    intro hz
    exact (not_lt_of_ge hi) ((hzero i).mpr hz)

end Erdos3.NilpotentLieFiltration

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

theorem bchRemove_factorization {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (A P B : VectorPolynomial σ ℚ L) :
    lieBCH s (lieBCH s A (bchRemove s A P B)) B = P := by
  let a : NilpotentLieBCHGroup.PolynomialGroup σ hnil := ⟨A⟩
  let g : NilpotentLieBCHGroup.PolynomialGroup σ hnil := ⟨P⟩
  let c : NilpotentLieBCHGroup.PolynomialGroup σ hnil := ⟨B⟩
  have h : a * (a⁻¹ * g * c⁻¹) * c = g := by group
  exact congrArg NilpotentLieBCHGroup.coord h

theorem bchRemove_constant {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (A P B : VectorPolynomial σ ℚ L) (hA : coefficients A 0 = 0) (hB : coefficients B 0 = 0) :
    coefficients (bchRemove s A P B) 0 = coefficients P 0 := by
  have h₁ := eval_lieBCH (fun _ : σ => (0 : ℚ)) s (lieBCH s (-A) P) (-B)
  have h₂ := eval_lieBCH (fun _ : σ => (0 : ℚ)) s (-A) P
  rw [h₂] at h₁
  simp only [map_neg, eval_zero_eq_coefficient, hA, hB, neg_zero] at h₁
  apply h₁.trans
  change ((1 : NilpotentLieBCHGroup L s hnil) * ⟨coefficients P 0⟩ * 1).coord = _
  simp only [one_mul, mul_one]

end VectorPolynomial

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

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

theorem monomial_mem_gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ) (v : σ → ℕ)
    (α : σ →₀ ℕ) (x : L) (hx : basisGradeProjection b w (Finsupp.weight v α) x = x) :
    monomial (R := ℚ) α x ∈ gradedPolynomialSubmodule b w v := by
  intro β
  rw [coefficients_monomial]
  by_cases h : α = β
  · subst β
    simpa only [Finsupp.single_eq_same, LinearMap.restrictScalars_apply] using hx
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero]

noncomputable def gradedPolynomialSubalgebra (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { gradedPolynomialSubmodule b w v with
    lie_mem' := by
      intro P Q hP hQ
      classical
      rw [← sum_monomial_coefficients P, ← sum_monomial_coefficients Q]
      simp only [Finsupp.sum]
      rw [sum_lie_sum (coefficients P).support (coefficients Q).support
        (fun α => monomial (R := ℚ) α (coefficients P α))
        (fun β => monomial (R := ℚ) β (coefficients Q β))]
      apply (gradedPolynomialSubmodule b w v).sum_mem
      intro α _
      apply (gradedPolynomialSubmodule b w v).sum_mem
      intro β _
      rw [lie_monomial]
      apply monomial_mem_gradedPolynomialSubmodule
      rw [map_add]
      exact hb.projection_lie b w (hP α) (hQ β) }

theorem homogeneous_mem_gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ) (v : σ → ℕ)
    (j : ℕ) (P : VectorPolynomial σ ℚ L)
    (hhom : ∀ α, Finsupp.weight v α ≠ j → coefficients P α = 0)
    (hgrade : ∀ α, basisGradeProjection b w j (coefficients P α) = coefficients P α) :
    P ∈ gradedPolynomialSubmodule b w v := by
  intro α
  by_cases hα : Finsupp.weight v α = j
  · simpa only [hα, LinearMap.restrictScalars_apply] using hgrade α
  · rw [hhom α hα, map_zero]

theorem gradedPolynomialSubmodule_projection_homogeneous (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (P : VectorPolynomial σ ℚ L) (hP : P ∈ gradedPolynomialSubmodule b w v)
    (j : ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight v α ≠ j) :
    coefficients (map ((basisGradeProjection b w j).restrictScalars ℚ) P) α = 0 := by
  rw [coefficients_map]
  change basisGradeProjection b w j (coefficients P α) = 0
  have he : basisGradeProjection b w (Finsupp.weight v α) (coefficients P α) = coefficients P α := hP α
  rw [← he]
  exact basisGradeProjection_other b w (Ne.symm hα) _

theorem bchRemove_mem_gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) (s : ℕ)
    (A P B : VectorPolynomial σ ℚ L)
    (hA : A ∈ gradedPolynomialSubmodule b w v) (hP : P ∈ gradedPolynomialSubmodule b w v)
    (hB : B ∈ gradedPolynomialSubmodule b w v) :
    bchRemove s A P B ∈ gradedPolynomialSubmodule b w v := by
  let U := gradedPolynomialSubalgebra b w hb v
  exact lieBCH_mem U s (lieBCH_mem U s (U.neg_mem hA) hP) (U.neg_mem hB)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficientSubmodule_sup (V W : Submodule ℚ L) :
    coefficientSubmodule (σ := σ) (V ⊔ W) = coefficientSubmodule V ⊔ coefficientSubmodule W := by
  classical
  apply le_antisymm
  · intro P hP
    rw [← sum_monomial_coefficients P]
    change ∑ α ∈ (coefficients P).support, monomial α (coefficients P α) ∈ _
    apply Submodule.sum_mem
    intro α _
    obtain ⟨v, hv, w, hw, he⟩ := Submodule.mem_sup.mp (hP α)
    rw [← he]
    have hmono : monomial (R := ℚ) α (v + w) = monomial α v + monomial α w :=
      TensorProduct.tmul_add _ _ _
    rw [hmono]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (monomial_mem_coefficientSubmodule V α hv))
      (Submodule.mem_sup_right (monomial_mem_coefficientSubmodule W α hw))
  · apply sup_le
    · intro P hP α
      exact Submodule.mem_sup_left (hP α)
    · intro P hP α
      exact Submodule.mem_sup_right (hP α)

theorem coefficients_lie_constant (P : VectorPolynomial σ ℚ L) (x : L) (α : σ →₀ ℕ) :
    coefficients ⁅P, monomial (R := ℚ) 0 x⁆ α = ⁅coefficients P α, x⁆ := by
  induction P using TensorProduct.induction_on with
  | zero =>
    rw [zero_lie (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L)]
    simp
  | tmul q y =>
    simp only [monomial, LieAlgebra.ExtendScalars.bracket_tmul,
      MvPolynomial.monomial_zero', MvPolynomial.C_1, mul_one,
      coefficients_tmul, coefficients_tmul, smul_lie]
  | add P Q hP hQ =>
    rw [LieRing.add_lie P Q, map_add, Finsupp.add_apply, hP, hQ,
      map_add, Finsupp.add_apply, LieRing.add_lie]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

theorem monomial_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (r : ℕ) (α : σ →₀ ℕ) (x : L)
    (hx : basisGradeProjection b w (Finsupp.weight v α + r) x = x) :
    monomial (R := ℚ) α x ∈ shiftedGradedPolynomialSubmodule b w v r := by
  intro β
  rw [coefficients_monomial]
  by_cases h : α = β
  · subst β
    simpa only [Finsupp.single_eq_same, LinearMap.restrictScalars_apply] using hx
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero]

theorem shiftedGradedPolynomialSubmodule_invariant (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) (r : ℕ)
    (P Q : VectorPolynomial σ ℚ L)
    (hP : P ∈ gradedPolynomialSubmodule b w v)
    (hQ : Q ∈ shiftedGradedPolynomialSubmodule b w v r) :
    ⁅P, Q⁆ ∈ shiftedGradedPolynomialSubmodule b w v r := by
  classical
  rw [← sum_monomial_coefficients P, ← sum_monomial_coefficients Q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients P).support (coefficients Q).support
    (fun α => monomial (R := ℚ) α (coefficients P α))
    (fun β => monomial (R := ℚ) β (coefficients Q β))]
  apply (shiftedGradedPolynomialSubmodule b w v r).sum_mem
  intro α _
  apply (shiftedGradedPolynomialSubmodule b w v r).sum_mem
  intro β _
  rw [lie_monomial]
  apply monomial_mem_shiftedGradedPolynomialSubmodule
  rw [map_add, Nat.add_assoc]
  exact hb.projection_lie b w (hP α) (hQ β)

theorem pderiv_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (P : VectorPolynomial σ ℚ L)
    (hP : P ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1)) (i : σ) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L P ∈
      shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 := by
  intro α
  rw [coefficients_pderiv, map_smul]
  have h := congrArg (fun x => (α i + 1 : ℚ) • x) (hP (α + Finsupp.single i 1))
  simpa only [map_add, Finsupp.weight_single, one_smul] using h

theorem shiftedGradedPolynomialSubmodule_projection_homogeneous (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (r : ℕ) (P : VectorPolynomial σ ℚ L)
    (hP : P ∈ shiftedGradedPolynomialSubmodule b w v r)
    (j : ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight v α + r ≠ j) :
    coefficients (VectorPolynomial.map ((basisGradeProjection b w j).restrictScalars ℚ) P) α = 0 := by
  rw [coefficients_map]
  change basisGradeProjection b w j (coefficients P α) = 0
  have he : basisGradeProjection b w (Finsupp.weight v α + r) (coefficients P α) =
      coefficients P α := hP α
  rw [← he]
  exact basisGradeProjection_other b w (Ne.symm hα) _

theorem shifted_one_projection_homogeneous (b : Basis ι ℝ L) (w : ι → ℕ)
    (P : VectorPolynomial σ ℚ L)
    (hP : P ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1)
    {j : ℕ} (hj : 0 < j) (α : σ →₀ ℕ)
    (hα : Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1) :
    coefficients (VectorPolynomial.map ((basisGradeProjection b w j).restrictScalars ℚ) P) α = 0 := by
  apply shiftedGradedPolynomialSubmodule_projection_homogeneous b w (fun _ => 1) 1 P hP j α
  omega

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) (r : ℕ)
    (P : PolynomialGroup σ hnil) (Q : VectorPolynomial σ ℚ L)
    (hP : P.coord ∈ gradedPolynomialSubmodule b w v)
    (hQ : Q ∈ shiftedGradedPolynomialSubmodule b w v r) :
    dualAdjoint P Q ∈ shiftedGradedPolynomialSubmodule b w v r :=
  dualAdjoint_mem_of_invariant (gradedPolynomialSubalgebra b w hb v)
    (shiftedGradedPolynomialSubmodule b w v r)
    (fun A hA B hB => shiftedGradedPolynomialSubmodule_invariant b w hb v r A B hA hB)
    P hP Q hQ

theorem formalLogDerivative_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (i : σ) (P : PolynomialGroup σ hnil)
    (hP : P.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1)) :
    formalLogDerivative i P ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 :=
  formalLogDerivative_mem_of_invariant (gradedPolynomialSubalgebra b w hb (fun _ : σ => 1))
    (shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1)
    (fun A hA B hB => shiftedGradedPolynomialSubmodule_invariant b w hb _ 1 A B hA hB)
    i P hP (pderiv_mem_shiftedGradedPolynomialSubmodule b w P.coord hP i)

theorem polynomial_derivative_removal_preserves_shifted_grading
    (b : Basis ι ℝ L) (w : ι → ℕ) (hb : BasisHomogeneousBrackets b w)
    (i : σ) (A B : PolynomialGroup σ hnil) (small rational : VectorPolynomial σ ℚ L)
    (hA : A.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1))
    (hB : B.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1))
    (hsmall : small ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1)
    (hrational : rational ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1) :
    dualAdjoint A⁻¹ (small - formalLogDerivative i A) ∈
        shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 ∧
      dualAdjoint B rational - formalLogDerivative i B ∈
        shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 := by
  let W := shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1
  have hYA := formalLogDerivative_mem_shiftedGradedPolynomialSubmodule b w hb i A hA
  have hYB := formalLogDerivative_mem_shiftedGradedPolynomialSubmodule b w hb i B hB
  constructor
  · exact dualAdjoint_mem_shiftedGradedPolynomialSubmodule b w hb _ 1 A⁻¹ _
      ((gradedPolynomialSubmodule b w _).neg_mem hA) (W.sub_mem hsmall hYA)
  · exact W.sub_mem
      (dualAdjoint_mem_shiftedGradedPolynomialSubmodule b w hb _ 1 B rational hB hrational) hYB

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CurrentPolynomialDerivativeRemoval
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def PolynomialLiftSystem (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ k, S k = dualAdjoint P (R k)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem PolynomialLiftSystemMod.exact_left (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ L) (h : PolynomialLiftSystemMod V P S R) :
    ∃ S₀ : κ → VectorPolynomial σ ℚ L,
      PolynomialLiftSystem P S₀ R ∧ ∀ k, S k - S₀ k ∈ coefficientSubmodule V :=
  ⟨fun k => dualAdjoint P (R k), fun _ => rfl, h⟩

theorem PolynomialDerivativeSystemMod.exact_system (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (h : PolynomialDerivativeSystemMod V P small rational extra) :
    ∃ error : σ → VectorPolynomial σ ℚ L,
      (∀ i, error i ∈ coefficientSubmodule V) ∧
      PolynomialDerivativeSystem P small rational (fun i => extra i + error i) := by
  refine ⟨fun i => formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i), h, ?_⟩
  intro i
  change formalLogDerivative i P = small i + dualAdjoint P (rational i) +
    (extra i + (formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i)))
  abel

theorem PolynomialLiftSystemMod.remove (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P A B : PolynomialGroup σ hnil) (hA : ∀ α, coefficients A.coord α ∈ U)
    (S R : κ → VectorPolynomial σ ℚ L) (h : PolynomialLiftSystemMod V P S R) :
    PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹)
      (fun k => dualAdjoint A⁻¹ (S k)) (fun k => dualAdjoint B (R k)) := by
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ U := (coefficientLieSubalgebra U).neg_mem hA
  intro k
  change dualAdjoint A⁻¹ (S k) - dualAdjoint (A⁻¹ * P * B⁻¹) (dualAdjoint B (R k)) ∈ _
  rw [dualAdjoint_mul, dualAdjoint_mul, dualAdjoint_inv_cancel, ← dualAdjoint_sub]
  exact dualAdjoint_mem_coefficientSubmodule U V hUV A⁻¹ _ hAi (h k)

theorem PolynomialDerivativeSystemMod.remove (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P A B : PolynomialGroup σ hnil) (hA : ∀ α, coefficients A.coord α ∈ U)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (h : PolynomialDerivativeSystemMod V P small rational extra) :
    PolynomialDerivativeSystemMod V (A⁻¹ * P * B⁻¹)
      (fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A))
      (fun i => dualAdjoint B (rational i) - formalLogDerivative i B)
      (fun i => dualAdjoint A⁻¹ (extra i)) := by
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ U := (coefficientLieSubalgebra U).neg_mem hA
  intro i
  have herr := dualAdjoint_mem_coefficientSubmodule U V hUV A⁻¹
    (formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i)) hAi (h i)
  have hmem : dualAdjoint A⁻¹
      (formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i)) ∈
      coefficientSubmodule V := herr
  change formalLogDerivative i (A⁻¹ * P * B⁻¹) -
    (dualAdjoint A⁻¹ (small i - formalLogDerivative i A) +
      dualAdjoint (A⁻¹ * P * B⁻¹) (dualAdjoint B (rational i) - formalLogDerivative i B) +
      dualAdjoint A⁻¹ (extra i)) ∈ coefficientSubmodule V
  convert hmem using 1
  rw [formalLogDerivative_remove]
  simp only [dualAdjoint_mul, dualAdjoint_add, dualAdjoint_sub, dualAdjoint_inv_cancel]
  abel

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem polynomial_grade_eq_of_sub_mem_next (j : ℕ)
    (X Y : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hXY : ∀ α, coefficients (X - Y) α ∈ F.realification.layer (j + 1)) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) X =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) Y := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [coefficients_map, coefficients_map]
  have h := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers j _ (hXY α)
  simp only [map_sub, Finsupp.sub_apply] at h
  exact sub_eq_zero.mp h

include hlayers in
theorem polynomial_grade_adjoint_eq (hs : 2 ≤ s) (j : ℕ)
    (A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (X : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (dualAdjoint A X) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) X := by
  apply F.polynomial_grade_eq_of_sub_mem_next b w hlayers j
  exact F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j A hA X

include hlayers in
theorem polynomial_grade_logDerivative_eq (hs : 1 ≤ s) {j : ℕ} (hj : 0 < j)
    (i : σ) (A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (formalLogDerivative i A) =
      (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord := by
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hA α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hDlayer := pderiv_mem_submodule (F.realification.layer j) A.coord hAlayer i
  have hrem := F.realification.polynomialFiltration.dualLogDerivative_sub_tangent_mem_layer hs
    (i := j) (j := j) (formalPolynomialJetHom i A)
    (by rw [formalPolynomialJet_base]; exact hAlayer)
    (by rw [formalPolynomialJet_tangent]; exact hDlayer)
  rw [formalPolynomialJet_tangent] at hrem
  have hnext : ∀ α, coefficients (formalLogDerivative i A -
      (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord) α ∈ F.realification.layer (j + 1) := by
    intro α
    exact F.realification.antitone (by omega : j + 1 ≤ j + j) (hrem α)
  have hgrade := F.polynomial_grade_eq_of_sub_mem_next b w hlayers j _ _ hnext
  have hfix : VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) A.coord = A.coord := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map]
    exact hA α
  rw [← pderiv_map, hfix] at hgrade
  exact hgrade

include hlayers in
theorem current_derivative_removal_projection (hs : 2 ≤ s) {j : ℕ} (hj : 0 < j)
    (i : σ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α)
    (small rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint A⁻¹ (small - formalLogDerivative i A)) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) small -
        (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord ∧
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint B rational - formalLogDerivative i B) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) rational -
        (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) B.coord := by
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hA α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hBlayer : ∀ α, coefficients B.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hB α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ F.realification.layer j :=
    (coefficientSubmodule (F.realification.layer j)).neg_mem hAlayer
  constructor
  · rw [F.polynomial_grade_adjoint_eq b w hlayers hs j A⁻¹ hAi, map_sub,
      F.polynomial_grade_logDerivative_eq b w hlayers (by omega) hj i A hA]
  · rw [map_sub, F.polynomial_grade_adjoint_eq b w hlayers hs j B hBlayer,
      F.polynomial_grade_logDerivative_eq b w hlayers (by omega) hj i B hB]

include hlayers in
theorem current_derivative_defect_preserved (hs : 2 ≤ s) {j : ℕ} (hj : 0 < j)
    (i : σ) (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α)
    (small rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    let π := VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
    let D := (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
    D (π (A⁻¹ * P * B⁻¹).coord) - π (dualAdjoint A⁻¹ (small - formalLogDerivative i A)) -
        π (dualAdjoint B rational - formalLogDerivative i B) =
      D (π P.coord) - π small - π rational := by
  dsimp only
  let E := LinearMap.ker (basisGradeProjection (b.baseChange ℝ) w j - LinearMap.id)
  have hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w j x = x := by
    intro x hx
    exact sub_eq_zero.mp hx
  have hgrades := F.polynomial_bchRemove_grades b w hlayers E j hE A.coord P.coord B.coord
    (fun α => sub_eq_zero.mpr (hA α)) (fun α => sub_eq_zero.mpr (hB α))
  have hP : VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
      (A⁻¹ * P * B⁻¹).coord =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord - A.coord - B.coord :=
    hgrades.1
  have hparts := F.current_derivative_removal_projection b w hlayers hs hj i A B hA hB small rational
  rw [hP, hparts.1, hparts.2, map_sub, map_sub]
  abel

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal
namespace OAI

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

theorem directionalDerivative_single {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] (i : σ) (P : VectorPolynomial σ ℚ L) :
    directionalDerivative (Pi.single i 1) P = (MvPolynomial.pderiv i).toLinearMap.rTensor L P := by
  simp [directionalDerivative, Pi.single_apply]

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedLogDerivative_eq_formal (i : σ)
    (P : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (F.adaptedLogDerivative (Pi.single i 1) P : VectorPolynomial σ ℚ L) =
      formalLogDerivative (hnil := F.lowerCentralSeries_eq_bot) i ⟨P.val⟩ := by
  let φ := (F.adaptedLieSubalgebra (fun _ : σ => 1)).incl
  apply dualLinearLift_logDerivative_eq
    (VectorPolynomial.lowerCentralSeries_eq_bot (σ := σ) F.lowerCentralSeries_eq_bot)
    ⊤ φ φ.toLinearMap (fun a b _ => φ.map_lie a b)
    (F.adaptedPolynomialJet (Pi.single i 1) P) (by trivial)
    (formalPolynomialJetHom i (⟨P.val⟩ : PolynomialGroup σ F.lowerCentralSeries_eq_bot))
  rw [dualLinearLift_apply, F.adaptedPolynomialJet_base, F.adaptedPolynomialJet_tangent]
  change dualConstantLie P.val + dualInfinitesimal (directionalDerivative (Pi.single i 1) P.val) =
    dualConstantLie P.val + dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.val)
  rw [directionalDerivative_single]

omit [Fintype σ] [DecidableEq σ] in
theorem realAdaptedAdjoint_eq_formal (v : σ → ℕ) (P : F.RealAdaptedPolynomialGroup v)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra v) :
    F.realAdaptedPolynomialMap v (dualAdjoint P x) =
      dualAdjoint (F.realFullPolynomialHom v P) (F.realAdaptedPolynomialMap v x) :=
  map_dualAdjoint (F.realFullPolynomialLie v) P x

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem coefficientBound_iff_norm [Fintype ι] (b : Basis ι ℝ L)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (P : VectorPolynomial σ ℚ L) :
    CoefficientBound b T M P ↔ ∀ α, ‖b.equivFun (coefficients P α)‖ ≤ M / monomialScale T α := by
  constructor
  · intro h α
    exact (pi_norm_le_iff_of_nonneg (div_nonneg hM (monomialScale_pos T hT α).le)).mpr (h α)
  · intro h α i
    exact (norm_le_pi_norm (b.equivFun (coefficients P α)) i).trans (h α)

theorem CoefficientBound.neg (b : Basis ι ℝ L) (T : σ → ℝ) {M : ℝ}
    {P : VectorPolynomial σ ℚ L} (h : CoefficientBound b T M P) : CoefficientBound b T M (-P) := by
  intro α i
  simpa only [map_neg, Finsupp.neg_apply, abs_neg] using h α i

theorem CoefficientBound.sub (b : Basis ι ℝ L) (T : σ → ℝ) {M N : ℝ}
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientBound b T M P) (hQ : CoefficientBound b T N Q) :
    CoefficientBound b T (M + N) (P - Q) := by
  intro α i
  simp only [map_sub, Finsupp.sub_apply]
  exact (abs_sub _ _).trans ((add_le_add (hP α i) (hQ α i)).trans_eq (by ring))

theorem CoefficientGrid.sub (b : Basis ι ℝ L) (l : ℕ)
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientGrid b l P) (hQ : CoefficientGrid b l Q) :
    CoefficientGrid b l (P - Q) := by
  intro α
  simp only [map_sub, Finsupp.sub_apply]
  exact realDenominatorGrid_sub l _ _ (hP α) (hQ α)

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hF in
theorem gradedPolynomial_mem_adapted (w : σ → ℕ) (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω w) :
    P ∈ F.realification.adaptedLieSubalgebra w := by
  intro α
  have h := F.realGradeProjection_mem_layer b ω hF (Finsupp.weight w α) (coefficients P α)
  have he : basisGradeProjection (b.baseChange ℝ) ω (Finsupp.weight w α) (coefficients P α) = coefficients P α := hP α
  rw [he] at h
  exact h

include hF in
theorem shiftedGradedPolynomial_mem_adapted (w : σ → ℕ) (r : ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) ω w r) :
    P ∈ F.realification.adaptedLieSubalgebra w := by
  intro α
  have h := F.realGradeProjection_mem_layer b ω hF (Finsupp.weight w α + r) (coefficients P α)
  have he : basisGradeProjection (b.baseChange ℝ) ω (Finsupp.weight w α + r) (coefficients P α) = coefficients P α := hP α
  rw [he] at h
  exact F.realification.antitone (Nat.le_add_right _ _) h

include b ω hF in
theorem exists_real_adapted_representation (w : σ → ℕ) (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : P ∈ F.realification.adaptedLieSubalgebra w) :
    ∃ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w, F.realAdaptedPolynomialMap w x = P := by
  obtain ⟨x, hx⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF ⟨P, hP⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem realAdaptedCoefficientBound_iff_formal (w : σ → ℕ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.RealAdaptedCoefficientBound b ω hF w T M x ↔
      CoefficientBound (b.baseChange ℝ) T M (F.realAdaptedPolynomialMap w x) :=
  F.realAdaptedCoefficientBound_polynomial_iff b ω hF w T hT hM ⟨x⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem exists_adapted_polynomial_list_lift (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (rs : List (PolynomialGroup σ F.lowerCentralSeries_eq_bot))
    (hadapted : ∀ r ∈ rs, r.coord ∈ F.adaptedLieSubalgebra w) :
    ∃ xs : List (F.adaptedPolynomialFiltration w).Group,
      xs.map (F.adaptedFullPolynomialHom w) = rs := by
  induction rs with
  | nil => exact ⟨[], rfl⟩
  | cons r rs ih =>
    obtain ⟨xs, hxs⟩ := ih (fun x hx => hadapted x (List.mem_cons_of_mem r hx))
    let x : (F.adaptedPolynomialFiltration w).Group := ⟨⟨r.coord, hadapted r (List.mem_cons_self)⟩⟩
    have hx : F.adaptedFullPolynomialHom w x = r := NilpotentLieBCHGroup.ext rfl
    exact ⟨x :: xs, by rw [List.map_cons, hx, hxs]⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalInductionTerminal
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ κ K L : Type*} [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L]

variable [Fintype κ]

theorem basisPolynomialLift_coefficients (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (x : K) (α : σ →₀ ℕ) :
    coefficients (basisPolynomialLift b S x) α =
      ∑ k, b.equivFun x k • coefficients (S k) α := by
  classical
  change realCoefficient α (b.constr ℝ S x) = _
  rw [Basis.constr_apply_fintype (S := ℝ)]
  simp only [map_sum, map_smul, realCoefficient_apply]

theorem realLinearPolynomial_mem_of_basis (b : Basis κ ℝ K)
    (S : K →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (W : (σ →₀ ℕ) → Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (S (b k)) α ∈ W α) (x : K) (α : σ →₀ ℕ) :
    coefficients (S x) α ∈ W α := by
  classical
  change ((realCoefficient α).comp S) x ∈ W α
  rw [← b.sum_repr x, map_sum]
  apply (W α).sum_mem
  intro k _
  rw [map_smul]
  exact (W α).smul_mem _ (h k α)

theorem basisPolynomialLift_mem (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (W : (σ →₀ ℕ) → Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (S k) α ∈ W α) (x : K) (α : σ →₀ ℕ) :
    coefficients (basisPolynomialLift b S x) α ∈ W α :=
  realLinearPolynomial_mem_of_basis b (basisPolynomialLift b S) W
    (fun k α => by rw [basisPolynomialLift_basis]; exact h k α) x α

theorem basisPolynomialLift_residual (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (I : K →ₗ[ℝ] ℝ ⊗[ℚ] L)
    (W : Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (S k - monomial 0 (I (b k))) α ∈ W)
    (x : K) (α : σ →₀ ℕ) :
    coefficients (basisPolynomialLift b S x - monomial 0 (I x)) α ∈ W := by
  let D : K →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
    basisPolynomialLift b S - (realMonomial 0).comp I
  have hD : ∀ k β, coefficients (D (b k)) β ∈ W := by
    intro k β
    simp only [D, LinearMap.sub_apply, LinearMap.comp_apply, realMonomial_apply,
      basisPolynomialLift_basis]
    exact h k β
  have hx := realLinearPolynomial_mem_of_basis b D (fun _ => W) hD x α
  simp only [D, LinearMap.sub_apply, LinearMap.comp_apply, realMonomial_apply] at hx
  exact hx

theorem basisPolynomialLift_shiftedGraded {ι : Type*} (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (w : ι → ℕ) (v : σ → ℕ) (r : ℕ)
    (h : ∀ k, S k ∈ shiftedGradedPolynomialSubmodule e w v r) (x : K) :
    basisPolynomialLift b S x ∈ shiftedGradedPolynomialSubmodule e w v r := by
  intro α
  let W := fun β : σ →₀ ℕ => LinearMap.ker
    (basisGradeProjection e w (Finsupp.weight v β + r) - LinearMap.id)
  have hm := basisPolynomialLift_mem b S W (fun k β => by
    change basisGradeProjection e w (Finsupp.weight v β + r) (coefficients (S k) β) -
      coefficients (S k) β = 0
    exact sub_eq_zero.mpr (h k β)) x α
  exact sub_eq_zero.mp hm

theorem basisPolynomialLift_coefficientBound {ι : Type*} (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (T : σ → ℝ) (M : ℝ)
    (h : ∀ k, CoefficientBound e T M (S k)) (x : K) :
    CoefficientBound e T ((Fintype.card κ : ℝ) * M * ‖b.equivFun x‖)
      (basisPolynomialLift b S x) := by
  classical
  intro α i
  rw [basisPolynomialLift_coefficients]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  calc
    |∑ k, b.equivFun x k * e.repr (coefficients (S k) α) i| ≤
        ∑ k, |b.equivFun x k * e.repr (coefficients (S k) α) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : κ, ‖b.equivFun x‖ * (M / monomialScale T α) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm (b.equivFun x) k) (h k α i)
        (abs_nonneg _) (norm_nonneg _)
    _ = ((Fintype.card κ : ℝ) * M * ‖b.equivFun x‖) / monomialScale T α := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem basisPolynomialLift_coefficientGrid {ι : Type*} (b : Basis κ ℝ K)
    (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (l m : ℕ) (hR : ∀ k, CoefficientGrid e m (R k))
    (x : K) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    CoefficientGrid e (m * l) (basisPolynomialLift b R x) := by
  intro α
  have h := realDenominatorGrid_linear_combination l m (b.equivFun x)
    (fun k i => e.repr (coefficients (R k) α) i) hx (fun k => hR k α)
  convert h using 1
  ext i
  rw [basisPolynomialLift_coefficients]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply,
    Finset.sum_apply, Pi.smul_apply]

end VectorPolynomial

namespace NilpotentLieBCHGroup

variable {σ κ K L : Type*} [Fintype κ] [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥}

theorem PolynomialLiftSystemMod.extend_basis (b : Basis κ ℝ K)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (h : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R) :
    PolynomialLiftSystemMod (V.restrictScalars ℚ) P
      (basisPolynomialLift b S) (basisPolynomialLift b R) := by
  let D := basisPolynomialLift b S -
    (dualAdjointRealLinearEquiv P).toLinearMap.comp (basisPolynomialLift b R)
  intro x α
  apply realLinearPolynomial_mem_of_basis b D (fun _ => V) _ x α
  intro k β
  change coefficients (basisPolynomialLift b S (b k) -
    dualAdjoint P (basisPolynomialLift b R (b k))) β ∈ V
  rw [basisPolynomialLift_basis, basisPolynomialLift_basis]
  exact h k β

omit [Fintype κ] in
theorem basisPolynomialLift_adjoint (b : Basis κ ℝ K) (A : PolynomialGroup σ hnil)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    basisPolynomialLift b (fun k => dualAdjoint A (S k)) =
      (dualAdjointRealLinearEquiv A).toLinearMap.comp (basisPolynomialLift b S) := by
  apply b.ext
  intro k
  simp only [basisPolynomialLift_basis, LinearMap.comp_apply,
    LinearEquiv.coe_coe, dualAdjointRealLinearEquiv_apply]

theorem basisPolynomialLift_adjoint_residual (b : Basis κ ℝ K)
    (A : PolynomialGroup σ hnil) (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (I : K →ₗ[ℝ] ℝ ⊗[ℚ] L) (W : Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (dualAdjoint A (S k) - monomial 0 (I (b k))) α ∈ W)
    (x : K) (α : σ →₀ ℕ) :
    coefficients (dualAdjoint A (basisPolynomialLift b S x) - monomial 0 (I x)) α ∈ W := by
  have hx := basisPolynomialLift_residual b (fun k => dualAdjoint A (S k)) I W h x α
  rw [basisPolynomialLift_adjoint] at hx
  exact hx

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L μ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]

structure FormalStageGeometry (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V)) (j H : ℕ) where
  bracketSpace : Submodule ℚ L
  currentSpace : Submodule ℚ L
  bracketRank : ℕ
  currentRank : ℕ
  bracketBasis : Basis (Fin bracketRank) ℚ bracketSpace
  currentBasis : Basis (Fin currentRank) ℚ currentSpace
  bracket_grade : ∀ x ∈ bracketSpace.baseChange ℝ,
    basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x
  bracket_U : bracketSpace.baseChange ℝ ≤ U.toSubmodule
  bracket_K : j = 2 → bracketSpace.baseChange ℝ ≤ K.baseChange ℝ
  bracket_V : 2 < j → bracketSpace.baseChange ℝ ≤ V.baseChange ℝ
  bracket_complete : ∀ x ∈ U,
    basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x →
    (j = 2 → x ∈ K.baseChange ℝ) → (2 < j → x ∈ V.baseChange ℝ) →
    x ∈ bracketSpace.baseChange ℝ
  current_grade : ∀ x ∈ currentSpace.baseChange ℝ,
    basisGradeProjection (b.baseChange ℝ) w j x = x
  current_U : currentSpace.baseChange ℝ ≤ U.toSubmodule
  current_projection : ∀ x ∈ U, basisGradeProjection (b.baseChange ℝ) w j x ∈ currentSpace.baseChange ℝ
  bracket_matrix_height : ∀ i z,
    RationalHeightLE (bracketSystemMatrix bracketBasis f (fun z => (eK z : L)) i z) H
  current_matrix_height : ∀ i z, RationalHeightLE (subspaceQuotientMatrix currentBasis f i z) H
  bracket_basis_height : ∀ i z, RationalHeightLE (b.repr (bracketBasis z : L) i) H
  current_basis_height : ∀ i z, RationalHeightLE (b.repr (currentBasis z : L) i) H

theorem FormalInductionState.bracket_source {s j H : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
    {eK : Basis κ ℚ K} {f : Basis ι ℚ (L ⧸ V)} {T : σ → ℝ} {p : ℝ}
    (X : F.FormalInductionState b w U V K eK T j p)
    (G : FormalStageGeometry b w U V K eK f j H)
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule) (hj : 2 ≤ j) :
    ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients X.P.coord α) ∈
      G.bracketSpace.baseChange ℝ := by
  intro α
  apply G.bracket_complete _ (hU _ _ (X.mem_U α))
  · exact basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j - 1} _
  · intro hj2
    subst j
    exact X.horizontal α
  · intro hj2
    exact X.lower_log α (j - 1) (by omega) (by omega)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepDropTerminalContainment
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem stepDropBracketKernel_baseChange [Fintype κ]
    (K V : Submodule ℚ L) (e : Basis κ ℚ K) :
    (stepDropBracketKernel K V).baseChange ℝ = stepDropBracketKernel (K.baseChange ℝ) (V.baseChange ℝ) := by
  apply le_antisymm
  · intro x hx k hk
    exact lie_mem_real_baseChange (stepDropBracketKernel K V) K V
      (fun _ ha _ hb => ha _ hb) hx hk
  · intro x hx
    rw [stepDropBracketKernel_eq_iInf K V e, real_baseChange_iInf]
    rw [Submodule.mem_iInf]
    intro z
    rw [realification_comap]
    change (rightLieLinear (R := ℚ) (e z : L)).baseChange ℝ x ∈ V.baseChange ℝ
    rw [rightLieLinear_baseChange, rightLieLinear_apply]
    exact hx _ (Submodule.tmul_mem_baseChange_of_mem 1 (e z).property)

theorem stepDropSubmodule_baseChange [Fintype κ]
    (b : Basis ι ℚ L) (w : ι → ℕ) (U : LieSubalgebra ℚ L)
    (V K : Submodule ℚ L) (e : Basis κ ℚ K) :
    (stepDropSubmodule b w U V K).baseChange ℝ =
      stepDropSubmodule (b.baseChange ℝ) w (realificationLieSubalgebra U) (V.baseChange ℝ) (K.baseChange ℝ) := by
  simp only [stepDropSubmodule, realification_inf, realification_comap,
    stepDropBracketKernel_baseChange K V e, basisGradeProjection,
    basisCoordinateProjection_baseChange, LinearMap.baseChange_sub, LinearMap.baseChange_id,
    realificationLieSubalgebra_toSubmodule]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def stepDropSystem (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) :
    L →ₗ[ℚ] (StepDropRow υ χ κ ν → ℚ) :=
  LinearMap.pi fun
    | .inl i => (fU.coord i).comp U.toSubmodule.mkQ
    | .inr (.inl i) => (fK.coord i).comp (K.mkQ.comp (basisGradeProjection b w 1))
    | .inr (.inr (.inl z)) => (fV.coord z.2).comp
        (V.mkQ.comp ((rightLieLinear (eK z.1 : L)).comp (basisGradeProjection b w 1)))
    | .inr (.inr (.inr i)) => (fV.coord i).comp
        (V.mkQ.comp (LinearMap.id - basisGradeProjection b w 1))

theorem stepDropSystem_ker [Fintype κ] (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) :
    LinearMap.ker (stepDropSystem b w U V K fU fK fV eK) = stepDropSubmodule b w U V K := by
  ext x
  rw [LinearMap.mem_ker, mem_stepDropSubmodule]
  constructor
  · intro hx
    have hU := (stepDrop_quotient_mem_iff U.toSubmodule fU x).mpr
      (fun i => congrFun hx (.inl i))
    have hK := (stepDrop_quotient_mem_iff K fK (basisGradeProjection b w 1 x)).mpr
      (fun i => congrFun hx (.inr (.inl i)))
    have hbr : basisGradeProjection b w 1 x ∈ stepDropBracketKernel K V := by
      rw [stepDropBracketKernel_eq_iInf K V eK, Submodule.mem_iInf]
      intro z
      exact (stepDrop_quotient_mem_iff V fV _).mpr
        (fun i => congrFun hx (.inr (.inr (.inl (z, i)))))
    have hV := (stepDrop_quotient_mem_iff V fV (x - basisGradeProjection b w 1 x)).mpr
      (fun i => congrFun hx (.inr (.inr (.inr i))))
    exact ⟨hU, hK, hbr, hV⟩
  · rintro ⟨hU, hK, hbr, hV⟩
    funext i
    rcases i with i | i | ⟨z, i⟩ | i
    · exact (stepDrop_quotient_mem_iff U.toSubmodule fU x).mp hU i
    · exact (stepDrop_quotient_mem_iff K fK _).mp hK i
    · exact (stepDrop_quotient_mem_iff V fV _).mp (hbr (eK z) (eK z).property) i
    · exact (stepDrop_quotient_mem_iff V fV _).mp hV i

theorem stepDropSystem_basis_height (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H B : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (hbr : ∀ i j z, RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) B)
    (i : StepDropRow υ χ κ ν) (j : μ) :
    RationalHeightLE (stepDropSystem b w U V K fU fK fV eK (b j) i) (max H B) := by
  classical
  have hp : basisGradeProjection b w 1 (b j) = if w j = 1 then b j else 0 :=
    basisCoordinateProjection_basis b {i | w i = 1} j
  have hzero := rationalHeightLE_zero (hH.trans (Nat.le_max_left H B))
  rcases i with i | i | ⟨z, i⟩ | i
  · exact (hU i j).mono (Nat.le_max_left H B)
  · change RationalHeightLE (fK.repr (K.mkQ (basisGradeProjection b w 1 (b j))) i) _
    rw [hp]
    split_ifs
    · exact (hK i j).mono (Nat.le_max_left H B)
    · simpa only [map_zero, Finsupp.zero_apply] using hzero
  · change RationalHeightLE (fV.repr (V.mkQ ⁅basisGradeProjection b w 1 (b j), (eK z : L)⁆) i) _
    rw [hp]
    split_ifs
    · exact (hbr i j z).mono (Nat.le_max_right H B)
    · simpa only [zero_lie, map_zero, Finsupp.zero_apply] using hzero
  · change RationalHeightLE (fV.repr (V.mkQ (b j - basisGradeProjection b w 1 (b j))) i) _
    rw [hp]
    split_ifs
    · simpa only [sub_self, map_zero, Finsupp.zero_apply] using hzero
    · simpa only [sub_zero] using (hV i j).mono (Nat.le_max_left H B)

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
theorem polynomial_lift_matching_remainder (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ)
    (X Y : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hX : ∀ α, coefficients X α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hmatch : ∀ α, coefficients
      (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) X - Y) α ∈ V) :
    ∀ α, coefficients (X - Y) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro α
  rw [map_sub, Finsupp.sub_apply]
  apply F.real_matching_grade_remainder b w hlayers V hV j _ _ (hX α)
  have h := hmatch α
  simpa only [map_sub, Finsupp.sub_apply, coefficients_map, LinearMap.restrictScalars_apply] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFormalCurrentLayerStep
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem current_derivative_polynomials_separate
    {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (V : Submodule ℚ L) (f : Basis ι ℚ (L ⧸ V))
    {l : ℕ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, ‖realQuotientCoordinateMap f (coefficients (S i) α)‖ ≤
      Real.exp p / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈
      realDenominatorGrid l)
    (hsum : ∀ i α, coefficients (S i + R i) α ∈ V.baseChange ℝ) :
    ∀ i α, coefficients (S i) α ∈ V.baseChange ℝ ∧
      coefficients (R i) α ∈ V.baseChange ℝ := by
  have hTone (i : σ) : 1 ≤ T i :=
    (Real.one_le_exp (separationBudget_nonneg hp)).trans (hT i)
  intro i α
  have hscale : Real.exp (separationBudget p) ≤ T i * monomialScale T α :=
    (hT i).trans (le_mul_of_one_le_right (zero_le_one.trans (hTone i))
      (one_le_monomialScale T hTone α))
  have hnorm : ‖realQuotientCoordinateMap f (coefficients (S i) α)‖ ≤
      Real.exp p / Real.exp (separationBudget p) :=
    (hsmall i α).trans (div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.exp_pos _) hscale)
  have hzero : realQuotientCoordinateMap f (coefficients (S i) α) +
      realQuotientCoordinateMap f (coefficients (R i) α) = 0 := by
    have h := (realQuotientCoordinateMap_eq_zero_iff f _).mpr (hsum i α)
    simpa only [map_add, Finsupp.add_apply] using h
  obtain ⟨hS, hR⟩ := controlled_zero_sum_separation hl hp hι hlp _ _ hnorm (hrational i α) hzero
  exact ⟨(realQuotientCoordinateMap_eq_zero_iff f _).mp hS,
    (realQuotientCoordinateMap_eq_zero_iff f _).mp hR⟩

theorem current_derivative_terms_vanish_of_invariant_polynomial
    {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (V : Submodule ℚ L) (f : Basis ι ℚ (L ⧸ V))
    {l : ℕ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : ∀ α, coefficients P α ∈ V.baseChange ℝ)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, ‖realQuotientCoordinateMap f (coefficients (S i) α)‖ ≤
      Real.exp p / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈
      realDenominatorGrid l)
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P - S i - R i) α ∈ V.baseChange ℝ) :
    ∀ i α, coefficients (S i) α ∈ V.baseChange ℝ ∧
      coefficients (R i) α ∈ V.baseChange ℝ := by
  apply current_derivative_polynomials_separate V f hl hp hι hlp T hT S R hsmall hrational
  intro i α
  have hD : coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P) α ∈
      V.baseChange ℝ := by
    rw [coefficients_pderiv]
    exact ((V.baseChange ℝ).restrictScalars ℚ).smul_mem _ (hP _)
  have h := (V.baseChange ℝ).sub_mem hD (hsplit i α)
  simp only [map_sub, Finsupp.sub_apply] at h
  simp only [map_add, Finsupp.add_apply]
  convert h using 1
  abel

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem eval₂_lie_mem_of_coefficients {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    (V : Submodule ℝ L) (P : VectorPolynomial σ ℚ L) (x : L)
    (hP : ∀ α, ⁅coefficients P α, x⁆ ∈ V) (t : σ → ℝ) : ⁅eval₂ t P, x⁆ ∈ V := by
  classical
  rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum, eval₂_monomial, sum_lie, smul_lie]
  exact V.sum_mem (fun α _ => V.smul_mem _ (hP α))

namespace NilpotentLieFiltration

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem formal_current_layer_derivative_equation (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) {j : ℕ} (hj : 2 ≤ j)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hU : ∀ α, coefficients P.coord α ∈ U)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : PolynomialDerivativeSystem P small rational extra) :
    ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V := by
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hUvalue (t : σ → ℝ) : eval₂ t P.coord ∈ Uq :=
    (eval₂_mem_iff_coefficients U.toSubmodule P.coord).mpr hU t
  apply F.real_current_layer_polynomial_derivative_equation b w hlayers hs Uq V K hUV hV hj
    P.coord hUvalue hK hlower
    (fun t k hk => eval₂_lie_mem_of_coefficients _ P.coord k (fun α => hbracket α k hk) t)
    small rational hrational (fun i t => eval₂ t (extra i))
    (fun i t => realPolynomialJet i t P)
    (fun i t => realPolynomialJet_base i t P) (fun i t => realPolynomialJet_tangent i t P)
  · intro i t
    have h := (eval₂_mem_iff_coefficients _ _).mpr (hextra i) t
    simpa only [map_sub, eval₂_map] using h
  · intro i t
    simpa only [realPolynomialJet_baseHom] using
      PolynomialDerivativeSystem.real_evaluation P small rational extra hsystem i t

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
theorem formal_current_layer_derivative_equation_mod (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) {j : ℕ} (hj : 2 ≤ j)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hU : ∀ α, coefficients P.coord α ∈ U)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational extra) :
    ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V := by
  obtain ⟨error, herror, hexact⟩ := PolynomialDerivativeSystemMod.exact_system
    (V.restrictScalars ℚ) P small rational extra hsystem
  apply F.formal_current_layer_derivative_equation b w hlayers hs U V K hUV hV hj
    P hU hK hlower hbracket small rational (fun i => extra i + error i) hrational _ hexact
  intro i α
  have heq : extra i + error i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord) =
      (extra i - VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) + error i := by abel
  rw [heq, map_add, Finsupp.add_apply]
  exact Submodule.add_mem _ (hextra i α) (Submodule.mem_sup_left (herror i α))

theorem formal_current_layer_correction_preserves_lifts_mod {κ : Type*} (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℚ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : κ → ℝ ⊗[ℚ] L)
    (hSR : PolynomialLiftSystemMod V P S R)
    (hS : ∀ t α, coefficients (S t - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1))
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1)) :
    PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹)
        (fun t => dualAdjoint A⁻¹ (S t)) (fun t => dualAdjoint B (R t)) ∧
      ∀ t α,
        coefficients (dualAdjoint A⁻¹ (S t) - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1) ∧
        coefficients (dualAdjoint B (R t) - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1) := by
  refine ⟨PolynomialLiftSystemMod.remove U V hUV P A B hAU S R hSR, ?_⟩
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ F.realification.layer j :=
    (coefficientSubmodule (F.realification.layer j)).neg_mem hA
  intro t α
  have hleft := F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j A⁻¹ hAi (S t)
  have hright := F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j B hB (R t)
  constructor
  · have h := (V ⊔ F.realification.layer (j + 1)).add_mem (Submodule.mem_sup_right (hleft α)) (hS t α)
    convert h using 1
    simp only [map_sub, Finsupp.sub_apply]
    abel
  · have h := (V ⊔ F.realification.layer (j + 1)).add_mem (Submodule.mem_sup_right (hright α)) (hR t α)
    convert h using 1
    simp only [map_sub, Finsupp.sub_apply]
    abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem pderiv_coordinate_grid (q : L →ₗ[ℚ] (ι → ℝ)) (P : VectorPolynomial σ ℚ L) (l : ℕ)
    (hP : ∀ α, q (coefficients P α) ∈ realDenominatorGrid l) (i : σ) (α : σ →₀ ℕ) :
    q (coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L P) α) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hP (α + Finsupp.single i 1)
  rw [coefficients_pderiv, map_smul]
  refine ⟨fun n => (α i + 1 : ℤ) * z n, ?_⟩
  funext n
  have hzn : (z n : ℝ) = (l : ℝ) * q (coefficients P (α + Finsupp.single i 1)) n := congrFun hz n
  change (((α i + 1 : ℤ) * z n : ℤ) : ℝ) =
    (l : ℝ) * (((α i + 1 : ℚ) : ℝ) * q (coefficients P (α + Finsupp.single i 1)) n)
  simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_one, hzn]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem formal_correction_sub_mem_layer (j : ℕ)
    (P A B : PolynomialGroup σ F.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.layer j) :
    ∀ α, coefficients ((A⁻¹ * P * B⁻¹).coord - P.coord) α ∈ F.layer j := by
  have h := F.polynomialFiltration.correction_removal_preserves_lower_layers (j := j + 1)
    A P B (by rw [Nat.add_sub_cancel]; exact hA)
    (by rw [Nat.add_sub_cancel]; exact hB) (by omega)
  rw [Nat.add_sub_cancel] at h
  exact h

theorem formal_correction_preserves_bracket_remainder (V : Submodule ℚ L) (j : ℕ)
    (P A B : PolynomialGroup σ F.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.layer j)
    (x : L) (hbracket : ∀ α, ⁅coefficients P.coord α, x⁆ ∈ V ⊔ F.layer (j + 1)) :
    ∀ α, ⁅coefficients (A⁻¹ * P * B⁻¹).coord α, x⁆ ∈ V ⊔ F.layer (j + 1) := by
  intro α
  have hx : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hdiff := F.formal_correction_sub_mem_layer j P A B hA hB α
  have hlie := F.lie_mem hdiff hx
  have h := (V ⊔ F.layer (j + 1)).add_mem (Submodule.mem_sup_right hlie) (hbracket α)
  simp only [map_sub, Finsupp.sub_apply, sub_lie, sub_add_cancel] at h
  exact h

variable {μ : Type*} (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_correction_preserves_projected_log {j : ℕ}
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j) :
    ∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ)
        (A⁻¹ * P * B⁻¹).coord =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord := by
  intro d hd
  apply F.polynomial_grade_eq_of_sub_mem_next b w hlayers d
  intro α
  exact F.realification.antitone (Nat.succ_le_of_lt hd)
    (F.realification.formal_correction_sub_mem_layer j P A B hA hB α)

include hlayers in
theorem formal_correction_advances_log_conditions {j : ℕ} (hj : 2 ≤ j)
    (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (hcurrent : ∀ α, coefficients (VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (A⁻¹ * P * B⁻¹).coord) α ∈ V) :
    (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ K) ∧
      ∀ α d, 2 ≤ d → d < j + 1 →
        basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ V := by
  have hbelow := F.formal_correction_preserves_projected_log b w hlayers P A B hA hB
  have hcoef (d : ℕ) (hd : d < j) (α : σ →₀ ℕ) :
      basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) =
        basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) := by
    have h := congrArg (fun X : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients X α) (hbelow d hd)
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
    exact h
  constructor
  · intro α
    rw [hcoef 1 (by omega)]
    exact hK α
  · intro α d hd hdj
    rcases lt_or_eq_of_le (show d ≤ j by omega) with hlt | rfl
    · rw [hcoef d hlt]
      exact hlower α d hd hlt
    · have h := hcurrent α
      simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
      exact h

include hlayers in
theorem formal_correction_preserves_horizontal_extra (hs : 2 ≤ s) {j : ℕ} (hj : 2 ≤ j)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    ∀ i α, coefficients (dualAdjoint A⁻¹ (extra i) - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (A⁻¹ * P * B⁻¹).coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have hlow := F.formal_correction_preserves_projected_log b w hlayers P A B hA hB 1 (by omega)
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ F.realification.layer j :=
    (coefficientSubmodule (F.realification.layer j)).neg_mem hA
  intro i α
  rw [← pderiv_map, hlow, pderiv_map]
  have hdiff := F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j A⁻¹ hAi (extra i)
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem
    (Submodule.mem_sup_right (hdiff α)) (hextra i α)
  convert h using 1
  simp only [map_sub, Finsupp.sub_apply]
  abel

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ReducedSquareCoefficientCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem reducedSquareDifference_basis_height (a : ReducedSquareBasisIndex s ω) (i : ι) :
    RationalHeightLE (e.repr (F.reducedSquareDifference (F.reducedSquareBasis e ω hF a)) i) 1 := by
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareDifference_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl j =>
    rw [F.adaptedSquareBasis_inl, sub_self, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl
  | inr j =>
    rw [F.adaptedSquareBasis_inr, sub_zero]
    exact basis_repr_height_one e j.val i

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FirstCoefficientLatticeCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_lattice_ready_firstCoefficient_basis
    {σ ι E : Type*} [AddCommGroup E] [Module ℝ E] {d : ℕ}
    (ω : ι → ℕ) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (b : Basis (Fin d) ℝ E) :
    ∃ (e : Equiv.Perm (Fin d)) (a : ℕ), a ≤ d ∧
      (∀ i, i.val < a ↔ (rows (e i)).val.1 = 0) ∧
      ∀ (f : E ≃ₗ[ℝ] E),
        (∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
          LinearMap.toMatrix b b f.toLinearMap i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j) →
        let b' := b.reindex e.symm
        let A := b'.equivFun.symm.trans (f.trans b'.equivFun)
        (∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0) ∧
        (∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1) ∧
        (∀ i j, i.val < a → j.val < a →
          (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j) := by
  obtain ⟨e, a, ha, hm, hz⟩ := exists_sorted_firstCoefficient_rows ω rows
  refine ⟨e, a, ha, hz, ?_⟩
  intro f hf
  dsimp only
  simp only [basis_coordinate_linearEquiv_matrix]
  have hfirst (i) (hi : i.val < a) : ω (rows (e i)).val.2 = 1 :=
    (firstCoefficientIndex_zero_iff_grade_one ω (rows (e i))).mp ((hz i).mp hi)
  exact ⟨sorted_basis_upper_zero b (fun i => ω (rows i).val.2) f.toLinearMap hf e hm,
    sorted_basis_diagonal_one b (fun i => ω (rows i).val.2) f.toLinearMap hf e,
    sorted_basis_initial_identity b (fun i => ω (rows i).val.2) f.toLinearMap hf e hfirst⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype υ] [Fintype χ] [Fintype κ] [Fintype ν]

theorem exists_stepDrop_bounded_basis (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H B : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (hbr : ∀ i j z, RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) B) :
    ∃ r : ℕ, r ≤ Fintype.card (StepDropRow υ χ κ ν) ∧
      ∃ e : Basis (Fin (Module.finrank ℚ (stepDropSubmodule b w U V K)))
        ℚ (stepDropSubmodule b w U V K),
        ∀ i j, RationalHeightLE (b.repr (e i : L) j)
          ((Fintype.card μ + 1) * rationalKernelHeight r (max H B) ^ Fintype.card μ) := by
  classical
  let P := stepDropSystem b w U V K fU fK fV eK
  have hP : ∀ i j, RationalHeightLE ((Pi.basisFun ℚ (StepDropRow υ χ κ ν)).repr (P (b i)) j) (max H B) := by
    intro i j
    change RationalHeightLE (P (b i) j) _
    exact stepDropSystem_basis_height b w U V K fU fK fV eK hH hU hK hV hbr j i
  obtain ⟨r, hr, v, hspan, hv⟩ := exists_bounded_span_kernel_generators b
    (Pi.basisFun ℚ (StepDropRow υ χ κ ν)) P b
    (hH.trans (Nat.le_max_left H B)) (basis_repr_height_one b) hP
  have hspan' : Submodule.span ℚ (Set.range v) = stepDropSubmodule b w U V K := by
    simpa only [b.span_eq, top_inf_eq, P, stepDropSystem_ker] using hspan
  have hv' : ∀ i j, RationalHeightLE (b.repr (v i) j)
      ((Fintype.card μ + 1) * rationalKernelHeight r (max H B) ^ Fintype.card μ) := by
    simpa only [mul_one] using hv
  obtain ⟨e, he⟩ := exists_bounded_submodule_basis_from_spanning b _ v hspan' hv'
  exact ⟨r, hr, e, he⟩

theorem exists_stepDrop_basis_exp_height (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (hbr : ∀ i j z, RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hrows : (Fintype.card (StepDropRow υ χ κ ν) : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ e : Basis (Fin (Module.finrank ℚ (stepDropSubmodule b w U V K)))
      ℚ (stepDropSubmodule b w U V K), ∀ i j,
      (((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 9)) ∧
      (((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + 2) ^ 9)) := by
  obtain ⟨r, hr, e, he⟩ := exists_stepDrop_bounded_basis b w U V K fU fK fV eK hH hU hK hV hbr
  have hrp : (r : ℝ) ≤ p := (Nat.cast_le.mpr hr).trans hrows
  have hb := stepDrop_basis_height_budget (Fintype.card μ) r H hp hμ hrp hHp
  refine ⟨e, fun i j => ?_⟩
  have hij : RationalHeightLE (b.repr (e i : L) j)
      ((Fintype.card μ + 1) * rationalKernelHeight r H ^ Fintype.card μ) := by
    simpa only [max_self] using he i j
  exact ⟨(Nat.cast_le.mpr hij.1).trans hb, (Nat.cast_le.mpr hij.2).trans hb⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedCoordinateExtraction
namespace OAI

section

namespace Erdos3

open Module

theorem transport_coordinate_derivative_system
    {σ E H : Type*} [Fintype σ] [DecidableEq σ]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]
    {a d : ℕ} (ha : a ≤ d) (b : Basis (Fin d) ℝ E)
    (η : (Fin a → ℝ) ≃ₗ[ℝ] H) (P : E →ₗ[ℝ] H)
    (hP : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = P x)
    (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] E) (f : E ≃ₗ[ℝ] E)
    (scale : Fin d → ℝ) (bound : ℝ)
    (D : CoordinateDerivativeSystem ha T (b.equivFun.toLinearMap.comp Y)
      (b.equivFun.symm.trans (f.trans b.equivFun)) scale bound) :
    let K := D.K.map η.toLinearMap
    K = Submodule.span ℝ (Set.range (fun j => η ((D.basisMatrix.map (Rat.castHom ℝ)).col j))) ∧
    ∃ R S : K →ₗ[ℝ] E,
      S = f.toLinearMap.comp R ∧
      (∀ x, P (R x) = x.val) ∧ (∀ x, P (S x) = x.val) ∧
      (∀ x, ‖(EuclideanSpace.equiv (Fin d) ℝ).symm
        (fun j => scale j * b.equivFun (S x) j)‖ ≤ bound * ‖η.symm x.val‖) ∧
      (∀ j, ∃ x : K, x.val = η ((D.basisMatrix.map (Rat.castHom ℝ)).col j) ∧
        b.equivFun (R x) ∈ realDenominatorGrid D.liftDenominator) ∧
      ∀ i, ∃ (s r : E) (k : K),
        Y (Pi.basisFun ℝ σ i) = s + f r + S k ∧
        b.equivFun r ∈ realDenominatorGrid D.derivativeDenominator ∧
        ‖(EuclideanSpace.equiv (Fin d) ℝ).symm
          (fun j => scale j * b.equivFun s j)‖ ≤ bound / T i := by
  let K := D.K.map η.toLinearMap
  let eK : D.K ≃ₗ[ℝ] K := η.submoduleMap D.K
  let R : K →ₗ[ℝ] E := b.equivFun.symm.toLinearMap.comp
    (D.rationalLift.comp eK.symm.toLinearMap)
  let S : K →ₗ[ℝ] E := b.equivFun.symm.toLinearMap.comp
    (D.geometricLift.comp eK.symm.toLinearMap)
  have hR (x : K) : b.equivFun (R x) = D.rationalLift (eK.symm x) :=
    b.equivFun.apply_symm_apply _
  have hS (x : K) : b.equivFun (S x) = D.geometricLift (eK.symm x) :=
    b.equivFun.apply_symm_apply _
  have heK (x : K) : (eK.symm x).val = η.symm x.val := rfl
  constructor
  · rw [D.span_eq, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, rfl⟩
  refine ⟨R, S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    apply b.equivFun.injective
    rw [hS, D.factorization]
    change b.equivFun (f (b.equivFun.symm (D.rationalLift (eK.symm x)))) =
      b.equivFun (f (R x))
    rfl
  · intro x
    rw [← hP, hR]
    have h : (fun i => D.rationalLift (eK.symm x) (Fin.castLE ha i)) =
        (eK.symm x).val := funext (D.rational_horizontal (eK.symm x))
    rw [h, heK, LinearEquiv.apply_symm_apply]
  · intro x
    rw [← hP, hS]
    have h : (fun i => D.geometricLift (eK.symm x) (Fin.castLE ha i)) =
        (eK.symm x).val := funext (D.geometric_horizontal (eK.symm x))
    rw [h, heK, LinearEquiv.apply_symm_apply]
  · intro x
    simp only [hS]
    exact D.norm_scaled (eK.symm x)
  · intro j
    obtain ⟨x, hx, hgrid⟩ := D.rational_on_basis j
    refine ⟨eK x, ?_, ?_⟩
    · change η x.val = _
      rw [hx]
    · rw [hR, LinearEquiv.symm_apply_apply]
      exact hgrid
  · intro i
    refine ⟨b.equivFun.symm (D.slow i), b.equivFun.symm (D.rational i),
      eK (D.horizontal i), ?_, ?_, ?_⟩
    · apply b.equivFun.injective
      simp only [map_add, LinearEquiv.apply_symm_apply, hS, LinearEquiv.symm_apply_apply]
      exact D.derivative_eq i
    · simpa only [LinearEquiv.apply_symm_apply] using D.derivative_grid i
    · simpa only [LinearEquiv.apply_symm_apply] using D.slow_bound i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LayerOneProjectionMatrixBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix

theorem rational_horizontal_basis_transport
    {V ι κ ν : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℚ V) (η : (κ → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] V))
    (A : Matrix ι κ ℚ)
    (hA : ∀ x, (b.baseChange ℝ).equivFun (η x) = A.map (Rat.castHom ℝ) *ᵥ x)
    (K : Submodule ℝ (κ → ℝ)) (Q : Matrix κ ν ℚ)
    (hK : K = Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col))
    (hQ : LinearIndependent ℝ (Q.map (Rat.castHom ℝ)).col)
    {H J : ℕ} (hAH : ∀ i j, RationalHeightLE (A i j) H)
    (hQJ : ∀ i j, RationalHeightLE (Q i j) J) :
    ∃ v : ν → V,
      (∀ j, (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j)) ∧
      K.map η.toLinearMap = (Submodule.span ℚ (Set.range v)).baseChange ℝ ∧
      LinearIndependent ℚ v ∧
      ∀ i j, RationalHeightLE (b.repr (v j) i) ((Fintype.card κ + 1) * (H * J) ^ Fintype.card κ) := by
  let v : ν → V := fun j => b.equivFun.symm ((A * Q).col j)
  have hvc (i : ι) (j : ν) : b.repr (v j) i = (A * Q) i j :=
    congrFun (b.equivFun.apply_symm_apply ((A * Q).col j)) i
  have hv (j : ν) : (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j) := by
    apply (b.baseChange ℝ).equivFun.injective
    rw [hA]
    funext i
    rw [Basis.equivFun_apply, Basis.baseChange_repr_tmul, hvc]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · rw [hK, Submodule.map_span, Submodule.baseChange_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨v j, ⟨j, rfl⟩, hv j⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, (hv j).symm⟩
  · have hreal : LinearIndependent ℝ (fun j => (1 : ℝ) ⊗ₜ[ℚ] v j) := by
      simpa only [hv, Function.comp_def, LinearEquiv.coe_coe] using
        hQ.map' η.toLinearMap (LinearMap.ker_eq_bot.mpr η.injective)
    apply LinearIndependent.of_comp (TensorProduct.mk ℚ ℝ V 1)
    exact LinearIndependent.restrict_scalars' ℚ hreal
  · intro i j
    rw [hvc]
    exact rationalHeightLE_matrix_mul A Q hAH hQJ i j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

universe u v

namespace Erdos3

namespace RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

variable {H : Type u} [LieRing H] [LieAlgebra ℚ H]

def optionProductMap (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) :
    H →ₗ⁅ℚ⁆ (∀ i : Option ι, optionLieSpace L₀ L i) :=
  liePiMap (optionMaps φ₀ φ)

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end


