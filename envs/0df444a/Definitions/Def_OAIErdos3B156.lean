-- Prove2me | Definitions.Def_OAIErdos3B156
-- name    : OAIErdos3B156
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T23:57:24.79343+00:00
-- url     : https://prove2.me/theorems/fa942801-d440-465b-95bc-8559bdd445f9
-- title:
--   OpenAI Erdős-3 split, definitions bundle 157 of 177
-- statement:
--   Definitions bundle 157 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B155`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 157 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.BoundedInitialStateFactorization`, `OAI.Erdos3.NilpotentLieFiltration.BoundedInitialStateFactorization.mono`, `OAI.Erdos3.NilpotentLieFiltration.CommonFactorizationSpec`, `OAI.Erdos3.NilpotentLieFiltration.CommonInitialStateSpec`, `OAI.Erdos3.NilpotentLieFiltration.CommonSymbolFactorizationSpec`, `OAI.Erdos3.NilpotentLieFiltration.CommonTerminalStateSpec`, `OAI.Erdos3.NilpotentLieFiltration.ControlledSymbolBasisChangeSpec`, `OAI.Erdos3.NilpotentLieFiltration.FastTerminalFactorization`, `OAI.Erdos3.NilpotentLieFiltration.FastTerminalFactorization.mono`, `OAI.Erdos3.NilpotentLieFiltration.FastTerminalStateSpec`, `OAI.Erdos3.NilpotentLieFiltration.FullInitialStateSpec`, `OAI.Erdos3.NilpotentLieFiltration.NormalizedTerminalFactorization`, `OAI.Erdos3.NilpotentLieFiltration.NormalizedTerminalFactorization.mono`, `OAI.Erdos3.NilpotentLieFiltration.NormalizedTerminalStateSpec`, `OAI.Erdos3.NilpotentLieFiltration.SymbolTerminalFactorization`, `OAI.Erdos3.NilpotentLieFiltration.SymbolTerminalFactorization.controlled`, `OAI.Erdos3.NilpotentLieFiltration.SymbolTerminalFactorization.mono`, `OAI.Erdos3.NilpotentLieFiltration.TerminalCompositionSpec`, `OAI.Erdos3.NilpotentLieFiltration.UnnormalizedCommonSymbolFactorizationSpec`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedBasis_change_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedBasis_change_height`, `OAI.Erdos3.NilpotentLieFiltration.associatedGradedBasis_projection`, `OAI.Erdos3.NilpotentLieFiltration.associatedGraded_projection_basis_independent`, `OAI.Erdos3.NilpotentLieFiltration.associatedGraded_submodule_basis_independent`, `OAI.Erdos3.NilpotentLieFiltration.bounded_coefficient_derivative_point`, `OAI.Erdos3.NilpotentLieFiltration.bounded_coefficient_difference_inputs`, `OAI.Erdos3.NilpotentLieFiltration.common_coefficient_derivative_system`, `OAI.Erdos3.NilpotentLieFiltration.exists_commonFactorization_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_initialState_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_symbolFactorization_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_common_terminalState_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_controlled_symbol_basis_change`, `OAI.Erdos3.NilpotentLieFiltration.exists_fast_terminalState_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_formal_stepDrop_subalgebra_factorization`, `OAI.Erdos3.NilpotentLieFiltration.exists_full_fast_quotient_bases`, `OAI.Erdos3.NilpotentLieFiltration.exists_full_initialState_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_initialFormalState_from_common`, `OAI.Erdos3.NilpotentLieFiltration.exists_initialFormalState_from_common_family`, `OAI.Erdos3.NilpotentLieFiltration.exists_normalized_terminalState_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_stepDrop_from_formal_state`, `OAI.Erdos3.NilpotentLieFiltration.exists_terminalComposition_bound`, `OAI.Erdos3.NilpotentLieFiltration.exists_uniform_formal_induction_factorization`, `OAI.Erdos3.NilpotentLieFiltration.exists_unnormalized_common_symbolFactorization_bound`, `OAI.Erdos3.NilpotentLieFiltration.gradedFrequency_top_basis_independent`, `OAI.Erdos3.NilpotentLieFiltration.gradedSymbolPolynomial_basis_independent`, `OAI.Erdos3.NilpotentLieFiltration.nativeSymbolNormalize`, `OAI.Erdos3.NilpotentLieFiltration.nativeSymbolNormalize_constant`, `OAI.Erdos3.NilpotentLieFiltration.nativeSymbolNormalize_symbol`, `OAI.Erdos3.NilpotentLieFiltration.native_symbol_basis_independent`, `OAI.Erdos3.NilpotentLieFiltration.native_symbol_grid`, `OAI.Erdos3.NilpotentLieFiltration.native_symbol_slow`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolBasis_change_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolBasis_change_height`, `OAI.Erdos3.NilpotentLieFiltration.realAdaptedGradedPolynomialHom_eq_of_symbol_eq`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientAdjoint_eq_of_symbol_eq`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientDirectionMap_eq_of_symbol_eq`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolHom_groupHom_coord`, `OAI.Erdos3.NilpotentLieFiltration.symbolPointwiseSubalgebra_basis_independent`, `OAI.Erdos3.NilpotentLieFiltration.symbolTerminalFactorization_of_graded`, `OAI.Erdos3.NilpotentLieFiltration.symbolTerminalFactorization_of_native`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_fixed_adapted_symbol_factorization_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.fixedAdaptedSymbolTransferInput`, `OAI.Erdos3.exists_derivative_difference_inputs`, `OAI.Erdos3.rational_basis_coordinates_logHeight`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B056
import Definitions.Def_OAIErdos3B125
import Definitions.Def_OAIErdos3B175

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TerminalControlledFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem exists_full_fast_quotient_bases
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hdim : 2 * (Fintype.card ι : ℝ) + (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, H ≤ H' ∧ 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 294) ∧
      ∃ dU : ℕ, dU ≤ Fintype.card ι ∧
      ∃ fU : Basis (Fin dU) ℚ (F.AssociatedGraded ⧸ (F.fullFastGradedDiagonal W).toSubmodule),
      ∃ dV : ℕ, dV ≤ Fintype.card ι ∧
      ∃ fV : Basis (Fin dV) ℚ (F.AssociatedGraded ⧸ F.fullFastGradedRelative e ω hF W),
        (∀ i j, RationalHeightLE (fU.repr ((F.fullFastGradedDiagonal W).toSubmodule.mkQ
          (F.associatedGradedBasis e ω hF j)) i) H') ∧
        (∀ i j, RationalHeightLE (fV.repr ((F.fullFastGradedRelative e ω hF W).mkQ
          (F.associatedGradedBasis e ω hF j)) i) H') := by
  have hn0 : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hm0 : 0 ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hm : (Fintype.card κ : ℝ) ≤ p := by linarith
  have hUcard : (Fintype.card (κ ⊕ TopGradedBasisIndex s ω) : ℝ) ≤ p := by
    have h := Nat.cast_le (α := ℝ).mpr (fullFastDiagonalGenerators_card (κ := κ) (s := s) ω)
    push_cast at h
    linarith
  obtain ⟨HU, hHU, hHUp, dU, hdU, fU, hfU⟩ := exists_submodule_quotient_basis_exp
    (F.associatedGradedBasis e ω hF) (F.fullFastGradedDiagonal W).toSubmodule
    (F.fullFastDiagonalGenerators e ω hF v) (F.fullFastDiagonalGenerators_span e ω hF W v hspan)
    hH (F.fullFastDiagonalGenerators_height e ω hF v hH hv) hp hUcard hHp
  have hn : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p := by
    have hcard : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
      (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
    have h := Nat.cast_le (α := ℝ).mpr hcard
    push_cast at h
    linarith
  have hq : (Fintype.card (QuotientTopBasisIndex s ω) : ℝ) ≤ p := by
    have h := Nat.cast_le (α := ℝ).mpr
      (Fintype.card_subtype_le (fun i : ι => ¬ s + 1 ≤ ω i))
    linarith
  obtain ⟨Hz, hHz, hHzp, z, hz, hzh⟩ :=
    F.exists_full_fast_relative_generators_exp e ω hF W v hspan hH hv hp hn hm hq hHp
  obtain ⟨HV, hHV, hHVp, dV, hdV, fV, hfV⟩ := exists_submodule_quotient_basis_exp
    (F.associatedGradedBasis e ω hF) (F.fullFastGradedRelative e ω hF W) z hz hHz hzh
    (by positivity : 0 ≤ (p + 2) ^ 40)
    (hm.trans (le_power_budget hp (by decide : 1 ≤ 40))) hHzp
  have hVbudget : (HV : ℝ) ≤ Real.exp ((p + 2) ^ 294) :=
    exponential_budget_comp hp (by positivity) 40 7 le_rfl hHVp
  have hUbudget : (HU : ℝ) ≤ Real.exp ((p + 2) ^ 294) := hHUp.trans
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 7 ≤ 294)))
  have hbudget : (H : ℝ) ≤ Real.exp ((p + 2) ^ 294) :=
    hHp.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 294)))
  refine ⟨max H (max HU HV), Nat.le_max_left _ _, hH.trans (Nat.le_max_left _ _), ?_,
    dU, hdU, fU, dV, hdV, fV, ?_, ?_⟩
  · rw [Nat.cast_max, Nat.cast_max]
    exact max_le hbudget (max_le hUbudget hVbudget)
  · intro i j
    exact (hfU i j).mono ((Nat.le_max_left HU HV).trans (Nat.le_max_right _ _))
  · intro i j
    exact (hfV i j).mono ((Nat.le_max_right HU HV).trans (Nat.le_max_right _ _))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_induction_factorization (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧
    ∀ {L μ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (G : ∀ j, 2 ≤ j → j ≤ s → FormalStageGeometry b w U V K eK f j H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hRanks : ∀ j hj hjs, ((G j hj hjs).bracketRank : ℝ) ≤ p ∧
      ((G j hj hjs).currentRank : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + E) ^ E) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T 2 p),
    ∃ q : ℝ, p ≤ q ∧ 0 ≤ q ∧ q ≤ (p + E) ^ E ∧
      ∃ W : F.FormalInductionRun b w U V K eK T X.P (s - 1) q,
        (W.denominator : ℝ) ≤ Real.exp ((p + E) ^ E) ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + E) ^ E) ∧ W.denominator ∣ m ∧
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + E) ^ E)) W.left.prod.coord ∧
          CoefficientGrid (b.baseChange ℝ) m W.right.prod.coord ∧
          F.FormalCorrectionProperty b w U W.left.prod ∧
          F.FormalCorrectionProperty b w U W.right.prod := by
  obtain ⟨D, _, hiteration⟩ := exists_uniform_formal_induction_iteration s
  obtain ⟨C, _, hproducts⟩ := exists_formal_induction_run_product_controls s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D
  obtain ⟨E, hE, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C C) ^ C)
  refine ⟨E, hE, ?_⟩
  intro L μ ι κ σ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV eK f hK H hH G
    hKernelBasis hQuotient hStructure p hp hμ hι hκ hσ hRanks hsp hHp T hT X
  let t := (p + D) ^ D
  let z := (t + C) ^ C
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have htotal : t + z ≤ (p + E) ^ E := by
    simpa [Q, t, z, Polynomial.eval₂_pow] using hbudget p hp
  have htcap : t ≤ (p + E) ^ E := by linarith
  have hzcap : z ≤ (p + E) ^ E := by linarith
  have hT' : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr htcap).trans (hT i)
  obtain ⟨q, hpq, hq, hqt, W, hWden⟩ :=
    hiteration F b w hF hgraded hs U V K hUV hU hV eK f hK hH G
      hKernelBasis hQuotient hStructure hp hμ hι hκ hσ hRanks hsp hHp T hT' X
  have hpt : p ≤ t := hpq.trans hqt
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨m, hm, hmp, hdm, hleft, hright, hleftGood, hrightGood⟩ :=
    hproducts F b w hF hgraded hTpos (Nat.sub_le s 1) W hH hStructure ht hqt
      (hμ.trans hpt) (hσ.trans hpt) (hHp.trans (Real.exp_le_exp.mpr hpt)) hWden
  exact ⟨q, hpq, hq, hqt.trans htcap, W,
    hWden.trans (Real.exp_le_exp.mpr htcap), m, hm,
    hmp.trans (Real.exp_le_exp.mpr hzcap), hdm,
    hleft.mono _ T hTpos (Real.exp_le_exp.mpr hzcap), hright, hleftGood, hrightGood⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_stepDrop_subalgebra_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ υ χ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (_hU : BasisGradedSubmodule b w U.toSubmodule) (_hV : BasisGradedSubmodule b w V)
    (η : L →ₗ[ℚ] ℚ) (_hη : ∀ x ∈ V, basisGradeProjection b w s x = x → η x = 0)
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (G : ∀ j, 2 ≤ j → j ≤ s →
      FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hQuotientU : ∀ i z, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b z)) i) H)
    (_hQuotientK : ∀ i z, RationalHeightLE (fK.repr (K.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hυ : (Fintype.card υ : ℝ) ≤ p)
    (_hχ : (Fintype.card χ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hRanks : ∀ j hj hjs, ((G j hj hjs).bracketRank : ℝ) ≤ p ∧
      ((G j hj hjs).currentRank : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : F.FormalInductionState b w (realificationLieSubalgebra U) V K eK T 2 p),
    ∃ Z : LieSubalgebra ℚ L, BasisGradedSubmodule b w Z.toSubmodule ∧
      (∀ x ∈ Z, η (basisGradeProjection b w s x) = 0) ∧
      ∃ e : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
        (∀ i j, ((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        ∃ A P B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          A * P * B = X.P ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) A ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) B ∧
          coefficients P.coord 0 = 0 ∧
          P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
          (∀ α, coefficients P.coord α ∈ realificationLieSubalgebra Z) ∧
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A.coord ∧
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            CoefficientGrid (b.baseChange ℝ) m B.coord := by
  obtain ⟨E, hE, hfactor⟩ := exists_uniform_formal_induction_factorization s
  obtain ⟨D, hD, hbasis⟩ := exists_stepDrop_basis_uniform_budget
  let C := max E D
  refine ⟨C, hE.trans (Nat.le_max_left E D), ?_⟩
  intro L μ υ χ ι κ σ _ _ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV η hη eK f
    fU fK hK H hH G hKernelBasis hQuotient hQuotientU hQuotientK hStructure
    p hp hμ hυ hχ hι hκ hσ hRanks hsp hHp T hT X
  have hEC : (p + E) ^ E ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_left E D)
  have hDC : (p + D) ^ D ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_right E D)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hRU : BasisGradedSubmodule (b.baseChange ℝ) w (realificationLieSubalgebra U).toSubmodule :=
    hU.baseChange b w U.toSubmodule
  have hRV := hV.baseChange b w V
  have hRUV : ∀ u ∈ realificationLieSubalgebra U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ :=
    fun _ hu _ hv => lie_mem_real_baseChange U.toSubmodule V V hUV hu hv
  obtain ⟨q, _, _, _, W, _, m, hm, hmbound, _, hleft, hright, hleftGood, hrightGood⟩ :=
    hfactor F b w hF hgraded hs (realificationLieSubalgebra U) V K hRUV hRU hRV eK f hK hH G
      hKernelBasis hQuotient hStructure hp hμ hι hκ hσ hRanks hsp hHp T
      (fun i => (Real.exp_le_exp.mpr hEC).trans (hT i)) X
  obtain ⟨e, he⟩ := hbasis b w U V K fU fK f eK hH hQuotientU hQuotientK hQuotient
    hKernelBasis hStructure hp hμ hυ hχ hκ hι hHp
  let Z := stepDropSubalgebra b w (F.adaptedBasis_weight_pos b w hF) hgraded U V K hU hUV
  have hcoeff : ∀ α, coefficients W.state.P.coord α ∈ realificationLieSubalgebra Z := by
    intro α
    exact W.terminal_coefficients_mem_rational_stepDrop hs hF α
  refine ⟨Z, stepDropSubmodule_graded b w U V K hU hV,
    (fun _ hx => stepDropSubmodule_top_frequency b w U V K hU hV η hs hη hx), e, ?_,
    W.left.prod, W.state.P, W.right.prod, W.factorization, hleftGood, hrightGood,
    W.state.constant_zero, W.state.graded, hcoeff,
    hleft.mono _ T hTpos (Real.exp_le_exp.mpr hEC), m, hm,
    hmbound.trans (Real.exp_le_exp.mpr hEC), hright⟩
  intro i j
  exact ⟨(he i j).1.trans (Real.exp_le_exp.mpr hDC), (he i j).2.trans (Real.exp_le_exp.mpr hDC)⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_stepDrop_from_formal_state (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ υ χ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (_hU : BasisGradedSubmodule b w U.toSubmodule) (_hV : BasisGradedSubmodule b w V)
    (η : L →ₗ[ℚ] ℚ) (_hη : ∀ x ∈ V, basisGradeProjection b w s x = x → η x = 0)
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hQuotientU : ∀ i z, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b z)) i) H)
    (_hQuotientK : ∀ i z, RationalHeightLE (fK.repr (K.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hυ : (Fintype.card υ : ℝ) ≤ p)
    (_hχ : (Fintype.card χ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : F.FormalInductionState b w (realificationLieSubalgebra U) V K eK T 2 p),
    ∃ Z : LieSubalgebra ℚ L, BasisGradedSubmodule b w Z.toSubmodule ∧
      (∀ x ∈ Z, η (basisGradeProjection b w s x) = 0) ∧
      ∃ e : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
        (∀ i j, ((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        ∃ A P B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          A * P * B = X.P ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) A ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) B ∧
          coefficients P.coord 0 = 0 ∧
          P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
          (∀ α, coefficients P.coord α ∈ realificationLieSubalgebra Z) ∧
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A.coord ∧
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            CoefficientGrid (b.baseChange ℝ) m B.coord := by
  classical
  obtain ⟨E, _, hfinal⟩ := exists_formal_stepDrop_subalgebra_factorization s
  obtain ⟨D, hD, hgeometryBudget⟩ := exists_formal_geometry_uniform_budget
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C D) ^ D + Polynomial.C E) ^ E)
  refine ⟨C, hC, ?_⟩
  intro L μ υ χ ι κ σ _ _ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV η hη eK f
    fU fK hK H hH hKernelBasis hQuotient hQuotientU hQuotientK hStructure
    p hp hμ hυ hχ hι hκ hσ hsp hHp T hT X
  let u := (p + D) ^ D
  let r := 2 * Fintype.card υ + Fintype.card χ + Fintype.card ι + Fintype.card μ
  let J := formalGeometryHeight (Fintype.card μ) r H
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpu : p ≤ u := by
    calc
      p ≤ p + D := le_add_of_nonneg_right (Nat.cast_nonneg D)
      _ ≤ (p + D) ^ D := by
        have hDr : (2 : ℝ) ≤ D := Nat.cast_le.mpr hD
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + D)
          (show 1 ≤ D by omega)
  have hr : (r : ℝ) ≤ 5 * p := by
    dsimp [r]
    push_cast
    linarith
  have hHJ : H ≤ J := formalGeometryHeight_ge_input _ _ _
  have hJ : 1 ≤ J := hH.trans hHJ
  have hJu : (J : ℝ) ≤ Real.exp u := hgeometryBudget _ _ _ p hp hμ hr hHp
  have hcap : (u + E) ^ E ≤ (p + C) ^ C := by
    simpa [u, Polynomial.eval₂_pow] using hbudget p hp
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hgeometry (j : ℕ) (hj : 2 ≤ j) :
      ∃ G : FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j J,
        G.bracketRank ≤ Fintype.card μ ∧ G.currentRank ≤ Fintype.card μ := by
    apply exists_rational_formal_stage_geometry b w U V K hU fU fK f eK hH
    · dsimp [r]; omega
    · dsimp [r]; omega
    · dsimp [r]; omega
    · exact hQuotientU
    · exact hQuotientK
    · exact hQuotient
    · exact hKernelBasis
    · exact hStructure
    · exact hj
  choose G hG using hgeometry
  obtain ⟨Z, hZ, hZη, e, he, A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff,
    hbound, m, hm, hmbound, hgrid⟩ :=
    hfinal F b w hF hgraded hs U V K hUV hU hV η hη eK f fU fK hK hJ
      (fun j hj _ => G j hj)
      (fun i z => (hKernelBasis i z).mono hHJ)
      (fun i z => (hQuotient i z).mono hHJ)
      (fun i z => (hQuotientU i z).mono hHJ)
      (fun i z => (hQuotientK i z).mono hHJ)
      (fun i z k => (hStructure i z k).mono hHJ)
      hu (hμ.trans hpu) (hυ.trans hpu) (hχ.trans hpu) (hι.trans hpu) (hκ.trans hpu) (hσ.trans hpu)
      (fun j hj _ => ⟨(Nat.cast_le.mpr (hG j hj).1).trans (hμ.trans hpu),
        (Nat.cast_le.mpr (hG j hj).2).trans (hμ.trans hpu)⟩)
      (hsp.trans hpu) hJu T (fun i => (Real.exp_le_exp.mpr hcap).trans (hT i))
      (X.enlarge hpu hTpos)
  refine ⟨Z, hZ, hZη, e, ?_, A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff,
    hbound.mono _ T hTpos (Real.exp_le_exp.mpr hcap), m, hm,
    hmbound.trans (Real.exp_le_exp.mpr hcap), hgrid⟩
  intro i j
  exact ⟨(he i j).1.trans (Real.exp_le_exp.mpr hcap), (he i j).2.trans (Real.exp_le_exp.mpr hcap)⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "bG" => F.associatedGradedBasis e ω hF
local notation "FG" => F.associatedGradedFiltration
local notation "U" => F.fullFastGradedDiagonal W
local notation "V" => F.fullFastGradedRelative e ω hF W
local notation "PG" => PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot

def FastTerminalFactorization (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (T : σ → ℝ) (original : PG) (p : ℝ) : Prop :=
  ∃ Z : LieSubalgebra ℚ F.AssociatedGraded, BasisGradedSubmodule bG ω Z.toSubmodule ∧
    (∀ x ∈ Z, η (basisGradeProjection bG ω (s + 1) x) = 0) ∧
    ∃ bZ : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
      (∀ i j, (((bG).repr (bZ i : F.AssociatedGraded) j).num.natAbs : ℝ) ≤ Real.exp p ∧
        (((bG).repr (bZ i : F.AssociatedGraded) j).den : ℝ) ≤ Real.exp p) ∧
      ∃ A P B : PG, A * P * B = original ∧
        (FG).FormalCorrectionProperty bG ω (realificationLieSubalgebra U) A ∧
        (FG).FormalCorrectionProperty bG ω (realificationLieSubalgebra U) B ∧
        coefficients P.coord 0 = 0 ∧
        P.coord ∈ gradedPolynomialSubmodule ((bG).baseChange ℝ) ω (fun _ : σ => 1) ∧
        (∀ α, coefficients P.coord α ∈ realificationLieSubalgebra Z) ∧
        CoefficientBound ((bG).baseChange ℝ) T (Real.exp p) A.coord ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ CoefficientGrid ((bG).baseChange ℝ) m B.coord

omit [Fintype σ] [Fintype ι] in
theorem FastTerminalFactorization.mono
    {η : F.AssociatedGraded →ₗ[ℚ] ℚ} {T : σ → ℝ} {original : PG} {p q : ℝ}
    (h : F.FastTerminalFactorization e ω hF W η T original p)
    (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.FastTerminalFactorization e ω hF W η T original q := by
  obtain ⟨Z, hZ, hη, bZ, hbZ, A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff,
    hbound, m, hm, hmp, hgrid⟩ := h
  have hepq := Real.exp_le_exp.mpr hpq
  exact ⟨Z, hZ, hη, bZ, fun i j => ⟨(hbZ i j).1.trans hepq, (hbZ i j).2.trans hepq⟩,
    A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff, hbound.mono _ T hT hepq,
    m, hm, hmp.trans hepq, hgrid⟩

def FastTerminalStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hsp : (s + 1 : ℕ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (k : ℕ) (_hk : (k : ℝ) ≤ p) (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis (Fin k) ℚ K)
    (_hKb : ∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j).val i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ V, basisGradeProjection bG ω (s + 1) x = x → η x = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : (FG).FormalInductionState bG ω (realificationLieSubalgebra U) V
      (F.gradedHorizontalKernel e ω hF K) (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 p),
    F.FastTerminalFactorization e ω hF W η T X.P ((p + C) ^ C)

theorem exists_fast_terminalState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.FastTerminalStateSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h := exists_stepDrop_from_formal_state.{uL, uι, 0, 0, 0, 0, uσ} (s + 1)
  obtain ⟨c, _, hformal⟩ := h
  obtain ⟨C, hC, hbudget⟩ := exists_fastTerminalParameter_budget c
  refine ⟨C, hC, ?_⟩
  intro σ ι τ L _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hsp hHp hstructure
    hW v hv hheight k hk K bK hKb η hη T hT X
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hthree : 0 ≤ 3 * p := by positivity
  have hp3 : p ≤ 3 * p := by linarith
  have hsize : 2 * (Fintype.card ι : ℝ) + (Fintype.card τ : ℝ) ≤ 3 * p := by linarith
  have hUV := F.exists_full_fast_quotient_bases e ω hF W v hv hH hheight hthree hsize
    (hHp.trans (Real.exp_le_exp.mpr hp3))
  obtain ⟨Huv, hHHuv, hHuv, hHuvp, dU, hdU, fU, dV, hdV, fV, hfU, hfV⟩ := hUV
  have hkcard : (Fintype.card (Fin k) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hk
  have hK := F.exists_gradedHorizontalKernel_quotient_basis e ω hF K bK hH
    (fun j i => hKb i j) hp hkcard hHp
  obtain ⟨Hk, _, hHkp, dK, hdK, fK, hfK⟩ := hK
  let q := fastTerminalParameter p
  have hcontrol := fastTerminalParameter_controls hp
  have hpq : p ≤ q := hcontrol.1
  have hq : 0 ≤ q := hp.trans hpq
  have hHH : H ≤ max Huv Hk := hHHuv.trans (le_max_left _ _)
  have hcommon : ((max Huv Hk : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_max]
    exact max_le (hHuvp.trans (Real.exp_le_exp.mpr hcontrol.2.1))
      (hHkp.trans (Real.exp_le_exp.mpr hcontrol.2.2))
  have hdim (d : ℕ) (hd : d ≤ Fintype.card ι) : (Fintype.card (Fin d) : ℝ) ≤ q := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr hd).trans (hι.trans hpq)
  have hstructureG (i j r : ι) :
      RationalHeightLE ((F.associatedGradedBasis e ω hF).repr
        ⁅F.associatedGradedBasis e ω hF i, F.associatedGradedBasis e ω hF j⁆ r) (max Huv Hk) := by
    rw [F.associatedGradedBasis_bracket e ω hF]
    split_ifs
    · exact (hstructure i j r).mono hHH
    · exact rationalHeightLE_zero (hH.trans hHH)
  have hout : F.FastTerminalFactorization e ω hF W η T X.P ((q + c) ^ c) :=
    hformal F.associatedGradedFiltration (F.associatedGradedBasis e ω hF) ω
      (F.associatedGradedFiltration_layer e ω hF) (F.associatedGradedBasis_homogeneous_brackets e ω hF)
      (by omega) (F.fullFastGradedDiagonal W) (F.fullFastGradedRelative e ω hF W)
      (F.gradedHorizontalKernel e ω hF K)
      (fun _ hu _ hv => F.fullFastGradedRelative_lie_mem e ω hF W hu hv)
      (F.fullFastGradedDiagonal_graded e ω hF W hW) (F.fullFastGradedRelative_graded e ω hF W hW)
      η hη (F.gradedHorizontalKernelBasis e ω hF K bK) fV fU fK
      (F.gradedHorizontalKernel_real_pure e ω hF K) (hHuv.trans (le_max_left _ _))
      (fun i j => (F.gradedHorizontalKernelBasis_height e ω hF K bK hH (fun z r => hKb r z) j i).mono hHH)
      (fun i j => (hfV i j).mono (le_max_left _ _))
      (fun i j => (hfU i j).mono (le_max_left _ _))
      (fun i j => (hfK i j).mono (le_max_right _ _)) hstructureG hq
      (hι.trans hpq) (hdim dU hdU) (hdim dK hdK) (hdim dV hdV) (hkcard.trans hpq)
      (hσ.trans hpq) (hsp.trans hpq) hcommon T
      (fun i => (Real.exp_le_exp.mpr (hbudget p hp)).trans (hT i)) (X.enlarge hpq hTpos)
  exact hout.mono F e ω hF W (hbudget p hp) hTpos

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "bG" => F.associatedGradedBasis e ω hF
local notation "SG" => F.RealPolynomialSymbolGroup (fun _ : σ => 1)
local notation "φ" => F.realGradedSymbolPolynomialHom e ω hF (fun _ : σ => 1)

def SymbolTerminalFactorization (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (T : σ → ℝ) (original : SG) (p : ℝ) : Prop :=
  ∃ Z : LieSubalgebra ℚ F.AssociatedGraded, BasisGradedSubmodule bG ω Z.toSubmodule ∧
    (∀ x ∈ Z, η (basisGradeProjection bG ω (s + 1) x) = 0) ∧
    ∃ bZ : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
      (∀ i j, (((bG).repr (bZ i : F.AssociatedGraded) j).num.natAbs : ℝ) ≤ Real.exp p ∧
        (((bG).repr (bZ i : F.AssociatedGraded) j).den : ℝ) ≤ Real.exp p) ∧
      ∃ A P B : SG, A * P * B = original ∧
        A.coord ∈ realificationLieSubalgebra
          (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) (F.fullFastGradedDiagonal W)) ∧
        B.coord ∈ realificationLieSubalgebra
          (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) (F.fullFastGradedDiagonal W)) ∧
        P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) Z) ∧
        F.SymbolSlowBound e ω hF (fun _ : σ => 1) T (Real.exp p) A ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ F.SymbolRationalGrid e ω hF (fun _ : σ => 1) m B

theorem symbolTerminalFactorization_of_graded
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (original : SG) (p : ℝ)
    (h : F.FastTerminalFactorization e ω hF W η T (φ original) p) :
    F.SymbolTerminalFactorization e ω hF W η T original p := by
  obtain ⟨Z, hZ, hZη, bZ, hbZ, A, P, B, hfactor, hA, hB, _, hdegree, hcoeff,
    hbound, m, hm, hmp, hgrid⟩ := h
  obtain ⟨a, ha⟩ := F.exists_symbol_of_gradedPolynomial e ω hF (fun _ : σ => 1) A hA.2.1
  obtain ⟨c, hc⟩ := F.exists_symbol_of_gradedPolynomial e ω hF (fun _ : σ => 1) P hdegree
  obtain ⟨b, hb⟩ := F.exists_symbol_of_gradedPolynomial e ω hF (fun _ : σ => 1) B hB.2.1
  refine ⟨Z, hZ, hZη, bZ, hbZ, a, c, b, ?_, ?_, ?_, ?_, ?_, m, hm, hmp, ?_⟩
  · apply F.realGradedSymbolPolynomialHom_injective e ω hF (fun _ : σ => 1)
    rw [map_mul, map_mul, ha, hc, hb]
    exact hfactor
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ : σ => 1)
      (F.fullFastGradedDiagonal W) a.coord).mpr
    intro α
    change coefficients (φ a).coord α ∈ _
    rw [ha]
    exact hA.1 α
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ : σ => 1)
      (F.fullFastGradedDiagonal W) b.coord).mpr
    intro α
    change coefficients (φ b).coord α ∈ _
    rw [hb]
    exact hB.1 α
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ : σ => 1) Z c.coord).mpr
    intro α
    change coefficients (φ c).coord α ∈ _
    rw [hc]
    exact hcoeff α
  · apply F.symbolSlowBound_of_gradedPolynomial e ω hF (fun _ : σ => 1) T (Real.exp p) a
    rw [ha]
    exact hbound
  · apply F.symbolRationalGrid_of_gradedPolynomial e ω hF (fun _ : σ => 1) m b
    rw [hb]
    exact hgrid

theorem symbolTerminalFactorization_of_native
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (p : ℝ)
    (h : F.FastTerminalFactorization e ω hF W η T
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g) p) :
    F.SymbolTerminalFactorization e ω hF W η T
      (F.realPolynomialSymbolHom e ω hF (fun _ : σ => 1) (F.realAdaptedPolynomialGroupHom (fun _ => 1) g)) p := by
  apply F.symbolTerminalFactorization_of_graded e ω hF W η T _ p
  rw [F.realGradedSymbolPolynomialHom_native]
  exact h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem SymbolTerminalFactorization.mono
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    {η : F.AssociatedGraded →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ}
    (h : F.SymbolTerminalFactorization b ω hF W η T X p) (hpq : p ≤ q)
    (hT : ∀ i, 0 < T i) : F.SymbolTerminalFactorization b ω hF W η T X q := by
  obtain ⟨Z, hZ, hη, bZ, hbZ, A, P, B, hprod, hA, hB, hP, hslow, m, hm, hmp, hgrid⟩ := h
  have he := Real.exp_le_exp.mpr hpq
  exact ⟨Z, hZ, hη, bZ, (fun i j => ⟨(hbZ i j).1.trans he, (hbZ i j).2.trans he⟩),
    A, P, B, hprod, hA, hB, hP,
    F.symbolSlowBound_mono b ω hF (fun _ => 1) T hT he A hslow, m, hm, hmp.trans he, hgrid⟩

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem native_symbol_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealAdaptedPolynomialGroup w) (hg : F.RealAdaptedCoefficientBound b ω hF w T M g.coord) :
    F.SymbolSlowBound b ω hF w T M
      (F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)) :=
  F.polynomialSlowBound_symbol b ω hF w T M (F.realAdaptedPolynomialGroupHom w g)
    ((F.realAdaptedCoefficientBound_polynomial_iff b ω hF w T hT hM g).mp hg)

theorem native_symbol_grid (l : ℕ) (g : F.RealAdaptedPolynomialGroup w)
    (hg : F.RealAdaptedCoefficientGrid b ω hF w l g.coord) :
    F.SymbolRationalGrid b ω hF w l
      (F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)) :=
  F.polynomialRationalGrid_symbol b ω hF w l (F.realAdaptedPolynomialGroupHom w g)
    ((F.realAdaptedCoefficientGrid_polynomial_iff b ω hF w l g).mp hg)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem SymbolTerminalFactorization.controlled
    {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (hp : 0 ≤ p) (hT : ∀ i, 0 < T i)
    (h : F.SymbolTerminalFactorization b ω hF W (F.gradedFrequency b ω hF η) T X p) :
    F.ControlledSymbolFactorization b ω hF η T X (p + 1) := by
  classical
  obtain ⟨Z, hZ, hη, bZ, hbZ, A, P, B, hprod, _, _, hP, hslow, m, hm, hmp, hgrid⟩ := h
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hb : ∀ i j, RationalHeightLE
      ((F.associatedGradedBasis b ω hF).repr (bZ i : F.AssociatedGraded) j) H := by
    intro i j
    exact rationalHeightLE_ceil_exp ((rationalLogHeight_le_iff _ p).mpr (hbZ i j))
  obtain ⟨w, hw, hheight⟩ := exists_bounded_ambient_spanning
    (F.associatedGradedBasis b ω hF) Z bZ bZ.span_eq hH hb
  let v : ι → F.AssociatedGraded := fun i => w (Fintype.equivFin ι i)
  have hrange : Set.range v = Set.range w := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fintype.equivFin ι i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(Fintype.equivFin ι).symm i, congrArg w ((Fintype.equivFin ι).apply_symm_apply i)⟩
  have he : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  refine ⟨m, A, P, B, Z, v, hm, hmp.trans he, hprod,
    F.symbolSlowBound_mono b ω hF (fun _ => 1) T hT he A hslow, hgrid, ?_, hZ, ?_, ?_, hP⟩
  · rw [hrange]
    exact hw
  · intro i j
    exact rationalLogHeight_le_of_height (hheight (Fintype.equivFin ι i) j) (ceil_exp_le_exp_add_one hp)
  · intro x hx hproj
    have hz := hη x hx
    rw [hproj] at hz
    exact hz

end Erdos3.NilpotentLieFiltration

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

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realPolynomialSymbolHom_groupHom_coord (g : F.RealAdaptedPolynomialGroup w) :
    (F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)).coord =
      F.realExtendedSymbolMap w g.coord :=
  F.realSymbolOfPolynomial_realAdaptedPolynomialMap b ω hF w g.coord

noncomputable def nativeSymbolNormalize (g : F.RealAdaptedPolynomialGroup w) :
    F.RealAdaptedPolynomialGroup w :=
  F.realAdaptedPolynomialGroupLift w b ω hF
    (F.realPolynomialSymbolLift b ω hF w
      (F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)))

theorem nativeSymbolNormalize_symbol (g : F.RealAdaptedPolynomialGroup w) :
    F.realExtendedSymbolMap w (F.nativeSymbolNormalize b ω hF w g).coord =
      F.realExtendedSymbolMap w g.coord := by
  have he : F.realPolynomialSymbolHom b ω hF w
      (F.realAdaptedPolynomialGroupHom w (F.nativeSymbolNormalize b ω hF w g)) =
      F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g) := by
    unfold nativeSymbolNormalize
    rw [F.realAdaptedPolynomialGroupHom_lift, F.realPolynomialSymbolHom_lift]
  have hc := congrArg NilpotentLieBCHGroup.coord he
  simpa only [F.realPolynomialSymbolHom_groupHom_coord] using hc

theorem nativeSymbolNormalize_constant (g : F.RealAdaptedPolynomialGroup w) :
    coefficients (F.realAdaptedPolynomialMap w (F.nativeSymbolNormalize b ω hF w g).coord) 0 = 0 := by
  let X : F.RealPolynomialSymbolGroup w :=
    F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)
  have hX : coefficients (F.realSymbolRepresentative b ω hF w X.coord) 0 = 0 :=
    F.realSymbolRepresentative_constant b ω hF w X.coord
  change coefficients (F.realAdaptedPolynomialGroupHom w
    (F.realAdaptedPolynomialGroupLift w b ω hF (F.realPolynomialSymbolLift b ω hF w X))).coord.val 0 = 0
  rw [F.realAdaptedPolynomialGroupHom_lift, F.realPolynomialSymbolLift_log, hX]

theorem realAdaptedGradedPolynomialHom_eq_of_symbol_eq
    (g h : F.RealAdaptedPolynomialGroup w)
    (he : F.realExtendedSymbolMap w g.coord = F.realExtendedSymbolMap w h.coord) :
    F.realAdaptedGradedPolynomialHom b ω hF w g = F.realAdaptedGradedPolynomialHom b ω hF w h := by
  apply NilpotentLieBCHGroup.ext
  change F.realAdaptedGradedPolynomialLie b ω hF w g.coord =
    F.realAdaptedGradedPolynomialLie b ω hF w h.coord
  rw [F.realAdaptedGradedPolynomialLie_symbol, F.realAdaptedGradedPolynomialLie_symbol]
  change F.realGradedSymbolPolynomial b ω hF w (F.realExtendedSymbolMap w g.coord) =
    F.realGradedSymbolPolynomial b ω hF w (F.realExtendedSymbolMap w h.coord)
  rw [he]

include b ω hF in
theorem realFirstCoefficientDirectionMap_eq_of_symbol_eq [Fintype σ]
    (g h : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (he : F.realExtendedSymbolMap (fun _ => 1) g.coord = F.realExtendedSymbolMap (fun _ => 1) h.coord) :
    F.realFirstCoefficientDirectionMap g.coord = F.realFirstCoefficientDirectionMap h.coord := by
  classical
  apply (Pi.basisFun ℝ σ).ext
  intro i
  apply F.realFirstCoefficientGradedPolynomial_injective b ω hF (fun _ => 1)
  change F.realFirstCoefficientGradedPolynomial b ω hF (fun _ => 1)
      (F.realFirstCoefficientDirectionMap g.coord (Pi.single i 1)) =
    F.realFirstCoefficientGradedPolynomial b ω hF (fun _ => 1)
      (F.realFirstCoefficientDirectionMap h.coord (Pi.single i 1))
  rw [F.realFirstCoefficientGradedPolynomial_direction, F.realFirstCoefficientGradedPolynomial_direction,
    F.realAdaptedGradedPolynomialHom_eq_of_symbol_eq b ω hF (fun _ => 1) g h he]

include b ω hF in
theorem realFirstCoefficientAdjoint_eq_of_symbol_eq
    (g h : F.RealAdaptedPolynomialGroup w)
    (he : F.realExtendedSymbolMap w g.coord = F.realExtendedSymbolMap w h.coord)
    (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientAdjoint w g x = F.realFirstCoefficientAdjoint w h x := by
  apply F.realFirstCoefficientGradedPolynomial_injective b ω hF w
  rw [F.realFirstCoefficientGradedPolynomial_adjoint, F.realFirstCoefficientGradedPolynomial_adjoint,
    F.realAdaptedGradedPolynomialHom_eq_of_symbol_eq b ω hF w g h he]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem bounded_coefficient_derivative_point
    {σ ι κ L : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis κ ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))
    (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (C M N : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hN : 0 ≤ N) (l m : ℕ)
    (hslow : ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (M + N) x → ∀ i,
      |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
          C * (M + N) / monomialScale T (rows i).val.1)
    (hgrid : ∀ x, F.FirstCoefficientGrid e ω hF (fun _ => 1) l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈ realDenominatorGrid m)
    (h h₀ : σ → ℤ) (hhbox : ∀ i, |(h i : ℝ)| ≤ T i) (hh₀box : ∀ i, |(h₀ i : ℝ)| ≤ T i)
    (S S₀ R R₀ Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hh : F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (S + F.realFirstCoefficientAdjoint (fun _ => 1) B R + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hh₀ : F.realFirstCoefficientDirectionMap B.coord (fun i => (h₀ i : ℝ)) -
      (S₀ + F.realFirstCoefficientAdjoint (fun _ => 1) B R₀ + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hS : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T M S)
    (hS₀ : F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T N S₀)
    (hR : F.FirstCoefficientGrid e ω hF (fun _ => 1) l R)
    (hR₀ : F.FirstCoefficientGrid e ω hF (fun _ => 1) l R₀) :
    let Y := F.fastCoefficientDirectionCoordinates U b B
    let A := LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap
    let scale := fun i => monomialScale T (rows i).val.1
    ∃ r : κ → ℝ, r ∈ realDenominatorGrid m ∧
      derivativeGridPoint T scale Y A (h - h₀) r ∈ derivativeGridPoints T scale Y A m ∧
      ‖derivativeGridPoint T scale Y A (h - h₀) r‖ ≤ max 2 (C * (M + N)) := by
  dsimp only
  let V := F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
  let r := b.equivFun (V.mkQ (R - R₀))
  let a := b.equivFun (V.mkQ (S - S₀))
  have hdiff := F.coefficient_common_derivative_difference V B
    (fun i => (h i : ℝ)) (fun i => (h₀ i : ℝ)) S S₀ R R₀ Z hh hh₀
  have hdiff' : F.realFirstCoefficientDirectionMap B.coord (fun i => ((h - h₀) i : ℝ)) -
      ((S - S₀) + F.realFirstCoefficientAdjoint (fun _ => 1) B (R - R₀)) ∈ V := by
    have hcast : (fun i => ((h - h₀) i : ℝ)) =
        (fun i => (h i : ℝ)) - (fun i => (h₀ i : ℝ)) := by
      funext i
      simp only [Pi.sub_apply, Int.cast_sub]
    rw [hcast]
    exact hdiff
  have heq := F.fastCoefficientDerivative_coordinates U b B hB
    (fun i => ((h - h₀) i : ℝ)) (S - S₀) (R - R₀) hdiff'
  have hr : r ∈ realDenominatorGrid m := hgrid (R - R₀)
    (F.firstCoefficientGrid_sub e ω hF (fun _ => 1) l R R₀ hR hR₀)
  have ha : ∀ i, |a i| ≤ C * (M + N) / monomialScale T (rows i).val.1 :=
    hslow (S - S₀) (F.firstCoefficientSlowBound_sub e ω hF (fun _ => 1) T M N S S₀ hS hS₀)
  refine ⟨r, hr, derivativeGridPoint_mem _ _ _ _ m (h - h₀) r hr, ?_⟩
  apply derivativeGridPoint_bound T hT _ (fun i => monomialScale_pos T hT (rows i).val.1)
    _ _ (h - h₀) r a 2 (C * (M + N)) (by norm_num) (mul_nonneg hC (add_nonneg hM hN)) ?_ heq ha
  intro i
  change |((h i - h₀ i : ℤ) : ℝ)| ≤ 2 * T i
  rw [Int.cast_sub]
  exact (abs_sub _ _).trans (by linarith [hhbox i, hh₀box i])

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

theorem bounded_coefficient_difference_inputs
    {σ ι κ L : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis κ ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))
    (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (l m : ℕ)
    (hslow : ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (M + M) x → ∀ i,
      |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
          C * (M + M) / monomialScale T (rows i).val.1)
    (hgrid : ∀ x, F.FirstCoefficientGrid e ω hF (fun _ => 1) l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈ realDenominatorGrid m)
    (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (hh₀ : h₀ ∈ H)
    (S R : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hbox : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ T i)
    (hcommon : ∀ h ∈ H, F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ => 1) B (R h) + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hS : ∀ h ∈ H, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T M (S h))
    (hR : ∀ h ∈ H, F.FirstCoefficientGrid e ω hF (fun _ => 1) l (R h)) :
    let Y := F.fastCoefficientDirectionCoordinates U b B
    let A := LinearMap.toMatrix b b (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap
    let scale := fun i => monomialScale T (rows i).val.1
    ∃ D : Finset (σ → ℤ), D.card = H.card ∧
      ∃ q : (σ → ℤ) → κ → ℝ, ∀ h ∈ D,
        q h ∈ realDenominatorGrid m ∧
        ‖derivativeGridPoint T scale Y A h (q h)‖ ≤ max 2 (C * (M + M)) := by
  dsimp only
  apply exists_derivative_difference_inputs T _ _ _ m H h₀ (max 2 (C * (M + M)))
  intro h hh
  obtain ⟨r, hr, _, hnorm⟩ := F.bounded_coefficient_derivative_point
    e ω hF U b rows B hB T hT C M M hC hM hM l m hslow hgrid
    h h₀ (hbox h hh) (hbox h₀ hh₀) (S h) (S h₀) (R h) (R h₀) Z
    (hcommon h hh) (hcommon h₀ hh₀) (hS h hh) (hS h₀ hh₀) (hR h hh) (hR h₀ hh₀)
  exact ⟨r, hr, hnorm⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix TensorProduct

theorem common_coefficient_derivative_system
    {σ ι L : Type*} [Fintype σ] [DecidableEq σ] {d : ℕ}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1) ⧸
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)))
    (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (hblock : ∀ i j, (rows j).val.1 ≠ i.val.1 →
      b.repr ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
          (F.realFirstCoefficientBasis e ω hF (fun _ => 1) i)) j = 0)
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : (F.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra (fun _ => 1) U))
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (l m : ℕ)
    (hslow : ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (M + M) x → ∀ i,
      |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
          C * (M + M) / monomialScale T (rows i).val.1)
    (hgrid : ∀ x, F.FirstCoefficientGrid e ω hF (fun _ => 1) l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈ realDenominatorGrid m)
    (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (hh₀ : h₀ ∈ H)
    (S R : (σ → ℤ) → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hbox : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ T i)
    (hcommon : ∀ h ∈ H, F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ => 1) B (R h) + Z) ∈
        F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U))
    (hS : ∀ h ∈ H, F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T M (S h))
    (hR : ∀ h ∈ H, F.FirstCoefficientGrid e ω hF (fun _ => 1) l (R h))
    (haction : ∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
      LinearMap.toMatrix b b
        (F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB).toLinearMap i j =
          (1 : Matrix (Fin d) (Fin d) ℝ) i j)
    (hm : 0 < m) (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hdim : ((Fintype.card σ + Fintype.card (Fin d) : ℕ) : ℝ) ≤ p)
    (hmcap : (m : ℝ) ≤ Real.exp p) (hRcap : max 2 (C * (M + M)) ≤ Real.exp p)
    (hδcap : δ⁻¹ ≤ Real.exp p) (Tmin : ℝ)
    (hmin : Real.exp ((p + 2) ^ 3) < Tmin) (hside : ∀ i, Tmin ≤ T i) :
    ∃ (perm : Equiv.Perm (Fin d)) (a : ℕ) (ha : a ≤ d),
      (∀ i, i.val < a ↔ (rows (perm i)).val.1 = 0) ∧
      let b' := b.reindex perm.symm
      let f := F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB
      let A' := b'.equivFun.symm.trans (f.trans b'.equivFun)
      ∃ η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)),
      (∀ x, η (fun i => b'.equivFun x (Fin.castLE ha i)) =
        F.realFastCoefficientHorizontal (fun _ => 1) (by simp)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U) x) ∧
      Nonempty (CoordinateDerivativeSystem ha T (F.fastCoefficientDirectionCoordinates U b' B) A'
        (fun i => monomialScale T (rows (perm i)).val.1) (Real.exp ((p + 2) ^ 3))) := by
  have hTpos : ∀ i, 0 < T i := fun i => lt_of_lt_of_le zero_lt_one (hT i)
  obtain ⟨D, hDcard, q, hq⟩ := F.bounded_coefficient_difference_inputs e ω hF U b rows
    B hB T hTpos C M hC hM l m hslow hgrid H h₀ hh₀ S R Z hbox hcommon hS hR
  let V := F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
  let Y := V.mkQ.comp (F.realFirstCoefficientDirectionMap B.coord)
  let f := F.realFastCoefficientAdjoint (fun _ => 1) (by simp) U B hB
  have hDdense : δ * ∏ i, T i ≤ (D.card : ℝ) := by rw [hDcard]; exact hdense
  obtain ⟨perm, a, ha, hzero, hsystem⟩ :=
    firstCoefficient_coordinate_system ω rows b Y f haction T hT m hm
    (max 2 (C * (M + M))) δ
    ((by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)) hδ D q
    (fun h hh => (hq h hh).1) (fun h hh => (hq h hh).2) hDdense
    p hp hdim hmcap hRcap hδcap Tmin hmin hside
  have hblock' : ∀ i j, (rows (perm j)).val.1 ≠ i.val.1 →
      (b.reindex perm.symm).repr (V.mkQ
        (F.realFirstCoefficientBasis e ω hF (fun _ => 1) i)) j = 0 := by
    intro i j hij
    simpa only [Basis.repr_reindex_apply, Equiv.symm_symm] using hblock i (perm j) hij
  let η := F.realFastCoefficientHorizontalEquiv e ω hF (fun _ : σ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
    (b.reindex perm.symm) (fun i => rows (perm i)) hblock' ha hzero
  refine ⟨perm, a, ha, hzero, η, ?_, hsystem⟩
  exact F.realFastCoefficientHorizontalEquiv_projection e ω hF (fun _ : σ => 1) (by simp)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
    (b.reindex perm.symm) (fun i => rows (perm i)) hblock' ha hzero

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf

def BoundedInitialStateFactorization (g₀ : G) (T : σ → ℝ) (rankBound : ℕ) (p : ℝ) : Prop :=
  ∃ k : ℕ, k ≤ rankBound ∧
    ∃ (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis (Fin k) ℚ K),
    ∃ Hk : ℕ, 1 ≤ Hk ∧ (Hk : ℝ) ≤ Real.exp p ∧
      (∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j).val i) Hk) ∧
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
        ∃ x g z : G, x * g * z = g₀ ∧
          F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T (Real.exp p) x.val.coord ∧
          F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) m z.val.coord ∧
          ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
            (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
            (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
            (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 p,
            X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val

def CommonInitialStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hd : (d : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (b : Basis (Fin d) ℝ Q) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (Fin d → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (Cscale : ℝ) (_hC : 0 ≤ Cscale) (_hCp : Cscale ≤ Real.exp p)
    (_hweighted : ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
      (∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x → ∀ i,
        |b.equivFun ((J).mkQ x) i| ≤ Cscale * M / monomialScale T (rows i).val.1) ∧
      (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Cscale * M) (sectionMap y)))
    (δ : ℕ) (_hδ : 0 < δ) (_hδp : (δ : ℝ) ≤ Real.exp p)
    (_hprojectionGrid : ∀ m x, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m x →
      b.equivFun ((J).mkQ x) ∈ realDenominatorGrid (δ * m))
    (_hsectionGrid : ∀ m (y : Fin d → ℝ), y ∈ realDenominatorGrid m →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) (δ * m) (sectionMap y))
    (_hblock : ∀ i j, (rows j).val.1 ≠ i.val.1 →
      b.repr ((J).mkQ (F.realFirstCoefficientBasis e ω hF (fun _ : σ => 1) i)) j = 0)
    (_haction : ∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
      LinearMap.toMatrix b b (ρ g₀).toLinearMap i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.BoundedInitialStateFactorization e ω hF W g₀ T d ((p + C) ^ C)

theorem exists_initialFormalState_from_common (C D : ℕ)
    (hbudget : ∀ p : ℝ, 0 ≤ p →
      commonInitialParameter p + 1 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + 2) ^ 3 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + C) ^ C ≤ (p + D) ^ D)
    (hinit : ∀ a : ℕ, F.ExtractedInitialStateSpec (σ := σ) (τ := τ) (a := a) (d := d) e ω hF W C) :
    F.CommonInitialStateSpec (σ := σ) (τ := τ) (d := d) e ω hF W D := by
  intro H p hH hp hι hσ hτ hd hHp hstructure hW v hv hheight g₀ hzero
    b rows sectionMap hsection Cscale hC hCp hweighted δ hδ hδp hprojectionGrid hsectionGrid
    hblock haction T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR
    density hdensity hdensityp hdense
  let q := commonExtractionParameter p
  let r := commonInitialParameter p
  have hcontrol := commonExtractionParameter_controls hp
  have hpq : p ≤ q := hcontrol.1
  have hqr : q ≤ r := hcontrol.2.2.2
  have hpr : p ≤ r := hpq.trans hqr
  have hq : 0 ≤ q := hp.trans hpq
  have hr : 0 ≤ r := hp.trans hpr
  have hepq := Real.exp_le_exp.mpr hpq
  have hepr := Real.exp_le_exp.mpr hpr
  have hb := hbudget p hp
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTlarge (i : σ) : Real.exp (r + 1) ≤ T i :=
    (Real.exp_le_exp.mpr hb.1).trans (hT i)
  have hTone (i : σ) : 1 ≤ T i := (Real.one_le_exp (by linarith : 0 ≤ r + 1)).trans (hTlarge i)
  have hproducts := commonExtractionParameter_products hp hC hCp hM hMp δ l hδp hlp
  have hdim : ((Fintype.card σ + Fintype.card (Fin d) : ℕ) : ℝ) ≤ q := by
    rw [Nat.cast_add, Fintype.card_fin]
    calc
      _ ≤ p + p := add_le_add hσ hd
      _ ≤ q := by linarith [hcontrol.2.1]
  have hmin : Real.exp ((q + 2) ^ 3) < Real.exp (r + 1) :=
    Real.exp_lt_exp.mpr (by change r < r + 1; linarith)
  have hextract := F.common_coefficient_derivative_system e ω hF Wf b rows hblock
    g₀.val g₀.property T hTone Cscale M hC hM l (δ * l)
    ((hweighted T hTpos (M + M) (add_nonneg hM hM)).1)
    (hprojectionGrid l) Hshifts h₀ hh₀ S R Z hbox hcommon hS hR haction
    (Nat.mul_pos hδ hl) density q hdensity hq hdense hdim hproducts.2 hproducts.1
    (hdensityp.trans hepq) (Real.exp (r + 1)) hmin hTlarge
  obtain ⟨perm, a, ha, _, η, hη, ⟨sys⟩⟩ := hextract
  have hsection' := F.exists_reindexed_fast_coefficient_section e ω hF
    (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf b rows sectionMap hsection δ Cscale
    hprojectionGrid hsectionGrid hweighted perm
  obtain ⟨sectionMap', hright', hproj', hgrid', hweighted'⟩ := hsection'
  have har : (a : ℝ) ≤ r := (Nat.cast_le.mpr ha).trans (hd.trans hpr)
  have hTr (i : σ) : Real.exp ((r + C) ^ C) ≤ T i :=
    (Real.exp_le_exp.mpr hb.2.2).trans (hT i)
  have hout := hinit a H r hH hr (hι.trans hpr) (hσ.trans hpr) (hτ.trans hpr) har
    (hHp.trans hepr) hstructure hW v hv hheight g₀ hzero (b.reindex perm.symm)
    (fun i => rows (perm i)) ha η hη sectionMap' hright' Cscale hC (hCp.trans hepr)
    hweighted' δ hδ (hδp.trans hepr) hproj' hgrid' T hTr
    (Real.exp r) (Real.exp_nonneg _) le_rfl sys
  obtain ⟨hk, K, bK, Hk, hHk, hHkp, hKheight, m, hm, hmp, x, g, z, hfactor, hx, hz, X, hX⟩ := hout
  refine ⟨sys.k, hk.trans ha, K, bK, Hk, hHk,
    hHkp.trans (Real.exp_le_exp.mpr hb.2.1), hKheight, m, hm,
    hmp.trans (Real.exp_le_exp.mpr hb.2.2), x, g, z, hfactor, ?_, hz,
    X.enlarge hb.2.2 hTpos, hX⟩
  exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hTpos
    (Real.exp_le_exp.mpr hb.2.2) x.val.coord hx

theorem exists_common_initialState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) (d : ℕ),
        F.CommonInitialStateSpec (σ := σ) (τ := τ) (d := d) e ω hF W C := by
  have h := exists_extracted_initialState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨C, _, hinit⟩ := h
  obtain ⟨D, hD, hbudget⟩ := exists_commonInitialParameter_budget C
  refine ⟨D, hD, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W d
  exact F.exists_initialFormalState_from_common e ω hF W C D hbudget
    (fun a => hinit F e ω hF W a d)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

omit [Fintype σ] [DecidableEq σ] [Fintype ι] in
theorem BoundedInitialStateFactorization.mono
    {g₀ : G} {T : σ → ℝ} {d d' : ℕ} {p q : ℝ}
    (h : F.BoundedInitialStateFactorization e ω hF W g₀ T d p)
    (hd : d ≤ d') (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.BoundedInitialStateFactorization e ω hF W g₀ T d' q := by
  obtain ⟨k, hk, K, bK, Hk, hHk, hHkp, hKb, m, hm, hmp, x, g, z, hfactor, hx, hz, X, hX⟩ := h
  have hepq := Real.exp_le_exp.mpr hpq
  refine ⟨k, hk.trans hd, K, bK, Hk, hHk, hHkp.trans hepq, hKb, m, hm, hmp.trans hepq,
    x, g, z, hfactor, ?_, hz, X.enlarge hpq hT, hX⟩
  exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT hepq x.val.coord hx

def FullInitialStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.BoundedInitialStateFactorization e ω hF W g₀ T
      (Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1)) ((p + C) ^ C)

omit [DecidableEq σ] in
theorem exists_initialFormalState_from_common_family (c C D : ℕ)
    (hcoords : FullFastCoefficientCoordinateSpec.{uσ, uι, uτ, uL} s c)
    (hcommonState : ∀ d : ℕ,
      F.CommonInitialStateSpec (σ := σ) (τ := τ) (d := d) e ω hF W C)
    (hbudget : ∀ p : ℝ, 0 ≤ p → (fullInitialParameter s c p + C) ^ C ≤ (p + D) ^ D) :
    F.FullInitialStateSpec (σ := σ) (τ := τ) e ω hF W D := by
  intro H p hH hp hι hσ hτ hHp hstructure hW v hv hheight g₀ hzero T hT
    M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR density hdensity hdensityp hdense
  have hcoordinateData := hcoords F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    W hW v hv hH hheight hp hι hσ hτ hHp
  obtain ⟨d, hd, rows, _, b, sectionMap, δ, hδ, hδp, hproj, hgrid, hright,
    hweighted, hblock, haction⟩ := hcoordinateData
  let q := fullInitialParameter s c p
  have hcontrol := fullInitialParameter_controls s c hp
  have hpq : p ≤ q := hcontrol.1
  have hq : 0 ≤ q := hp.trans hpq
  have hepq := Real.exp_le_exp.mpr hpq
  have hcoordinateBound : Real.exp ((p + c) ^ c) ≤ Real.exp q :=
    Real.exp_le_exp.mpr hcontrol.2.2
  have hdim : (d : ℝ) ≤ q := by
    have hd' : (d : ℝ) ≤
        (Fintype.card ι : ℝ) * (s + 2) * ((Fintype.card σ : ℝ) + 1) ^ (s + 1) := by
      exact_mod_cast hd
    apply hd'.trans
    apply le_trans _ hcontrol.2.1
    gcongr
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTq (i : σ) : Real.exp ((q + C) ^ C) ≤ T i :=
    (Real.exp_le_exp.mpr (hbudget p hp)).trans (hT i)
  have hout := hcommonState d H q hH hq (hι.trans hpq) (hσ.trans hpq) (hτ.trans hpq) hdim
    (hHp.trans hepq) hstructure hW v hv hheight g₀ hzero b rows sectionMap hright
    (Real.exp ((p + c) ^ c)) (Real.exp_nonneg _) hcoordinateBound hweighted
    δ hδ (hδp.trans hcoordinateBound) hproj hgrid hblock (haction g₀.val g₀.property)
    T hTq M hM (hMp.trans hepq) l hl (hlp.trans hepq) Hshifts h₀ hh₀ S R Z
    hbox hcommon hS hR density hdensity (hdensityp.trans hepq) hdense
  exact hout.mono F e ω hF W hd (hbudget p hp) hTpos

theorem exists_full_initialState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.FullInitialStateSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h₁ := exists_fullFast_coefficient_coordinate_bound.{uσ, uι, uτ, uL} s
  obtain ⟨c, _, hcoords⟩ := h₁
  have h₂ := exists_common_initialState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨C, _, hcommonState⟩ := h₂
  obtain ⟨D, hD, hbudget⟩ := exists_fullInitialParameter_budget s c C
  refine ⟨D, hD, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W
  exact F.exists_initialFormalState_from_common_family e ω hF W c C D hcoords
    (hcommonState F e ω hF W) hbudget

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W)

def NormalizedTerminalFactorization (g₀ : G) (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (T : σ → ℝ) (p : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
    ∃ x g z : G, x * g * z = g₀ ∧
      F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T (Real.exp p) x.val.coord ∧
      F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) m z.val.coord ∧
      F.FastTerminalFactorization e ω hF W η T
        (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val) p

omit [Fintype σ] [Fintype ι] in
theorem NormalizedTerminalFactorization.mono
    {g₀ : G} {η : F.AssociatedGraded →ₗ[ℚ] ℚ} {T : σ → ℝ} {p q : ℝ}
    (h : F.NormalizedTerminalFactorization e ω hF W g₀ η T p)
    (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.NormalizedTerminalFactorization e ω hF W g₀ η T q := by
  obtain ⟨m, hm, hmp, x, g, z, hfactor, hx, hz, hterminal⟩ := h
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpq), x, g, z, hfactor, ?_, hz,
    hterminal.mono F e ω hF W hpq hT⟩
  exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr hpq) x.val.coord hx

def NormalizedTerminalStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hsp : (s + 1 : ℕ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (g₀ : G) (d : ℕ) (_hd : (d : ℝ) ≤ p)
    (_hinitial : F.BoundedInitialStateFactorization e ω hF W g₀ T d p),
    F.NormalizedTerminalFactorization e ω hF W g₀ η T ((p + C) ^ C)

theorem exists_normalized_terminalState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.NormalizedTerminalStateSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h := exists_fast_terminalState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨C, hC, hterminal⟩ := h
  refine ⟨C, hC, ?_⟩
  intro σ ι τ L _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hsp hHp hstructure
    hW v hv hheight η hη T hT g₀ d hd hinitial
  obtain ⟨k, hk, K, bK, Hk, _, hHkp, hKb, m, hm, hmp, x, g, z, hfactor, hx, hz, X, hX⟩ := hinitial
  have hcommon : ((max H Hk : ℕ) : ℝ) ≤ Real.exp p := by
    rw [Nat.cast_max]
    exact max_le hHp hHkp
  have hkr : (k : ℝ) ≤ p := (Nat.cast_le.mpr hk).trans hd
  have hout := hterminal F e ω hF W (max H Hk) p (hH.trans (le_max_left _ _)) hp hs
    hι hσ hτ hsp hcommon (fun i j k => (hstructure i j k).mono (le_max_left _ _))
    hW v hv (fun j i => (hheight j i).mono (le_max_left _ _)) k hkr K bK
    (fun i j => (hKb i j).mono (le_max_right _ _)) η hη T hT X
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hpC : p ≤ (p + C) ^ C := by
    have hCr : (2 : ℝ) ≤ C := Nat.cast_le.mpr hC
    calc
      p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg C)
      _ ≤ (p + C) ^ C := by
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + C)
          (show 1 ≤ C by omega)
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpC), x, g, z, hfactor, ?_, hz, ?_⟩
  · exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hTpos
      (Real.exp_le_exp.mpr hpC) x.val.coord hx
  · exact (congrArg (fun P => F.FastTerminalFactorization e ω hF W η T P ((p + C) ^ C)) hX).mp hout

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def CommonTerminalStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.NormalizedTerminalFactorization e ω hF W g₀ η T ((p + C) ^ C)

theorem exists_common_terminalState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.CommonTerminalStateSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h₁ := exists_full_initialState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨c, _, hinit⟩ := h₁
  have h₂ := exists_normalized_terminalState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨C, _, hterminal⟩ := h₂
  obtain ⟨D, hD, hbudget⟩ := exists_commonTerminalParameter_budget s c C
  refine ⟨D, hD, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure
    hW v hv hheight η hη g₀ hzero T hT
    M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR density hdensity hdensityp hdense
  let q := commonTerminalParameter s c p
  have hcontrol := commonTerminalParameter_controls s c hp
  have hpq : p ≤ q := hcontrol.1
  have hq : 0 ≤ q := hp.trans hpq
  have hp₀q : (p + c) ^ c ≤ q := hcontrol.2.2.1
  have hqfinal : q ≤ (p + D) ^ D := (hbudget p hp).1
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTinitial (i : σ) : Real.exp ((p + c) ^ c) ≤ T i :=
    (Real.exp_le_exp.mpr (hp₀q.trans hqfinal)).trans (hT i)
  have hi := hinit F e ω hF W H p hH hp hι hσ hτ hHp hstructure hW v hv hheight g₀ hzero
    T hTinitial M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR density hdensity hdensityp hdense
  have hiq := hi.mono F e ω hF W le_rfl hp₀q hTpos
  have hd : ((Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) : ℕ) : ℝ) ≤ q := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    apply le_trans _ hcontrol.2.1
    gcongr
  have hTterminal (i : σ) : Real.exp ((q + C) ^ C) ≤ T i :=
    (Real.exp_le_exp.mpr (hbudget p hp).2).trans (hT i)
  have hout := hterminal F e ω hF W H q hH hq hs (hι.trans hpq) (hσ.trans hpq) (hτ.trans hpq)
    hcontrol.2.2.2 (hHp.trans (Real.exp_le_exp.mpr hpq)) hstructure hW v hv hheight
    η hη T hTterminal g₀ _ hd hiq
  exact hout.mono F e ω hF W (hbudget p hp).2 hTpos

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup

universe uσ uι uL

variable {σ : Type uσ} {ι : Type uι} {L : Type uL}
  [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W)

def TerminalCompositionSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (_hT : ∀ i, 0 < T i) (g₀ : G),
    F.NormalizedTerminalFactorization e ω hF W g₀ η T p →
    F.FastTerminalFactorization e ω hF W η T
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g₀.val) ((p + C) ^ C)

theorem exists_terminalComposition_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
        [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.TerminalCompositionSpec (σ := σ) e ω hF W C := by
  have hs := exists_formal_polynomial_product_bound.{uσ, uι, uL} (s + 1) 1 2
  obtain ⟨a, _, hslow⟩ := hs
  have hr := exists_formal_polynomial_product_grid.{uσ, uι, uL} (s + 1) 2
  obtain ⟨b, _, hgrid⟩ := hr
  obtain ⟨C, hC, hbudget⟩ := exists_terminalComposition_budget a b
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF W H p hH hp hι hσ hHp hstructure hW η T hT g₀ hn
  obtain ⟨l, hl, hlp, x, g, z, hnative, hx, hz, hterminal⟩ := hn
  obtain ⟨Z, hZ, hZη, bZ, hbZ, A, P, B, hformal, hA, hB, hzero, hdegree, hcoeff,
    hAbound, m, hm, hmp, hBgrid⟩ := hterminal
  let φ := F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1)
  let bG := F.associatedGradedBasis e ω hF
  let FG := F.associatedGradedFiltration
  have hgraded := F.associatedGradedBasis_homogeneous_brackets e ω hF
  have hlayers := F.associatedGradedFiltration_layer e ω hF
  have hstructureG (i j k : ι) : RationalHeightLE (bG.repr ⁅bG i, bG j⁆ k) H := by
    rw [F.associatedGradedBasis_bracket e ω hF]
    split_ifs
    · exact hstructure i j k
    · exact rationalHeightLE_zero hH
  have h2p : 0 ≤ 2 * p := by positivity
  have hp2 : p ≤ 2 * p := by linarith
  have hι2 := hι.trans hp2
  have hσ2 := hσ.trans hp2
  have hH2 := hHp.trans (Real.exp_le_exp.mpr hp2)
  have hxb := F.realAdaptedGradedPolynomialHom_bound e ω hF (fun _ : σ => 1) T hT
    (Real.exp_nonneg p) x.val hx
  have hzg := F.realAdaptedGradedPolynomialHom_grid e ω hF (fun _ : σ => 1) l z.val hz
  have hxc := F.realAdaptedGradedPolynomialHom_correction e ω hF W hW x
  have hzc := F.realAdaptedGradedPolynomialHom_correction e ω hF W hW z
  have hinput : Real.exp p ≤ Real.exp ((2 * p + 2) ^ 1) :=
    Real.exp_le_exp.mpr (by rw [pow_one]; linarith)
  have hleft := hslow FG bG ω hlayers H (2 * p) hH h2p hι2 hσ2 hH2 hstructureG T hT
    [φ x.val, A] (by simp) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hxc.2.1
      · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hA.2.1) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hxb.mono _ T hT hinput
      · exact hAbound.mono _ T hT hinput)
  have hleftBound : CoefficientBound (bG.baseChange ℝ) T (Real.exp ((2 * p + a) ^ a))
      (φ x.val * A).coord := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hleft
  have hdenom : ((l * m : ℕ) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
  have hcommonB : CoefficientGrid (bG.baseChange ℝ) (l * m) B.coord :=
    fun α => realDenominatorGrid_subset_of_dvd hm (dvd_mul_left m l) (hBgrid α)
  have hcommonz : CoefficientGrid (bG.baseChange ℝ) (l * m) (φ z.val).coord :=
    fun α => realDenominatorGrid_subset_of_dvd hl (dvd_mul_right l m) (hzg α)
  have hg := hgrid FG bG ω hlayers H (2 * p) hH h2p hι2 hσ2 hH2 hstructureG
    (l * m) (Nat.mul_pos hl hm) hdenom
  obtain ⟨n, hn, hnp, _, hproducts⟩ := hg
  have hright := hproducts [B, φ z.val] (by simp) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hB.2.1
    · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hzc.2.1) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hcommonB
    · exact hcommonz)
  have hrightGrid : CoefficientGrid (bG.baseChange ℝ) n (B * φ z.val).coord := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hright
  have hnative' : φ x.val * φ g.val * φ z.val = φ g₀.val := by
    calc
      _ = φ (x.val * g.val * z.val) := by simp only [map_mul]
      _ = φ g₀.val := congrArg φ (congrArg Subtype.val hnative)
  have hfactor : (φ x.val * A) * P * (B * φ z.val) = φ g₀.val := by
    calc
      _ = φ x.val * (A * P * B) * φ z.val := by group
      _ = φ x.val * φ g.val * φ z.val := congrArg (fun t => φ x.val * t * φ z.val) hformal
      _ = _ := hnative'
  have hb := hbudget p hp
  have hep := Real.exp_le_exp.mpr hb.1
  exact ⟨Z, hZ, hZη, bZ, fun i j => ⟨(hbZ i j).1.trans hep, (hbZ i j).2.trans hep⟩,
    φ x.val * A, P, B * φ z.val, hfactor, hxc.mul hgraded hA, hB.mul hgraded hzc,
    hzero, hdegree, hcoeff, hleftBound.mono _ T hT (Real.exp_le_exp.mpr hb.2.1),
    n, hn, hnp.trans (Real.exp_le_exp.mpr hb.2.2), hrightGrid⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def CommonFactorizationSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.FastTerminalFactorization e ω hF W η T
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g₀.val) ((p + C) ^ C)

theorem exists_commonFactorization_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.CommonFactorizationSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h₁ := exists_common_terminalState_bound.{uσ, uι, uτ, uL} s
  obtain ⟨c, _, hcommon⟩ := h₁
  have h₂ := exists_terminalComposition_bound.{uσ, uι, uL} s
  obtain ⟨C, _, hcompose⟩ := h₂
  obtain ⟨D, hD, hbudget⟩ := exists_commonTerminalParameter_budget s c C
  refine ⟨D, hD, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure
    hW v hv hheight η hη g₀ hzero T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z
    hbox hcommonIdentity hS hR density hdensity hdensityp hdense
  let q := commonTerminalParameter s c p
  have hcontrol := commonTerminalParameter_controls s c hp
  have hpq : p ≤ q := hcontrol.1
  have hq : 0 ≤ q := hp.trans hpq
  have hp₀q : (p + c) ^ c ≤ q := hcontrol.2.2.1
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTcommon (i : σ) : Real.exp ((p + c) ^ c) ≤ T i :=
    (Real.exp_le_exp.mpr (hp₀q.trans (hbudget p hp).1)).trans (hT i)
  have hn := hcommon F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure hW v hv hheight
    η hη g₀ hzero T hTcommon M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommonIdentity
    hS hR density hdensity hdensityp hdense
  have hnq := hn.mono F e ω hF W hp₀q hTpos
  have hout := hcompose F e ω hF W H q hH hq (hι.trans hpq) (hσ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hstructure hW η T hTpos g₀ hnq
  exact hout.mono F e ω hF W (hbudget p hp).2 hTpos

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def CommonSymbolFactorizationSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.SymbolTerminalFactorization e ω hF W η T
      (F.realPolynomialSymbolHom e ω hF (fun _ : σ => 1)
        (F.realAdaptedPolynomialGroupHom (fun _ : σ => 1) g₀.val)) ((p + C) ^ C)

theorem exists_common_symbolFactorization_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.CommonSymbolFactorizationSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h := exists_commonFactorization_bound.{uσ, uι, uτ, uL} s
  obtain ⟨C, hC, hfactor⟩ := h
  refine ⟨C, hC, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure
    hW v hv hheight η hη g₀ hzero T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z
    hbox hcommon hS hR density hdensity hdensityp hdense
  apply F.symbolTerminalFactorization_of_native e ω hF W η T g₀.val ((p + C) ^ C)
  exact hfactor F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure hW v hv hheight η hη g₀ hzero
    T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z hbox hcommon hS hR density hdensity hdensityp hdense

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def UnnormalizedCommonSymbolFactorizationSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.SymbolTerminalFactorization e ω hF W η T
      (F.realPolynomialSymbolHom e ω hF (fun _ : σ => 1)
        (F.realAdaptedPolynomialGroupHom (fun _ : σ => 1) g₀.val)) ((p + C) ^ C)

theorem exists_unnormalized_common_symbolFactorization_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.UnnormalizedCommonSymbolFactorizationSpec (σ := σ) (τ := τ) e ω hF W C := by
  obtain ⟨C, hC, hfactor⟩ := exists_common_symbolFactorization_bound.{uσ, uι, uτ, uL} s
  refine ⟨C, hC, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure
    hW v hv hheight η hη g₀ T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z
    hbox hcommon hS hR density hdensity hdensityp hdense
  let g := F.nativeSymbolNormalize e ω hF (fun _ : σ => 1) g₀.val
  have hsymbol : F.realExtendedSymbolMap (fun _ => 1) g.coord =
      F.realExtendedSymbolMap (fun _ => 1) g₀.val.coord :=
    F.nativeSymbolNormalize_symbol e ω hF (fun _ => 1) g₀.val
  have hprojection : F.adaptedReducedRealSymbolHom (fun _ => 1) g =
      F.adaptedReducedRealSymbolHom (fun _ => 1) g₀.val := by
    apply NilpotentLieBCHGroup.ext
    rw [F.adaptedReducedRealSymbolHom_coord, F.adaptedReducedRealSymbolHom_coord, hsymbol]
  have hfast : g ∈ F.realFastDiagonalSubgroup (fun _ => 1)
      (F.fastPointwiseSquare e ω hF (fun _ => 1) W) := by
    rw [F.mem_realFastDiagonalSubgroup, hprojection]
    exact g₀.property
  let g' : F.realFastDiagonalSubgroup (fun _ : σ => 1)
      (F.fastPointwiseSquare e ω hF (fun _ => 1) W) := ⟨g, hfast⟩
  have hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g'.val.coord) 0 = 0 :=
    F.nativeSymbolNormalize_constant e ω hF (fun _ => 1) g₀.val
  have hdir := F.realFirstCoefficientDirectionMap_eq_of_symbol_eq e ω hF g g₀.val hsymbol
  have hadj := F.realFirstCoefficientAdjoint_eq_of_symbol_eq e ω hF (fun _ => 1) g g₀.val hsymbol
  have hcommon' : ∀ h ∈ Hshifts,
      F.realFirstCoefficientDirectionMap g'.val.coord (fun i => (h i : ℝ)) -
        (S h + F.realFirstCoefficientAdjoint (fun _ => 1) g'.val (R h) + Z) ∈
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1)
          (F.fastPointwiseSquare e ω hF (fun _ => 1) W)) := by
    intro h hh
    change F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ => 1) g (R h) + Z) ∈ _
    rw [hdir, hadj]
    exact hcommon h hh
  have hout := hfactor F e ω hF W H p hH hp hs hι hσ hτ hHp hstructure
    hW v hv hheight η hη g' hzero T hT M hM hMp l hl hlp Hshifts h₀ hh₀ S R Z
    hbox hcommon' hS hR density hdensity hdensityp hdense
  have heq : F.realPolynomialSymbolHom e ω hF (fun _ => 1)
      (F.realAdaptedPolynomialGroupHom (fun _ => 1) g'.val) =
      F.realPolynomialSymbolHom e ω hF (fun _ => 1)
        (F.realAdaptedPolynomialGroupHom (fun _ => 1) g₀.val) := by
    apply NilpotentLieBCHGroup.ext
    rw [F.realPolynomialSymbolHom_groupHom_coord, F.realPolynomialSymbolHom_groupHom_coord]
    exact hsymbol
  rw [heq] at hout
  exact hout

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedAdaptedSymbolFactorizationBasis
namespace OAI

section

namespace Erdos3

open Module

theorem rational_basis_coordinates_logHeight
    {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (c : Basis κ ℚ V) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hentries : ∀ i j, RationalHeightLE (c.repr (b i) j) H)
    (x : V) (hx : ∀ i, rationalLogHeight (b.repr x i) ≤ p) (j : κ) :
    rationalLogHeight (c.repr x j) ≤ (p + 2) ^ 4 := by
  classical
  let K := ⌈Real.exp p⌉₊
  have hK : (K : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hKH : ((K * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp p :=
        mul_le_mul hK hH (Nat.cast_nonneg H) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  have hcoord := linearMap_coordinate_height b c (LinearMap.id : V →ₗ[ℚ] V)
    hentries x (fun i => rationalHeightLE_ceil_exp (hx i)) j
  have hcost := rational_sum_cost_le_exp (Fintype.card ι) (K * H) hp 2 1 hKH
    (by simpa only [pow_one] using hι.trans (show p ≤ p + 2 by linarith))
  exact rationalLogHeight_le_of_height hcoord hcost

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ L) (ν : κ → ℕ)
  (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})) (w : σ → ℕ)

theorem gradedSymbolPolynomial_basis_independent :
    F.gradedSymbolPolynomial c ν hC w = F.gradedSymbolPolynomial b ω hF w := by
  apply LinearMap.ext
  intro x
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  apply coefficients.injective
  ext α
  rw [F.gradedSymbolPolynomial_coefficient_symbol, F.gradedSymbolPolynomial_coefficient_symbol]

theorem symbolPointwiseSubalgebra_basis_independent (W : LieSubalgebra ℚ F.AssociatedGraded) :
    F.symbolPointwiseSubalgebra c ν hC w W = F.symbolPointwiseSubalgebra b ω hF w W := by
  ext x
  simp only [F.mem_symbolPointwiseSubalgebra_iff,
    F.gradedSymbolPolynomial_basis_independent b ω hF c ν hC w]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ L) (ν : κ → ℕ)
  (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem polynomialSymbolBasis_change_coordinate [DecidableEq σ] (w : σ → ℕ)
    (i : SymbolBasisIndex w ω) (j : SymbolBasisIndex w ν) :
    (F.polynomialSymbolBasis c ν hC w).repr (F.polynomialSymbolBasis b ω hF w i) j =
      if i.val.1 = j.val.1 then c.repr (b i.val.2) j.val.2 else 0 := by
  classical
  rw [F.polynomialSymbolBasis_apply, F.polynomialSymbolBasis_repr_map,
    F.adaptedMonomialBasis_coe, coefficients_monomial]
  by_cases hij : i.val.1 = j.val.1
  · simp only [hij, Finsupp.single_eq_same, ite_true]
  · simp only [Finsupp.single_eq_of_ne (Ne.symm hij), map_zero, Finsupp.zero_apply, if_neg hij]

theorem associatedGradedBasis_change_coordinate (i : ι) (j : κ) :
    (F.associatedGradedBasis c ν hC).repr (F.associatedGradedBasis b ω hF i) j =
      if ω i = ν j then c.repr (b i) j else 0 := by
  classical
  rw [F.associatedGradedBasis_repr, F.associatedGradedBasis_apply,
    F.polynomialSymbolBasis_change_coordinate]
  simp only [unitMonomial_injective.eq_iff]

theorem associatedGradedBasis_projection (k : ℕ) (i : ι) :
    basisGradeProjection (F.associatedGradedBasis c ν hC) ν k (F.associatedGradedBasis b ω hF i) =
      if ω i = k then F.associatedGradedBasis b ω hF i else 0 := by
  classical
  by_cases hik : ω i = k
  · rw [if_pos hik]
    apply (F.associatedGradedBasis c ν hC).repr.injective
    ext j
    simp only [basisGradeProjection_repr, F.associatedGradedBasis_change_coordinate]
    by_cases hj : ν j = k
    · rw [if_pos hj]
    · rw [if_neg hj, if_neg (show ω i ≠ ν j by omega)]
  · rw [if_neg hik]
    apply (F.associatedGradedBasis c ν hC).repr.injective
    ext j
    simp only [basisGradeProjection_repr, F.associatedGradedBasis_change_coordinate,
      map_zero, Finsupp.zero_apply]
    by_cases hj : ν j = k
    · rw [if_pos hj, if_neg (show ω i ≠ ν j by omega)]
    · rw [if_neg hj]

theorem associatedGraded_projection_basis_independent (k : ℕ) :
    basisGradeProjection (F.associatedGradedBasis c ν hC) ν k =
      basisGradeProjection (F.associatedGradedBasis b ω hF) ω k := by
  apply (F.associatedGradedBasis b ω hF).ext
  intro i
  rw [F.associatedGradedBasis_projection b ω hF c ν hC,
    F.associatedGradedBasis_projection b ω hF b ω hF]

theorem associatedGraded_submodule_basis_independent (U : Submodule ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.associatedGradedBasis c ν hC) ν U ↔
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U := by
  simp only [BasisGradedSubmodule, F.associatedGraded_projection_basis_independent b ω hF c ν hC]

theorem gradedFrequency_top_basis_independent (η : L →ₗ[ℚ] ℚ) (x : F.AssociatedGraded)
    (hx : basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x) :
    F.gradedFrequency c ν hC η x = F.gradedFrequency b ω hF η x := by
  have hm : x ∈ LinearMap.range (F.associatedGradedPieceMap s) := by
    rw [F.associatedGradedPieceMap_range b ω hF]
    rw [← hx]
    exact basisCoordinateProjection_mem_span (F.associatedGradedBasis b ω hF) {i | ω i = s} x
  obtain ⟨v, hv⟩ := hm
  rw [← hv, F.gradedFrequency_top_piece c ν hC, F.gradedFrequency_top_piece b ω hF]

theorem polynomialSymbolBasis_change_height (w : σ → ℕ) {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i j, RationalHeightLE (c.repr (b i) j) H)
    (i : SymbolBasisIndex w ω) (j : SymbolBasisIndex w ν) :
    RationalHeightLE ((F.polynomialSymbolBasis c ν hC w).repr
      (F.polynomialSymbolBasis b ω hF w i) j) H := by
  classical
  rw [F.polynomialSymbolBasis_change_coordinate]
  split_ifs
  · exact hb i.val.2 j.val.2
  · exact rationalHeightLE_zero hH

theorem associatedGradedBasis_change_height {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i j, RationalHeightLE (c.repr (b i) j) H) (i : ι) (j : κ) :
    RationalHeightLE ((F.associatedGradedBasis c ν hC).repr
      (F.associatedGradedBasis b ω hF i) j) H := by
  classical
  rw [F.associatedGradedBasis_change_coordinate]
  split_ifs
  · exact hb i j
  · exact rationalHeightLE_zero hH

theorem native_symbol_basis_independent (w : σ → ℕ) (g : F.RealAdaptedPolynomialGroup w) :
    F.realPolynomialSymbolHom c ν hC w (F.realAdaptedPolynomialGroupHom w g) =
      F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g) := by
  apply NilpotentLieBCHGroup.ext
  rw [F.realPolynomialSymbolHom_groupHom_coord, F.realPolynomialSymbolHom_groupHom_coord]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix NNReal

def ControlledSymbolBasisChangeSpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hb : ∀ i j, RationalHeightLE (c.repr (b i) j) H)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i) (η : L →ₗ[ℚ] ℚ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)),
    F.ControlledSymbolFactorization b ω hF η T X p →
      F.ControlledSymbolFactorization c ν hC η T X ((p + C) ^ C)

theorem exists_controlled_symbol_basis_change (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ControlledSymbolBasisChangeSpec s C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let P : Polynomial ℕ := (Q + 2) ^ 3 + Polynomial.X + (Polynomial.X + 2) ^ 4
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF c ν hc H p hH hp hι hκ hσ hHp hb T hT η X hX
  classical
  let w := fun _ : σ => 1
  let q : ℝ := (p + (s + 2 : ℕ)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℕ) from le_add_of_nonneg_right (Nat.cast_nonneg _)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2 : ℕ) by have := Nat.cast_nonneg (α := ℝ) s; push_cast; linarith)
      (show 1 ≤ s + 2 by omega)
  have hcost : 0 ≤ (q + 2) ^ 3 + p := by positivity
  have hheight : 0 ≤ (p + 2) ^ 4 := by positivity
  have hbound : (q + 2) ^ 3 + p + (p + 2) ^ 4 ≤ (p + C) ^ C := by
    simpa [P, Q, q, Polynomial.eval₂_pow] using hfinal p hp
  have hcostC : (q + 2) ^ 3 + p ≤ (p + C) ^ C := by linarith
  have hheightC : (p + 2) ^ 4 ≤ (p + C) ^ C := by linarith
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s (fun _ => Nat.zero_lt_one) (F.adaptedBasis_weight_le_step b ω hF)
  let : Fintype (SymbolBasisIndex w ν) :=
    symbolBasisIndexFintype w ν s (fun _ => Nat.zero_lt_one) (F.adaptedBasis_weight_le_step c ν hc)
  let Bb := F.polynomialSymbolBasis b ω hF w
  let Bc := F.polynomialSymbolBasis c ν hc w
  let M : Matrix (SymbolBasisIndex w ν) (SymbolBasisIndex w ω) ℚ := fun i j => Bc.repr (Bb j) i
  have hMb : ∀ i j, RationalHeightLE (M i j) H :=
    fun i j => F.polynomialSymbolBasis_change_height b ω hF c ν hc w hH hb j i
  have hDb : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s (fun _ => Nat.zero_lt_one)
      (F.adaptedBasis_weight_le_step b ω hF))).trans
        (by simpa only [q, Nat.cast_add, Nat.cast_ofNat] using
          symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hDc : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ν s (fun _ => Nat.zero_lt_one)
      (F.adaptedBasis_weight_le_step c ν hc))).trans
        (by simpa only [q, Nat.cast_add, Nat.cast_ofNat] using
          symbol_dimension_bound_le_power s (Fintype.card κ) (Fintype.card σ) hp hκ hσ)
  have hHq : (H : ℝ) ≤ Real.exp q := hHp.trans (Real.exp_le_exp.mpr hpq)
  have hδ : (matrixDenominator M : ℝ) ≤ Real.exp ((q + 2) ^ 3) :=
    real_basis_transfer_denominator Bb Bc hq hDb hDc hHq hMb
  have hblock : ∀ i j, i.val.1 ≠ j.val.1 → M i j = 0 := by
    intro i j hij
    change (F.polynomialSymbolBasis c ν hc w).repr (F.polynomialSymbolBasis b ω hF w j) i = 0
    rw [F.polynomialSymbolBasis_change_coordinate, if_neg hij.symm]
  obtain ⟨m, E, R, B, Z, v, hm, hmp, hprod, hE, hB, hv, hZ, hh, hη, hR⟩ := hX
  let n := matrixDenominator M * m
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos M) hm
  have hnC : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    dsimp only [n]
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((q + 2) ^ 3) * Real.exp p := mul_le_mul hδ hmp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((q + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcostC
  have hgrid : F.SymbolRationalGrid c ν hc w n B :=
    real_basis_coordinates_grid Bb Bc m B.coord hB
  have hslow : F.SymbolSlowBound c ν hc w T (Real.exp ((p + C) ^ C)) E := by
    dsimp only [SymbolSlowBound] at hE
    intro i
    have hcoord := congrFun (real_basis_coordinates_transfer Bb Bc E.coord) i
    change |(Bc.baseChange ℝ).repr E.coord i| ≤ _
    rw [hcoord]
    have hEcoord : ∀ j : SymbolBasisIndex w ω,
        |(Bb.baseChange ℝ).repr E.coord j| ≤ Real.exp p / monomialScale T j.val.1 := by
      simpa only [Bb, w] using hE
    have hweighted := weighted_matrix_mulVec_bound (fun i : SymbolBasisIndex w ν => i.val.1)
      (fun j : SymbolBasisIndex w ω => j.val.1) (fun i j => (M i j : ℝ))
      (fun i j hij => by rw [hblock i j hij, Rat.cast_zero]) (H : ℝ≥0)
      (fun i j => (hMb i j).abs_real_le) (monomialScale T) (monomialScale_pos T hT)
      (Real.exp_nonneg p) (fun j => (Bb.baseChange ℝ).repr E.coord j) hEcoord i
    have hfactor : ((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) * ((H : ℝ) + 1) ≤
        Real.exp ((q + 2) ^ 3) := by
      have hHlarge : (H : ℝ) ≤ Real.exp ((q + 2) ^ 1) :=
        hHq.trans (Real.exp_le_exp.mpr (by simp))
      calc
        _ ≤ ((Fintype.card (SymbolBasisIndex w ω) : ℝ) + 1) *
            (Real.exp ((q + 2) ^ 1) + 1) :=
          mul_le_mul_of_nonneg_left (add_le_add hHlarge le_rfl) (by positivity)
        _ ≤ _ := matrix_weighted_factor_le_exp_power _ hq hDb 1 (by decide)
    apply hweighted.trans
    apply div_le_div_of_nonneg_right _ (monomialScale_pos T hT i.val.1).le
    calc
      _ ≤ Real.exp ((q + 2) ^ 3) * Real.exp p := mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg p)
      _ = Real.exp ((q + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcostC
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← finrank_eq_card_basis c, finrank_eq_card_basis b]
  let e := Fintype.equivOfCardEq hcard
  let v' : κ → F.AssociatedGraded := fun i => v (e i)
  have hrange : Set.range v' = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, congrArg v (e.apply_symm_apply i)⟩
  refine ⟨n, E, R, B, Z, v', hn, hnC, hprod, hslow, hgrid, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrange]
    exact hv
  · exact (F.associatedGraded_submodule_basis_independent b ω hF c ν hc Z.toSubmodule).mpr hZ
  · intro i j
    have hx : ∀ k, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v (e i)) k) ≤ p := hh (e i)
    have hbc : ∀ j k, RationalHeightLE ((F.associatedGradedBasis c ν hc).repr
        (F.associatedGradedBasis b ω hF j) k) H :=
      F.associatedGradedBasis_change_height b ω hF c ν hc hH hb
    have htransfer := rational_basis_coordinates_logHeight (F.associatedGradedBasis b ω hF)
      (F.associatedGradedBasis c ν hc) hp hι hHp hbc (v (e i)) hx j
    exact htransfer.trans hheightC
  · intro x hx htop
    have htop' : basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x := by
      rw [← F.associatedGraded_projection_basis_independent b ω hF c ν hc s]
      exact htop
    exact (F.gradedFrequency_top_basis_independent b ω hF c ν hc η x htop').trans (hη x hx htop')
  · rw [F.symbolPointwiseSubalgebra_basis_independent b ω hF c ν hc w]
    simpa only [w] using hR

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

def fixedAdaptedSymbolTransferInput (p q : ℝ) : ℝ :=
  ((p + 3) ^ 5 + q + 1 + 2) ^ 4 + q + 1

theorem exists_fixed_adapted_symbol_factorization_basis (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ (c : Basis (Fin (finrank ℚ L)) ℚ L)
        (ν : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      ∃ hC : ∀ j, D.filtration.layer j =
        Submodule.span ℚ (c '' {i | j ≤ ν i}),
      Monotone ν ∧ IsCentralLieBasis c ∧
      (∀ j i, rationalLogHeight (D.basis.repr (c j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (c.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants c i j k) ≤ (p + 3) ^ 11) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates c D.lattice ∧
      bchSubgroupCoordinates c D.lattice ⊆ denominatorGrid N ∧
      ∀ {q : ℝ}, p ≤ q →
      ∀ {σ : Type*} [Fintype σ], (Fintype.card σ : ℝ) ≤ q →
      ∀ (b : Basis (Fin (finrank ℚ L)) ℚ L)
        (ω : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ j, D.filtration.layer j =
          Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ q) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ (η : L →ₗ[ℚ] ℚ)
        (X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)),
        D.filtration.ControlledSymbolFactorization b ω hF η T X q →
        D.filtration.ControlledSymbolFactorization c ν hC η T X
          ((fixedAdaptedSymbolTransferInput p q + C) ^ C) := by
  obtain ⟨C, hC, hchange⟩ :=
    NilpotentLieFiltration.exists_controlled_symbol_basis_change s
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD
  obtain ⟨c, ν, N, hν, hc, hlayers, hcoord, hinv, hbracket,
    hN, hNp, hin, hout⟩ := D.exists_controlled_adapted_basis hp hD
  refine ⟨c, ν, N, hlayers, hν, hc, hcoord, hinv, hbracket,
    hN, hNp, hin, hout, ?_⟩
  intro q hpq σ _ hσ b ω hF hb T hT η X hX
  let t : ℝ := (p + 3) ^ 5 + q + 1
  let R : ℝ := (t + 2) ^ 4 + q + 1
  have hq : 0 ≤ q := hp.trans hpq
  have hA : 0 ≤ (p + 3) ^ 5 := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hqR : q ≤ R := by
    dsimp only [R]
    linarith [show 0 ≤ (t + 2) ^ 4 by positivity]
  have hR : 0 ≤ R := hq.trans hqR
  have hd : (Fintype.card (Fin d) : ℝ) ≤ q := by
    simpa only [Fintype.card_fin] using hD.1.trans hpq
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ q := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hd
  have hH₀ : (⌈Real.exp ((p + 3) ^ 5)⌉₊ : ℝ) ≤ Real.exp t :=
    (ceil_exp_le_exp_add_one hA).trans
      (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  have hbc : ∀ i j, rationalLogHeight (c.repr (b i) j) ≤ (t + 2) ^ 4 := by
    intro i j
    exact rational_basis_coordinates_logHeight D.basis c ht (hd.trans hqt) hH₀
      (fun i j => rationalHeightLE_ceil_exp (hinv i j)) (b i)
      (fun j => (hb i j).trans hqt) j
  have hH : (⌈Real.exp ((t + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp R :=
    (ceil_exp_le_exp_add_one (by positivity)).trans
      (Real.exp_le_exp.mpr (by dsimp [R]; linarith))
  apply hchange D.filtration b ω hF c ν hlayers
    ⌈Real.exp ((t + 2) ^ 4)⌉₊ R (one_le_ceil_exp _) hR
    (hdim.trans hqR) (hdim.trans hqR) (hσ.trans hqR) hH
    (fun i j => rationalHeightLE_ceil_exp (hbc i j)) T hT η X
  exact hX.mono D.filtration b ω hF hqR hT

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end


