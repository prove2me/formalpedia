-- Prove2me | Definitions.Def_OAIE3v2B238
-- name    : OAIE3v2B238
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:56:40.29348+00:00
-- url     : https://prove2.me/theorems/a8db8c2c-8c36-4b5a-be77-86dc802769c6
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 243 of 311
-- statement:
--   Definitions bundle 243 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B301`, `OAIE3v2B220`, `OAIE3v2B221`, `OAIE3v2B222` of this split.
--
--   Modules: `Estimates/BiasedNativeTerminal.lean`, `Estimates/MixedFixedReduction.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/TerminalControlledFactorization.lean`, `Estimates/UnconditionalStepDrop.lean`, `Estimates/UnnormalizedCommonSymbolFactorization.lean`, `Geometry/ActualFixedSpatialDenseSliceCenter.lean`, `Geometry/ActualFixedSpatialRetainedModulusBudget.lean`, `Lattices/ActualFixedSpatialGoodPrimeDeletion.lean`, `Lattices/ActualFixedSpatialSlicedForecastFromResidueBox.lean`, `Linear/BiasedChosenBasisStepDrop.lean`, `Linear/CommonRankCoefficientCorrections.lean`, `Linear/FullFastHorizontalSpanning.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/RankIntervalFactorization.lean`, `Linear/RankUnadaptedFactorization.lean`, `Probability/ActualFixedSpatialUnchargedDensity.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B301
import Definitions.Def_OAIE3v2B220
import Definitions.Def_OAIE3v2B221
import Definitions.Def_OAIE3v2B222

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "bG" => F.associatedGradedBasis e ω hF

theorem exists_gradedHorizontalKernel_quotient_basis [Fintype ι] [Fintype κ]
    (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ j i, RationalHeightLE ((F.layerOneBasis e ω hF).repr (b j : L ⧸ F.layer 2) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hk : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
      ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ f : Basis (Fin d) ℚ (F.AssociatedGraded ⧸ F.gradedHorizontalKernel e ω hF K),
        ∀ i j, RationalHeightLE (f.repr ((F.gradedHorizontalKernel e ω hF K).mkQ (bG j)) i) H' := by
  exact exists_submodule_quotient_basis_exp bG (F.gradedHorizontalKernel e ω hF K)
    (fun j => (F.gradedHorizontalKernelBasis e ω hF K b j : F.AssociatedGraded))
    (F.gradedHorizontalKernelBasis_span e ω hF K b) hH
    (F.gradedHorizontalKernelBasis_height e ω hF K b hH hb) hp hk hHp

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TerminalControlledFactorization
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnnormalizedCommonSymbolFactorization
namespace OAI

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

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BiasedNativeTerminal
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped BigOperators

theorem exists_synchronized_native_terminal (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedNativeTerminalSpec s C := by
  obtain ⟨a, _, hcommon⟩ := exists_synchronized_native_common_coefficients s
  obtain ⟨b, _, hterminal⟩ := exists_unnormalized_common_symbolFactorization_bound s
  let Q : Polynomial ℕ := ((Polynomial.X + 2) ^ 3 + 3 * Polynomial.X + 1 + Polynomial.C a) ^ a
  let P : Polynomial ℕ := Polynomial.X + Q
  let R : Polynomial ℕ := P + (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ d D e ω hF H l m p hH hl hm hp hs hι hσ hτ hd hHp hlp hmp hgrid hc hb
    W v hv hW hh η hη T hT g S h₀ hh₀ hbox hdense hdata
  let q : ℝ := ((p + 2) ^ 3 + 3 * p + 1 + a) ^ a
  let r : ℝ := p + q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := add_nonneg hp hq
  have hpr : p ≤ r := le_add_of_nonneg_right hq
  have hqr : q ≤ r := le_add_of_nonneg_left hp
  have hterminalPos : 0 ≤ (r + b) ^ b := by positivity
  have hbound : r + (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [R, P, Q, r, q, Polynomial.eval₂_pow] using hfinal p hp
  have hterminalC : (r + b) ^ b ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨n, hn, hnq, _, _, A, B, D₀, small, rational, Z, hprod, hB, hA, hD, _, _, _, hgood⟩ :=
    hcommon D e ω hF H l m p hH hl hm hp hι hσ hd hHp hlp hmp hgrid hc hb
      T hTpos g S h₀ hh₀ W hbox hdata
  let B' : D.filtration.realFastDiagonalSubgroup (fun _ : σ => 1)
      (D.filtration.fastPointwiseSquare e ω hF (fun _ => 1) W) := ⟨B, hB⟩
  have hfactor := hterminal D.filtration e ω hF W H r hH hr hs
    (hι.trans hpr) (hσ.trans hpr) (hτ.trans hpr) (hHp.trans (Real.exp_le_exp.mpr hpr)) hc
    hW v hv hh η hη B' T (fun i => (Real.exp_le_exp.mpr hterminalC).trans (hT i))
    (Real.exp q) (Real.exp_nonneg q) (Real.exp_le_exp.mpr hqr)
    n hn (hnq.trans (Real.exp_le_exp.mpr hqr)) S h₀ hh₀ small rational Z
    hbox (fun h hh => (hgood h hh).1) (fun h hh => (hgood h hh).2.1) (fun h hh => (hgood h hh).2.2)
    (Real.exp (-p)) (Real.exp_pos _) (by
      simpa only [Real.exp_neg, inv_inv] using Real.exp_le_exp.mpr hpr) hdense
  exact ⟨A, B, D₀, hprod, hA, hD,
    SymbolTerminalFactorization.mono D.filtration e ω hF W hfactor hterminalC hTpos⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

theorem exists_biased_native_terminal (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedNativeTerminalSpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_biased_synchronized_square_family s c hI
  obtain ⟨b, _, hterminal⟩ := exists_synchronized_native_terminal s
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let G : Polynomial ℕ := ((Polynomial.X + 3) ^ 11 + 2 * Polynomial.X + 5) ^ 11
  let Q : Polynomial ℕ := B + (Polynomial.X + 4) ^ 11 + (Polynomial.X + 4) ^ 5 + G + Polynomial.X + 2
  let P : Polynomial ℕ := B + (Q + 1) + (Q + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let k : ℝ := (p + a) ^ a
  let q : ℝ := k + (p + 4) ^ 11 + (p + 4) ^ 5 + squareGeometryBudget p + p + 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have h11 : 0 ≤ (p + 4) ^ 11 := by positivity
  have h5 : 0 ≤ (p + 4) ^ 5 := by positivity
  have hgeom := squareGeometryBudget_nonneg hp
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hkq : k ≤ q := by dsimp [q]; linarith
  have h11q : (p + 4) ^ 11 ≤ q := by dsimp [q]; linarith
  have h5q : (p + 4) ^ 5 ≤ q := by dsimp [q]; linarith
  have hGq : squareGeometryBudget p ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq1 : 0 ≤ q + 1 := by linarith
  have hlast : 0 ≤ (q + 1 + b) ^ b := by positivity
  have hbound : k + (q + 1) + (q + 1 + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, B, G, k, q, squareGeometryBudget, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hqC : q + 1 ≤ (p + C) ^ C := by linarith
  have hbC : (q + 1 + b) ^ b ≤ (p + C) ^ C := by linarith
  have hkq1 : k ≤ q + 1 := by linarith
  have hpq1 : p ≤ q + 1 := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, hconstruct⟩ := hfamily hs D p hp T hT
  obtain ⟨hdim, hinverse, hstructure⟩ := D.basis_geometry_of_forward_height e hp hT.1 he
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨S, h₀, l, m, W, u, hh₀, hcount, hl, hlk, hm, hmk, _, hu, hW, hheight, hη, hshift, hdata⟩ :=
    hconstruct g hgOrbit η hvert origin lengths hlengths hσ
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  let H := ⌈Real.exp q⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp q
  have hHp : (H : ℝ) ≤ Real.exp (q + 1) := ceil_exp_le_exp_add_one hq
  have hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hstructure i j k).trans h11q)
  have hb : ∀ i j, RationalHeightLE (e.repr (D.basis j) i) H :=
    fun i j => rationalHeightLE_ceil_exp ((hinverse j i).trans h5q)
  have hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers e ω hF)).repr (u i) j) H :=
    fun i j => rationalHeightLE_ceil_exp ((hheight i j).trans hkq)
  have hτ : (Fintype.card (Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i})) : ℝ) ≤ q + 1 := by
    rw [Fintype.card_fin]
    exact hgeometry.1.trans (hGq.trans (by linarith))
  have hdense : Real.exp (-(q + 1)) * (∏ i, (lengths i : ℝ)) ≤ S.card :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hkq1))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  have hdata' := RationalFilteredNilmanifold.SynchronizedNativeSquareData.mono
    D e ω hF hdata hkq1 hkq1 hTpos
  obtain ⟨A, M, R, hprod, hA, hR, hfactor⟩ := hterminal D e ω hF H l m (q + 1)
    hH hl hm hq1 hs (hdim.trans hpq1) (hσ.trans hpq1) hτ (hT.1.1.trans hpq1) hHp
    (hlk.trans (Real.exp_le_exp.mpr hkq1)) (hmk.trans (Real.exp_le_exp.mpr hkq1))
    (hT.1.2.1.trans (Real.exp_le_exp.mpr hpq1)) hc hb W u hu hW hh
    (D.filtration.gradedFrequency e ω hF η) hη (fun i => (lengths i : ℝ))
    (fun i => (Real.exp_le_exp.mpr hbC).trans (hlarge i)) g S h₀ hh₀
    (fun h hh => (hshift h hh).1) hdense hdata'
  exact ⟨l, W, A, M, R, hl, hlk.trans (Real.exp_le_exp.mpr hkC), hprod,
    D.filtration.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1)
      (fun i => (lengths i : ℝ)) hTpos (Real.exp_le_exp.mpr hqC) A.coord hA, hR,
    SymbolTerminalFactorization.mono D.filtration e ω hF W hfactor hbC hTpos⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedReductionData

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem translation_positive (h δ : ℤ) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u *
      V.eval k (fun j => correlationInput h (n u + δ) j.1)‖) :
    ∃ (a : MixedExpansionIndex V) (b : Fin (D.translation.selectedExpansion k a).count)
      (c : Fin (D.lower h δ a).count), Real.exp (-(q + 3 * P)) ≤
        ‖𝔼 u ∈ S, f u * D.correction h δ k a b c (n u)‖ := by
  have hc : Real.exp (-q) ≤ ‖𝔼 u ∈ S, star (f u) * star
      (V.eval k (fun j => correlationInput h (n u + δ) j.1))‖ := by
    simpa only [← star_mul, ← star_finite_expect, norm_star, mul_comm] using hcorr
  obtain ⟨a, b, c, habc⟩ := D.translation_negative h δ S n k (fun u => star (f u)) q hc
  exact ⟨a, b, c, by simpa only [← star_mul, ← star_finite_expect, norm_star, mul_comm] using habc⟩

end NativeMixedReductionData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFixedReduction
namespace OAI

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem double_translation (h₁ h₂ h₃ h₄ δ : ℤ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin 4 → Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤
      ‖𝔼 u ∈ S, f u * translatedMixedProduct V k h₁ h₂ h₃ h₄ δ (n u)‖) :
    ∃ (t : D.TranslationCode k) (c : D.LowerCode t h₂ h₄ δ),
      Real.exp (-(q + 6 * P)) ≤ ‖𝔼 u ∈ S,
        f u * D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
          D.translationLower t h₂ h₄ δ c (n u) *
          untranslatedMixedProduct V (D.translationCoordinates k t) h₁ h₂ h₃ h₄ (n u)‖ := by
  let f₄ (u : X) := f u * star (V.eval (k 0) (fun j => correlationInput h₁ (n u) j.1)) *
    V.eval (k 1) (fun j => correlationInput h₂ (n u + δ) j.1) *
    V.eval (k 2) (fun j => correlationInput h₃ (n u) j.1)
  have hc₄ : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f₄ u *
      star (V.eval (k 3) (fun j => correlationInput h₄ (n u + δ) j.1))‖ := by
    simpa only [f₄, translatedMixedProduct, fourPointProduct, mul_assoc] using hcorr
  obtain ⟨a₄, b₄, c₄, h₄'⟩ := D.translation_negative h₄ δ S n (k 3) f₄ q hc₄
  let f₂ (u : X) := f u * star (V.eval (k 0) (fun j => correlationInput h₁ (n u) j.1)) *
    V.eval (k 2) (fun j => correlationInput h₃ (n u) j.1) *
    star (D.correction h₄ δ (k 3) a₄ b₄ c₄ (n u))
  have hc₂ : Real.exp (-(q + 3 * P)) ≤ ‖𝔼 u ∈ S, f₂ u *
      V.eval (k 1) (fun j => correlationInput h₂ (n u + δ) j.1)‖ := by
    simpa only [f₄, f₂, mul_assoc, mul_left_comm, mul_comm] using h₄'
  obtain ⟨a₂, b₂, c₂, h₂'⟩ := D.translation_positive h₂ δ S n (k 1) f₂ (q + 3 * P) hc₂
  let t : D.TranslationCode k := ⟨a₂, a₄, b₂, b₄⟩
  let c : D.LowerCode t h₂ h₄ δ := ⟨c₂, c₄⟩
  refine ⟨t, c, ?_⟩
  rw [show (q + 3 * P) + 3 * P = q + 6 * P by ring] at h₂'
  have hmean : (𝔼 u ∈ S, f₂ u * D.correction h₂ δ (k 1) a₂ b₂ c₂ (n u)) =
      𝔼 u ∈ S, f u * D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
        D.translationLower t h₂ h₄ δ c (n u) *
        untranslatedMixedProduct V (D.translationCoordinates k t) h₁ h₂ h₃ h₄ (n u) := by
    apply Finset.expect_congr rfl
    intro u _
    exact D.correction_factorization k t h₁ h₂ h₃ h₄ δ (n u) c (f u) hrel
  rwa [← hmean]

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem reduce_quadruple (h₁ h₂ h₃ h₄ δ : ℤ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin 4 → Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤
      ‖𝔼 u ∈ S, f u * translatedMixedProduct V k h₁ h₂ h₃ h₄ δ (n u)‖) :
    ∃ (a : D.ReductionCode k) (c : D.LowerCode a.translations h₂ h₄ δ),
      Real.exp (-(q + 7 * P)) ≤ ‖𝔼 u ∈ S,
        f u * D.globalError k a ![h₁, h₂, h₃, n u, δ] *
          D.translationLower a.translations h₂ h₄ δ c (n u)‖ := by
  obtain ⟨t, c, ht⟩ := D.double_translation h₁ h₂ h₃ h₄ δ hrel S n k f q hcorr
  let g (u : X) := f u * D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
    D.translationLower t h₂ h₄ δ c (n u)
  have hg : Real.exp (-(q + 6 * P)) ≤ ‖𝔼 u ∈ S, g u *
      mixedParallelogramProduct V (D.translationCoordinates k t) ![h₁, h₂, h₃, n u]‖ := by
    simpa only [g, untranslatedMixedProduct_eq V (D.translationCoordinates k t)
      h₁ h₂ h₃ h₄ _ hrel] using ht
  obtain ⟨j, hj⟩ := (D.parallelogram (D.translationCoordinates k t)).select_sample_product_correlation
    S (fun u => ![h₁, h₂, h₃, n u]) g hg
  refine ⟨⟨t, j⟩, c, ?_⟩
  rw [show (q + 6 * P) + P = q + 7 * P by ring] at hj
  have hglobal (u : X) : D.globalError k ⟨t, j⟩ ![h₁, h₂, h₃, n u, δ] =
      D.translationGlobal k t ![h₁, h₂, h₃, n u, δ] *
        ((D.parallelogram (D.translationCoordinates k t)).test j).eval ![h₁, h₂, h₃, n u] := rfl
  simpa only [hglobal, g, mul_assoc, mul_left_comm, mul_comm] using hj

end Erdos3.NativeMixedReductionData

end

section

namespace Erdos3.NativeMixedReductionData

open scoped BigOperators

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem reduce_family {I X : Type*} (H : Finset I) (hH : H.Nonempty)
    (S : I → Finset X) (n : I → X → ℤ) (h₁ h₂ h₃ h₄ δ : I → ℤ)
    (k : Fin 4 → Fin V.outputDim) (f : I → X → ℂ) (q : ℝ)
    (hrel : ∀ i ∈ H, -h₁ i + h₂ i + h₃ i - h₄ i = 0)
    (hcorr : ∀ i ∈ H, Real.exp (-q) ≤
      ‖𝔼 u ∈ S i, f i u * translatedMixedProduct V k (h₁ i) (h₂ i) (h₃ i) (h₄ i) (δ i) (n i u)‖) :
    ∃ (a : D.ReductionCode k) (Q : Finset I), Q ⊆ H ∧ Q.Nonempty ∧
      Real.exp (-(5 * P)) * (H.card : ℝ) ≤ (Q.card : ℝ) ∧
      ∀ i ∈ Q, ∃ c : D.LowerCode a.translations (h₂ i) (h₄ i) (δ i),
        Real.exp (-(q + 7 * P)) ≤ ‖𝔼 u ∈ S i,
          f i u * D.globalError k a ![h₁ i, h₂ i, h₃ i, n i u, δ i] *
            D.translationLower a.translations (h₂ i) (h₄ i) (δ i) c (n i u)‖ := by
  let rel (i : I) (_ : Unit) (a : D.ReductionCode k) : Prop :=
    ∃ c : D.LowerCode a.translations (h₂ i) (h₄ i) (δ i),
      Real.exp (-(q + 7 * P)) ≤ ‖𝔼 u ∈ S i,
        f i u * D.globalError k a ![h₁ i, h₂ i, h₃ i, n i u, δ i] *
          D.translationLower a.translations (h₂ i) (h₄ i) (δ i) c (n i u)‖
  have hchoice : ∀ i ∈ H, ∀ b, ∃ a, rel i b a := by
    intro i hi _
    exact D.reduce_quadruple (h₁ i) (h₂ i) (h₃ i) (h₄ i) (δ i) (hrel i hi)
      (S i) (n i) k (f i) q (hcorr i hi)
  obtain ⟨a, Q, hsub, hQ, hsize, hfixed⟩ :=
    exists_large_fixed_choices H hH rel hchoice (D.reductionCode_card k)
  refine ⟨a (), Q, hsub, hQ, ?_, fun i hi => hfixed i hi ()⟩
  simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize

end Erdos3.NativeMixedReductionData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3.NativeMultilinearIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q P : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

theorem reduce_mixed (D : NativeMixedReductionData B.mixed P) :
    ∃ (a : D.ReductionCode (fun _ => B.coordinate)) (R : Finset B.quadruples), R.Nonempty ∧
      Real.exp (-(q + 5 * P)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (R.card : ℝ) ∧
      ∀ t ∈ R, ∃ c : D.LowerCode a.translations (t.val.2.1 - t.val.1).val
          (t.val.2.2 - t.val.1).val (B.delta t),
        Real.exp (-(q + 7 * P)) ≤ ‖𝔼 n ∈ B.intervalSet t,
          B.residual t n * D.globalError (fun _ => B.coordinate) a (B.sample t n) *
            D.translationLower a.translations (t.val.2.1 - t.val.1).val
              (t.val.2.2 - t.val.1).val (B.delta t) c n‖ := by
  classical
  have hnonempty : (Finset.univ : Finset B.quadruples).Nonempty := by
    obtain ⟨t, ht⟩ := B.quadruples_nonempty
    exact ⟨⟨t, ht⟩, Finset.mem_univ _⟩
  obtain ⟨a, R, _, hR, hsize, hcor⟩ := D.reduce_family Finset.univ hnonempty
    B.intervalSet (fun _ n => n)
    (fun t => (t.val.2.1.val : ℤ)) (fun t => ((t.val.2.1 - t.val.1).val : ℤ))
    (fun t => (t.val.2.2.val : ℤ)) (fun t => ((t.val.2.2 - t.val.1).val : ℤ))
    B.delta (fun _ => B.coordinate) B.residual q
    (fun t _ => (B.interval t).integer_relation) (fun t _ => B.mixed_correlation t)
  refine ⟨a, R, hR, ?_, hcor⟩
  calc
    Real.exp (-(q + 5 * P)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
        Real.exp (-(5 * P)) * (Real.exp (-q) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(5 * P)) * (B.quadruples.card : ℝ) :=
      mul_le_mul_of_nonneg_left B.quadruples_density (Real.exp_nonneg _)
    _ ≤ (R.card : ℝ) := by simpa only [Finset.card_univ, Fintype.card_coe] using hsize

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

theorem reduce_with_budget {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)
    (D : NativeMixedReductionData B.mixed P) (hq : q ≤ K) (hc : q + 7 * P ≤ K)
    (hg : mixedErrorBudget P ≤ K) (hl : mixedErrorPairBudget P ≤ K) :
    Nonempty (NativeReducedIntervalFamily B D K) := by
  obtain ⟨a, R, hR, hsize, hcor⟩ := B.reduce_mixed D
  have hp : 0 ≤ P := le_trans (by norm_num) D.budget_two
  have hsize' : Real.exp (-K) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (R.card : ℝ) := by
    apply le_trans _ hsize
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    linarith only [hp, hc]
  classical
  exact ⟨{
    base_budget := hq
    correlation_budget := hc
    global_budget := hg
    lower_budget := hl
    code := a
    retained := R
    retained_nonempty := hR
    density := hsize'
    lowerChoice := fun t => Classical.choose (hcor t.val t.property)
    correlation := fun t => (Real.exp_le_exp.mpr (neg_le_neg hc)).trans
      (Classical.choose_spec (hcor t.val t.property)) }⟩

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3.NativeReducedIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
  {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K)

theorem interval_length_ratio (t : R.retained) :
    Real.exp (-K) ≤ ((B.interval t.val).length : ℝ) / N :=
  (Real.exp_le_exp.mpr (neg_le_neg R.base_budget)).trans (B.interval t.val).length_ratio

end Erdos3.NativeReducedIntervalFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BiasedChosenBasisStepDrop
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

theorem exists_biased_chosen_basis_step_drop (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedChosenBasisStepDropSpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_biased_native_terminal s c hI
  obtain ⟨b, _, hcompose⟩ := exists_controlled_symbol_composition (s + 1)
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q : Polynomial ℕ := B + (Polynomial.X + 4) ^ 11 + Polynomial.X + 2
  let P : Polynomial ℕ := B + (Q + 1) + (Q + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let k : ℝ := (p + a) ^ a
  let q : ℝ := k + (p + 4) ^ 11 + p + 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have h11 : 0 ≤ (p + 4) ^ 11 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hkq : k ≤ q := by dsimp [q]; linarith
  have h11q : (p + 4) ^ 11 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq1 : 0 ≤ q + 1 := by linarith
  have hlast : 0 ≤ (q + 1 + b) ^ b := by positivity
  have hbound : k + (q + 1) + (q + 1 + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, B, k, q, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hbC : (q + 1 + b) ^ b ≤ (p + C) ^ C := by linarith
  have hkq1 : k ≤ q + 1 := by linarith
  have hpq1 : p ≤ q + 1 := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, hconstruct⟩ := hfamily hs D p hp T hT
  obtain ⟨hdim, _, hstructure⟩ := D.basis_geometry_of_forward_height e hp hT.1 he
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨l, W, A, M, R, hl, hlk, hprod, hA, hR, hterminal⟩ :=
    hconstruct g hgOrbit η hvert origin lengths hlengths hσ
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  let H := ⌈Real.exp q⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp q
  have hHp : (H : ℝ) ≤ Real.exp (q + 1) := ceil_exp_le_exp_add_one hq
  have hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hstructure i j k).trans h11q)
  let φ : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1) →*
      D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1) :=
    (D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)).comp
      (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1))
  have hinner : D.filtration.ControlledSymbolFactorization e ω hF η
      (fun i => (lengths i : ℝ)) (φ M) (k + 1) :=
    SymbolTerminalFactorization.controlled D.filtration e ω hF W hk hTpos hterminal
  have hinner' := ControlledSymbolFactorization.mono D.filtration e ω hF hinner
    (show k + 1 ≤ q + 1 by linarith) hTpos
  have houter : D.filtration.SymbolSlowBound e ω hF (fun _ => 1)
      (fun i => (lengths i : ℝ)) (Real.exp (q + 1)) (φ A) :=
    D.filtration.symbolSlowBound_mono e ω hF (fun _ => 1) (fun i => (lengths i : ℝ)) hTpos
      (Real.exp_le_exp.mpr hkq1) (φ A)
      (D.filtration.native_symbol_slow e ω hF (fun _ => 1) (fun i => (lengths i : ℝ)) hTpos
        (Real.exp_nonneg k) A hA)
  have hrat : D.filtration.SymbolRationalGrid e ω hF (fun _ => 1) l (φ R) :=
    D.filtration.native_symbol_grid e ω hF (fun _ => 1) l R hR
  have hfull := hcompose D.filtration e ω hF H (q + 1) hH hq1
    (hdim.trans hpq1) (hσ.trans hpq1) hHp hc (fun i => (lengths i : ℝ)) hTpos η
    l hl (hlk.trans (Real.exp_le_exp.mpr hkq1)) (φ A) (φ M) (φ R) houter hrat hinner'
  have heq : φ A * φ M * φ R = φ g := by
    rw [← map_mul, ← map_mul, hprod]
  rw [heq] at hfull
  exact ControlledSymbolFactorization.mono D.filtration e ω hF hfull hbC hTpos

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionalStepDrop
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

universe uσ uL

theorem exists_translated_step_drop_succ (s c : ℕ) (hs : 1 ≤ s)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ TranslatedStepDropSpec.{uσ, uL} (s + 1) C := by
  obtain ⟨a, _, hchosen⟩ := exists_biased_chosen_basis_step_drop s c hI
  obtain ⟨b, _, hchange⟩ := exists_controlled_symbol_basis_change (s + 1)
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let U : Polynomial ℕ := B + Polynomial.X + 3
  let P : Polynomial ℕ := B + U + (U + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ν hD p hp hσ T hT η _hη hvertical origin lengths hlengths hlarge hbias
  let k : ℝ := (p + a) ^ a
  let u : ℝ := k + p + 3
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hku : k ≤ u := by dsimp [u]; linarith
  have hpu : p ≤ u := by dsimp [u]; linarith
  have hp2u : p + 2 ≤ u := by dsimp [u]; linarith
  have hlast : 0 ≤ (u + b) ^ b := by positivity
  have hbound : k + u + (u + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, U, B, k, u, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hbC : (u + b) ^ b ≤ (p + C) ^ C := by linarith
  obtain ⟨τS, hSA, hSM, hST⟩ := exists_real_module_topology
    (D.filtration.squareFinBasis D.basis ν (hD 2))
  let : TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := τS
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hSM
  let : T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) := hST
  obtain ⟨τQ, hQA, hQM, hQT⟩ := exists_real_module_topology
    (D.filtration.reducedSquareBasis D.basis ν hD)
  let : TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := τQ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := hQA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := hQM
  let : T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1))) := hQT
  obtain ⟨e, ω, hF, _N, _hN, _hin, _hout, he, _hgeometry, hconstruct⟩ := hchosen hs D p hp T hT
  obtain ⟨g, hg⟩ := D.filtration.nativePolynomialOrbit_surjective (fun _ : σ => 1) D.basis ν hD T.orbit
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  have hfactor := hconstruct g hg η hvertical origin lengths hlengths hσ
    (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp (p + 1)
  have hHp : (H : ℝ) ≤ Real.exp u := by
    have he := ceil_exp_le_exp_add_one (show 0 ≤ p + 1 by linarith)
    exact he.trans (Real.exp_le_exp.mpr (by linarith))
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ u := by
    rw [Fintype.card_fin, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hT.1.1.trans hpu
  have hd : (Fintype.card (Fin d) : ℝ) ≤ u := by
    simpa only [Fintype.card_fin] using hT.1.1.trans hpu
  have hentries : ∀ i j, RationalHeightLE (D.basis.repr (e i) j) H :=
    fun i j => rationalHeightLE_ceil_exp (he i j)
  have hfactor' := ControlledSymbolFactorization.mono D.filtration e ω hF hfactor hku hTpos
  have hdeclared := hchange D.filtration e ω hF D.basis ν hD H u hH hu hdim hd (hσ.trans hpu)
    hHp hentries (fun i => (lengths i : ℝ)) hTpos η _ hfactor'
  have hsym : D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
      (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) g) = T.symbol D.basis ν hD := by
    exact (D.filtration.native_symbol_basis_independent e ω hF D.basis ν hD (fun _ => 1) g).symm.trans
      (T.symbol_of_native D.basis ν hD g hg).symm
  rw [hsym] at hdeclared
  exact ControlledSymbolFactorization.mono D.filtration D.basis ν hD hdeclared hbC hTpos

theorem exists_translated_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ TranslatedStepDropSpec.{uσ, uL} s C := by
  have h : ∀ n : ℕ, ∃ C : ℕ, 2 ≤ C ∧ TranslatedStepDropSpec.{uσ, uL} (n + 1) C := by
    intro n
    induction n with
    | zero => exact ⟨4, by decide, translatedStepDropSpec_one⟩
    | succ n ih =>
      obtain ⟨C, _hC, hI⟩ := ih
      exact exists_translated_step_drop_succ (n + 1) C (by omega) hI
  cases s with
  | zero => omega
  | succ n => exact h n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankUnadaptedFactorization
namespace OAI

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_rank_biased_symbol_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (T : D.Niltest (fun _ : σ => 1)) → T.ComplexityLE p →
      (η : L →ₗ[ℚ] ℚ) →
      (∀ z ∈ R.realSubgroup s r, ∀ x, T.observable (z • x) =
        character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
      ∃ ξ : L →ₗ[ℚ] ℚ,
        (∀ x ∈ R.filtration.layer s r, ξ x = η x) ∧
        D.filtration.ControlledSymbolFactorization D.basis ω hF ξ (fun i => (lengths i : ℝ))
          (T.symbol D.basis ω hF) ((p + C) ^ C) := by
  obtain ⟨c, _, hstep⟩ := exists_translated_step_drop s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_biased_factorization_budget c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d r _ _ _ _ D R ω hF p hp hσ T hT η hvert origin lengths hlengths hlarge hbias
  have hS : R.filtration.layer s r ≤ D.filtration.layer s := by
    intro y hy
    have h := R.filtration.layer_le_associatedDegree s r hy
    rwa [R.associated] at h
  have hchar : ∀ y ∈ R.filtration.layer s r, ∀ t : ℝ, ∀ x,
      T.observable ((⟨t ⊗ₜ[ℚ] y⟩ : D.RealGroup) • x) =
        character ((t * (η y : ℝ) : ℝ) : CircleFourier.Circle) * T.observable x := by
    intro y hy t x
    have hz : (⟨t ⊗ₜ[ℚ] y⟩ : D.RealGroup) ∈ R.realSubgroup s r :=
      Submodule.tmul_mem_baseChange_of_mem t hy
    simpa only [realifyFunctional_tmul] using hvert _ hz x
  have hQ : (translatedIntegerBox origin lengths).Nonempty := by
    refine ⟨origin, (mem_translatedIntegerBox origin lengths origin).mpr ?_⟩
    intro i
    have hi := hlengths i
    exact ⟨le_rfl, by omega⟩
  obtain ⟨ξ, U, hU, hOrbit, hheight, hUvert, hrestrict, hUbias⟩ :=
    T.exists_biased_mode_restricting_frequency hp hT _ hS η hchar _ hQ hbias
  let q := rankVerticalSelectionBudget p
  have hpq : p ≤ q := by
    have h := (rankVerticalSelectionBudget_bounds hp).1
    dsimp only [q]
    linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hfact := hstep D ω hF q hq (hσ.trans hpq) U hU ξ hheight hUvert origin lengths hlengths
    (fun i => (Real.exp_le_exp.mpr (hbudget p hp).2).trans (hlarge i)) hUbias
  have hsymbol : U.symbol D.basis ω hF = T.symbol D.basis ω hF := by
    unfold RationalFilteredNilmanifold.Niltest.symbol
    apply congrArg (D.filtration.realPolynomialSymbolHom D.basis ω hF (fun _ => 1))
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun o : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) => o.log) hOrbit
  rw [hsymbol] at hfact
  exact ⟨ξ, hrestrict, NilpotentLieFiltration.ControlledSymbolFactorization.mono
    D.filtration D.basis ω hF hfact (hbudget p hp).2 (fun i => by exact_mod_cast hlengths i)⟩

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_rank_biased_refiltration (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (T : D.Niltest (fun _ : σ => 1)) → T.ComplexityLE p →
      (η : L →ₗ[ℚ] ℚ) →
      (∀ z ∈ R.realSubgroup s r, ∀ x, T.observable (z • x) =
        character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
      R.ControlledRankBracketFactorization ω hF η (fun i => (lengths i : ℝ))
        (T.symbol D.basis ω hF) ((p + C) ^ C) := by
  obtain ⟨C, hC, hfactor⟩ := exists_rank_biased_symbol_factorization s hs
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d r _ _ _ _ D R ω hF p hp hσ T hT η hvert origin lengths hlengths hlarge hbias
  obtain ⟨ξ, hrestrict, h⟩ := hfactor D R ω hF p hp hσ T hT η hvert origin lengths hlengths hlarge hbias
  exact R.controlledRankBracketFactorization_of_frequency_restriction ω hF ξ η _ _ _ h hrestrict

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_rank_unadapted_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p → R.ComplexityLE p →
      (T : D.Niltest (fun _ : σ => 1)) → T.ComplexityLE p →
      (η : L →ₗ[ℚ] ℚ) →
      (∀ z ∈ R.realSubgroup s r, ∀ x, T.observable (z • x) =
        character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
      ∃ F : R.AdaptedData,
        F.rank.ComplexityLE ((p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ (p + C) ^ C) ∧
        (∀ j i, rationalLogHeight (F.basis.repr (D.basis j) i) ≤ (p + C) ^ C) ∧
        F.rank.ControlledRankBracketFactorization F.weight F.layers η (fun i => (lengths i : ℝ))
          (T.symbol F.basis F.weight F.layers) ((p + C) ^ C) := by
  obtain ⟨c, _, hfactor⟩ := exists_rank_biased_refiltration s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_adapted_factorization_budget c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d r _ _ _ _ D R p hp hσ hR T hT η hvert origin lengths hlengths hlarge hbias
  obtain ⟨F, hFR, hforward, hback, S, horbit, hobs, hS⟩ := R.exists_adapted_niltest T hp hR hT
  let q := rankAdaptedNiltestBudget p
  have hpq : p ≤ q := le_rankAdaptedNiltestBudget hp
  have hq : 0 ≤ q := hp.trans hpq
  obtain ⟨hqC, hfactorC, hforwardC, hbackC⟩ := hbudget p hp
  have hvertS : ∀ z ∈ F.rank.realSubgroup s r, ∀ x, S.observable (z • x) =
      character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * S.observable x := by
    intro z hz x
    rw [hobs]
    exact hvert z hz x
  have heval (x : σ → ℤ) : S.eval x = T.eval x := by
    unfold RationalFilteredNilmanifold.Niltest.eval
    rw [hobs, horbit]
    rfl
  have hbiasS : Real.exp (-q) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, S.eval x‖ := by
    simp only [heval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias
  have hfact := hfactor F.model F.rank F.weight F.layers q hq (hσ.trans hpq)
    S hS η hvertS origin lengths hlengths
    (fun i => (Real.exp_le_exp.mpr hfactorC).trans (hlarge i)) hbiasS
  have hsymbol : S.symbol F.basis F.weight F.layers = T.symbol F.basis F.weight F.layers := by
    unfold RationalFilteredNilmanifold.Niltest.symbol
    apply congrArg (D.filtration.realPolynomialSymbolHom F.basis F.weight F.layers (fun _ => 1))
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun o : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) => o.log) horbit
  change F.rank.ControlledRankBracketFactorization F.weight F.layers η (fun i => (lengths i : ℝ))
    (S.symbol F.basis F.weight F.layers) ((q + c) ^ c) at hfact
  rw [hsymbol] at hfact
  refine ⟨F, hFR.mono F.rank hqC,
    (fun i j => (hforward i j).trans hforwardC),
    (fun j i => (hback j i).trans hbackC), ?_⟩
  exact RationalFilteredNilmanifold.DegreeRankStructure.ControlledRankBracketFactorization.mono
    F.rank F.weight F.layers hfact hfactorC (fun i => by exact_mod_cast hlengths i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_rank_interval_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : NativeRankInterval W out H t branch p p) →
      Real.exp ((p + C) ^ C) ≤ (I.length : ℝ) →
      ∃ i : Fin I.expansion.count,
        ∃ R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r,
          R₀.ComplexityLE ((p + C) ^ C) ∧ R₀.realSubgroup s r = ⊥ ∧
          ∃ F : (piRank (I.productModels i) (I.productRanks i R₀)).AdaptedData,
            F.rank.ComplexityLE ((p + C) ^ C) ∧
            (∀ j k, rationalLogHeight ((pi (I.productModels i)).basis.repr (F.basis j) k) ≤
              (p + C) ^ C) ∧
            (∀ k j, rationalLogHeight (F.basis.repr ((pi (I.productModels i)).basis k) j) ≤
              (p + C) ^ C) ∧
            F.rank.ControlledRankBracketFactorization F.weight F.layers
              (piFrequency (I.productFrequencies i)) (fun _ : Unit => (I.length : ℝ))
              (I.productSymbol i F.basis F.weight F.layers) ((p + C) ^ C) := by
  obtain ⟨a, _, hproduct⟩ := exists_rank_interval_product s hs
  obtain ⟨c, _, hfactor⟩ := exists_rank_unadapted_factorization s hs
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C a) ^ a + 2 * X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I hlarge
  let u := (p + a) ^ a + 2 * p + 1
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hQu : (p + a) ^ a ≤ u := by dsimp [u]; linarith
  have h2pu : 2 * p ≤ u := by dsimp [u]; linarith
  have hone : 1 ≤ u := by dsimp [u]; linarith
  have hsum : u + (u + c) ^ c ≤ (p + C) ^ C := by
    simpa [U, X, u, Polynomial.eval₂_pow] using hbudget p hp
  have hfactor0 : 0 ≤ (u + c) ^ c := by positivity
  have huC : u ≤ (p + C) ^ C := by linarith
  have hfactorC : (u + c) ^ c ≤ (p + C) ^ C := by linarith
  obtain ⟨i, R₀, hR₀, hzero, htest⟩ := hproduct hp hbp I
  let : FiniteDimensional ℚ
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) :=
    (productFinBasis (I.productModels i)).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) :=
    realification_moduleTopology_t2 (productFinBasis (I.productModels i))
  obtain ⟨T, hT, hR, horbit, _, hvert, hbias⟩ := htest
  have hbiasu : Real.exp (-u) ≤
      ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (I.start : ℤ)) (fun _ => I.length), T.eval x‖ :=
    (Real.exp_le_exp.mpr (neg_le_neg h2pu)).trans hbias
  obtain ⟨F, hFR, hforward, hback, hF⟩ := hfactor (pi (I.productModels i))
    (piRank (I.productModels i) (I.productRanks i R₀)) u hu (by simpa using hone)
    (hR.mono _ hQu) T (hT.mono hQu) (piFrequency (I.productFrequencies i)) hvert
    (fun _ : Unit => (I.start : ℤ)) (fun _ => I.length) (fun _ => I.length_pos)
    (fun _ => (Real.exp_le_exp.mpr hfactorC).trans hlarge) hbiasu
  have hsymbol := I.productSymbol_eq i F.basis F.weight F.layers T horbit
  rw [hsymbol] at hF
  refine ⟨i, R₀, hR₀.mono R₀ (hQu.trans huC), hzero, F, hFR.mono F.rank hfactorC,
    (fun j k => (hforward j k).trans hfactorC),
    (fun k j => (hback k j).trans hfactorC), ?_⟩
  exact DegreeRankStructure.ControlledRankBracketFactorization.mono F.rank F.weight F.layers
    hF hfactorC (fun _ => by exact_mod_cast I.length_pos)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_rank_interval_sunflower (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : NativeRankInterval W out H t branch p p) →
      Real.exp ((p + C) ^ C) ≤ (I.length : ℝ) →
      ∃ i : Fin I.expansion.count,
        ∃ R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r,
          R₀.ComplexityLE ((p + C) ^ C) ∧ R₀.realSubgroup s r = ⊥ ∧
          ∃ F : (piRank (I.productModels i) (I.productRanks i R₀)).AdaptedData,
            F.rank.ComplexityLE ((p + C) ^ C) ∧
            (∀ j k, rationalLogHeight ((pi (I.productModels i)).basis.repr (F.basis j) k) ≤
              (p + C) ^ C) ∧
            (∀ k j, rationalLogHeight (F.basis.repr ((pi (I.productModels i)).basis k) j) ≤
              (p + C) ^ C) ∧
            ∃ (l : ℕ) (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)
              (v : Fin (finrank ℚ (∀ k : Option (Fin 4),
                optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) →
                (pi (I.productModels i)).filtration.AssociatedGraded),
              0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              Submodule.span ℚ (Set.range v) = U.toSubmodule ∧
              BasisGradedSubmodule
                ((pi (I.productModels i)).filtration.associatedGradedBasis F.basis F.weight F.layers)
                F.weight U.toSubmodule ∧
              (∀ j k, rationalLogHeight
                (((pi (I.productModels i)).filtration.associatedGradedBasis F.basis F.weight F.layers).repr
                  (v j) k) ≤ (p + C) ^ C) ∧
              I.BracketKernel i U ∧ I.SunflowerKernel i U ∧
              (pi (I.productModels i)).filtration.SymbolFactorizationIn F.basis F.weight F.layers
                (fun _ : Unit => (I.length : ℝ)) (I.productSymbol i F.basis F.weight F.layers)
                ((p + C) ^ C) l U := by
  obtain ⟨C, hC, hfactor⟩ := exists_rank_interval_factorization s hs
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I hlarge
  obtain ⟨i, R₀, hR₀, hzero, F, hF, hforward, hback, hfact⟩ := hfactor hp hbp I hlarge
  obtain ⟨l, U, v, hl, hlp, hv, hU, hheight, hker, hinside⟩ :=
    DegreeRankStructure.ControlledRankBracketFactorization.exists_in F.rank F.weight F.layers hfact
  exact ⟨i, R₀, hR₀, hzero, F, hF, hforward, hback, l, U, v, hl, hlp, hv, hU, hheight,
    hker, I.sunflowerKernel_of_real i U hker, hinside⟩

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_rank_sunflower_witness (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : NativeRankInterval W out H t branch p p) →
      Real.exp ((p + C) ^ C) ≤ (I.length : ℝ) →
      Nonempty (I.SunflowerWitness ((p + C) ^ C)) := by
  obtain ⟨C, hC, hexists⟩ := exists_rank_interval_sunflower s hs
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H t branch hp hbp I hlarge
  obtain ⟨i, R₀, hR₀, hzero, F, hF, hforward, hback, l, U, v, hl, hlp, hv, hU, hheight,
    hker, hsunflower, hinside⟩ := hexists hp hbp I hlarge
  exact ⟨{
    index := i
    lowerRank := R₀
    lower_complexity := hR₀
    lower_top := hzero
    adapted := F
    adapted_complexity := hF
    forward := hforward
    backward := hback
    denominator := l
    subalgebra := U
    spanning := v
    denominator_pos := hl
    denominator_bound := hlp
    span := hv
    graded := hU
    height := hheight
    bracket := hker
    sunflower := hsunflower
    factorization := hinside
  }⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_common_rank_interval_data (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : α → ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : ∀ a, NativeRankInterval W out H (t a) branch p p) →
      (S : Finset α) → S.Nonempty →
      (∀ a ∈ S, Real.exp ((p + C) ^ C) ≤ ((I a).length : ℝ)) →
      ∃ (K : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L)) (T : Finset α),
        T ⊆ S ∧ T.Nonempty ∧ Real.exp (-((p + C) ^ C)) * S.card ≤ (T.card : ℝ) ∧
        (∀ d, K d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
          ⌈Real.exp (refiltrationCoordinateBudget ((p + C) ^ C))⌉₊) ∧
        ∀ a ∈ T, ∃ E : (I a).SunflowerWitness ((p + C) ^ C),
          (∀ d : Fin (s + 1), E.projection d.val = K d) ∧
          ∀ d : Fin (s + 1), (I a).refilteredHorizontalImage E.index E.subalgebra d.val =
            W.rank.filtration.horizontalImageOfSubmodule (K d) d.val := by
  obtain ⟨c, _, hwitness⟩ := exists_rank_sunflower_witness s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_common_data_budget s c
  refine ⟨C, hC, ?_⟩
  intro α r N _ b p W out H t branch hp hbp I S hS hlarge
  let P := (p + c) ^ c
  have hP : 0 ≤ P := by dsimp [P]; positivity
  obtain ⟨hPC, hcostC⟩ := hbudget p hp
  have hQ : 0 ≤ (p + C) ^ C := hP.trans hPC
  have hex (a : α) (ha : a ∈ S) : Nonempty ((I a).SunflowerWitness P) :=
    hwitness hp hbp (I a) ((Real.exp_le_exp.mpr hPC).trans (hlarge a ha))
  let D (a : α) (ha : a ∈ S) := Classical.choice (hex a ha)
  obtain ⟨K, T, hTS, hT, hsize, _, hdata⟩ := exists_common_rank_projection_family I S hS hP D
  have hdim : (W.dim : ℝ) ≤ p := W.complexity.1.1.trans hbp
  have hcard : Fintype.card (Σ _ : Fin 4, Fin W.dim) = 4 * W.dim := by simp
  have hn : (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) ≤ 4 * p := by
    rw [hcard, Nat.cast_mul]
    norm_num
    linarith
  have hA := refiltrationCoordinateBudget_nonneg hP
  have hcost : 3 * (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) *
      Fintype.card (Σ _ : Fin 4, Fin W.dim) * (refiltrationCoordinateBudget P + 2) * (s + 1) ≤
      (p + C) ^ C := by
    apply le_trans _ hcostC
    change 3 * (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) *
      Fintype.card (Σ _ : Fin 4, Fin W.dim) * (refiltrationCoordinateBudget P + 2) * (s + 1) ≤
      3 * (4 * p) * (4 * p) * (refiltrationCoordinateBudget P + 2) * (s + 1)
    gcongr
  have hnew (a : α) (ha : a ∈ T) : ∃ E : (I a).SunflowerWitness ((p + C) ^ C),
      (∀ d : Fin (s + 1), E.projection d.val = K d) ∧
      ∀ d : Fin (s + 1), (I a).refilteredHorizontalImage E.index E.subalgebra d.val =
        W.rank.filtration.horizontalImageOfSubmodule (K d) d.val := by
    obtain ⟨E, hproj, hhor⟩ := hdata a ha
    exact ⟨E.mono hPC, hproj, hhor⟩
  refine ⟨K, T, hTS, hT, ?_, ?_, hnew⟩
  · apply le_trans _ hsize
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith
  · obtain ⟨a, ha⟩ := hT
    obtain ⟨E, hproj, _⟩ := hnew a ha
    intro d
    rw [← hproj d]
    exact E.projection_mem_candidates hQ d.val

end Erdos3

end

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_common_rank_relation (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)}, 0 ≤ p → b ≤ p →
      (R : NativeRankRelation W out H p p) →
      Real.exp ((p + C) ^ C) ≤ N → Nonempty (R.CommonData ((p + C) ^ C)) := by
  classical
  obtain ⟨c, _, hcommon⟩ := exists_common_rank_interval_data s hs
  obtain ⟨C, hC, hbudget⟩ := exists_common_rank_relation_budget c
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H hp hbp R hN
  let A := (p + c) ^ c
  have hsum : p + A ≤ (p + C) ^ C := hbudget p hp
  have hAQ : A ≤ (p + C) ^ C := by linarith
  obtain ⟨t₀, ht₀⟩ := R.quadruples_nonempty
  let : Nonempty R.quadruples := ⟨⟨t₀, ht₀⟩⟩
  have hlong (t : R.quadruples) (_ht : t ∈ (Finset.univ : Finset R.quadruples)) :
      Real.exp ((p + c) ^ c) ≤ ((R.interval t).length : ℝ) :=
    (R.interval t).length_exp_lower_bound ((Real.exp_le_exp.mpr hsum).trans hN)
  obtain ⟨K, T, _, hT, hsize, _, hdata⟩ :=
    hcommon hp hbp R.interval Finset.univ Finset.univ_nonempty hlong
  let e : R.quadruples ↪ (ZMod N × ZMod N × ZMod N) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Q := T.map e
  have hQR : Q ⊆ R.quadruples := by
    intro t ht
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp ht
    exact u.property
  have hQ : Q.Nonempty := by
    obtain ⟨u, hu⟩ := hT
    exact ⟨e u, Finset.mem_map.mpr ⟨u, hu, rfl⟩⟩
  have hsize' : Real.exp (-A) * (R.quadruples.card : ℝ) ≤ (T.card : ℝ) := by
    simpa only [Finset.card_univ, Fintype.card_coe] using hsize
  have hdensity : Real.exp (-(p + A)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ Q.card := by
    calc
      _ = Real.exp (-A) * (Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
        rw [show -(p + A) = -A + -p by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (-A) * R.quadruples.card :=
        mul_le_mul_of_nonneg_left R.density (Real.exp_pos _).le
      _ ≤ T.card := hsize'
      _ = Q.card := by simp only [Q, Finset.card_map]
  have hwitness (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ Q) :
      ∃ E : (R.interval ⟨t, hQR ht⟩).SunflowerWitness ((p + C) ^ C),
        ∀ d : Fin (s + 1), E.projection d.val = K d := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨E, hproj, _⟩ := hdata u hu
    exact ⟨E.mono hAQ, hproj⟩
  refine ⟨{
    quadruples := Q
    subset := hQR
    nonempty := hQ
    density := ?_
    spaces := K
    witness := fun t ht => Classical.choose (hwitness t ht)
    projection := fun t ht => Classical.choose_spec (hwitness t ht) }⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hsum))
    (by positivity)).trans hdensity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialSlicedForecastFromResidueBox
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def reparameterize
    (δslice' Ppres' : ℝ)
    (commonTuple : G → IntegerScalarCubeBox Empty S.value)
    (prescribed : ℕ → ℕ)
    (origin : ∀ p : path.primes, LayerSamplerLongVariables
      (allocatedShortAxis (I := I) U b S.value) G B → ZMod (p.val ^ path.exponent p.val))
    (hpres : ((∏ p : path.primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres')
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (hwidth : ∀ a p, δslice' ≤ width a p)
    (hlower : ∀ a p, 0 ≤ lower a p)
    (hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1) :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice' P Pbad Ppres' where
  base := path.base
  noise := path.noise
  sample := path.sample
  hs := path.hs
  read := path.read
  readNoise := path.readNoise
  readProjection := path.readProjection
  center := path.center
  commonTuple := commonTuple
  primes := path.primes
  prime := path.prime
  exponent := path.exponent
  prescribed := prescribed
  origin := origin
  Rbad := path.Rbad
  hbad := path.hbad
  RbadBound := path.RbadBound
  presBound := hpres
  lower := lower
  width := width
  hwidth := hwidth
  hlower := hlower
  hcontained := hcontained
  detFalse := path.detFalse
  detTrue := path.detTrue
  hjac := path.hjac
  hinverse := path.hinverse

variable {keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop} [DecidablePred keep]
variable {step : ℕ}
variable (box : ResidueBoxSlice
  (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value)
    (allocatedPrincipalSides B U b S) k.val) step)
variable (hlen : ∀ k, 0 < box.length k)
variable (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k <
  ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))
variable (hactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), keep (Sum.inr ⟨a.val,p⟩))
variable (hstep : 0 < step)
variable (hkernelLength : ∀ g, 2 ≤ box.length ⟨Sum.inl g, hkernel g⟩)
variable (hprescribed : ∀ p, path.prescribed p = padicValNat p step)
variable (horigin : ∀ (p : path.primes) (v : LayerSamplerLongVariables
    (allocatedShortAxis (I := I) U b S.value) G B),
  path.origin p v = ((Sum.elim
    (fun g => (box.start ⟨Sum.inl g,hkernel g⟩ : ℤ))
    (fun a => box.fiberParameterStart fixed (Sum.inr ⟨a.1.val,a.2⟩)) v : ℤ) :
      ZMod (p.val ^ path.exponent p.val)))
variable (hlower : ∀ a p, path.lower a p =
  (box.fiberParameterStart fixed (Sum.inr ⟨a.val,p⟩) : ℝ) /
    allocatedPrincipalSides B U b S ⟨a.val,p⟩)
variable (hwidth : ∀ a p, path.width a p =
  (ResidueBoxSlice.fiberParameterStride (keep := keep) (q := step) (Sum.inr ⟨a.val,p⟩) : ℝ) *
    (box.fiberParameterLength (Sum.inr ⟨a.val,p⟩) - 1 : ℕ) /
      allocatedPrincipalSides B U b S ⟨a.val,p⟩)

noncomputable def withResidueBoxSlice :
    ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres where
  path := path
  step := step
  step_pos := hstep
  kernelLength g := box.length ⟨Sum.inl g, hkernel g⟩
  kernelStart g := box.start ⟨Sum.inl g, hkernel g⟩
  kernelLength_two := hkernelLength
  kernelInside g t := by
    constructor
    · positivity
    · exact_mod_cast box.inside ⟨Sum.inl g, hkernel g⟩ t.val t.isLt
  principalLength j := box.fiberParameterLength (Sum.inr j)
  principalStep j := ResidueBoxSlice.fiberParameterStride (keep := keep) (q := step) (Sum.inr j)
  principalStart j := box.fiberParameterStart fixed (Sum.inr j)
  principalLength_pos j := box.fiberParameterLength_pos hlen (Sum.inr j)
  principalInside := box.fiberPrincipalParameter_inside hlen fixed hfixed
  principalStep_active a p := by
    simp only [ResidueBoxSlice.fiberParameterStride, if_pos (hactive a p)]
  prescribed_eq := hprescribed
  origin_eq := horigin
  lower_eq := hlower
  width_eq := hwidth

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialDenseSliceCenter
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

attribute [instance] ActualFixedSpatialDenseSliceInput.keepDecidable

namespace ActualFixedSpatialDenseSliceInput
variable {s q} (input : ActualFixedSpatialDenseSliceInput s q)

theorem side_pos (k : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n)) :
    0 < Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k := by
  cases k with
  | inl g => exact S.positive
  | inr j => exact allocatedPrincipalSides_pos B U b S j

omit [DecidableEq X] in
theorem length_pos (k : {k // input.keep k}) : 0 < input.box.length k := by
  have hp : (0 : ℝ) < ((Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U b S) k.val : ℕ) : ℝ) := Nat.cast_pos.mpr (side_pos (S := S) k.val)
  exact Nat.cast_pos.mp ((mul_pos (Real.exp_pos _) hp).trans_le (input.dense k))

noncomputable def principalLower
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a})
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) : ℝ :=
  (input.box.fiberParameterStart input.fixed (Sum.inr ⟨a.val,p⟩) : ℝ) /
    allocatedPrincipalSides B U b S ⟨a.val,p⟩

noncomputable def principalWidth
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a})
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) : ℝ :=
  (ResidueBoxSlice.fiberParameterStride (keep := input.keep) (q := input.step)
    (Sum.inr ⟨a.val,p⟩) : ℝ) *
    (input.box.fiberParameterLength (Sum.inr ⟨a.val,p⟩) - 1 : ℕ) /
      allocatedPrincipalSides B U b S ⟨a.val,p⟩

omit [DecidableEq X] in
theorem kernel_exp_width : Real.exp (-q.v) ≤ Real.exp (-input.cost) / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    Real.exp (-q.v) ≤ Real.exp (-input.cost - 1) := Real.exp_le_exp.mpr (by linarith [input.kernel_log])
    _ = Real.exp (-input.cost) / Real.exp 1 := Real.exp_sub _ _
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) htwo

end ActualFixedSpatialDenseSliceInput

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialUnchargedDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def referenceBadDepth (p : ℕ) : ℕ := by
  letI := path.primeNeZero
  exact allocatedCongruenceBadDepth (allocatedShortAxis (I := I) U b S.value)
    path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
    spatial kernel block path.primes path.exponent
    (modularForecastRankConstant m Dmod : ℝ) p

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialGoodPrimeDeletion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

local instance retainedReferencePrimeNeZero_reb9735_1 : ∀ p : path.primes, NeZero p.val :=
  path.primeNeZero
noncomputable def referenceRetainedPrimes (cutoff : ℕ) : Finset path.primes :=
  Finset.univ.filter (fun p => path.referenceBadDepth p.val ≠ 0 ∨
    path.prescribed p.val ≠ 0 ∨ p.val ≤ cutoff)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedModulusBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

@[instance_reducible] noncomputable def retainedLabelDecidableEq (cutoff : ℕ) :
    DecidableEq (path.referenceRetainedPrimes cutoff) := Classical.decEq _

attribute [local instance] retainedLabelDecidableEq

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

end OAI
end


