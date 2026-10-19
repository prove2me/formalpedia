-- Prove2me | Definitions.Def_OAIE3v2B165
-- name    : OAIE3v2B165
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:35:02.551462+00:00
-- url     : https://prove2.me/theorems/aa0e5d1b-cbf1-4022-87a8-4d83e1dc6587
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 167 of 311
-- statement:
--   Definitions bundle 167 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152`, `OAIE3v2B153`, `OAIE3v2B154` of this split.
--
--   Modules: `Dynamics/CompatibleReducedFastReset.lean`, `Estimates/CommonNativeSquareFactors.lean`, `Estimates/FastGradedRelativeInvariance.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/NormalizedCommonFamily.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/RealNormalizedSquareFactorization.lean`, `Estimates/ReducedNativeFactorization.lean`, `Estimates/ReindexSymbolFactorization.lean`, `Estimates/TerminalControlledFactorization.lean`, `Estimates/UnconditionalStepDrop.lean`, `Estimates/UniformFrozenDescent.lean`, `Estimates/UnnormalizedCommonSymbolFactorization.lean`, `Fourier/SquareModeGradedFrequency.lean`, `Linear/FixedAdaptedSymbolFactorizationBasis.lean`, `Linear/NativeRankQuotientOrbit.lean`, `Linear/ReducedSquareGradedKernel.lean`, `Linear/ReindexQuotientBasis.lean`, `Linear/SquareBasisGeometry.lean`, `Nilpotent/NativeSquareNiltest.lean`, `Polynomial/NativePolynomialOrbit.lean`, `Polynomial/RealReducedSquarePolynomial.lean`, `Polynomial/RealSquarePolynomialFactors.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152
import Definitions.Def_OAIE3v2B153
import Definitions.Def_OAIE3v2B154

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem reducedSquareSndSymbolMap_basis_height
    (a : ReducedSquareSymbolIndex s w ω) (b : QuotientTopSymbolIndex s w ω) :
    RationalHeightLE ((F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b) 1 :=
  filteredPolynomialSymbolMap_basis_height F.squareFiltration.quotientTop F.quotientTop
    (F.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
    (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w le_rfl
    (fun i j => F.reducedSquareSnd_basis_height e ω hF j i) a b

theorem reducedSquareSndSymbolMap_monomial_blocks
    (a : ReducedSquareSymbolIndex s w ω) (b : QuotientTopSymbolIndex s w ω)
    (hab : b.val.1 ≠ a.val.1) :
    (F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b = 0 :=
  filteredPolynomialSymbolMap_monomial_blocks F.squareFiltration.quotientTop F.quotientTop
    (F.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
    (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w a b hab

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]

theorem exists_controlled_reduced_fast_lift {κ : Type*} [Fintype κ]
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    (hU : BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hrows : (Fintype.card (ReducedSquareSymbolIndex s w ω ⊕ QuotientTopSymbolIndex s w ω) : ℝ) ≤ p)
    (hcols : ((Fintype.card (ReducedSquareSymbolIndex s w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
      (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ g : F.quotientTop.RealPolynomialSymbolGroup w,
        g.coord ∈ realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
          (F.reducedSquareRealLinearLift w S g).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (F.reducedSquareRealLinearLift w S g) = g) ∧
      (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ (B : ℝ), 0 ≤ B →
        ∀ g : F.quotientTop.RealPolynomialSymbolGroup w,
          F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T B g →
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((q + 2) ^ 18) * B) (F.reducedSquareRealLinearLift w S g)) ∧
      (∀ g : F.quotientTop.RealPolynomialSymbolGroup w,
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l g →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m
          (F.reducedSquareRealLinearLift w S g)) := by
  obtain ⟨S, m, hm, hmp, hlm, hsolve, hslow, hgrid⟩ :=
    NilpotentLieBCHGroup.exists_controlled_fast_lift
      (F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.reducedSquareSymbolBasis e ω hF w) (F.quotientTopSymbolBasis e ω hF w)
      (fun z => z.val.1) (fun z => z.val.1) U v hspan hU (F.reducedSquareSndSymbolMap w)
      (fun i j hij => F.reducedSquareSndSymbolMap_monomial_blocks e ω hF w j i hij)
      hH hl hv (fun i j => (F.reducedSquareSndSymbolMap_basis_height e ω hF w j i).mono hH)
      hp hrows hcols hHp hlp
  refine ⟨S, m, hm, hmp, hlm, ?_, ?_, ?_⟩
  · intro g hg
    exact hsolve g hg
  · intro T hT B hB g hg
    exact hslow (monomialScale T) (monomialScale_pos T hT) B hB g hg
  · intro g hg
    exact hgrid g hg

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CompatibleReducedFastReset
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

def ControlledReducedFastResetSpec (s a C : ℕ) : Prop :=
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
      (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
      (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      2 * (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card (ReducedSquareSymbolIndex s w ω ⊕ QuotientTopSymbolIndex s w ω) : ℝ) ≤ p →
      ((Fintype.card (ReducedSquareSymbolIndex s w ω) * Fintype.card κ : ℕ) : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H) →
      ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
        (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A D : F.quotientTop.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        (A⁻¹ * F.reducedSquareRealSymbolHom w E).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        (F.reducedSquareRealSymbolHom w R * D⁻¹).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) E →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
        F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) (A⁻¹ * F.reducedSquareRealSymbolHom w E) →
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l
          (F.reducedSquareRealSymbolHom w R * D⁻¹) →
        let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
        let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
        (E * c⁻¹) * (c * P * d) * (d⁻¹ * R) = E * P * R ∧
          (c * P * d).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (E * c⁻¹) = A ∧
          F.reducedSquareRealSymbolHom w (d⁻¹ * R) = D ∧
          F.reducedSquareRealSymbolHom w (c * P * d) =
            A⁻¹ * F.reducedSquareRealSymbolHom w (E * P * R) * D⁻¹ ∧
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (E * c⁻¹) ∧
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m (d⁻¹ * R)

def ReducedFastResetSpec (s a C : ℕ) : Prop :=
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
      (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H) →
      ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
        (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A D : F.quotientTop.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        (A⁻¹ * F.reducedSquareRealSymbolHom w E).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        (F.reducedSquareRealSymbolHom w R * D⁻¹).coord ∈
          realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) E →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
        F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) (A⁻¹ * F.reducedSquareRealSymbolHom w E) →
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l
          (F.reducedSquareRealSymbolHom w R * D⁻¹) →
        let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
        let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
        (E * c⁻¹) * (c * P * d) * (d⁻¹ * R) = E * P * R ∧
          (c * P * d).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (E * c⁻¹) = A ∧
          F.reducedSquareRealSymbolHom w (d⁻¹ * R) = D ∧
          F.reducedSquareRealSymbolHom w (c * P * d) =
            A⁻¹ * F.reducedSquareRealSymbolHom w (E * P * R) * D⁻¹ ∧
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (E * c⁻¹) ∧
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m (d⁻¹ * R)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_reduced_fast_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ControlledReducedFastResetSpec s a C := by
  obtain ⟨cs, _, hprodSlow⟩ := exists_symbol_slow_mul_inv_bound s
  obtain ⟨cr, _, hprodRat⟩ := exists_symbol_rational_inv_mul_bound s
  obtain ⟨C, hC, hbudget⟩ := exists_reduced_reset_budget a cs cr
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw _ _ U v hspan hU H l p hH hl hp
    hdim hσ hrows hcols hHp hlp hc hv
  let G := F.squareFiltration.quotientTop
  let b := F.reducedSquareBasis e ω hF
  let ν : ReducedSquareBasisIndex s ω → ℕ := fun i => squareBasisWeight ω i.val
  have hG := F.reducedSquareBasis_layers e ω hF
  have hstruct := F.reducedSquareBasis_structure_height e ω hF hH hc
  have hcard : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
    (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
  have hd : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p :=
    (Nat.cast_le.mpr hcard).trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hdim)
  let z := reducedResetParameter a p
  have hz : 0 ≤ z := reducedResetParameter_nonneg a hp
  have hpz : p ≤ z := le_reducedResetParameter a hp
  have hinput := (reducedResetParameter_controls a hp).1
  have hden := (reducedResetParameter_controls a hp).2.1
  have hgain := (reducedResetParameter_controls a hp).2.2
  have hlifts := F.exists_controlled_reduced_fast_lift w e ω hF U v hspan hU hH hl hv hp hrows hcols hHp hlp
  obtain ⟨S, n, hn, hnp, hln, hlift, hliftSlow, hliftRat⟩ := hlifts
  have hnz : (n : ℝ) ≤ Real.exp z := hnp.trans (Real.exp_le_exp.mpr hden)
  have hRats := hprodRat G b ν hG w hw H z hH hz
    (hd.trans hpz) (hσ.trans hpz) (hHp.trans (Real.exp_le_exp.mpr hpz)) hstruct n hn hnz
  obtain ⟨m, hmdata⟩ := hRats
  have hm := hmdata.1
  have hmp := hmdata.2.1
  have hnm := hmdata.2.2.1
  have hRat := hmdata.2.2.2
  have hbud := hbudget p hp
  refine ⟨S, m, hm, hmp.trans (Real.exp_le_exp.mpr hbud.2), hln.trans hnm, ?_⟩
  intro T hT E P R A D hP hleft hright hE hR hLeftSlow hRightRat
  let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
  let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
  have hc := (hlift _ hleft).1
  have hcq := (hlift _ hleft).2
  have hdmem := (hlift _ hright).1
  have hdq := (hlift _ hright).2
  have hreset := synchronize_splitting_projection (F.reducedSquareRealSymbolHom w)
    (NilpotentLieBCHGroup.realificationSubgroup
      (hnil := G.polynomialSymbol_lowerCentralSeries_eq_bot w) U) E P R c d A D hP hc hdmem hcq hdq
  refine ⟨hreset.1, hreset.2.1, hreset.2.2.1, hreset.2.2.2.1, hreset.2.2.2.2, ?_, ?_⟩
  · have hE' : G.SymbolSlowBound b ν hG w T (Real.exp (z + 2)) E := by
      apply G.symbolSlowBound_mono b ν hG w T hT _ E hE
      exact Real.exp_le_exp.mpr hinput
    have hcSlow := hliftSlow T hT (Real.exp ((p + 2) ^ a)) (Real.exp_nonneg _) _ hLeftSlow
    have hc' : G.SymbolSlowBound b ν hG w T (Real.exp (z + 2)) c := by
      apply G.symbolSlowBound_mono b ν hG w T hT _ c hcSlow
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hgain
    have hproduct := hprodSlow G b ν hG w hw H z hH hz (hd.trans hpz) (hσ.trans hpz)
      (hHp.trans (Real.exp_le_exp.mpr hpz)) hstruct T hT E c hE' hc'
    exact G.symbolSlowBound_mono b ν hG w T hT (Real.exp_le_exp.mpr hbud.1) _ hproduct
  · have hRn : G.SymbolRationalGrid b ν hG w n R :=
      G.symbolRationalGrid_mono b ν hG w hl hln R hR
    have hdn : G.SymbolRationalGrid b ν hG w n d := hliftRat _ hRightRat
    exact hRat d R hdn hRn

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def CompatibleReducedFastResetSpec (s a C : ℕ) : Prop :=
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
      (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.reducedSquareSymbolBasis e ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ j i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v j) i) H) →
      ∃ (S : F.quotientTop.PolynomialSymbol w →ₗ[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
        (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A B D : F.quotientTop.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        B.coord ∈ realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
        A * B * D = F.reducedSquareRealSymbolHom w (E * P * R) →
        F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) E →
        F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
        F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
          (Real.exp ((p + 2) ^ a)) A →
        F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
          (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l D →
        let c := F.reducedSquareRealLinearLift w S (A⁻¹ * F.reducedSquareRealSymbolHom w E)
        let d := F.reducedSquareRealLinearLift w S (F.reducedSquareRealSymbolHom w R * D⁻¹)
        (E * c⁻¹) * (c * P * d) * (d⁻¹ * R) = E * P * R ∧
          (c * P * d).coord ∈ realificationLieSubalgebra U ∧
          F.reducedSquareRealSymbolHom w (E * c⁻¹) = A ∧
          F.reducedSquareRealSymbolHom w (d⁻¹ * R) = D ∧
          F.reducedSquareRealSymbolHom w (c * P * d) = B ∧
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (E * c⁻¹) ∧
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w m (d⁻¹ * R)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativePolynomialOrbit
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

variable (F : NilpotentLieFiltration L (s + 1))

theorem nativeReducedPolynomialOrbit_log (g : F.RealAdaptedPolynomialGroup w) :
    (F.nativeReducedPolynomialOrbit w g).log =
      F.quotientTop.realAdaptedPolynomialMap w
        ((F.quotientTopPolynomialMap w).toLinearMap.baseChange ℝ g.coord) := by
  exact (F.realFilteredPolynomialMap_polynomial F.quotientTop
    (lieQuotientMap (F.layerIdeal (s + 1)))
    (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) w g.coord).symm

theorem nativeReducedPolynomialOrbit_symbol
    (b : Basis ι ℚ (L ⧸ F.layerIdeal (s + 1))) (ω : ι → ℕ)
    (hF : ∀ j, F.quotientTop.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (g : F.RealAdaptedPolynomialGroup w) :
    F.quotientTop.realPolynomialSymbolHom b ω hF w
      ⟨⟨(F.nativeReducedPolynomialOrbit w g).log,
        (F.nativeReducedPolynomialOrbit w g).property⟩⟩ =
      F.adaptedReducedRealSymbolHom w g := by
  apply NilpotentLieBCHGroup.ext
  change F.quotientTop.realSymbolOfPolynomial b ω hF w
    (F.nativeReducedPolynomialOrbit w g).log = _
  rw [F.nativeReducedPolynomialOrbit_log,
    F.quotientTop.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  have hmap : (F.quotientTop.polynomialSymbolMap w).toLinearMap.comp
      (F.quotientTopPolynomialMap w).toLinearMap = (F.adaptedReducedSymbolMap w).toLinearMap := by
    apply LinearMap.ext
    intro p
    rfl
  change (F.quotientTop.polynomialSymbolMap w).toLinearMap.baseChange ℝ
    ((F.quotientTopPolynomialMap w).toLinearMap.baseChange ℝ g.coord) =
      (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ g.coord
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hmap]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealSquarePolynomialFactors
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realReducedRelativeCoefficient_of_polynomial (hw : ∀ i, 0 < w i)
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hx : F.realReducedRelativeSquareSymbolMap w hw x = (F.reducedSquareRealRelativePart w g).coord) :
    F.realReducedRelativeCoefficient w hw g =
      F.realFirstCoefficientOfPolynomial b ω hF w
        (F.realAdaptedPolynomialMap w ((F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x)) := by
  rw [F.realFirstCoefficientOfPolynomial_normalized]
  exact (F.realReducedRelativeCoefficient_of_preimage w hw g x hx).symm

variable [Fintype σ]

include b ω hF in
theorem real_normalized_square_coefficient_identity (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (Q : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule (fun _ : σ => 1))
    (hQ : F.realReducedRelativeSquareSymbolMap (fun _ => 1) (fun _ => Nat.zero_lt_one) x =
      (F.reducedSquareRealRelativePart (fun _ => 1) Q).coord)
    (hx : F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
      F.realification.normalizedRelativeLog h e m (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)) :
    F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
        F.realFirstCoefficientConstant (fun _ => 1) e -
        F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) =
      F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) Q := by
  rw [F.realReducedRelativeCoefficient_of_polynomial b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) Q x hQ]
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra (fun _ : σ => 1) => p.val) hx
  change F.realAdaptedPolynomialMap (fun _ => 1)
      ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
    (F.realification.normalizedRelativeLog h e m
      (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val at hc
  rw [hc]
  exact (F.realFirstCoefficientOfPolynomial_normalizedRelativeLog b ω hF h e m g).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealNormalizedSquareFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem exists_real_normalized_square_factors (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (r : F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hf : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-e) (-m) (F.realAdaptedPolynomialMap (fun _ => 1) g.coord))
    (hs : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      F.realAdaptedPolynomialMap (fun _ => 1) g.coord) :
    ∃ x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule (fun _ : σ => 1),
      F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
          F.realification.normalizedRelativeLog h e m
            (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) ∧
      r = F.realRelativeSquarePolynomial (fun _ => 1) (fun _ => Nat.zero_lt_one) x *
        F.realSquareDiagonalPolynomialHom (fun _ => 1) g ∧
      F.realNormalizedFirstCoefficientMap (fun _ => 1) x =
        F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          F.realFirstCoefficientConstant (fun _ => 1) e -
          F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) := by
  have hzero := F.realSquarePolynomial_horizontal (fun _ : σ => 1) r
  rw [hf, hs] at hzero
  obtain ⟨x, hx, hcoeff⟩ := F.exists_real_normalizedRelative_preimage b ω hF h e m g hzero
  let y : F.RealAdaptedPolynomialGroup (fun _ : σ => 1) :=
    ⟨(F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x⟩
  have hshift : F.realAdaptedPolynomialTensor (fun _ => 1)
      (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        F.realification.normalizedShiftAdapted h (-e) (-m)
          (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) := Subtype.ext hf
  have hy : F.realAdaptedPolynomialGroupHom (fun _ => 1) y =
      F.realAdaptedPolynomialGroupHom (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r) *
        (F.realAdaptedPolynomialGroupHom (fun _ => 1) g)⁻¹ := by
    apply NilpotentLieBCHGroup.ext
    change F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
      lieBCH (s + 1)
        (F.realAdaptedPolynomialTensor (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord)
        (-(F.realAdaptedPolynomialTensor (fun _ => 1) g.coord))
    rw [hshift]
    exact hx
  have hfirst : F.realSquareFstPolynomialHom (fun _ => 1) r = y * g := by
    apply F.realAdaptedPolynomialGroupHom_injective (fun _ => 1) b ω hF
    rw [map_mul, hy]
    group
  have hsecond : F.realSquareSndPolynomialHom (fun _ => 1) r = g := by
    apply F.realAdaptedPolynomialGroupHom_injective (fun _ => 1) b ω hF
    apply NilpotentLieBCHGroup.ext
    exact Subtype.ext hs
  exact ⟨x, hx, F.realSquarePolynomial_factorization (fun _ => 1)
    (fun _ => Nat.zero_lt_one) r g x hfirst hsecond, hcoeff⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealReducedSquarePolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem realReducedRelativeSquareSymbolMap_of_square_factorization (hw : ∀ i, 0 < w i)
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (g : F.RealAdaptedPolynomialGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hr : r = F.realRelativeSquarePolynomial w hw x * F.realSquareDiagonalPolynomialHom w g) :
    F.realReducedRelativeSquareSymbolMap w hw x =
      (F.reducedSquareRealRelativePart w (F.squareFiltration.adaptedReducedRealSymbolHom w r)).coord := by
  rw [hr, map_mul, F.adaptedReducedRealSymbolHom_square_relative,
    F.adaptedReducedRealSymbolHom_square_diagonal]
  let k : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w :=
    ⟨F.realReducedRelativeSquareSymbolMap w hw x⟩
  have hk : F.reducedSquareRealSymbolHom w k = 1 := by
    apply NilpotentLieBCHGroup.ext
    exact F.realReducedRelativeSquareSymbolMap_projection w hw x
  have he := F.reducedSquareRealRelativePart_of_factors w k (F.adaptedReducedRealSymbolHom w g) hk
  exact (congrArg NilpotentLieBCHGroup.coord he).symm

variable [Fintype σ] (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem normalized_real_square_derivative_identity (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (r : F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hf : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-e) (-m) (F.realAdaptedPolynomialMap (fun _ => 1) g.coord))
    (hs : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      F.realAdaptedPolynomialMap (fun _ => 1) g.coord) :
    F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
        F.realFirstCoefficientConstant (fun _ => 1) e -
        F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) =
      F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) := by
  obtain ⟨x, hx, hr, _⟩ := F.exists_real_normalized_square_factors b ω hF h e m g r hf hs
  exact F.real_normalized_square_coefficient_identity b ω hF h e m g _ x
    (F.realReducedRelativeSquareSymbolMap_of_square_factorization (fun _ => 1)
      (fun _ => Nat.zero_lt_one) r g x hr) hx

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCommonFamily
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

universe uσ uι uL

theorem exists_native_normalized_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeNormalizedSquareSpec.{uσ, uι, uL} s C := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_realified_square_polynomial.{uσ, uL} (s + 1)
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ d _ _ _ D b ω hF p hp hD h g
  let f : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) :=
    polynomialOrbitOfLog (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord)
      (D.filtration.realAdaptedPolynomialMap_adapted (fun _ => 1) g.coord)
  obtain ⟨ε, γ, hγ, hε, q, hq, hfst, hsnd⟩ := hnorm D p hp hD (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) h f
  let q' : D.filtration.squareFiltration.realification.adaptedLieSubalgebra (fun _ : σ => 1) :=
    ⟨q, (D.filtration.squareFiltration.realification.mem_adaptedSubmodule (fun _ => 1) q).mpr hq⟩
  obtain ⟨r, _, hrf, hrs⟩ := D.filtration.exists_realSquarePolynomial_lift (fun _ => 1) b ω hF q'
  have hf : D.filtration.realAdaptedPolynomialMap (fun _ => 1)
        (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-ε.coord) (-γ.coord)
        (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) := hrf.trans hfst
  have hs : D.filtration.realAdaptedPolynomialMap (fun _ => 1)
        (D.filtration.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord := hrs.trans hsnd
  refine ⟨ε, γ, hγ, hε, r, hf, ?_, ?_⟩
  · apply D.filtration.realAdaptedPolynomialGroupHom_injective (fun _ => 1) b ω hF
    apply NilpotentLieBCHGroup.ext
    exact Subtype.ext hs
  · exact D.filtration.normalized_real_square_derivative_identity b ω hF h ε.coord γ.coord g r hf hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFrozenDescent
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem topQuotientModel_geometry (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N)
    {p : ℝ} (hp : 0 ≤ p)
    (hgeom : (F.ofAdaptedBasis b w hlayers Γ N hN hin hout).GeometryComplexityLE p) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).GeometryComplexityLE p := by
  apply F.coordinateQuotientModel_geometry b w hlayers (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ w i} (hlayers (s + 1)) Γ N hN hin hout hp
  · simpa only [Fintype.card_fin] using hgeom.1
  · exact hgeom.2.1
  · exact hgeom.2.2.1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)

theorem exists_controlled_reduced_square_geometry {p : ℝ}
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis b w (hlayers 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b w (hlayers 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.ofAdaptedBasis
        (D.filtration.squareFinBasis b w (hlayers 2)) (squareFinWeight w)
        (D.filtration.squareFinBasis_layers b w hlayers)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE
          (squareGeometryBudget p) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis b w (hlayers 2)) (squareFinWeight w)
        (D.filtration.squareFinBasis_layers b w hlayers)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE
          (squareGeometryBudget p) := by
  obtain ⟨b, w, hlayers, N, hN, hin, hout, hb, hgeom⟩ :=
    D.exists_controlled_square_geometry hp hD
  exact ⟨b, w, hlayers, N, hN, hin, hout, hb, hgeom,
    D.filtration.squareFiltration.topQuotientModel_geometry _ _ _ _ _ _ _ _
      (squareGeometryBudget_nonneg hp) hgeom⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedSquareBasis_projection_height (e : Basis ι ℚ L) (b : Basis κ ℚ L) (w : κ → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (i : κ ⊕ {i // 2 ≤ w i}) (k : ι) :
    RationalHeightLE (e.repr (F.squareFst (F.adaptedSquareBasis b w h i)) k) H ∧
      RationalHeightLE (e.repr (F.squareSnd (F.adaptedSquareBasis b w h i)) k) H := by
  cases i with
  | inl i =>
    simpa only [squareFst_apply, squareSnd_apply, adaptedSquareBasis_inl] using
      And.intro (hb k i) (hb k i)
  | inr i =>
    constructor
    · simpa only [squareFst_apply, adaptedSquareBasis_inr] using hb k i
    · simp only [squareSnd_apply, adaptedSquareBasis_inr, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero hH

variable [Fintype κ]

theorem squareFinBasis_projection_height (e : Basis ι ℚ L) (b : Basis κ ℚ L) (w : κ → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (i : Fin (Fintype.card (κ ⊕ {i // 2 ≤ w i}))) (k : ι) :
    RationalHeightLE (e.repr (F.squareFst (F.squareFinBasis b w h i)) k) H ∧
      RationalHeightLE (e.repr (F.squareSnd (F.squareFinBasis b w h i)) k) H := by
  simp only [squareFinBasis, Basis.reindex_apply]
  exact F.adaptedSquareBasis_projection_height e b w h hH hb _ k

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeSquareNiltest
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s m : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)
  [TopologicalSpace (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]

theorem exists_square_quotient_niltest_with_orbit
    (b : Basis (Fin m) ℚ F.squareLieSubalgebra) (v : Fin m → ℕ)
    (hlayers : ∀ j, F.squareFiltration.layer j = Submodule.span ℚ (b '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b (F.squareLattice Γ))
    (hout : bchSubgroupCoordinates b (F.squareLattice Γ) ⊆ denominatorGrid N)
    (w : σ → ℕ) (q : F.squareFiltration.realification.PolynomialOrbit w)
    (ε : F.realification.Group) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (χ : F.realification.Group → CircleFourier.Circle)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x, u (z • x) = character (χ z) * u x)
    (A B : ℝ≥0)
    (hLip : letI := realificationQuotientMetricSpace b (F.squareLattice Γ) N hN hout
      LipschitzWith A (F.realSquareObservable Γ ε u))
    (hb : ∀ x, ‖u x‖ ≤ B) :
    let D := F.squareFiltration.topQuotientModel b v hlayers (F.squareLattice Γ) N hN hin hout
    ∀ H : ℕ, 1 ≤ H →
      (∀ i j, RationalHeightLE (D.basis.repr
        (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) (b j)) i) H) →
      (∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H) →
    ∃ T : D.Niltest w,
      T.orbit = F.squareFiltration.realQuotientPolynomialOrbit
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
      (∀ z : F.squareFiltration.realification.Group,
        T.observable (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
          (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
          F.realSquareObservable Γ ε u (QuotientGroup.mk z)) ∧
      T.normBound = B ^ 2 ∧
      T.lipBound = rationalReconstructionLipschitzBound s m
        (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) H A (B ^ 2) ∧
      ∀ x : σ → ℤ, T.eval x = F.realSquareObservable Γ ε u
        (QuotientGroup.mk (F.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  dsimp only
  intro H hH he hc
  let D := F.squareFiltration.topQuotientModel b v hlayers (F.squareLattice Γ) N hN hin hout
  obtain ⟨f, hf, hfLip, hfBound⟩ := F.exists_lipschitz_realSquare_descent Γ
    b D.basis N N H hN hN hH hout D.outer_grid he hc ε u χ hu A B hLip hb
  let K := rationalReconstructionLipschitzBound s m
    (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) H A (B ^ 2)
  let T : D.Niltest w := {
    orbit := F.squareFiltration.realQuotientPolynomialOrbit
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q
    observable := f
    normBound := B ^ 2
    lipBound := K
    norm_le := fun x => by simpa only [NNReal.coe_pow] using hfBound x
    lipschitz := by
      let : MetricSpace (F.squareFiltration.quotientTop.realification.Group ⧸
          ((F.squareLattice Γ).map (F.squareFiltration.quotientStepHom
            (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl)).map realificationHom) :=
        realificationQuotientMetricSpace D.basis _ N hN D.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin, K]; exact le_rfl) }
  refine ⟨T, rfl, hf, rfl, rfl, ?_⟩
  intro x
  change f (QuotientGroup.mk ((F.squareFiltration.quotientTop.realification.polynomialOrbitEval w x)
    (F.squareFiltration.realQuotientPolynomialOrbit
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q))) = _
  exact (congrArg (fun g : F.squareFiltration.quotientTop.realification.Group =>
      f (QuotientGroup.mk g))
    (F.squareFiltration.realQuotientPolynomialOrbit_eval
      (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q x)).trans (hf _)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_correlating_vertical_mode_preserving_characters (T : D.Niltest w)
    {p ρ : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hρ : 0 < ρ) (hρp : (ρ / 2)⁻¹ ≤ Real.exp p)
    {Q : Finset (σ → ℤ)} (hQ : Q.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hcorr : ρ ≤ ‖finiteCorrelation Q f T.eval‖) :
    ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w),
      U.ComplexityLE p ∧ U.orbit = T.orbit ∧
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) =
          character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x) ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
        ∃ n : ℤ, realifyFunctional η z.coord = n) ∧
      (∀ (z : D.RealGroup) (c : ℂ),
        (∀ x, T.observable (z • x) = c * T.observable x) →
          ∀ x, U.observable (z • x) = c * U.observable x) ∧
      ρ / (2 * Real.exp (verticalDecompositionBudget p)) ≤ ‖finiteCorrelation Q f U.eval‖ := by
  obtain ⟨J, inst, hdecomp⟩ := T.exists_controlled_vertical_decomposition hp hT
    (ρ / 2) (by linarith) hρp
  let := inst
  obtain ⟨η, U, hcard, hheight, hU, hchar, hint, hpres, _, herr⟩ := hdecomp
  obtain ⟨j, hj⟩ := exists_correlating_summand hQ f T.eval (fun j => (U j).eval)
    hρ (Real.exp_pos _) hcard hf (fun x _ => herr x) hcorr
  have hne : ∃ x, (U j).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (U j).eval x = 0 := fun x => hzero _
    have hc0 : finiteCorrelation Q f (U j).eval = 0 := by simp [finiteCorrelation, heval]
    rw [hc0, norm_zero] at hj
    exact (not_le_of_gt (div_pos hρ (by positivity))) hj
  exact ⟨η j, U j, (hU j).1, (hU j).2, hheight j, hchar j, hint j hne,
    (fun z c hz x => hpres z c hz j x), hj⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def TranslatedStepDropSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {L : Type uL} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {d : ℕ} [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (p : ℝ) (_hp : 0 ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p)
    (η : L →ₗ[ℚ] ℚ) (_hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (_hvertical : ∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
      T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
        T.observable x)
    (origin : σ → ℤ) (lengths : σ → ℕ) (_hlengths : ∀ i, 0 < lengths i)
    (_hlarge : ∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ))
    (_hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖),
    D.filtration.ControlledSymbolFactorization D.basis ω _hF η (fun i => (lengths i : ℝ))
      (T.symbol D.basis ω _hF) ((p + C) ^ C)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s m : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)
  [TopologicalSpace (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  (bs : Basis (Fin m) ℚ F.squareLieSubalgebra) (ω : Fin m → ℕ)
  (hls : ∀ j, F.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ ω i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (F.squareLattice Γ))
  (hout : bchSubgroupCoordinates bs (F.squareLattice Γ) ⊆ denominatorGrid N)

local notation "Dq" => F.squareFiltration.topQuotientModel bs ω hls (F.squareLattice Γ) N hN hin hout

theorem exists_correlating_square_vertical_mode (hs : 1 ≤ s) (w : σ → ℕ)
    (ε : F.realification.Group) (η : L →ₗ[ℚ] ℚ)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x,
      u (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * u x)
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (S : (Dq).Niltest w)
    (hOrbit : S.orbit = F.squareFiltration.nativeReducedPolynomialOrbit w r)
    (hObs : ∀ z : F.squareFiltration.realification.Group,
      S.observable (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
        F.realSquareObservable Γ ε u (QuotientGroup.mk z))
    {p ρ : ℝ} (hp : 0 ≤ p) (hS : S.ComplexityLE p)
    (hρ : 0 < ρ) (hρp : (ρ / 2)⁻¹ ≤ Real.exp p)
    {A : Finset (σ → ℤ)} (hA : A.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ 1) (hcorr : ρ ≤ ‖finiteCorrelation A f S.eval‖) :
    ∃ (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
      (V : (Dq).Niltest w),
      V.ComplexityLE p ∧ V.orbit = F.squareFiltration.nativeReducedPolynomialOrbit w r ∧
      (∀ i, rationalLogHeight (ξ ((Dq).basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ z ∈ F.squareFiltration.quotientTop.realification.subgroup s, ∀ x,
        V.observable (z • x) =
          character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
      (∀ z : (Dq).RealGroup, z ∈ F.squareFiltration.quotientTop.realification.subgroup s →
        z ∈ (Dq).realLattice → ∃ n : ℤ, realifyFunctional ξ z.coord = n) ∧
      (∀ x : F.layer (s + 1), ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (F.squareRelativeLayer s hs x).val) = η x) ∧
      ρ / (2 * Real.exp (verticalDecompositionBudget p)) ≤ ‖finiteCorrelation A f V.eval‖ := by
  obtain ⟨ξ, V, hV, hVO, hheight, hchar, hint, hpres, hCorr⟩ :=
    S.exists_correlating_vertical_mode_preserving_characters hp hS hρ hρp hA f hf hcorr
  have hne : ∃ x, V.observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, V.eval x = 0 := fun _ => hzero _
    have hc0 : finiteCorrelation A f V.eval = 0 := by simp [finiteCorrelation, heval]
    rw [hc0, norm_zero] at hCorr
    exact (not_le_of_gt (div_pos hρ (by positivity))) hCorr
  refine ⟨ξ, V, hV, hVO.trans hOrbit, hheight, hchar, hint, ?_, hCorr⟩
  exact F.descended_square_mode_frequency_restriction hs Γ ε η u hu
    S.observable V.observable hObs ξ hchar hne hpres

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem reducedSquareDifference_basis (a : ReducedSquareBasisIndex s ω) :
    F.reducedSquareDifference (F.reducedSquareBasis e ω hF a) =
      Sum.elim (fun _ : ι => (0 : L)) (fun i : {i // 2 ≤ ω i} => e i.val) a.val := by
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareDifference_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl i => rw [F.adaptedSquareBasis_inl, sub_self]; rfl
  | inr i => rw [F.adaptedSquareBasis_inr, sub_zero]; rfl

theorem reducedSquareGradedDifference_basis (a : ReducedSquareBasisIndex s ω) :
    F.reducedSquareGradedDifference e ω hF (bW a) =
      Sum.elim (fun _ : ι => (0 : F.AssociatedGraded))
        (fun i : {i // 2 ≤ ω i} => F.associatedGradedBasis e ω hF i.val) a.val := by
  exact Basis.constr_basis _ _ _ a

theorem reducedSquareGradedDifference_gradeProjection (j : ℕ)
    (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.reducedSquareGradedDifference e ω hF (basisGradeProjection bW ωW j x) =
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (j + 1)
        (F.reducedSquareGradedDifference e ω hF x) := by
  have he : (F.reducedSquareGradedDifference e ω hF).comp (basisGradeProjection bW ωW j) =
      (basisGradeProjection (F.associatedGradedBasis e ω hF) ω (j + 1)).comp
        (F.reducedSquareGradedDifference e ω hF) := by
    apply (bW).ext
    intro a
    simp only [LinearMap.comp_apply, basisGradeProjection, basisCoordinateProjection_basis,
      Set.mem_ofPred_eq]
    simp only [apply_ite, map_zero, F.reducedSquareGradedDifference_basis]
    rcases a with ⟨a, ha⟩
    cases a with
    | inl i => simp only [Sum.elim_inl, map_zero, ite_self]
    | inr i =>
      simp only [Sum.elim_inr, squareBasisWeight, basisCoordinateProjection_basis, Set.mem_ofPred_eq]
      have hi : (ω i.val - 1 = j) ↔ ω i.val = j + 1 := by have h := i.property; omega
      simp only [hi]
  exact LinearMap.congr_fun he x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastGradedRelativeInvariance
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

variable (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem fastGradedRelativeKernel_graded
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule bW ωW (F.fastGradedRelativeKernel W) := by
  intro j x hx
  refine ⟨hW j x hx.1, ?_⟩
  change F.reducedSquareGradedSndMap (basisGradeProjection bW ωW j x) = 0
  unfold reducedSquareGradedSndMap
  rw [F.squareFiltration.quotientTop.associatedGradedMap_gradeProjection F.quotientTop
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem j x]
  change basisGradeProjection (F.quotientTop.associatedGradedBasis (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)) (fun i => ω i.val) j
      (F.reducedSquareGradedSndMap x) = 0
  rw [show F.reducedSquareGradedSndMap x = 0 from hx.2, map_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReducedSquareGradedKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

theorem quotientTopGradedMap_piece (j : ℕ) (x : F.layer j) :
    F.quotientTopGradedMap (F.associatedGradedPieceMap j x) =
      F.quotientTop.associatedGradedPieceMap j
        ⟨lieQuotientMap (F.layerIdeal (s + 1)) x,
          F.quotientLie_mem (F.layerIdeal (s + 1)) (t := s) le_rfl x.property⟩ :=
  F.quotientGradedMap_piece (F.layerIdeal (s + 1)) (t := s) le_rfl j x

theorem reducedSquareGradedSnd_piece (j : ℕ) (x : F.squareFiltration.layer j) :
    F.reducedSquareGradedSndMap
      (F.squareFiltration.quotientTopGradedMap (F.squareFiltration.associatedGradedPieceMap j x)) =
    F.quotientTopGradedMap (F.associatedGradedPieceMap j ⟨x.val.val.2, x.property.2.1⟩) := by
  simp only [reducedSquareGradedSndMap, quotientTopGradedMap]
  rfl

theorem reducedSquareGradedPiece_kernel_relative (j : ℕ) (hpos : 1 ≤ j) (hj : j ≤ s)
    (x : F.squareFiltration.layer j)
    (hx : F.reducedSquareGradedSndMap
      (F.squareFiltration.quotientTopGradedMap (F.squareFiltration.associatedGradedPieceMap j x)) = 0) :
    F.reducedSquareGradedRelativePiece j hpos ⟨x.val.val.1 - x.val.val.2, x.property.2.2⟩ =
      F.squareFiltration.quotientTopGradedMap (F.squareFiltration.associatedGradedPieceMap j x) := by
  rw [F.reducedSquareGradedSnd_piece] at hx
  have hsnd := (F.quotientTopGradedMap_piece_eq_zero_iff j hj _).mp hx
  have hd := (F.reducedSquareGradedDiagonalPiece_eq_zero_iff j hj
    ⟨x.val.val.2, x.property.2.1⟩).mpr hsnd
  have hdec := congrArg F.squareFiltration.quotientTopGradedMap
    (F.squareGradedPiece_decomposition j hpos x)
  rw [map_add] at hdec
  change _ = F.reducedSquareGradedDiagonalPiece j ⟨x.val.val.2, x.property.2.1⟩ +
    F.reducedSquareGradedRelativePiece j hpos ⟨x.val.val.1 - x.val.val.2, x.property.2.2⟩ at hdec
  rw [hd, zero_add] at hdec
  exact hdec.symm

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem exists_reducedSquareGradedRelativePiece_of_pure_kernel
    (j : ℕ) (hpos : 1 ≤ j) (hj : j ≤ s)
    (y : F.squareFiltration.quotientTop.AssociatedGraded)
    (hy : basisGradeProjection bW ωW j y = y) (hker : F.reducedSquareGradedSndMap y = 0) :
    ∃ x : F.layer (j + 1), F.reducedSquareGradedRelativePiece j hpos x = y := by
  obtain ⟨q, hq⟩ := F.squareFiltration.quotientTop.exists_associatedGradedPieceMap_of_pure
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) j y hy
  obtain ⟨x, hx, hxq⟩ := q.property
  have he : F.squareFiltration.quotientTopGradedMap
      (F.squareFiltration.associatedGradedPieceMap j ⟨x, hx⟩) = y := by
    rw [F.squareFiltration.quotientTopGradedMap_piece]
    refine Eq.trans ?_ hq
    apply congrArg (F.squareFiltration.quotientTop.associatedGradedPieceMap j)
    exact Subtype.ext hxq
  refine ⟨⟨x.val.1 - x.val.2, hx.2.2⟩, ?_⟩
  exact (F.reducedSquareGradedPiece_kernel_relative j hpos hj ⟨x, hx⟩
    (by rw [he]; exact hker)).trans he

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SquareModeGradedFrequency
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

local notation "bq" => F.reducedSquareBasis b ω hF
local notation "ωq" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "hq" => F.reducedSquareBasis_layers b ω hF

theorem square_gradedFrequency_restriction (hs : 1 ≤ s)
    (η : L →ₗ[ℚ] ℚ)
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (hrestriction : ∀ x : F.layer (s + 1),
      ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (F.squareRelativeLayer s hs x).val) = η x)
    (x : F.layer (s + 1)) :
    F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ
        (F.reducedSquareGradedRelativePiece s hs x) =
      F.gradedFrequency b ω hF η (F.associatedGradedPieceMap (s + 1) x) := by
  change F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ
    (F.squareFiltration.quotientTopGradedMap
      (F.squareFiltration.associatedGradedPieceMap s (F.squareRelativeLayer s hs x))) = _
  rw [F.squareFiltration.quotientTopGradedMap_piece,
    F.squareFiltration.quotientTop.gradedFrequency_top_piece,
    F.gradedFrequency_top_piece]
  exact hrestriction x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TerminalControlledFactorization
namespace OAI

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

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realPolynomialSymbolHom_groupHom_coord (g : F.RealAdaptedPolynomialGroup w) :
    (F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)).coord =
      F.realExtendedSymbolMap w g.coord :=
  F.realSymbolOfPolynomial_realAdaptedPolynomialMap b ω hF w g.coord

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedAdaptedSymbolFactorizationBasis
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexSymbolFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : ι ≃ κ)
  (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)}))

theorem graded_top_annihilation_reindex_iff (η : L →ₗ[ℚ] ℚ)
    (W : LieSubalgebra ℚ F.AssociatedGraded) :
    (∀ x ∈ W, basisGradeProjection
        (F.associatedGradedBasis (b.reindex e) (fun k => ω (e.symm k)) hF')
        (fun k => ω (e.symm k)) s x = x →
      F.gradedFrequency (b.reindex e) (fun k => ω (e.symm k)) hF' η x = 0) ↔
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0) := by
  rw [F.associatedGradedBasis_reindex b ω hF e hF',
    F.gradedFrequency_reindex b ω hF e hF' η]
  simp only [basisGradeProjection_reindex]

theorem graded_top_annihilation_iff_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (η : L →ₗ[ℚ] ℚ) (W : LieSubalgebra ℚ F.AssociatedGraded) :
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis c ν hC) ν s x = x →
      F.gradedFrequency c ν hC η x = 0) ↔
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0) := by
  subst c
  subst ν
  exact F.graded_top_annihilation_reindex_iff b ω hF e hC η W

theorem graded_submodule_iff_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (U : Submodule ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.associatedGradedBasis c ν hC) ν U ↔
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U := by
  subst c
  subst ν
  rw [F.associatedGradedBasis_reindex b ω hF e hC]
  exact basisGradedSubmodule_reindex_iff (F.associatedGradedBasis b ω hF) ω e U

theorem associatedGradedBasis_repr_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (x : F.AssociatedGraded) (i : ι) :
    (F.associatedGradedBasis c ν hC).repr x (e i) =
      (F.associatedGradedBasis b ω hF).repr x i := by
  subst c
  subst ν
  rw [F.associatedGradedBasis_reindex b ω hF e hC,
    Basis.repr_reindex_apply, Equiv.symm_apply_apply]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReindexQuotientBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ : Type*}

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem quotientTopBasis_reindex (e : ι ≃ κ)
    (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)})) :
    F.quotientTopBasis (b.reindex e) (fun k => ω (e.symm k)) hF' =
      (F.quotientTopBasis b ω hF).reindex (reindexWeightSurvivors s ω e) := by
  apply DFunLike.ext
  intro i
  simp only [F.quotientTopBasis_apply, Basis.reindex_apply]
  rfl

variable [Fintype ι]

theorem squareTopQuotientModel_basis_reindex (Γ : Subgroup F.squareFiltration.Group)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ)
    (hout : bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ ⊆ denominatorGrid N) :
    (F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
      (F.squareFinBasis_layers b ω hF) Γ N hN hin hout).basis =
        (F.reducedSquareBasis b ω hF).reindex (reducedSquareFinIndexEquiv s ω) := by
  change (F.squareFiltration.quotientTopBasis (F.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
    (F.squareFinBasis_layers b ω hF)).reindex (Fintype.equivFin _) = _
  have hb := F.squareFiltration.quotientTopBasis_reindex
    (F.adaptedSquareBasis b ω (hF 2)) (squareBasisWeight ω) (F.adaptedSquareBasis_layers b ω hF)
    (Fintype.equivFin _) (F.squareFinBasis_layers b ω hF)
  calc
    _ = ((F.reducedSquareBasis b ω hF).reindex
        (reindexWeightSurvivors s (squareBasisWeight ω) (Fintype.equivFin _))).reindex
          (Fintype.equivFin _) := congrArg (fun c => c.reindex (Fintype.equivFin _)) hb
    _ = _ := by
      apply DFunLike.ext
      intro i
      simp only [Basis.reindex_apply]
      exact (Basis.reindex_apply (F.reducedSquareBasis b ω hF)
        (reducedSquareFinIndexEquiv s ω) i).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionalStepDrop
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace RationalFilteredNilmanifold.Niltest

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem symbol_of_native (T : D.Niltest w) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (g : D.filtration.RealAdaptedPolynomialGroup w) (hg : D.filtration.nativePolynomialOrbit w g = T.orbit) :
    T.symbol b ω hF = D.filtration.realPolynomialSymbolHom b ω hF w
      (D.filtration.realAdaptedPolynomialGroupHom w g) := by
  have he := congrArg (fun a : D.filtration.realification.PolynomialOrbit w =>
    D.filtration.realPolynomialSymbolHom b ω hF w ⟨⟨a.log, a.property⟩⟩) hg
  exact he.symm

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedDiagonalChoiceInput {s : ℕ} (x : Fin 2 → ℤ)
    (j : Fin 2 × MixedReplicatedIndex (s + 2)) : ℤ := x j.1.rev

end Erdos3

end

end OAI
end


