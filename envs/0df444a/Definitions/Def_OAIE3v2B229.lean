-- Prove2me | Definitions.Def_OAIE3v2B229
-- name    : OAIE3v2B229
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:24:11.449922+00:00
-- url     : https://prove2.me/theorems/de19a47d-06d7-477c-8433-33ed713b4a27
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 234 of 311
-- statement:
--   Definitions bundle 234 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B206`, `OAIE3v2B207`, `OAIE3v2B208`, `OAIE3v2B209`, `OAIE3v2B210` of this split.
--
--   Modules: `Dynamics/ActualPathCurrentGradeReset.lean`, `Estimates/ControlledPrescribedMarkedNativeFactorization.lean`, `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/NativeMajorCorrelationFamily.lean`, `Geometry/CertifiedFullChartRecoveredTerminal.lean`, `Geometry/TerminalChartSlowEvaluation.lean`, `Linear/ControlledProjectionUniformBudget.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/PreparedPolynomialIdentity.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B206
import Definitions.Def_OAIE3v2B207
import Definitions.Def_OAIE3v2B208
import Definitions.Def_OAIE3v2B209
import Definitions.Def_OAIE3v2B210

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ActualPathCurrentGradeReset
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem exists_actual_path_current_grade_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {τ ι κ L : Type*} [Fintype τ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (v : τ → ℕ), (∀ i, 0 < v i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card τ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : τ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (U : LieSubalgebra ℚ F.AssociatedGraded) (vg : κ → F.PolynomialSymbol v),
        Submodule.span ℚ (Set.range vg) = (F.symbolPointwiseSubalgebra b ω hF v U).toSubmodule →
        (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF v).repr (vg i) z) H) →
        ∀ {σ : Type*} (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ),
        ∀ hβ : ∀ i, β i ∈ weightedSupportLE v (w i),
        ∀ K : Set (σ → ℝ),
        (∀ u : τ → ℝ,
          (fun i => MvPolynomial.eval u (weightedHomogeneousComponent v (w i) (β i))) ∈ K) →
        ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
          (E R : F.RealPolynomialSymbolGroup w) (k : ℕ), k ≤ s + 1 →
        (∀ t ∈ K, ∀ j < k, F.realSymbolGradeEvaluation b ω hF w j t
          (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈ realificationLieSubalgebra U) →
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v
          (fun i => weightedHomogeneousComponent v (w i) (β i))
          (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        ∀ (El Pl Rl : F.RealPolynomialSymbolGroup v),
        El * Pl * Rl = F.realPolynomialSymbolHom b ω hF v
          (F.weightedAdaptedRealChartHom w v β hβ g) →
        Pl.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) →
        F.SymbolSlowBound b ω hF v T (Real.exp ((p + 2) ^ a)) El →
        F.SymbolSlowBound b ω hF v T (Real.exp ((p + 2) ^ a)) (pull E) →
        F.SymbolRationalGrid b ω hF v l Rl → F.SymbolRationalGrid b ω hF v l (pull R) →
        ∃ E' P' R' : F.RealPolynomialSymbolGroup v,
          E' * P' * R' = F.realPolynomialSymbolHom b ω hF v
            (F.weightedAdaptedRealChartHom w v β hβ g) ∧
          P'.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) ∧
          F.realSymbolGradeQuotientHom v k (pull E) = F.realSymbolGradeQuotientHom v k E' ∧
          F.realSymbolGradeQuotientHom v k R' = F.realSymbolGradeQuotientHom v k (pull R) ∧
          F.SymbolSlowBound b ω hF v T (Real.exp ((p + C) ^ C)) E' ∧
          F.SymbolRationalGrid b ω hF v m R' ∧
          F.SymbolSlowBound b ω hF v T (Real.exp ((p + C) ^ C)) ((pull E)⁻¹ * E') ∧
          F.SymbolRationalGrid b ω hF v m (R' * (pull R)⁻¹) := by
  obtain ⟨cr, _, hreset⟩ := exists_symbol_reset_from_common_quotient s a
  obtain ⟨cs, _, hslowprod⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨ct, _, hratprod⟩ := exists_symbol_rational_product_bound s 2
  obtain ⟨C, hC, hbudget⟩ := exists_actual_path_reset_budget a cr cs ct
  refine ⟨C, hC, ?_⟩
  intro τ ι κ L _ _ _ _ _ F b ω hF v hv H l p hH hl hp hι hτ hκ hHp hlp hb T hT
  let z : ℝ := (p + cr) ^ cr + (p + 2) ^ a + p + 2
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have ha0 : 0 ≤ (p + 2) ^ a := by positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hpz : p ≤ z := by dsimp [z]; linarith
  have hrz : (p + cr) ^ cr ≤ z := by dsimp [z]; linarith
  have haz : (p + 2) ^ a ≤ z := by dsimp [z]; linarith
  have hbud := hbudget p hp
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨m₁, hm₁, hm₁bound, hlm₁, hresetm⟩ :=
    hreset F b ω hF v hv H l p hH hl hp hι hτ hκ hHp hlp hb T
      (fun i => (Real.exp_le_exp.mpr hbud.1).trans (hT i))
  obtain ⟨m₂, hm₂, hm₂bound, hm₁m₂, hproducts⟩ := hratprod F b ω hF v hv H z hH hz
    (hι.trans hpz) (hτ.trans hpz) (hHp.trans (Real.exp_le_exp.mpr hpz)) hb m₁ hm₁
    (hm₁bound.trans (Real.exp_le_exp.mpr hrz))
  refine ⟨m₂, hm₂, hm₂bound.trans (Real.exp_le_exp.mpr hbud.2.2), hlm₁.trans hm₁m₂, ?_⟩
  intro U vg hspan hvg σ w β hβ K hK g E R k hk hx
  dsimp only
  let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v
    (fun i => weightedHomogeneousComponent v (w i) (β i))
    (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  intro El Pl Rl hlocal hPl hEl hE hRl hR
  obtain ⟨P₀, hP₀, hidentity⟩ := F.exists_actual_path_common_quotient_splitting
    b ω hF w v β hβ U K hK g E R k hx El Pl Rl hlocal
  obtain ⟨hprod, hmid, hEq, hRq, hslow, hgrid⟩ := hresetm
    (F.symbolPointwiseSubalgebra b ω hF v U) vg hspan
    (F.symbolPointwiseSubalgebra_basisGraded b ω hF v hv U) hvg k hk El Pl Rl
    (pull E) P₀ (pull R) hPl hP₀
    (congrArg (F.realSymbolGradeQuotientHom v k) hidentity) hEl hE hRl hR
  let A := F.truncateRealSymbol b ω hF v k ((pull E)⁻¹ * El)
  let D := F.truncateRealSymbol b ω hF v k (Rl * (pull R)⁻¹)
  have hslowdiff : F.SymbolSlowBound b ω hF v T
      (Real.exp ((p + C) ^ C)) ((pull E)⁻¹ * (El * A⁻¹)) := by
    have hinput : ∀ x ∈ [(pull E)⁻¹, El * A⁻¹],
        F.SymbolSlowBound b ω hF v T (Real.exp ((z + 2) ^ 1)) x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · apply (F.symbolSlowBound_inv_iff b ω hF v T _ _).mpr
        exact F.symbolSlowBound_mono b ω hF v T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using haz.trans (by linarith : z ≤ z + 2)))
          _ hE
      · exact F.symbolSlowBound_mono b ω hF v T hTpos
          (Real.exp_le_exp.mpr (by simpa only [pow_one] using hrz.trans (by linarith : z ≤ z + 2)))
          _ hslow
    have h := hslowprod F b ω hF v hv H z hH hz (hι.trans hpz) (hτ.trans hpz)
      (hHp.trans (Real.exp_le_exp.mpr hpz)) hb T hTpos [(pull E)⁻¹, El * A⁻¹] (by simp) hinput
    simp only [List.prod_cons, List.prod_nil, mul_one] at h
    exact F.symbolSlowBound_mono b ω hF v T hTpos (Real.exp_le_exp.mpr hbud.2.1) _ h
  have hgriddiff : F.SymbolRationalGrid b ω hF v m₂ ((D⁻¹ * Rl) * (pull R)⁻¹) := by
    have hinput : ∀ x ∈ [D⁻¹ * Rl, (pull R)⁻¹], F.SymbolRationalGrid b ω hF v m₁ x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hgrid
      · exact F.symbolRationalGrid_inv b ω hF v m₁
          (F.symbolRationalGrid_mono b ω hF v hl hlm₁ _ hR)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hproducts [D⁻¹ * Rl, (pull R)⁻¹] (by simp) hinput
  exact ⟨El * A⁻¹, A * Pl * D, D⁻¹ * Rl, hprod.trans hlocal, hmid, hEq.symm, hRq,
    F.symbolSlowBound_mono b ω hF v T hTpos (Real.exp_le_exp.mpr hbud.1) _ hslow,
    F.symbolRationalGrid_mono b ω hF v hm₁ hm₁m₂ _ hgrid, hslowdiff, hgriddiff⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

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

theorem exists_realFilteredSymbolGroupMap_grid
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ g : F.RealPolynomialSymbolGroup w,
        F.SymbolRationalGrid b ω hF w l g →
        G.SymbolRationalGrid c ν hG w m (F.realFilteredSymbolGroupMap G φ hφ w g) := by
  let d := F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w
  have hd := F.filteredSymbolMapDenominator_le_exp G b ω hF c ν hG φ hφ w
    hH hentries hp hsource htarget hHp
  refine ⟨d * l, Nat.mul_pos
    (F.filteredSymbolMapDenominator_pos G b ω hF c ν hG φ hφ w) hl, ?_,
    dvd_mul_left _ _, ?_⟩
  · rw [Nat.cast_mul]
    calc
      (d : ℝ) * l ≤ Real.exp ((p + 2) ^ 3) * Real.exp p :=
        mul_le_mul hd hlp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p + 2) ^ 4) := by
        apply Real.exp_le_exp.mpr
        have hp3 : p ≤ (p + 2) ^ 3 := le_power_budget hp (by omega)
        calc
          (p + 2) ^ 3 + p ≤ 2 * (p + 2) ^ 3 := by linarith
          _ ≤ (p + 2) * (p + 2) ^ 3 := by gcongr; linarith
          _ = (p + 2) ^ 4 := by ring
  · exact F.realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ w l

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem exists_controlled_prescribed_fast_symbol_factorization (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype ξ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w ν)]
        (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : ξ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      BasisBlockInvariant (F.polynomialSymbolBasis b ω hF w) (fun z => z.val.1) U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card (SymbolBasisIndex w ω ⊕ SymbolBasisIndex w ν) : ℝ) ≤ p →
      ((Fintype.card (SymbolBasisIndex w ω) * Fintype.card ξ : ℕ) : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H) →
      (∀ j i, RationalHeightLE ((F.polynomialSymbolBasis b ω hF w).repr (v j) i) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
        ∀ (E P R : F.RealPolynomialSymbolGroup w) (EF RF : G.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
        G.SymbolSlowBound c ν hG w T (Real.exp ((p + 2) ^ a)) EF →
        F.SymbolRationalGrid b ω hF w l R → G.SymbolRationalGrid c ν hG w l RF →
        ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ * EF).coord ∈
          realificationLieSubalgebra (U.map (F.filteredPolynomialSymbolMap G φ hφ w)) →
        (RF * (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈
          realificationLieSubalgebra (U.map (F.filteredPolynomialSymbolMap G φ hφ w)) →
        ∃ E' P' R' : F.RealPolynomialSymbolGroup w,
          E' * P' * R' = E * P * R ∧
          P'.coord ∈ realificationLieSubalgebra U ∧
          F.realFilteredSymbolGroupMap G φ hφ w E' = EF ∧
          F.realFilteredSymbolGroupMap G φ hφ w R' = RF ∧
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + C) ^ C)) E' ∧
          F.SymbolRationalGrid b ω hF w m R' := by
  obtain ⟨ceF, hceF, hslowF⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨ceG, hceG, hslowG⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨crF, hcrF, hrationalF⟩ := exists_symbol_rational_product_bound s 2
  obtain ⟨crG, hcrG, hrationalG⟩ := exists_symbol_rational_product_bound s 2
  let ce := max ceF ceG
  let cr := max crF crG
  obtain ⟨C, hC, hbudget⟩ := exists_fastSymbolCorrectionBudget a ce cr
  refine ⟨C, hC, ?_⟩
  intro σ ι κ ξ L M _ _ _ _ _ _ _ _ F G b ω hF c ν hG φ hφ w hw _ _
    U v hspan hU H l p hH hl hp hι hκ hσ hrows hcols hHp hlp hb hc hentries hv
  classical
  let p₀ : ℝ := p + (p + 2) ^ a + (p + 2) ^ 4 + 2
  let p₁ : ℝ := p₀ + (p₀ + ce) ^ ce + (p₀ + cr) ^ cr
  let p₂ : ℝ := p₁ + ((p₁ + 2) ^ 10 + 2) ^ 36 + ((p₁ + 2) ^ 10 + 2) ^ 18 + 2
  have hbase : 0 ≤ p + 2 := add_nonneg hp (by norm_num)
  have ha0 : 0 ≤ (p + 2) ^ a := pow_nonneg hbase _
  have h40 : 0 ≤ (p + 2) ^ 4 := pow_nonneg hbase _
  have hp₀ : 0 ≤ p₀ := add_nonneg (add_nonneg (add_nonneg hp ha0) h40) (by norm_num)
  have hce0 : 0 ≤ (p₀ + ce) ^ ce := pow_nonneg (add_nonneg hp₀ (Nat.cast_nonneg _)) _
  have hcr0 : 0 ≤ (p₀ + cr) ^ cr := pow_nonneg (add_nonneg hp₀ (Nat.cast_nonneg _)) _
  have hp₁ : 0 ≤ p₁ := add_nonneg (add_nonneg hp₀ hce0) hcr0
  have hsection : 0 ≤ (p₁ + 2) ^ 10 + 2 :=
    add_nonneg (pow_nonneg (add_nonneg hp₁ (by norm_num)) _) (by norm_num)
  have h36 : 0 ≤ ((p₁ + 2) ^ 10 + 2) ^ 36 := pow_nonneg hsection _
  have h18 : 0 ≤ ((p₁ + 2) ^ 10 + 2) ^ 18 := pow_nonneg hsection _
  have hp₂ : 0 ≤ p₂ := add_nonneg (add_nonneg (add_nonneg hp₁ h36) h18) (by norm_num)
  have hpp₀ : p ≤ p₀ :=
    ((le_add_of_nonneg_right ha0).trans (le_add_of_nonneg_right h40)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have h₀₁ : p₀ ≤ p₁ := (le_add_of_nonneg_right hce0).trans (le_add_of_nonneg_right hcr0)
  have h₁₂ : p₁ ≤ p₂ :=
    ((le_add_of_nonneg_right h36).trans (le_add_of_nonneg_right h18)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have hpp₁ := hpp₀.trans h₀₁
  have hpp₂ := hpp₁.trans h₁₂
  have hdimF : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ p := by
    simp only [Fintype.card_sum, Nat.cast_add] at hrows
    linarith only [hrows, Nat.cast_nonneg (α := ℝ) (Fintype.card (SymbolBasisIndex w ν))]
  have hdimG : (Fintype.card (SymbolBasisIndex w ν) : ℝ) ≤ p := by
    simp only [Fintype.card_sum, Nat.cast_add] at hrows
    linarith only [hrows, Nat.cast_nonneg (α := ℝ) (Fintype.card (SymbolBasisIndex w ω))]
  let d := F.filteredSymbolMapDenominator G b ω hF c ν hG φ hφ w
  have hd : 0 < d := F.filteredSymbolMapDenominator_pos G b ω hF c ν hG φ hφ w
  have hdle := F.filteredSymbolMapDenominator_le G b ω hF c ν hG φ hφ w hH hentries
  have hdl : ((d * l : ℕ) : ℝ) ≤ Real.exp p₀ := by
    apply (kernel_inclusion_denominator_mul_le_exp _ _ H d l hp hdimG hdimF hHp hdle hlp).trans
    apply Real.exp_le_exp.mpr
    exact (le_add_of_nonneg_left (add_nonneg hp ha0)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  obtain ⟨l₁, hl₁, hl₁p, hdl₁, hprodG⟩ := hrationalG G c ν hG w hw H p₀ hH hp₀
    (hκ.trans hpp₀) (hσ.trans hpp₀) (hHp.trans (Real.exp_le_exp.mpr hpp₀)) hc
    (d * l) (Nat.mul_pos hd hl) hdl
  have hll₁ : l ∣ l₁ := (dvd_mul_left l d).trans hdl₁
  have hl₁p₁ : (l₁ : ℝ) ≤ Real.exp p₁ := by
    apply (hl₁p.trans (Real.exp_le_exp.mpr
      (shifted_power_self_mono hp₀ (by omega : 1 ≤ crG) (le_max_right crF crG)))).trans
      (Real.exp_le_exp.mpr ?_)
    exact le_add_of_nonneg_left (add_nonneg hp₀ hce0)
  obtain ⟨S, l₂, hl₂, hl₂p, hl₁₂, hsolve, hslowLift, hgridLift⟩ :=
    NilpotentLieBCHGroup.exists_controlled_fast_lift
      (F.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (G.polynomialSymbol_lowerCentralSeries_eq_bot w)
      (F.polynomialSymbolBasis b ω hF w) (G.polynomialSymbolBasis c ν hG w)
      (fun z => z.val.1) (fun z => z.val.1) U v hspan hU
      (F.filteredPolynomialSymbolMap G φ hφ w)
      (fun i j hij => F.filteredPolynomialSymbolMap_monomial_blocks G b ω hF c ν hG φ hφ w j i hij)
      hH hl₁ hv
      (fun i j => F.filteredPolynomialSymbolMap_basis_height G b ω hF c ν hG φ hφ w hH hentries j i)
      hp₁ (hrows.trans hpp₁) (hcols.trans hpp₁) (hHp.trans (Real.exp_le_exp.mpr hpp₁)) hl₁p₁
  simp only [Basis.equivFun_apply] at hslowLift hgridLift
  have hl₂p₂ : (l₂ : ℝ) ≤ Real.exp p₂ := by
    apply hl₂p.trans (Real.exp_le_exp.mpr ?_)
    exact ((le_add_of_nonneg_left hp₁).trans (le_add_of_nonneg_right h18)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  obtain ⟨m, hm, hmp, hl₂m, hprodF⟩ := hrationalF F b ω hF w hw H p₂ hH hp₂
    (hι.trans hpp₂) (hσ.trans hpp₂) (hHp.trans (Real.exp_le_exp.mpr hpp₂)) hb l₂ hl₂ hl₂p₂
  have hbound : (p₂ + ce) ^ ce + (p₂ + cr) ^ cr ≤ (p + C) ^ C := hbudget p hp
  have hfinalE : (p₂ + ce) ^ ce ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hp₂ (Nat.cast_nonneg cr)) cr)).trans hbound
  have hfinalR : (p₂ + cr) ^ cr ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg hp₂ (Nat.cast_nonneg ce)) ce)).trans hbound
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr
    ((shifted_power_self_mono hp₂ (by omega : 1 ≤ crF) (le_max_left crF crG)).trans hfinalR)), (hll₁.trans hl₁₂).trans hl₂m, ?_⟩
  intro T hT E P R EF RF hP hE hEF hR hRF hleft hright
  let π := F.realFilteredSymbolGroupMap G φ hφ w
  let lift := NilpotentLieBCHGroup.realLinearCoordinateLift
    (hL := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w) S
  let A := lift ((π E)⁻¹ * EF)
  let D := lift (RF * (π R)⁻¹)
  obtain ⟨hA, hAimage⟩ := hsolve ((π E)⁻¹ * EF) hleft
  obtain ⟨hD, hDimage⟩ := hsolve (RF * (π R)⁻¹) hright
  have himageA : π A = (π E)⁻¹ * EF := hAimage
  have himageD : π D = RF * (π R)⁻¹ := hDimage
  have hAfast : A.coord ∈ realificationLieSubalgebra U := hA
  have hDfast : D.coord ∈ realificationLieSubalgebra U := hD
  have hslowπ := F.realFilteredSymbolGroupMap_slow_exp G b ω hF c ν hG φ hφ w
    hH hentries hp hdimF hHp T hT (Real.exp_nonneg _) E hE
  have h34 : (p + 2) ^ 3 ≤ (p + 2) ^ 4 := pow_le_pow_right₀ (by linarith only [hp]) (by omega)
  have hslowπ' : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + 2) ^ (1 : ℕ))) (π E) := by
    apply G.symbolSlowBound_mono c ν hG w T hT _ _ hslowπ
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    calc
      _ ≤ (p + 2) ^ 4 + (p + 2) ^ a := add_le_add h34 le_rfl
      _ = (p + 2) ^ a + (p + 2) ^ 4 := add_comm _ _
      _ ≤ p + (p + 2) ^ a + (p + 2) ^ 4 :=
        add_le_add (le_add_of_nonneg_left hp) le_rfl
      _ ≤ p₀ := le_add_of_nonneg_right (by norm_num)
      _ ≤ p₀ + 2 := le_add_of_nonneg_right (by norm_num)
  have hslowEF : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + 2) ^ (1 : ℕ))) EF := by
    apply G.symbolSlowBound_mono c ν hG w T hT _ _ hEF
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    exact (((le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right h40)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  have hslowDis : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + ce) ^ ce)) ((π E)⁻¹ * EF) := by
    have hh := hslowG G c ν hG w hw H p₀ hH hp₀ (hκ.trans hpp₀) (hσ.trans hpp₀)
      (hHp.trans (Real.exp_le_exp.mpr hpp₀)) hc T hT [(π E)⁻¹, EF] (by simp) (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact (G.symbolSlowBound_inv_iff c ν hG w T _ _).mpr hslowπ'
        · exact hslowEF)
    have hh' : G.SymbolSlowBound c ν hG w T (Real.exp ((p₀ + ceG) ^ ceG)) ((π E)⁻¹ * EF) := by
      simpa only [List.prod_cons, List.prod_nil, mul_one] using hh
    exact G.symbolSlowBound_mono c ν hG w T hT (Real.exp_le_exp.mpr
      (shifted_power_self_mono hp₀ (by omega : 1 ≤ ceG) (le_max_right ceF ceG))) _ hh'
  have hslowDis₁ : G.SymbolSlowBound c ν hG w T (Real.exp p₁) ((π E)⁻¹ * EF) := by
    apply G.symbolSlowBound_mono c ν hG w T hT _ _ hslowDis
    apply Real.exp_le_exp.mpr
    exact (le_add_of_nonneg_left hp₀).trans (le_add_of_nonneg_right hcr0)
  have hslowA : F.SymbolSlowBound b ω hF w T
      (Real.exp (((p₁ + 2) ^ 10 + 2) ^ 18) * Real.exp p₁) A := by
    exact hslowLift (monomialScale T) (monomialScale_pos T hT)
      (Real.exp p₁) (Real.exp_nonneg _) ((π E)⁻¹ * EF) hslowDis₁
  have hslowA₂ : F.SymbolSlowBound b ω hF w T (Real.exp ((p₂ + 2) ^ (1 : ℕ))) A := by
    apply F.symbolSlowBound_mono b ω hF w T hT _ _ hslowA
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    calc
      _ = p₁ + ((p₁ + 2) ^ 10 + 2) ^ 18 := add_comm _ _
      _ ≤ p₁ + ((p₁ + 2) ^ 10 + 2) ^ 36 + ((p₁ + 2) ^ 10 + 2) ^ 18 :=
        add_le_add (le_add_of_nonneg_right h36) le_rfl
      _ ≤ p₂ := le_add_of_nonneg_right (by norm_num)
      _ ≤ p₂ + 2 := le_add_of_nonneg_right (by norm_num)
  have hslowE₂ : F.SymbolSlowBound b ω hF w T (Real.exp ((p₂ + 2) ^ (1 : ℕ))) E := by
    apply F.symbolSlowBound_mono b ω hF w T hT _ _ hE
    apply Real.exp_le_exp.mpr
    have hh : (p + 2) ^ a ≤ p₀ :=
      ((le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right h40)).trans
        (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
    simp only [pow_one]
    exact (hh.trans (h₀₁.trans h₁₂)).trans (le_add_of_nonneg_right (by norm_num))
  have hgridπ : G.SymbolRationalGrid c ν hG w (d * l) (π R) :=
    F.realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ w l R hR
  have hgridRF : G.SymbolRationalGrid c ν hG w (d * l) RF :=
    realDenominatorGrid_subset_of_dvd hl (dvd_mul_left l d) hRF
  have hgridDis : G.SymbolRationalGrid c ν hG w l₁ (RF * (π R)⁻¹) := by
    have hh := hprodG [RF, (π R)⁻¹] (by simp) (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hgridRF
      · exact G.symbolRationalGrid_inv c ν hG w (d * l) hgridπ)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hh
  have hgridD : F.SymbolRationalGrid b ω hF w l₂ D := hgridLift _ hgridDis
  have hgridR₂ : F.SymbolRationalGrid b ω hF w l₂ R :=
    realDenominatorGrid_subset_of_dvd hl (hll₁.trans hl₁₂) hR
  refine ⟨E * A, A⁻¹ * P * D⁻¹, D * R, by
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left], ?_, ?_, ?_, ?_, ?_⟩
  · exact (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).mul_mem
      ((NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).mul_mem
        ((NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).inv_mem hAfast) hP)
      ((NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).inv_mem hDfast)
  · change π (E * A) = EF
    rw [map_mul, himageA, mul_inv_cancel_left]
  · change π (D * R) = RF
    rw [map_mul, himageD, inv_mul_cancel_right]
  · have hh := hslowF F b ω hF w hw H p₂ hH hp₂ (hι.trans hpp₂) (hσ.trans hpp₂)
      (hHp.trans (Real.exp_le_exp.mpr hpp₂)) hb T hT [E, A] (by simp) (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hslowE₂
        · exact hslowA₂)
    have hh' : F.SymbolSlowBound b ω hF w T (Real.exp ((p₂ + ceF) ^ ceF)) (E * A) := by
      simpa only [List.prod_cons, List.prod_nil, mul_one] using hh
    exact F.symbolSlowBound_mono b ω hF w T hT (Real.exp_le_exp.mpr
      ((shifted_power_self_mono hp₂ (by omega : 1 ≤ ceF) (le_max_left ceF ceG)).trans hfinalE)) _ hh'
  · have hh := hprodF [D, R] (by simp) (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hgridD
      · exact hgridR₂)
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hh

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_common_refiltered_terminal_discrepancies (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (HMap l : ℕ) (pMap : ℝ), 1 ≤ HMap → 0 < l → 0 ≤ pMap →
      (∀ i j, RationalHeightLE (c.repr (φ (b j)) i) HMap) →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (HMap : ℝ) ≤ Real.exp pMap → (l : ℝ) ≤ Real.exp pMap →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧ l ∣ m ∧
        ∀ (HCompare : ℕ) (pCompare : ℝ), 1 ≤ HCompare → 0 ≤ pCompare →
        (Fintype.card κ : ℝ) ≤ pCompare → (Fintype.card σ : ℝ) ≤ pCompare →
        (Fintype.card χ : ℝ) ≤ pCompare → (HCompare : ℝ) ≤ Real.exp pCompare →
        Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pCompare →
        (∀ i j z, RationalHeightLE (c.repr ⁅c i, c j⁆ z) HCompare) →
        ∀ side : σ → ℝ, (∀ i, Real.exp ((pCompare + C) ^ C) ≤ side i) →
        ∀ q : ℝ, Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pCompare + 2) ^ a) →
        ∀ (W : LieSubalgebra ℚ F.AssociatedGraded)
          (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
        Submodule.span ℚ (Set.range vg) =
          (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
            (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
        (∀ i z, RationalHeightLE
          ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) HCompare) →
        ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
        F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
        ∃ E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
          E * P * R = F.realPolynomialSymbolHom b ω hF (fun _ => 1) g ∧
          P.coord ∈ realificationLieSubalgebra
            (F.symbolPointwiseSubalgebra b ω hF (fun _ : σ => 1) W) ∧
          F.SymbolSlowBound b ω hF (fun _ : σ => 1) side (Real.exp q) E ∧
          F.SymbolRationalGrid b ω hF (fun _ : σ => 1) l R ∧
          ∀ E₀ R₀ : G.RealPolynomialSymbolGroup (fun _ : σ => 1),
            (E₀⁻¹ * G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
              (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) * R₀⁻¹).coord ∈
                realificationLieSubalgebra
                  (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
                    (W.map (F.associatedGradedMap G φ hφ))) →
            G.SymbolSlowBound c ν hG (fun _ : σ => 1) side
              (Real.exp ((pCompare + 2) ^ a)) E₀ →
            G.SymbolRationalGrid c ν hG (fun _ : σ => 1) m R₀ →
            ((F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1) E)⁻¹ * E₀).coord ∈
              realificationLieSubalgebra
                (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
                  (W.map (F.associatedGradedMap G φ hφ))) ∧
            (R₀ * (F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1) R)⁻¹).coord ∈
              realificationLieSubalgebra
                (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
                  (W.map (F.associatedGradedMap G φ hφ))) := by
  obtain ⟨C, hC, hcompare⟩ := exists_controlled_terminal_symbol_comparison s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ χ L M _ _ _ _ _ _ _ _ F G b ω hF c ν hG φ hφ _ _
    HMap l pMap hHMap hl hpMap hentries hsource htarget hHMapExp hlExp
  obtain ⟨m, hm, hmExp, hlm, hmapGrid⟩ :=
    F.exists_realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ (fun _ : σ => 1)
      hHMap hentries hpMap hsource htarget hHMapExp l hl hlExp
  refine ⟨m, hm, hmExp, hlm, ?_⟩
  intro HCompare pCompare hHCompare hpCompare hκ hσ hχ hHCompareExp hgridAbsorb
    hbracket side hside q hslowAbsorb W vg hspan hvg g hnative
  have hsidePos : ∀ i, 0 < side i := fun i => (Real.exp_pos _).trans_le (hside i)
  obtain ⟨E, P, R, hprod, hP, hE, hR⟩ :=
    hnative.symbolFactors F b ω hF side q l W g
  refine ⟨E, P, R, hprod, hP, hE, hR, ?_⟩
  intro E₀ R₀ hterminal hE₀ hR₀
  let π := F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1)
  let U := G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
    (W.map (F.associatedGradedMap G φ hφ))
  let P₀ := E₀⁻¹ * G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
    (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) * R₀⁻¹
  have hmapP : (π P).coord ∈ realificationLieSubalgebra U :=
    F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) W P.coord hP
  have hmapSlow : G.SymbolSlowBound c ν hG (fun _ : σ => 1) side
      (Real.exp ((pCompare + 2) ^ a)) (π E) := by
    have hslow := F.realFilteredSymbolGroupMap_slow_exp G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) hHMap hentries hpMap hsource hHMapExp side hsidePos
      (Real.exp_nonneg q) E hE
    have hslow' : G.SymbolSlowBound c ν hG (fun _ : σ => 1) side
        (Real.exp ((pMap + 2) ^ 3 + q)) (π E) := by
      simpa only [Real.exp_add] using hslow
    exact G.symbolSlowBound_mono c ν hG (fun _ : σ => 1) side hsidePos hslowAbsorb _ hslow'
  have hmapGridR : G.SymbolRationalGrid c ν hG (fun _ : σ => 1) m (π R) :=
    hmapGrid R hR
  have hcompareProd : π E * π P * π R = E₀ * P₀ * R₀ := by
    calc
      π E * π P * π R = π (F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1) g) := by
        rw [← map_mul, ← map_mul, hprod]
      _ = G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
          (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) :=
        F.realFilteredSymbolGroupMap_symbol G b ω hF c ν hG φ hφ (fun _ : σ => 1) g
      _ = E₀ * P₀ * R₀ := by
        dsimp only [P₀]
        group
  exact hcompare G c ν hG (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    U vg hspan HCompare m pCompare hHCompare hm hpCompare hκ hσ hχ hHCompareExp
    (hmExp.trans hgridAbsorb) hbracket hvg side hside
    (π E) (π P) (π R) E₀ P₀ R₀ hmapP hterminal hcompareProd hmapSlow hE₀ hmapGridR hR₀

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_prescribed_marked_native_factorizations (s a : ℕ) :
    ∃ Cf Cnative : ℕ, 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (τ : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (U : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule →
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
    ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card ξ : ℝ) ≤ p → (Fintype.card μ : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
    ∃ m : ℕ, 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf p) + Cnative) ^ Cnative) ∧
      l ∣ m ∧
    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
    ∀ X EF RF : (G.realification.adaptedPolynomialFiltration w).Group,
      G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
      G.PolynomialRationalGrid c w l RF →
      coefficients ((EF⁻¹ * X * RF⁻¹).coord :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
        G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 →
    ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group),
      F.realPolynomialGroupMap G φ hφ w g = X →
    ∀ E P R : F.RealPolynomialSymbolGroup w,
      E * P * R = F.realPolynomialSymbolHom b ω hF w g →
      P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolRationalGrid b ω hF w l R →
      ((F.realFilteredSymbolGroupMap G φ hφ w E)⁻¹ *
        G.realPolynomialSymbolHom c τ hG w EF).coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) →
      (G.realPolynomialSymbolHom c τ hG w RF *
        (F.realFilteredSymbolGroupMap G φ hφ w R)⁻¹).coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c τ hG w (U.map (F.associatedGradedMap G φ hφ))) →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration w).Group)
      (q : (F.gradedRefiltration U).realification.PolynomialOrbit w),
      e * middle * r = g ∧
      F.realPolynomialGroupMap G φ hφ w e = EF ∧
      F.realPolynomialGroupMap G φ hφ w r = RF ∧
      F.realPolynomialGroupMap G φ hφ w middle = EF⁻¹ * X * RF⁻¹ ∧
      F.PolynomialSlowBound b w T (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf p) + Cnative) ^ Cnative)) e ∧
      F.PolynomialRationalGrid b w m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra U).incl)).toLinearMap
        q.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration U).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra U).incl
        ((F.gradedRefiltration U).realification.polynomialOrbitRealEval w t q) =
          F.adaptedPolynomialRealValueHom w t middle := by
  obtain ⟨Cf, hCf, hfast⟩ := exists_controlled_prescribed_fast_symbol_factorization s a
  obtain ⟨Cnative, hCnative, hnative⟩ := exists_controlled_marked_native_factorization s 1
  refine ⟨Cf, Cnative, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ L M _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c τ hG w hw hsurj
    bk U v hU hvspan H l p hH hl hp hι hκ hξ hμ hσ hHp hlp hb hc hkernel hentries hv
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hF)
  let : Fintype (SymbolBasisIndex w τ) :=
    symbolBasisIndexFintype w τ s hw (G.adaptedBasis_weight_le_step c τ hG)
  let Q := pointwiseFastSectionInput s p
  have hpQ : p ≤ Q := pointwiseFastSectionInput_ge s hp
  have hQ : 0 ≤ Q := hp.trans hpQ
  have hcounts := F.pointwiseSymbolSpanning_section_counts (ξ := μ) G b ω hF c τ hG w hw
    hp hι hκ hμ hσ
  obtain ⟨n, hn, hnp, hln, hcorrect⟩ := hfast F G b ω hF c τ hG φ hφ w hw
    (F.symbolPointwiseSubalgebra b ω hF w U) (F.pointwiseSymbolSpanningFamily b ω hF w v)
    (F.pointwiseSymbolSpanningFamily_span b ω hF w U hU v hvspan)
    (F.symbolPointwiseSubalgebra_blockInvariant b ω hF w U)
    H l Q hH hl hQ (hι.trans hpQ) (hκ.trans hpQ) (hσ.trans hpQ)
    hcounts.2.1 hcounts.2.2 (hHp.trans (Real.exp_le_exp.mpr hpQ))
    (hlp.trans (Real.exp_le_exp.mpr hpQ)) hb hc hentries
    (F.pointwiseSymbolSpanningFamily_height b ω hF w v hH hv)
  let B := fullMarkedNativeInput s a Cf p
  have hslow0 : 0 ≤ (p + 2) ^ a := by positivity
  have hfast0 : 0 ≤ (Q + Cf) ^ Cf := by positivity
  have hQB : Q ≤ B := by
    change Q ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hfast0, hslow0]
  have hpB : p ≤ B := hpQ.trans hQB
  have hB : 0 ≤ B := hp.trans hpB
  have hfastB : (Q + Cf) ^ Cf ≤ B := by
    change _ ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hslow0, hQ]
  have hslowB : (p + 2) ^ a ≤ B := by
    change _ ≤ (Q + Cf) ^ Cf + (p + 2) ^ a + Q
    linarith only [hfast0, hQ]
  obtain ⟨m, hm, hmp, hnm, hfactor⟩ := hnative F G φ hφ b ω hF c τ hG w hw hsurj
    bk H n B hH hn hB (hι.trans hpB) (hκ.trans hpB) (hξ.trans hpB) (hσ.trans hpB)
    (hHp.trans (Real.exp_le_exp.mpr hpB)) (hnp.trans (Real.exp_le_exp.mpr hfastB))
    hb hkernel hentries
  refine ⟨m, hm, hmp, hln.trans hnm, ?_⟩
  intro T hT X EF RF hEF hRF hconstant
  have hEFbound : CoefficientBound (c.baseChange ℝ) T
      (Real.exp ((B + 2) ^ 1)) EF.coord.val :=
    G.polynomialSlowBound_mono c w T hT
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hslowB.trans (by linarith only))) EF hEF
  have hRFgrid : CoefficientGrid (c.baseChange ℝ) n RF.coord.val := by
    obtain ⟨z, hz⟩ := G.polynomialRationalGrid_of_dvd c w hl hln RF hRF
    intro α
    exact ⟨fun i => z (α, i), funext (fun i => congrFun hz (α, i))⟩
  intro g hg E P R hprod hP hEslow hRgrid hleft hright
  have hscale : Real.exp ((p + 2) ^ a) ≤ Real.exp ((Q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith only [hp]) (by linarith only [hpQ]) a)
  have himage := F.symbolPointwiseSubalgebra_map G b ω hF c τ hG φ hφ w U hU
  rw [← himage] at hleft hright
  obtain ⟨E', P', R', hprod', hP', hEmark, hRmark, hEbound, hRden⟩ :=
    hcorrect T hT E P R (G.realPolynomialSymbolHom c τ hG w EF)
      (G.realPolynomialSymbolHom c τ hG w RF) hP
      (F.symbolSlowBound_mono b ω hF w T hT hscale E hEslow)
      (G.symbolSlowBound_mono c τ hG w T hT hscale _
        (G.polynomialSlowBound_symbol c τ hG w T _ EF hEF))
      hRgrid (G.polynomialRationalGrid_symbol c τ hG w l RF hRF) hleft hright
  have hEbound' : F.SymbolSlowBound b ω hF w T (Real.exp ((B + 2) ^ 1)) E' :=
    F.symbolSlowBound_mono b ω hF w T hT
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using hfastB.trans (by linarith only))) E' hEbound
  have hfirst : coefficients ((EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹).coord :
      VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
      G.realGradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) 1 := by
    rw [hg]
    exact hconstant
  obtain ⟨e, middle, r, q, hprod'', _, _, _, heF, hrF, hpF, heslow, hrden, hq, hvalues⟩ :=
    hfactor U hU T hT g E' P' R' (hprod'.trans hprod) hP' EF RF
      (congrArg NilpotentLieBCHGroup.coord hEmark)
      (congrArg NilpotentLieBCHGroup.coord hRmark) hEbound' hEFbound hRden hRFgrid hfirst
  exact ⟨e, middle, r, q, hprod'', heF, hrF, hpF.trans (by rw [hg]), heslow, hrden, hq, hvalues⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

noncomputable def phase (t m : ℕ) := normalizedMarkedPhase filtration generators weights marked t m

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMajorCorrelationFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem uniform_majorPhase_correlation_eq
    {m d : ℕ} {X L : Type} [Fintype X] [DecidableEq X]
    [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (D : RationalFilteredNilmanifold L t e) (T : D.Niltest (fun _ : X => 1))
    (N : X → ℕ) (hN : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (g : integerBox N → ℂ) (heval : ∀ u, g u = T.eval u.val) :
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hN).correlation
      (fun u => majorPhaseSample J d poly Ψ c F β (fun _ => 1) u.val)
      (fun u => star (W.eval N poly u.val) * g u) =
    𝔼 u ∈ integerBox N,
      W.eval N poly u * majorPhaseSample J d poly Ψ c F β T.conjugate.eval u := by
  rw [← FiniteProbabilityWeights.uniformFinset_complexMean (integerBox N) hN]
  unfold FiniteProbabilityWeights.correlation FiniteProbabilityWeights.complexMean
  apply Finset.sum_congr rfl
  intro u _
  dsimp only
  rw [heval u]
  simp only [majorPhaseSample, Niltest.eval_conjugate, star_mul, star_star, mul_one]
  ring

attribute [local instance] NativeSampleModelFamily.lie NativeSampleModelFamily.algebra
  NativeSampleModelFamily.topology NativeSampleModelFamily.topologicalAdd
  NativeSampleModelFamily.continuousSMul NativeSampleModelFamily.hausdorff

theorem exists_native_major_correlation_family
    {m d t : ℕ} {X η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (N : X → ℕ) (hN : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : η → MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (g : η → integerBox N → ℂ) (p : ℝ) (hp : 2 ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (native : ∀ j, NativeSampleModel (fun _ : X => 1) t p
      (fun u : integerBox N => u.val) (g j))
    (hcorr : ∀ j, Real.exp (-p) ≤
      ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hN).correlation
        (fun u => majorPhaseSample J d poly Ψ c (F j) β (fun _ => 1) u.val)
        (fun u => star ((W j).eval N poly u.val) * g j u)‖) :
    ∃ common : NativeSampleModelFamily (fun _ : X => 1) t (productNiltestBudget p)
      (fun u : integerBox N => u.val) g,
      ∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u *
          majorPhaseSample J d poly Ψ c (F j) β (common.test j).conjugate.eval u‖ := by
  let common := NativeSampleModelFamily.ofModels native hp hη
  refine ⟨common, ?_⟩
  intro j
  rw [← uniform_majorPhase_correlation_eq J (W j) common.model (common.test j)
    N hN poly Ψ c (F j) β (g j) (common.eval j)]
  exact hcorr j

theorem exists_native_major_correlation_family_of_detections
    {m d t : ℕ} {X η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (N : X → ℕ) (hN : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : η → MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (p : ℝ) (hp : 2 ≤ p) (hη : (Fintype.card η : ℝ) ≤ p)
    (hdetected : ∀ j,
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
        (g : integerBox N → ℂ),
        Nonempty (NativeSampleModel (fun _ : X => 1) t p
          (fun u : integerBox N => u.val) g) ∧
        Real.exp (-p) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hN).correlation
            (fun u => majorPhaseSample J d poly Ψ c (F j) β (fun _ => 1) u.val)
            (fun u => star (W.eval N poly u.val) * g u)‖) :
    ∃ (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (g : η → integerBox N → ℂ)
      (common : NativeSampleModelFamily (fun _ : X => 1) t (productNiltestBudget p)
        (fun u : integerBox N => u.val) g),
      ∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u *
          majorPhaseSample J d poly Ψ c (F j) β (common.test j).conjugate.eval u‖ := by
  classical
  choose W g hnative hcorr using hdetected
  let native := fun j => Classical.choice (hnative j)
  obtain ⟨common, hcommon⟩ := exists_native_major_correlation_family J W N hN
    poly Ψ c F β g p hp hη native hcorr
  exact ⟨W, g, common, hcommon⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
    (w : σ → ℕ)

theorem weightedAdaptedRealChartHom_constantChart
    (v : τ → ℕ) (x : σ → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w v
      (fun i => (MvPolynomial.C (x i) : MvPolynomial τ ℝ))
      (fun i => weightedSupportLE_C v (w i) (x i)) g =
      F.realification.adaptedConstantGroupHom v
        (F.adaptedPolynomialRealValueHom w x g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [F.weightedAdaptedRealChartHom_coord, F.realification.adaptedConstantGroupHom_log]
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro t
  simp only [map_sub, eval₂_realChartSubstitute, MvPolynomial.eval_C,
    VectorPolynomial.eval₂_monomial, Finsupp.prod_zero_index, one_smul,
    F.adaptedPolynomialRealValueHom_coord, sub_self]

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialIdentity
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct
open VectorPolynomial

namespace RankPreparationFamily

noncomputable def polynomial {I J : Type} [DecidableEq J] {s : ℕ}
    (L : RankPreparationFamily I J s) : VectorPolynomial I ℝ (J → ℝ) :=
  ∑ u, map (coordinateCopySum (L u).label) (L u).poly

end RankPreparationFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem quotientFunctional_kills_fast (U : Submodule ℚ F.AssociatedGraded)
    (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ) (x : F.AssociatedGraded) (hx : x ∈ U) :
    (ℓ.comp U.mkQ) x = 0 := by
  have hz : U.mkQ x = 0 := by
    change x ∈ LinearMap.ker U.mkQ
    rwa [Submodule.ker_mkQ]
  simp only [LinearMap.comp_apply, hz, map_zero]

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartRecoveredTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_long_coeff
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T Long : Type*}
    (keep : Long ↪ LayerSamplerVariables G I n B)
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D) (hH : 1 ≤ H)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hlong : ∀ i, H ≤ layerSamplerBox B U b S (keep i))
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (α : Long →₀ ℕ) (hα : α ≠ 0) (hdegree : α.degree ≤ j.val + 1) :
    Q (fun i => (((allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
      (Sum.inr ⟨j, i⟩)).coeff (α.mapDomain keep) : ℤ) : ℝ)) = 0 := by
  let frame : Option (LayerSamplerVariables G I n B) → X → ℝ :=
    fun k z => (jointIntegerFrame (a, v) k z : ℝ)
  let d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) :=
    ⟨α.mapDomain keep, by simpa only [Finsupp.degree_mapDomain] using hdegree⟩
  have hc : canonicalCoefficientSample U b hb o sample =
      QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (centeredAffineCoefficientArray U poly hm c frame) :=
    h.2.1.trans (affineSampleCoefficientTorus_subtractConstant U poly hm c frame)
  change Q (fun i => (((coefficientIntegerFloorPolynomial U b o sample
    (centeredAffineCoefficientArray U poly hm c frame) j i).coeff d.val : ℤ) : ℝ)) = 0
  apply canonicalCoefficientSample_floor_coeff_separate U b hb o sample _ hc j d Q hQU hD hgrid
  let M : ℝ := C * (((Fintype.card (I j) : ℝ) + 1) * R j)
  let scale : ℝ := monomialScale (layerSamplerBox B U b S) d.val
  have hscale : 0 < scale := monomialScale_pos _
    (fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S i)) d.val
  have hM : 0 ≤ M := mul_nonneg hC (mul_nonneg (by positivity) (hR j).le)
  have hnorm : ‖fun i => mixedLiftCoefficient (euclideanSubspace (U j))
      (b j) (o j) (sample j) d i‖ ≤ M / scale := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hM hscale.le)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using
      allocatedLayerLiftCoefficient_radius_bound B U b hR hσ S hσ1 o j hC hchart
        (sample j) (h.2.2.1 j).2 d i
  have hscaleH : H ≤ scale := by
    change H ≤ monomialScale (layerSamplerBox B U b S) (α.mapDomain keep)
    rw [monomialScale_mapDomain_embedding]
    exact le_monomialScale_of_ne_zero _ hH hlong hα
  intro t
  calc
    _ ≤ CQ * ‖fun i => mixedLiftCoefficient (euclideanSubspace (U j))
        (b j) (o j) (sample j) d i‖ := hQ _ t
    _ ≤ CQ * (M / scale) := mul_le_mul_of_nonneg_left hnorm hCQ
    _ = (CQ * M) / scale := (mul_div_assoc CQ M scale).symm
    _ < 1 / D := (div_lt_div_iff₀ hscale hD).mpr (by
      simpa only [one_mul] using hthreshold.trans_le hscaleH)

theorem allocatedRecoveredIntegerFullChart_tag_degree
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (j : Fin m) (i : J j) :
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
      (Sum.inr ⟨j, i⟩)).totalDegree ≤ j.val + 1 :=
  coefficientIntegerFloorPolynomial_degree U b o sample _ j i

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_top_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*}
    (keep : LayerSamplerVariables G I n B → Prop)
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    (Ktarget : Submodule ℝ (J j → ℝ)) (hker : LinearMap.ker Q ≤ Ktarget)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D) (hH : 1 ≤ H)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i => MvPolynomial.eval x (homogeneousComponent (j.val + 1)
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
          (Sum.inr ⟨j, i⟩)))))) ∈ Ktarget := by
  apply longChart_frozen_top_eval_mem
    (fun i => allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
      (Sum.inr ⟨j, i⟩)) keep fixed (j.val + 1)
    (allocatedRecoveredIntegerFullChart_tag_degree B U b o poly hm c a v sample j)
  intro α hdegree
  apply hker
  apply h.integerFullChart_long_coeff B U b hb o S hR hσ poly hm hσ1 c a v sample read j
    ⟨Subtype.val, Subtype.val_injective⟩ Q hQU hC hCQ hD hH hchart hQ hgrid
    (fun i => hlong i.val i.property) hthreshold α _ hdegree.le
  intro hz
  simp [hz] at hdegree

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_certified_frozen_top_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {Bstage p M H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K Bstage blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hBp : Bstage ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hM : 0 ≤ M) (hcap : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop) (hH : 1 ≤ H)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * M < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i => MvPolynomial.eval x (homogeneousComponent (fullTaggedVariableWeight J i)
      (integerSampledRealChart
        (fun z => freezePolynomial keep fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) i))) ∈ K := by
  obtain ⟨cs, _, hbudget, hK⟩ := hcertificate
  rw [hK]
  refine ⟨Set.mem_univ _, ?_⟩
  intro constraint hc
  have hspan : U constraint.tag ≤
      span ℝ (Set.range (fun q i => (constraint.generators q i : ℝ))) := by
    apply constraint.retained_le_span U hretained
    intro point hpoint
    rw [hK] at hpoint
    exact hpoint.2 constraint hc
  obtain ⟨d, _, Q, hker, hQ, D, hD, hDbound, hgrid⟩ :=
    exists_rationalTaggedSpanProjection constraint.generators hp (hJ constraint.tag)
      ((hbudget constraint hc).1.trans hBp)
      (fun q i => ((hbudget constraint hc).2 q i).trans hBp)
  have hQU : U constraint.tag ≤ LinearMap.ker Q := by
    rw [hker]
    exact hspan
  have hgrid' : ∀ z : J constraint.tag → ℤ, ∀ t,
      ∃ a : ℤ, (D : ℝ) * Q (fun i => (z i : ℝ)) t = a := by
    intro z t
    obtain ⟨w, hw⟩ := hgrid z
    exact ⟨w t, (hw t).symm⟩
  have hnumeric : Real.exp ((p + 2) ^ 9) *
      (C constraint.tag * (((Fintype.card (I constraint.tag) : ℝ) + 1) * R constraint.tag)) *
        (D : ℝ) < H := by
    have hE := Real.exp_nonneg ((p + 2) ^ 9)
    calc
      _ ≤ Real.exp ((p + 2) ^ 9) * M * (D : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcap constraint.tag) hE)
          (Nat.cast_nonneg D)
      _ ≤ Real.exp ((p + 2) ^ 9) * M * Real.exp ((p + 2) ^ 9) :=
        mul_le_mul_of_nonneg_left hDbound (mul_nonneg hE hM)
      _ = Real.exp ((p + 2) ^ 9) ^ 2 * M := by ring
      _ < H := hthreshold
  exact h.integerFullChart_frozen_top_range B U b hb o S hR hσ poly hm hσ1 c a v sample read
    constraint.tag keep Q hQU _ (le_of_eq hker) (hC constraint.tag)
    (Real.exp_nonneg _) (by exact_mod_cast hD) hH (hchart constraint.tag) hQ hgrid'
    hlong hnumeric fixed x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFrozenFullChart_certified_top_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {Bstage p M H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K Bstage blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hBp : Bstage ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hM : 0 ≤ M) (hcap : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop) (hH : 1 ≤ H)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * M < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i => MvPolynomial.eval x (homogeneousComponent (fullTaggedVariableWeight J i)
      (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) i))) ∈ K := by
  exact h.integerFullChart_certified_frozen_top_range B U b hb o S hR hσ poly hm
    hσ1 c a v sample read K hcertificate hretained hp hBp hJ C hC hchart hM hcap
    keep hH hlong hthreshold fixed x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (f : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem controlledSymbolFactorizationAtFast_projection_pullback
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (η : M →ₗ[ℚ] ℚ) (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hfactor : G.ControlledSymbolFactorizationAtFast f ν hG η T
      (F.realSymbolProjection G φ hφ (fun _ => 1) X) p U) :
    F.ControlledSymbolFactorizationAtFast e ω hF (η.comp φ.toLinearMap) T X
      (controlledProjectionBudget p) (U.comap (F.associatedGradedMap G φ hφ)) := by
  obtain ⟨l, E, P, R, v, hl, hlp, hprod, hE, hR, hv, hgraded, hvH, hzero, hP⟩ := hfactor
  obtain ⟨m, hm, hmp, _, hsplit⟩ :=
    F.exists_symbolFactorizationIn_projection_pullback G e ω hF f ν hG φ hφ
      hsurj hH hl hentries hp hrows hcols hHp hlp T hT X U
      ⟨E, P, R, hprod, hE, hR, hP⟩
  obtain ⟨u, hu, huH⟩ := F.exists_associatedGradedMap_comap_bounded_spanning
    G e ω hF f ν hG φ hφ U v hv hp hι hκ hvH
    (fun i j => rationalLogHeight_le_of_height (hentries j i) hHp)
  have hbase : 0 ≤ preimageBasisBudget p := preimageBasisBudget_nonneg hp
  have hq : 0 ≤ ((p + 2) ^ 10 + 2) := by positivity
  have hden : ((p + 2) ^ 10 + 2) ^ 36 ≤ controlledProjectionBudget p := by
    unfold controlledProjectionBudget
    exact (le_add_of_nonneg_right (by positivity)).trans
      (le_add_of_nonneg_right (by positivity))
  have hslow : ((p + 2) ^ 10 + 2) ^ 18 + p ≤ controlledProjectionBudget p := by
    unfold controlledProjectionBudget
    exact (le_add_of_nonneg_left (pow_nonneg hq 36)).trans
      (le_add_of_nonneg_right (add_nonneg hbase zero_le_one))
  have hheight : preimageBasisBudget p + 1 ≤ controlledProjectionBudget p := by
    unfold controlledProjectionBudget
    exact le_add_of_nonneg_left
      (add_nonneg (pow_nonneg hq 36) (add_nonneg (pow_nonneg hq 18) hp))
  obtain ⟨A, B, C, hABC, hA, hC, hB⟩ := hsplit.mono F e ω hF hslow hT
  exact ⟨m, A, B, C, u, hm, hmp.trans (Real.exp_le_exp.mpr hden),
    hABC, hA, hC, hu,
    F.associatedGradedMap_comap_graded G e ω hF f ν hG φ hφ U hgraded,
    fun i j => (huH i j).trans hheight,
    F.gradedFrequency_comap_top_zero G e ω hF f ν hG φ hφ η U hzero, hB⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end


