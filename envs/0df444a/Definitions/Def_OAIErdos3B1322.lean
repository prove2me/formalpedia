-- Prove2me | Definitions.Def_OAIErdos3B1322
-- name    : OAIErdos3B1322
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T17:10:03.5705+00:00
-- url     : https://prove2.me/theorems/6045bd30-646d-4915-aaa1-6fa1ab511217
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1323 of 1327
-- statement:
--   Definitions bundle 1323 of 1327 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1321`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1323 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.controlledSymbolFactorizationAtFast_projection_of_dimensions`, `OAI.Erdos3.NilpotentLieFiltration.controlledSymbolFactorizationAtFast_projection_pullback`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B069

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

end NilpotentLieFiltration
end Erdos3

end

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

variable {α β σ : Type*}
  (e : Basis α ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) (ω : α → ℕ)
  (hF : ∀ k, (optionProduct D₀ D).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ ω i}))
  (b : Basis β ℚ (PairAlgebra L₀ (L j))) (ν : β → ℕ)
  (hG : ∀ k, (pi (pairModels D₀ (D j))).filtration.layer k =
    Submodule.span ℚ (b '' {i | k ≤ ν i}))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {J : Type*} [Fintype J] {L : Type u} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  {s d₀ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))

end Erdos3.RationalFilteredNilmanifold

end

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

set_option maxHeartbeats 1000000 in
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

section

namespace Erdos3.NilpotentLieFiltration

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

variable {κ M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (G : NilpotentLieFiltration M s)
    (f : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem controlledSymbolFactorizationAtFast_projection_of_dimensions
    [Fintype σ] [Fintype ι] [Fintype κ]
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (η : M →ₗ[ℚ] ℚ) (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hfactor : G.ControlledSymbolFactorizationAtFast f ν hG η T
      (F.realSymbolProjection G φ hφ (fun _ => 1) X) p U) :
    F.ControlledSymbolFactorizationAtFast e ω hF (η.comp φ.toLinearMap) T X
      (controlledProjectionBudget (controlledProjectionDimensionInput s p))
      (U.comap (F.associatedGradedMap G φ hφ)) := by
  let :=  symbolBasisIndexFintype (fun _ : σ => 1) ω s (fun _ => Nat.zero_lt_one)
    (F.adaptedBasis_weight_le_step e ω hF)
  let :=  symbolBasisIndexFintype (fun _ : σ => 1) ν s (fun _ => Nat.zero_lt_one)
    (G.adaptedBasis_weight_le_step f ν hG)
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  let r : ℝ := controlledProjectionDimensionInput s p
  have hpR : p ≤ r := by
    change p ≤ 2 * q ^ 2 + p + 1
    nlinarith [sq_nonneg q]
  have hR : 0 ≤ r := hp.trans hpR
  have hq : 1 ≤ q := by
    apply one_le_pow₀
    have := Nat.cast_nonneg (α := ℝ) s
    linarith
  have hsource : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le _ _ s (fun _ => Nat.zero_lt_one)
      (F.adaptedBasis_weight_le_step e ω hF))).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have htarget : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le _ _ s (fun _ => Nat.zero_lt_one)
      (G.adaptedBasis_weight_le_step f ν hG))).trans
      (symbol_dimension_bound_le_power s (Fintype.card κ) (Fintype.card σ) hp hκ hσ)
  have hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ r := by
    simp only [Fintype.card_sum, Nat.cast_add]
    change _ ≤ 2 * q ^ 2 + p + 1
    nlinarith
  have hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ r := by
    rw [Nat.cast_mul]
    have hnonneg := Nat.cast_nonneg (α := ℝ)
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω))
    have hsquare := mul_self_le_mul_self hnonneg hsource
    change _ ≤ 2 * q ^ 2 + p + 1
    nlinarith
  exact F.controlledSymbolFactorizationAtFast_projection_pullback G e ω hF f ν hG φ hφ
    hsurj hH hentries hR (hι.trans hpR) (hκ.trans hpR) hrows hcols
    (hHp.trans (Real.exp_le_exp.mpr hpR)) T hT X η U
    (hfactor.mono G f ν hG hpR hT)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

end Erdos3.NilpotentLieFiltration

end

end OAI

end


