-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:55.716006+00:00
-- url     : https://prove2.me/theorems/d95e2ebc-8722-47f0-83d7-f41c69e2d047
-- title:
--   PDiag Form Div
-- statement:
--   Definitions and structural lemmas for PDiag Form Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagFormDiv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace DiagonalFormDivisor
set_option linter.unusedSectionVars false
section Generic
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm
theorem homog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_one] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm
theorem homog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  exacts [hf m h k, hg m h k]
theorem homog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm
  rw [mem_support_iff, coeff_neg, neg_ne_zero, ← mem_support_iff] at hm
  exact hf m hm
def fracPairs (c c' : (Σ k, ι k) → Φ) : Subring (Φ × Φ) where
  carrier := {w | ∃ (γ : K → ℕ) (r q : MRing ι), IsMultiHomog r γ ∧ IsMultiHomog q γ ∧ aeval c q ≠ 0 ∧
    aeval c' q ≠ 0 ∧ aeval c r = aeval c q * w.1 ∧ aeval c' r = aeval c' q * w.2}
  zero_mem' := ⟨0, 0, 1, homog_zero _, homog_one, by simp, by simp, by simp, by simp⟩
  one_mem' := ⟨0, 1, 1, homog_one, homog_one, by simp, by simp, by simp, by simp⟩
  add_mem' := by
    rintro w₁ w₂ ⟨γ₁, r₁, q₁, hr₁, hq₁, h₁, h₁', e₁, e₁'⟩ ⟨γ₂, r₂, q₂, hr₂, hq₂, h₂, h₂', e₂, e₂'⟩
    refine ⟨γ₁ + γ₂, r₁ * q₂ + q₁ * r₂, q₁ * q₂, homog_add (exHomog_mul hr₁ hq₂) (exHomog_mul hq₁ hr₂),
      exHomog_mul hq₁ hq₂, by simp [h₁, h₂], by simp [h₁', h₂'], ?_, ?_⟩
    · simp only [map_add, map_mul, e₁, e₂, Prod.fst_add]
      ring
    · simp only [map_add, map_mul, e₁', e₂', Prod.snd_add]
      ring
  mul_mem' := by
    rintro w₁ w₂ ⟨γ₁, r₁, q₁, hr₁, hq₁, h₁, h₁', e₁, e₁'⟩ ⟨γ₂, r₂, q₂, hr₂, hq₂, h₂, h₂', e₂, e₂'⟩
    refine ⟨γ₁ + γ₂, r₁ * r₂, q₁ * q₂, exHomog_mul hr₁ hr₂, exHomog_mul hq₁ hq₂, by simp [h₁, h₂],
      by simp [h₁', h₂'], ?_, ?_⟩
    · simp only [map_mul, e₁, e₂, Prod.fst_mul]
      ring
    · simp only [map_mul, e₁', e₂', Prod.snd_mul]
      ring
  neg_mem' := by
    rintro w ⟨γ, r, q, hr, hq, h, h', e, e'⟩
    exact ⟨γ, -r, q, homog_neg hr, hq, h, h', by simp [e], by simp [e']⟩
end Generic
section Geometry
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
  [Algebra Ω Φ]
def ratioPoly {R : Type} [CommRing R] (xb : ι → R) (ε : ν → R) (c₀ c₁ : κ → R) :
    (Σ k, T.wwIdx ι ν κ k) → MvPolynomial (Fin 2) R
  | ⟨.base, j⟩ => C (xb j)
  | ⟨.det, l⟩ => C (ε l)
  | ⟨.line0, k⟩ => C (c₀ k) + C (c₁ k) * X 0
  | ⟨.line1, k⟩ => C (c₀ k) + C (c₁ k) * X 1
def blockScale {M : Type} (u₁ u₂ u₃ u₄ : M) : T.WBlk → M
  | .base => u₁
  | .det => u₂
  | .line0 => u₃
  | .line1 => u₄
end Geometry
end DiagonalFormDivisor
end
end GroundTheory.Heights₂.Heights.Inter


