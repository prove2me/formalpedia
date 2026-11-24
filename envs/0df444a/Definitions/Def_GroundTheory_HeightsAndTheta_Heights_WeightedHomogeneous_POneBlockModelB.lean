-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:50.471801+00:00
-- url     : https://prove2.me/theorems/d39119ed-1116-43a7-bfc0-8431d12c2096
-- title:
--   POne Block Model B
-- statement:
--   Definitions and structural lemmas for POne Block Model B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelB.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
namespace LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
def prodSpan (L : Submodule (𝓞 K) (Fin m → K)) (d : ℕ) : Submodule (𝓞 K) (MvPolynomial (Fin m) K) :=
  Submodule.span (𝓞 K) {p | ∃ u : Fin d → Fin m → K, (∀ i, u i ∈ latticeDual L) ∧ p = ∏ i, latticeForm (u i)}
variable {φ : Fin (N + 1) → Fin m → K}
section Birational
variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}
def yEval (φ : Fin (N + 1) → Fin (r + 1) → K) : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ →+* LatticeField K r :=
  eval₂Hom (Int.castRingHom _) (latticeCoord φ)
def quotField (φ : Fin (N + 1) → Fin (r + 1) → K) : Subfield (LatticeField K r) where
  carrier := {s | ∃ (d : ℕ) (g h : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ), g.IsHomogeneous d ∧ h.IsHomogeneous d ∧
    yEval φ h ≠ 0 ∧ yEval φ g = s * yEval φ h}
  mul_mem' := by
    rintro s s' ⟨d, g, h, hg, hh, hne, he⟩ ⟨d', g', h', hg', hh', hne', he'⟩
    exact ⟨d + d', g * g', h * h', hg.mul hg', hh.mul hh', by rw [map_mul]; exact mul_ne_zero hne hne',
      by rw [map_mul, map_mul, he, he']; ring⟩
  one_mem' := ⟨0, 1, 1, isHomogeneous_one _ _, isHomogeneous_one _ _, by simp, by simp⟩
  add_mem' := by
    rintro s s' ⟨d, g, h, hg, hh, hne, he⟩ ⟨d', g', h', hg', hh', hne', he'⟩
    refine ⟨d + d', g * h' + h * g', h * h', (hg.mul hh').add (hh.mul hg'), hh.mul hh',
      by rw [map_mul]; exact mul_ne_zero hne hne', ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, he, he']
    ring
  zero_mem' := ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp, by simp⟩
  neg_mem' := by
    rintro s ⟨d, g, h, hg, hh, hne, he⟩
    exact ⟨d, -g, h, hg.neg, hh, hne, by rw [map_neg, he]; ring⟩
  inv_mem' := by
    rintro s ⟨d, g, h, hg, hh, hne, he⟩
    by_cases hs : s = 0
    · subst hs
      rw [inv_zero]
      exact ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp, by simp⟩
    · refine ⟨d, h, g, hh, hg, by rw [he]; exact mul_ne_zero hs hne, ?_⟩
      rw [he]
      field_simp
end Birational
end LatticeModel
end
end GroundTheory.Heights₂.Heights


