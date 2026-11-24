-- Prove2me | Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeDefs
-- name    : ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:13.399802+00:00
-- url     : https://prove2.me/theorems/3232f1ef-820c-430b-a6aa-09a974c96981
-- title:
--   Cone Defs
-- statement:
--   Definitions and structural lemmas for Cone Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/ConeDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ThetaSummability.Est
open Finset
def gap {r : ℕ} (x : Fin r → ℝ) (k : Fin r) : ℝ :=
  x k - (if h : k.val + 1 < r then x ⟨k.val + 1, h⟩ else 0)
def tailSum {r : ℕ} (y : Fin r → ℝ) (k : Fin r) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin r => k ≤ j), y j
def partialSum {r : ℕ} (s : Fin r → ℝ) (k : Fin r) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin r => i ≤ k), s i
def logCone (r : ℕ) (c : ℝ) : Set (Fin r → ℝ) :=
  {x | ∀ k, c ≤ gap x k}
def lowerBox (r : ℕ) (c : ℝ) : Set (Fin r → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Ici c)
def multCone (r : ℕ) (c : ℝ) : Set (Fin r → ℝ) :=
  {t | ∀ k : Fin r, (if h : k.val + 1 < r then c * t ⟨k.val + 1, h⟩ else c) ≤ t k}
example : (![2, 1] : Fin 2 → ℝ) ∈ logCone 2 1 := by
  intro k
  fin_cases k <;> simp [gap] <;> norm_num
example : (![4, 2] : Fin 2 → ℝ) ∈ multCone 2 2 := by
  intro k
  fin_cases k <;> simp <;> norm_num
example : partialSum (![-1, -1] : Fin 2 → ℝ) 1 = -2 := by
  simp [partialSum, Finset.sum_filter, Fin.sum_univ_two]
  norm_num
end ReciprocityTheory.ThetaSummability.Est


