-- Prove2me | Definitions.Def_CK_GeneralCK_EnergyIdentity
-- name    : CK_GeneralCK_EnergyIdentity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:23:51.553833+00:00
-- url     : https://prove2.me/theorems/e394a1c2-42e6-4176-ad77-245b05593fe2
-- title:
--   Courtade–Kumar proof module `GeneralCK.EnergyIdentity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EnergyIdentity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EnergyIdentity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EnergyIdentity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EnergyIdentity.lean)

import Definitions.Def_CK_GeneralCK_CubeAnalysis
import Definitions.Def_GeneralCK_energy_generator

namespace GeneralCK.Energy
open scoped BigOperators
open CubeAnalysis




@[simp] theorem flip_cons_zero {n : ℕ} (b : Bool) (x : Cube n) :
    flip (Fin.cons b x) 0 = Fin.cons (!b) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [flip]

@[simp] theorem flip_cons_succ {n : ℕ} (b : Bool) (x : Cube n) (i : Fin n) :
    flip (Fin.cons b x) i.succ = Fin.cons b (flip x i) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [flip, Ne.symm (Fin.succ_ne_zero i)]
  · by_cases hk : k = i
    · subst k
      simp [flip]
    · simp [flip, hk]




theorem generatorDensity_cons {n : ℕ} (v : Cube (n+1) → ℝ) (b : Bool)
    (x : Cube n) :
    generatorDensity v (Fin.cons b x) =
      J (slice v b x) * (slice v (!b) x - slice v b x) +
      generatorDensity (slice v b) x := by
  simp only [generatorDensity, Fin.sum_univ_succ, flip_cons_zero, flip_cons_succ,
    slice, mul_add]

theorem mean_add {n : ℕ} (u v : Cube n → ℝ) :
    mean (fun x => u x + v x) = mean u + mean v := by
  simp [mean, Finset.sum_add_distrib, mul_add]

/-- The recursive edge energy equals entropy's pairing with the cube generator.
This identity is algebraic and needs no restriction on the array values. -/
theorem energy_eq_generator (n : ℕ) (v : Cube n → ℝ) :
    energy n v = mean (fun x => J (v x) * ∑ i, (v (flip x i) - v x)) := by
  change energy n v = mean (generatorDensity v)
  induction n with
  | zero => simp [energy, generatorDensity, mean]
  | succ n ih =>
    rw [energy, ih, ih, mean_succ]
    have hfalse : slice (generatorDensity v) false = fun x =>
        J (slice v false x) * (slice v true x - slice v false x) +
        generatorDensity (slice v false) x := by
      funext x
      exact generatorDensity_cons v false x
    have htrue : slice (generatorDensity v) true = fun x =>
        J (slice v true x) * (slice v false x - slice v true x) +
        generatorDensity (slice v true) x := by
      funext x
      exact generatorDensity_cons v true x
    rw [hfalse, htrue, mean_add, mean_add]
    have hedge : mean (fun x => interiorCost (slice v false x) (slice v true x)) =
        (mean (fun x => J (slice v false x) * (slice v true x - slice v false x)) +
        mean (fun x => J (slice v true x) * (slice v false x - slice v true x))) / 2 := by
      unfold mean interiorCost
      rw [← mul_add, ← Finset.sum_add_distrib, mul_div_assoc]
      simp only [div_eq_mul_inv, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hedge]
    ring

end GeneralCK.Energy


