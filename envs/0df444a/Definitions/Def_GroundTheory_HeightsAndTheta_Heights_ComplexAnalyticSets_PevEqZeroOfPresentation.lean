-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:23.019798+00:00
-- url     : https://prove2.me/theorems/a66c53e0-2255-454e-8eff-e50ce129573c
-- title:
--   Pev Eq Zero Of Presentation
-- statement:
--   Definitions and structural lemmas for Pev Eq Zero Of Presentation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace IsGermCombination
variable {σ : Type} [Fintype σ] {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ}
theorem congr {f g : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) (h : ∀ᶠ z in 𝓝 w, f z = g z) :
    IsGermCombination w p g := by
  obtain ⟨c, hc, he⟩ := hf
  exact ⟨c, hc, by filter_upwards [he, h] with z hz h' using h' ▸ hz⟩
theorem add {f g : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) (hg : IsGermCombination w p g) :
    IsGermCombination w p (fun z => f z + g z) := by
  obtain ⟨c, hc, he⟩ := hf
  obtain ⟨c', hc', he'⟩ := hg
  refine ⟨fun i => c i + c' i, fun i => (hc i).add (hc' i), ?_⟩
  filter_upwards [he, he'] with z hz hz'
  simp only [Pi.add_apply, hz, hz', add_mul, Finset.sum_add_distrib]
theorem mul_left {f g : (σ → ℂ) → ℂ} (hg : AnalyticAt ℂ g w) (hf : IsGermCombination w p f) :
    IsGermCombination w p (fun z => g z * f z) := by
  obtain ⟨c, hc, he⟩ := hf
  refine ⟨fun i => g * c i, fun i => hg.mul (hc i), ?_⟩
  filter_upwards [he] with z hz
  simp only [Pi.mul_apply, hz, Finset.mul_sum, mul_assoc]
theorem neg {f : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) :
    IsGermCombination w p (fun z => - f z) :=
  (mul_left (g := fun _ => (-1 : ℂ)) analyticAt_const hf).congr (Eventually.of_forall fun z => by ring)
end IsGermCombination
def analyticSubring {d : ℕ} (y₀ : Fin d → ℂ) : Subring ((Fin d → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f y₀}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha
def evalAt {d : ℕ} (y₀ y : Fin d → ℂ) : analyticSubring y₀ →+* ℂ :=
  (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y).comp (analyticSubring y₀).subtype
def pev {d : ℕ} {y₀ : Fin d → ℂ} (y : Fin d → ℂ) (t : ℂ) : (analyticSubring y₀)[X] →+* ℂ :=
  (Polynomial.evalRingHom t).comp (Polynomial.mapRingHom (evalAt y₀ y))
section pev
variable {d : ℕ} {y₀ : Fin d → ℂ}
end pev
def presPoly {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ) (hc : ∀ j, AnalyticAt ℂ (c j) y₀) :
    (analyticSubring y₀)[X] :=
  X ^ N + ∑ j : Fin N, C (⟨c j, hc j⟩ : analyticSubring y₀) * X ^ (j : ℕ)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


