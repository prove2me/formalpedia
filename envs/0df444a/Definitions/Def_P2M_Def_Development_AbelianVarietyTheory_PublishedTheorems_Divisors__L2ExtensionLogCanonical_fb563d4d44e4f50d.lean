-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__L2ExtensionLogCanonical_fb563d4d44e4f50d
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__L2ExtensionLogCanonical_fb563d4d44e4f50d
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:56.733289+00:00
-- url     : https://prove2.me/theorems/b7e23a89-5926-45a1-ac06-41fb03b49945
-- title:
--   L2 Extension Log Canonical
-- statement:
--   Definitions and structural lemmas for L2 Extension Log Canonical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/L2ExtensionLogCanonical.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.Published
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
noncomputable section
namespace L2Extension
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
def jacAt (A : WeightedAtlas n Y ι La) (s : Fin n → ι → Y → ℂ) (P : Y) : ℂ :=
  (fderiv ℂ (A.zLoc (fun _ _ => 1) s (A.pick P)) (A.chart (A.pick P) P)).det
def psi (A : WeightedAtlas n Y ι La) (L : La) (s : Fin n → ι → Y → ℂ) (y : Y) : ℝ :=
  (n : ℝ) * Real.log (A.sqn L s y)
def resSq (A : WeightedAtlas n Y ι La) (E L : La) (s : Fin n → ι → Y → ℂ) (P : Y) (c : ℂ) : ℝ :=
  ‖c / jacAt A s P‖ ^ 2 * Real.exp (-A.ph E (A.pick P) P + (n : ℝ) * A.ph L (A.pick P) P)
def resConst (r : ℕ) : ℝ :=
  2 ^ (r + 1) * Real.pi ^ r / ((r - 1).factorial : ℝ)
end L2Extension
open L2Extension in

def L2ExtensionLogCanonical : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
  ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (ι : Type) (La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La),

    (∃ H : La, ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 →
      0 < A.leviAt i (A.ph H i) y ξ) →
  ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) →
  ∀ hS : (A.zeroSet s).Finite,

    (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) →

    (∀ y, A.sqn L s y ≤ 1) →
  ∀ δ : ℝ, 0 < δ →

    (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s →
      ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) →
  ∀ f : Y → ℂ, ∃ F : ι → Y → ℂ, A.IsSec (A.kap + E) F ∧
    (∀ P ∈ A.zeroSet s, F (A.pick P) P = f P) ∧
    ∫⁻ y, ENNReal.ofReal (2 ^ n * (1 / (1 + (δ * psi A L s y) ^ 2) *
        A.nsq (A.kap + E) F y * Real.exp (-psi A L s y))) ∂A.mu ≤
      ENNReal.ofReal (34 / δ * (resConst n * ∑ P ∈ hS.toFinset, resSq A E L s P (f P)))
end
end GlobalTheory.Published


