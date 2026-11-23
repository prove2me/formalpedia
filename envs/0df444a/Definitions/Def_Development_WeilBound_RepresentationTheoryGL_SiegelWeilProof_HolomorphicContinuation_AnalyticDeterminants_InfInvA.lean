-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:33.011553+00:00
-- url     : https://prove2.me/theorems/2b6c6508-bc29-4db2-9615-eaec2bd0650d
-- title:
--   Inf Inv A
-- statement:
--   Definitions and structural lemmas for Inf Inv A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/InfInvA.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def reK (e : M2 n) : M2 n := (1 / 2 : ℂ) • (e - eᴴ)
def imK (e : M2 n) : M2 n := (-Complex.I / 2) • (e + eᴴ)
def dK (F : M2 n → ℂ) (x e : M2 n) : ℂ := fderiv ℝ F x (reK e * x) + Complex.I * fderiv ℝ F x (imK e * x)
def KSet (n : ℕ) : Set (M2 n) := {g | InK g}
def LeftDeriv : Prop :=
  ∀ (n : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι → (∀ g, InK g ↔ ∃ k, ι k = g) →
    ∀ (F : M2 n → ℂ) (U : Set (M2 n)), IsOpen U → KSet n ⊆ U → ContDiffOn ℝ 1 F U →
    ∀ e : M2 n, e * JJ n = JJ n * e →
      Integrable (fun k => dK F (ι k) e) μ ∧ ∫ k, dK F (ι k) e ∂μ = 0
def LawDeriv : Prop :=
  ∀ (n : ℕ) (Θ : M2 n → ℂ) (Ω : Set (M2 n)), IsOpen Ω → {g | InG g} ⊆ Ω → DifferentiableOn ℂ Θ Ω →
    (∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x → Θ (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * Θ x) →
    ∀ x, InG x → ∀ Y : M2 n, Y.toBlocks₂₁ = 0 →
      fderiv ℂ Θ x (Y * x) = (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace) * Θ x
def eA (a b : Fin n) : M2 n := fromBlocks (Matrix.single a b 1) 0 0 (Matrix.single a b 1)
def eB (a b : Fin n) : M2 n := fromBlocks 0 (Matrix.single a b 1) (-Matrix.single a b 1) 0
def cA (Z : M2 n) (a b : Fin n) (x : M2 n) : ℂ := (x * Z * xᴴ).toBlocks₂₂ a b
def cB (Z : M2 n) (a b : Fin n) (x : M2 n) : ℂ := -(x * Z * xᴴ).toBlocks₂₁ a b
def PtId : Prop :=
  ∀ (n : ℕ) (Θ : M2 n → ℂ) (x Z : M2 n), InK x → ContDiffAt ℂ 1 Θ x →
    (∀ Y : M2 n, Y.toBlocks₂₁ = 0 → fderiv ℂ Θ x (Y * x) = (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace) * Θ x) →
    fderiv ℂ Θ x (x * Z) =
      ∑ a, ∑ b, (dK (fun y => cA Z a b y * Θ y) x (eA a b) + dK (fun y => cB Z a b y * Θ y) x (eB a b))
def CDiff : Prop := ∀ (n : ℕ) (Z : M2 n) (a b : Fin n), ContDiff ℝ ∞ (cA Z a b) ∧ ContDiff ℝ ∞ (cB Z a b)
end PositivityTheory.Rg.Sw.LVs.II


