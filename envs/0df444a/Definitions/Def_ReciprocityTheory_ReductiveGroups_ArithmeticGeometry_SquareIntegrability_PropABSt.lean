-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:51.597476+00:00
-- url     : https://prove2.me/theorems/6067416e-9b5b-4243-817f-390b6452a1b2
-- title:
--   Prop ABSt
-- statement:
--   Definitions and structural lemmas for Prop ABSt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropABSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
section
variable {ι : Type} [Fintype ι]
open Classical
def paTh (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  fun v => ∑' γ : lat Y.b, Y.ka γ * paU q γ F v
end
open Classical in

def PaIPJetStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (q c : ℕ), 1 ≤ q → ∀ (a : EuclideanSpace ℂ ι) (F G : EuclideanSpace ℂ ι → ℂ),
    F ∈ paPoly c → G ∈ paPoly c → paIP q (paU q a F) G = paIP q (paJet c (paU q a F)) G
open Classical in

def PaUnfoldStatement : Prop :=
  Ext.PackingCount → Ext.GaussianTailBound →
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q c : ℕ) (R0 : ℝ), 1 ≤ q → 0 < R0 →
    (∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
      Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I)) →
    (∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) →
    16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2 →
    ∀ F : EuclideanSpace ℂ ι → ℂ, F ∈ paPoly c →
      Y.l2 q (paTh Y q F) = (paIP q (paTh Y q F) F).re
open Classical in

def PaThIPStatement : Prop :=
  Ext.PackingCount → Ext.GaussianTailBound →
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q c : ℕ) (R0 : ℝ), 1 ≤ q → 0 < R0 →
    (∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) →
    16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2 →
    ∀ F G : EuclideanSpace ℂ ι → ℂ, F ∈ paPoly c → G ∈ paPoly c →
      HasSum (fun γ : lat Y.b => Y.ka γ * paIP q (paU q γ F) G) (paIP q (paTh Y q F) G)
end
end ReciprocityTheory.ChartRestriction.G.I2


