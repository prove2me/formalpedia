-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:53.683871+00:00
-- url     : https://prove2.me/theorems/3cd8abfc-f72c-492c-8559-46f291c8d7a0
-- title:
--   Core R
-- statement:
--   Definitions and structural lemmas for Core R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoreR.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped Matrix
variable {P ι : Type}
def qR0 [Fintype ι] (A : P → Matrix ι ι ℝ) (x : P → ι → ℝ) : P → ℝ :=
  fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (A w *ᵥ x w))
def gaussR [Fintype P] [Fintype ι] (Pm : P → Matrix ι ι ℝ) (x : P → ι → ℝ) : ℝ :=
  Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))
def boxR [Fintype ι] (t : P → ℝ) : Set (P → ι → ℝ) :=
  {x | ∀ w, ‖x w‖ ≤ t w}
def coreR [Fintype ι] (δ R : ℝ) : Set (P → ι → ℝ) :=
  {x | ∀ w, δ ≤ ‖x w‖ ∧ ‖x w‖ ≤ R}
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0


