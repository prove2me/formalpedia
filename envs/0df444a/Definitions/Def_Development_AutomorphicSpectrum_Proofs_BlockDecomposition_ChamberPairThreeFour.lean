-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:13.583815+00:00
-- url     : https://prove2.me/theorems/ebf2a60d-8499-4650-8b07-e89275db2919
-- title:
--   Chamber Pair Three Four
-- statement:
--   Definitions and structural lemmas for Chamber Pair Three Four, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEisGal
def coneI (r : ℝ) : Set (ℝ × ℝ) := {x | r < x.2 ∧ r < x.2 + x.1}
def coneC (r : ℝ) : Set (ℝ × ℝ) := {x | r < x.2 - x.1 ∧ r < x.2 + x.1}
def coneA (r : ℝ) : Set (ℝ × ℝ) := {x | r < x.2 - x.1 ∧ r < x.2}
abbrev yv (N : ℝ) : ℂ × ℂ → ℂ := aff 1 1 (1 - N)
abbrev zv (N : ℝ) : ℂ × ℂ → ℂ := aff 1 2 (1 - N)
abbrev nz (N : ℝ) : ℂ × ℂ → ℂ := aff (-1) 0 N
abbrev mc (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg 1 1 (1 - N) 0 1 1
abbrev ma (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg 1 2 (1 - N) 0 1 1
abbrev mb (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg 0 1 0 (-1) (-1) (2 * N - 1)
abbrev ml (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg (-1) 0 N 0 (-1) (N - 1)
def Om1 (N r : ℝ) : Set (ℝ × ℝ) := chgR 1 1 (1 - N) 0 1 1 ⁻¹' coneC r
def Om2 (N r : ℝ) : Set (ℝ × ℝ) := chgR 1 2 (1 - N) 0 1 1 ⁻¹' coneA r
def Om3 (N r : ℝ) : Set (ℝ × ℝ) := chgR 0 1 0 (-1) (-1) (2 * N - 1) ⁻¹' coneC r
def Om4 (N r : ℝ) : Set (ℝ × ℝ) := chgR (-1) 0 N 0 (-1) (N - 1) ⁻¹' coneI r ∩ {x | x.1 < 1 / 2}
def chamberPairOneTwo (M : ℝ) : Set (ℝ × ℝ) := {x | x.1 < -M ∧ M < x.1 + x.2}
def chamberPairTwoThree (M : ℝ) : Set (ℝ × ℝ) := {x | x.1 + x.2 < -M ∧ M < x.1 + 2 * x.2}
def chamberPairThreeFour (M : ℝ) : Set (ℝ × ℝ) := {x | x.1 + 2 * x.2 < -M ∧ M < x.2}
def chamberPairFourLast (M : ℝ) : Set (ℝ × ℝ) := {x | x.2 < -M ∧ x.1 < -M}
section Fac
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
end Fac
section Core
variable {T : Type} [TopologicalSpace T] [FirstCountableTopology T]
  {ES EA EB W : Type} [NormedAddCommGroup ES] [NormedSpace ℂ ES] [NormedAddCommGroup EA]
  [NormedSpace ℂ EA] [NormedAddCommGroup EB] [NormedSpace ℂ EB] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace W]
end Core
end GlobalTheory.CompanionTheory.RgEisGal


