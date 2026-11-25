-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
-- name    : CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:26:39.998394+00:00
-- url     : https://prove2.me/theorems/77f1f929-7767-4318-90e7-9f4c333fd981
-- title:
--   Nq Moved Example
-- statement:
--   Definitions and structural lemmas for Nq Moved Example, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqMovedExample.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NQText
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
structure PairData (P : M.Par) (l : ℕ) (lam : ℕ → ℝ) (c g b : ℝ) : Prop where
  c_pos : 0 < c
  g_ge : 1 + c ≤ g
  b_ge_three : 3 ≤ b
  b_ge_k : (P.k : ℝ) ≤ b
  b_ge_c : c + 2 ≤ b
  lam_le : ∀ s, 1 ≤ s → s ≤ P.k + 2 * P.r + 1 → |lam s| ≤ b
  gap : ∀ s, 1 ≤ s → s + 1 ≤ P.k - 1 → lam (s + 1) + g ≤ lam s
  ul_le : |P.u l| ≤ b ∧ |P.u' l| ≤ b
  pair : ∀ Y, I.OnCut P.u P.u' l Y → (∃ e, PairOK P.k lam P.u e (-Y)) ∧ ∃ e', PairOK P.k lam P.u' e' (-Y)
structure MovedData (P : M.Par) (l : ℕ) (lam : ℕ → ℝ) (c g b : ℝ) : Prop where
  c_pos : 0 < c
  g_ge : 1 + c ≤ g
  b_ge_three : 3 ≤ b
  b_ge_k : (P.k : ℝ) ≤ b
  b_ge_c : c + 2 ≤ b
  lam_le : ∀ s, 1 ≤ s → s ≤ P.k + 2 * P.r + 1 → |lam s| ≤ b
  gap : ∀ s, 1 ≤ s → s + 1 ≤ P.k - 1 → lam (s + 1) + g ≤ lam s
  inter : ∀ s, 1 ≤ s → s ≤ P.k - 1 → lam s + 1 / 2 ≤ P.u s ∧ P.u (s + 1) ≤ lam s - 1 / 2
  moved : ∀ i, i ≠ l → P.u' i = P.u i
  ul_le : |P.u l| ≤ b ∧ |P.u' l| ≤ b
noncomputable def P₁ : M.Par where
  k := 2
  r := 0
  T := 1
  T' := 1
  u := fun i => if i = 1 then 40 else 0
  u' := fun i => if i = 1 then 40 else if i = 2 then 36 else 0
end CompanionTheory.WaveGrid


