-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
-- name    : CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:35:48.223338+00:00
-- url     : https://prove2.me/theorems/7f936e6a-33f8-5b93-988e-d566de14ec96
-- title:
--   PStar Tie
-- statement:
--   Definitions and structural lemmas for PStar Tie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
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
noncomputable def PStar {n : ℕ} (lam : Fin n → ℝ) (c y : ℝ) : ℝ := ∏ s, (|y + lam s| + c)
def NQ (P : M.Par) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ₀ : ℝ) : Prop :=
  ∀ y ∈ Y, nn y * nn (y + 1) ≤ Λ₀ ^ 2 * (M.qC P (y : ℂ)).re
noncomputable def lamN {n : ℕ} (lam : Fin n → ℝ) (s : ℕ) : ℝ := if h : s - 1 < n then lam ⟨s - 1, h⟩ else 0
structure HypLam (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (c g b : ℝ) : Prop where
  hc : Formalism.QuantumDeterminants.IsHCParam lam
  lam_le : ∀ s, |lam s| ≤ b
  c_ge : 1 ≤ c
  b_ge_three : 3 ≤ b
  b_ge_k : Real.exp 1 * k ≤ b
  b_ge_c : c + 2 ≤ b
  g_ge : 2 * c ≤ g
  gap : ∀ s t : Fin (2 * r + k + 1), (t : ℕ) = s + 1 → lam t + g ≤ lam s
structure HypType (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b : ℝ) : Prop where
  half : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, u i - ((k : ℝ) - 1) / 2 = m
  inter : C7.LamInterlaces k r u fun s => lam (s.cast (by ring))
  u_le : ∀ i, 1 ≤ i → i ≤ k → |u i| ≤ b
section data
variable {P : M.Par} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {c g b : ℝ}
end data
noncomputable def nqΛ (P : M.Par) (b : ℝ) : ℝ := Real.sqrt (b ^ (8 * P.r + 20) / (P.T * P.T'))
noncomputable def P₂ : M.Par where
  k := 2
  r := 0
  T := 1
  T' := 1
  u := fun i => if i = 1 then 41 / 2 else 1 / 2
  u' := fun i => if i = 1 then 81 / 2 else 1 / 2
noncomputable def lam₂ : Fin (2 * P₂.r + P₂.k + 1) → ℝ := fun s => 10 - 20 * ((s : ℕ) : ℝ)
end CompanionTheory.WaveGrid


