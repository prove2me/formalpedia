-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShellInt
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShellInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:01.956376+00:00
-- url     : https://prove2.me/theorems/66e3e06f-aca9-40aa-b53f-18e67c27e708
-- title:
--   Shell Int
-- statement:
--   Definitions and structural lemmas for Shell Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShellInt.lean

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
namespace GlobalTheory.PoleInertCalc
variable {K : Type} [NormedField K]
def supN {m : ℕ} (ξ : Fin m → K × K) : ℝ := ⨆ i, max ‖(ξ i).1‖ ‖(ξ i).2‖
def hQ (d : K) {m : ℕ} (ξ : Fin m → K × K) : K := ∑ i, ((ξ i).1 ^ 2 - d * (ξ i).2 ^ 2)
def rad (d : K) {m : ℕ} (ξ : Fin m → K × K) : ℝ := max (max 1 (supN ξ)) ‖hQ d ξ‖
def c0 (q s : ℝ) : ℝ := (1 - q ^ (-s)) / (1 - q ^ (1 - s))
def nIso (q : ℝ) (m : ℕ) : ℝ := q ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q ^ m - q ^ ((m : ℤ) - 1)) - 1
def primDen (q : ℝ) (m e : ℕ) : ℝ :=
  if e = 0 then 1 - q ^ (-(2 * (m : ℤ))) else nIso q m * q ^ (-(2 * (m : ℤ))) * q ^ (1 - (e : ℤ))
def shellInt (q u : ℝ) (m j : ℕ) : ℝ :=
  u ^ j * primDen q m j + ∑ e ∈ Finset.range j, (primDen q m e - primDen q m (e + 1)) * u ^ (2 * j - e)
end GlobalTheory.PoleInertCalc
end


