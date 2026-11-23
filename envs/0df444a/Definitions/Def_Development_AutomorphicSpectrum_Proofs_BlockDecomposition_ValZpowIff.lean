-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:18.180946+00:00
-- url     : https://prove2.me/theorems/00e9c9cf-0915-4b46-a3d4-948803ebe9fb
-- title:
--   Val Zpow Iff
-- statement:
--   Definitions and structural lemmas for Val Zpow Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.CongIndex
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
noncomputable def red (ϖ : k) (c : ℕ) (x : k) :
    IsLocalRing.ResidueField (valuation k).integer := by
  classical
  exact if h : valuation k (x * (ϖ ^ c)⁻¹) ≤ 1 then
    IsLocalRing.residue _ ⟨x * (ϖ ^ c)⁻¹, h⟩ else 0
theorem scaled_le {ϖ : k} (h0 : ϖ ≠ 0) {c : ℕ} {x : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) : valuation k (x * (ϖ ^ c)⁻¹) ≤ 1 := by
  have hp : valuation k (ϖ ^ c) ≠ 0 := by
    simpa using (pow_ne_zero c h0)
  rw [map_mul, map_inv₀]
  exact mul_inv_le_one_of_le₀ hx zero_le'
variable {N : ℕ}
def Kset (ϖ : k) (c : Fin N → Fin N → ℕ) : Set (GL (Fin N) k) :=
  {g | ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j)
    ≤ valuation k (ϖ ^ c i j)}
end GlobalTheory.CompanionTheory.CongIndex


