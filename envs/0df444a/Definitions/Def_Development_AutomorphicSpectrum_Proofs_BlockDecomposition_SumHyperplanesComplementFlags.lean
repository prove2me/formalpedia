-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:10:02.86787+00:00
-- url     : https://prove2.me/theorems/f985a7b3-20bc-444c-804f-14033189864f
-- title:
--   Sum Hyperplanes Complement Flags
-- statement:
--   Definitions and structural lemmas for Sum Hyperplanes Complement Flags, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SumHyperplanesComplementFlags.lean

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
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
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
namespace GlobalTheory.CompanionTheory.GapOpMain
variable {k : Type} [Field k] [Fintype k] {n : ℕ} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
  {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {red : Γ →* GL (Fin (n + 1)) k} {ρ : Γ →* Module.End ℂ V} {t : Module.End ℂ V}
  {v : Submodule k (Fin (n + 1) → k) → V}
def dualEquiv (g : GL (Fin (n + 1)) k) : (Fin (n + 1) → k) ≃ (Fin (n + 1) → k) where
  toFun a := a ᵥ* (g⁻¹).val
  invFun b := b ᵥ* g.val
  left_inv a := by
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  right_inv a := by
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
def ux (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V) (gam : (Fin (n + 1) → k) → Γ) (y : V)
    (x : Fin (n + 1) → k) : V :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), ρ (gam a) (t y)
end GlobalTheory.CompanionTheory.GapOpMain
end


