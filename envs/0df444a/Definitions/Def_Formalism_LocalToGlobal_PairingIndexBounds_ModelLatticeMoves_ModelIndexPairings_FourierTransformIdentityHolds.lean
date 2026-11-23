-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
-- name    : Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:53.155203+00:00
-- url     : https://prove2.me/theorems/6af622ff-3a47-4111-b9a5-315ce1388056
-- title:
--   Fourier Transform Identity Holds
-- statement:
--   Definitions and structural lemmas for Fourier Transform Identity Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
section bichar
variable {c : B → A → k}
theorem IsBichar.map_zero_right (hc : IsBichar c) (b : B) : c b 0 = 1 := by
  have h := hc.2.2 b 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (hc.1 b 0) (by rw [mul_one]; exact h.symm)
end bichar
section Heisenberg₂
variable {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T}
end Heisenberg₂
def chi (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) : Multiplicative A₀ →* k where
  toFun s := c b ((Multiplicative.toAdd s : A₀) : A)
  map_one' := hc.map_zero_right b
  map_mul' _ _ := hc.2.2 b _ _
def eFam (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) : A → k := by
  classical exact fun t => if h : t + i.1.out ∈ A₀ then i.2 (Multiplicative.ofAdd ⟨t + i.1.out, h⟩) else 0
def wFam (c : B → A → k) (hc : IsBichar c) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T) (A₀ : AddSubgroup A) (θ : T)
    (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) : T := by
  classical exact if h : ∃ b, chi c hc A₀ b = i.2 then WA i.1.out (WB h.choose θ) else 0
end Formalism.L2.PairingIndexBounds.Mv


