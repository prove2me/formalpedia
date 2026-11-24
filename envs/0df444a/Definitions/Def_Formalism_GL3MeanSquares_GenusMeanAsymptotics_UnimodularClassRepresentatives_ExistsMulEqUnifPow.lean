-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T09:33:51.963431+00:00
-- url     : https://prove2.me/theorems/ace3e0e9-95e7-4e04-8edd-eb6e3540bf2c
-- title:
--   Exists Mul Eq Unif Pow
-- statement:
--   Definitions and structural lemmas for Exists Mul Eq Unif Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace NO
abbrev zR (𝔭 : Ideal (𝓞 F)) (z : K) : AddSubgroup K :=
  (pK K 𝔭 0).toAddSubgroup.map (AddMonoidHom.mulLeft z)
end NO
namespace NO
end NO
def matL {κ : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (f g : κ → κ → K) : AddSubgroup (Matrix κ κ K) where
  carrier := {M | ∀ i j, ∃ w ∈ pK K 𝔭 k, f i j * M i j = g i j * w}
  zero_mem' := fun i j => ⟨0, (pK K 𝔭 k).zero_mem, by simp⟩
  add_mem' := by
    intro M N hM hN i j
    obtain ⟨w, hw, e⟩ := hM i j
    obtain ⟨w', hw', e'⟩ := hN i j
    exact ⟨w + w', (pK K 𝔭 k).add_mem hw hw', by rw [Matrix.add_apply, mul_add, mul_add, e, e']⟩
  neg_mem' := by
    intro M hM i j
    obtain ⟨w, hw, e⟩ := hM i j
    exact ⟨-w, (pK K 𝔭 k).neg_mem hw, by rw [Matrix.neg_apply, mul_neg, mul_neg, e]⟩
namespace NO
def scal (κ : Type) (𝔭 : Ideal (𝓞 F)) (a : K) :
    (κ × κ → (pK K 𝔭 0).toAddSubgroup) →+ Matrix κ κ K where
  toFun v := Matrix.of fun i j => a * (v (i, j) : K)
  map_zero' := by
    ext i j
    simp
  map_add' v w := by
    ext i j
    simp [mul_add]
end NO
end Formalism.HermitianLattices.Ext.L3.D2


