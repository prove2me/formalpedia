-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechHdegOfSub
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechHdegOfSub
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:37:46.688815+00:00
-- url     : https://prove2.me/theorems/07cbabdd-06b5-4957-a5f0-8c0c605e3184
-- title:
--   PCech Hdeg Of Sub
-- statement:
--   Definitions and structural lemmas for PCech Hdeg Of Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechHdegOfSub.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechHdegOfSubSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
namespace Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] (G : Cell U → Type v)
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)
theorem Cdeg_top (i : ℕ) : Cdeg G (fun I => (⊤ : Submodule R (G I))) i = ⊤ := by
  ext s
  simp [Cdeg]
theorem cocyDeg_top (i : ℕ) :
    cocyDeg G (fun I => (⊤ : Submodule R (G I))) ρ i = LinearMap.ker (d G ρ i) := by
  rw [cocyDeg, Cdeg_top, inf_top_eq]
theorem bdryDeg_top (i : ℕ) :
    bdryDeg G (fun I => (⊤ : Submodule R (G I))) ρ i = bdry G ρ i := by
  cases i with
  | zero => rfl
  | succ i =>
    change (Cdeg G _ i).map (d G ρ i) = LinearMap.range (d G ρ i)
    rw [Cdeg_top, Submodule.map_top]
def hEquivHdegTop (i : ℕ) : H G ρ i ≃ₗ[R] Hdeg G (fun I => (⊤ : Submodule R (G I))) ρ i :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (cocyDeg_top G ρ i).symm) (by
    ext z
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
    change (z : Cochain G i) ∈ bdry G ρ i ↔ (z : Cochain G i) ∈ bdryDeg G _ ρ i
    rw [bdryDeg_top])
end Cech
end
end GroundTheory.Heights₂.Heights.Kleiman


