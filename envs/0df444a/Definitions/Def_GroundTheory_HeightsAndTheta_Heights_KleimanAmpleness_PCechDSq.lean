-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:02.328683+00:00
-- url     : https://prove2.me/theorems/5fe19f03-8397-43e6-9cc7-1c92e63c9ce9
-- title:
--   PCech DSq
-- statement:
--   Definitions and structural lemmas for PCech DSq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDSq.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
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
universe u v
namespace CechDSq
variable {n : ℕ}
variable {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
open Classical in

def restrictTo {i : ℕ} (s : Cech.Cochain G i) (K : Cell U) (A : Finset (Fin n)) : G K :=
  if h : ∃ L : Cech.Idx U i, L.1.1 = A ∧ A ⊆ K.1 then
    ρ h.choose.1 K (by rw [h.choose_spec.1]; exact h.choose_spec.2) (s h.choose)
  else 0
end CechDSq
end
end GroundTheory.Heights₂.Heights.Kleiman


