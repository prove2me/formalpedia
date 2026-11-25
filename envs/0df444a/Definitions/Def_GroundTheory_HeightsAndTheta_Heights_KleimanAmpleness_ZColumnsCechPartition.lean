-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:30:22.949367+00:00
-- url     : https://prove2.me/theorems/00ed6985-9df9-5161-88de-5d709168f0e9
-- title:
--   ZColumns Cech Partition
-- statement:
--   Definitions and structural lemmas for ZColumns Cech Partition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ZColumnsCechPartition.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
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
namespace Cech.Partition
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V]
  [Module R V]
def onSet {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (A : Finset (Fin n)) : V :=
  if h : A.card = i + 1 ∧ A ⊆ U then
    s ⟨⟨A, Finset.card_pos.mp (h.1 ▸ Nat.succ_pos i), h.2⟩, h.1⟩
  else 0
def coneY {i : ℕ} (k : Fin n) (z : Cech.Cochain (fun _ : Cell U => V) (i + 1)) (A : Finset (Fin n)) : V :=
  if k ∈ A then 0 else Cech.sgn (insert k A) k • onSet z (insert k A)
end Cech.Partition
end
end GroundTheory.Heights₂.Heights.Kleiman


