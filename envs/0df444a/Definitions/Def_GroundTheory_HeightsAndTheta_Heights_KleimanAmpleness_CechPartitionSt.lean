-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechPartitionSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechPartitionSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:00.792797+00:00
-- url     : https://prove2.me/theorems/ac075711-6a62-4915-9b98-aba44faa5453
-- title:
--   Cech Partition St
-- statement:
--   Definitions and structural lemmas for Cech Partition St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CechPartitionSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
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
def CechPartition.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    {n : ℕ} (U : Finset (Fin n)) (M : Cell U → Submodule S E) (m : ℕ) (a b : Fin m → Ω) (j : Fin m → Fin n),
    (∀ k, j k ∈ U) → ∑ k, a k * b k = 1 →
    (∀ k I, ∀ z ∈ M I, a k • z ∈ M I) → (∀ k I, ∀ z ∈ M I, b k • z ∈ M I) →
    (∀ k (I I' : Cell U), I'.1 = insert (j k) I.1 → ∀ z ∈ M I', ∃ e : ℕ, b k ^ e • z ∈ M I) →
    ∀ p : ℕ, ∀ s ∈ Cech.Cdeg (fun _ : Cell U => E) M (p + 1),
      Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) (p + 1) s = 0 →
        ∃ t ∈ Cech.Cdeg (fun _ : Cell U => E) M p, Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) p t = s
end
end GroundTheory.Heights₂.Heights.Kleiman


