-- Prove2me | Definitions.Def_Formalism_LatticeRigidity_PackCount
-- name    : Formalism_LatticeRigidity_PackCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:48:28.204204+00:00
-- url     : https://prove2.me/theorems/18b00d0f-01ca-49cd-bbd7-b1d3b83f619d
-- title:
--   Pack Count
-- statement:
--   Definitions and structural lemmas for Pack Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/PackCount.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SA.P7
def PackCount : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (V : ι → Type) [∀ v, NormedAddCommGroup (V v)]
    [∀ v, NormedSpace ℝ (V v)] [∀ v, FiniteDimensional ℝ (V v)] (N : ℕ),
    (∀ v, Module.finrank ℝ (V v) = N) →
    ∀ (S : Finset (∀ v, V v)) (lam : ℝ) (X : ι → ℝ), 0 < lam → (∀ v, 0 < X v) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        lam ≤ (∏ v, ‖x v - y v‖) ^ ((1 : ℝ) / Fintype.card ι)) →
      (∀ x ∈ S, ∀ v, ‖x v‖ ≤ X v) →
      (S.card : ℝ) ≤
        (1 + 2 * (∏ v, X v) ^ ((1 : ℝ) / Fintype.card ι) / lam) ^ (N * Fintype.card ι)
end Formalism.SA.P7


