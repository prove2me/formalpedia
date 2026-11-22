-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FiltLen
-- name    : Formalism_PeriodIntegrals_FiltLen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:05.160069+00:00
-- url     : https://prove2.me/theorems/241496c1-d0b9-4c31-9bde-590deb56b5cb
-- title:
--   Filt Len
-- statement:
--   Definitions and structural lemmas for Filt Len, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FiltLen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
def FiltLen : Prop :=
  ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (F : ℕ → Submodule R W) (a : ℕ),
    Antitone F → F 0 = ⊤ → F a = ⊥ →
    ∀ (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module R (V k)] (φ : ∀ k, W →ₗ[R] V k),
      (∀ k, ∀ x ∈ F k, φ k x = 0 → x ∈ F (k + 1)) →
      ∀ (M N : Submodule R W) (P Q : ∀ k, Submodule R (V k)), N ≤ M →
        (∀ k < a, (M ⊓ F k).map (φ k) ≤ P k) → (∀ k < a, Q k ≤ (N ⊓ F k).map (φ k)) →
        Module.length R (↥M ⧸ N.comap M.subtype) ≤
          ∑ k ∈ Finset.range a, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype)
end PI


