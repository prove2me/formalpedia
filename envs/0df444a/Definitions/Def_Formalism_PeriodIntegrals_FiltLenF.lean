-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FiltLenF
-- name    : Formalism_PeriodIntegrals_FiltLenF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:38:34.811513+00:00
-- url     : https://prove2.me/theorems/9500e0d3-0a60-4853-8557-0a4800fb561d
-- title:
--   Filt Len F
-- statement:
--   Definitions and structural lemmas for Filt Len F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FiltLenF.lean

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
def FiltLenF : Prop :=
  ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (F : ℕ → Submodule R W) (a : ℕ),
    Antitone F → F 0 = ⊤ → F a = ⊥ →
    ∀ (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module R (V k)] (φ : ∀ k, ↥(F k) →ₗ[R] V k),
      (∀ k, ∀ x : ↥(F k), φ k x = 0 → (x : W) ∈ F (k + 1)) →
      ∀ (M N : Submodule R W) (P Q : ∀ k, Submodule R (V k)), N ≤ M →
        (∀ k < a, (M.comap (F k).subtype).map (φ k) ≤ P k) →
        (∀ k < a, Q k ≤ (N.comap (F k).subtype).map (φ k)) →
        Module.length R (↥M ⧸ N.comap M.subtype) ≤
          ∑ k ∈ Finset.range a, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype)
end PI


