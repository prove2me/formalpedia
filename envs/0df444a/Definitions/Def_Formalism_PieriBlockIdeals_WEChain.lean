-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_WEChain
-- name    : Formalism_PieriBlockIdeals_WEChain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:05.295093+00:00
-- url     : https://prove2.me/theorems/13a3f94b-fcea-41c5-a5c1-c190b8365dee
-- title:
--   WEChain
-- statement:
--   Definitions and structural lemmas for WEChain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/WEChain.lean

import Definitions.Def_Formalism_PieriBlockIdeals_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
namespace Formalism.CohomologicalDescent
def WEChain : Prop :=
  ∀ (k j t q l h κ : ℕ) (K : Type) [Field K] [CharP K l]
    (U U' V V' : Fin (k + j + t + q) → ℤ) (b b' c c' : ℤ) (kc kp : Fin t → ℤ),
    l.Prime → t + 2 * κ < l →
    StrictAnti U → StrictAnti U' → StrictAnti V → StrictAnti V' →
    (∀ a, 0 ≤ U a) → (∀ a, U' a ≤ (h : ℤ)) → ∑ a, U a = ∑ a, U' a →
    (∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U a = b + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) →
    (∀ s : Fin t, ∃ a, V a = b' + ((s : ℕ) : ℤ)) →
    (∏ a, (X + C (((U a + c : ℤ)) : K))) = ∏ a, (X + C (((U' a + c : ℤ)) : K)) →
    (∏ a, (X + C (((V a + c' : ℤ)) : K))) = ∏ a, (X + C (((V' a + c' : ℤ)) : K)) →
    (∀ s, |kc s| ≤ (κ : ℤ)) → (∀ s, |kp s| ≤ (κ : ℤ)) →
    Multiset.map (fun s : Fin t => ((b + ((s : ℕ) : ℤ) - kc s : ℤ) : ZMod l)) Finset.univ.val ≤
      Multiset.map (fun a => ((U' a : ℤ) : ZMod l)) Finset.univ.val →
    Multiset.map (fun s : Fin t => ((b' + ((s : ℕ) : ℤ) - kp s : ℤ) : ZMod l)) Finset.univ.val ≤
      Multiset.map (fun a => ((V' a : ℤ) : ZMod l)) Finset.univ.val →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ) + (l : ℤ) * kp s - kc s) →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U a - U' a) ≤
      (q : ℤ) * h +
        ((l : ℤ) * (mwCount l b' t κ (Finset.univ.image V) : ℤ) +
          (mwCount l b t κ (Finset.univ.image U) : ℤ)) * ((t : ℤ) + 2 * κ)
end Formalism.CohomologicalDescent


