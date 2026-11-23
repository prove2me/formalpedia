-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Branch
-- name    : ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Branch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:48.312746+00:00
-- url     : https://prove2.me/theorems/778a1e86-011e-4bca-9e2f-ab50acc0cdea
-- title:
--   Branch
-- statement:
--   Definitions and structural lemmas for Branch, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/Branch.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
def IsGTFamily {K : Type*} [Field K] (ch : (n : ℕ) → (Fin n → ℤ) → (Fin n → K) → K) : Prop :=
  (∀ (lam : Fin 0 → ℤ) (t : Fin 0 → K), ch 0 lam t = 1) ∧
    ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ), Antitone lam → ∀ t : Fin (n + 1) → K, (∀ i, t i ≠ 0) →
      ch (n + 1) lam t =
        ∑ mu ∈ interl lam, ch n mu (fun i => t i.castSucc) * t (Fin.last n) ^ (wsum lam - wsum mu)
end ReciprocityTheory.ChartRestriction.TR.Weyl


