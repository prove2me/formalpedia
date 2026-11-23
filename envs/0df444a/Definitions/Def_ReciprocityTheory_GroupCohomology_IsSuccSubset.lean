-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
-- name    : ReciprocityTheory_GroupCohomology_IsSuccSubset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:24.040212+00:00
-- url     : https://prove2.me/theorems/18ef1560-7493-43cc-983c-b585bb24f6f9
-- title:
--   Is Succ Subset
-- statement:
--   Definitions and structural lemmas for Is Succ Subset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/IsSuccSubset.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
noncomputable section
universe u
open Cx
namespace InflationTower
variable {R : Type u} [CommRing R]
def Hs (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) : ℕ → ∀ m, Submodule R ((A m).H k)
  | 0 => fun _ => ⊤
  | j + 1 => fun m => (Hs A τ k j (m + 1)).map ((τ m).H k)
def Is (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1)) :
    ℕ → ∀ m, Set ((A m).X k)
  | 0 => fun m => {b | (A m).d k b = c m}
  | j + 1 => fun m => (τ m).f k '' Is A τ k c j (m + 1)
section Inj
variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))
end Inj
section Inj2
variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))
end Inj2
end InflationTower
end
universe u
end ReciprocityTheory.Coh


