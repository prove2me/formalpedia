-- Prove2me | Definitions.Def_GroundTheory_LocalFields_FilteredSurj
-- name    : GroundTheory_LocalFields_FilteredSurj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:11.514136+00:00
-- url     : https://prove2.me/theorems/03c1839c-9b12-46b8-bb59-95ff9c35db0a
-- title:
--   Filtered Surj
-- statement:
--   Definitions and structural lemmas for Filtered Surj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FilteredSurj.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField
open Filter Topology Uniformity
section Filtration
variable {G : Type*} [Group G]
@[to_additive AddFiltrationCauchy
]
def FiltrationCauchy (F : ℕ → Subgroup G) (x : ℕ → G) : Prop :=
  ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, x n / x m ∈ F N
@[to_additive AddFiltrationTendsto
]
def FiltrationTendsto (F : ℕ → Subgroup G) (x : ℕ → G) (y : G) : Prop :=
  ∀ N, ∃ M, ∀ n ≥ M, x n / y ∈ F N
@[to_additive AddFiltrationComplete
]
def FiltrationComplete (F : ℕ → Subgroup G) : Prop :=
  ∀ x : ℕ → G, FiltrationCauchy F x → ∃ y, FiltrationTendsto F x y
@[to_additive AddFiltrationSeparated
]
def FiltrationSeparated (F : ℕ → Subgroup G) : Prop :=
  ∀ g : G, (∀ n, g ∈ F n) → g = 1
end Filtration
section Surjectivity
variable {G H : Type*} [Group G] [Group H]
end Surjectivity
section Topological
end Topological
end GroundTheory.LocalField


