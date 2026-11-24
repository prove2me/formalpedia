-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:05.081269+00:00
-- url     : https://prove2.me/theorems/6a7a520c-cd2d-4872-9a22-53f0ca86073a
-- title:
--   Has Sum Cosets Euler Product
-- statement:
--   Definitions and structural lemmas for Has Sum Cosets Euler Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumCosetsEulerProduct.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory.CosetEuler
variable {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)]
section
variable (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G)
def offSet (T : Finset ι) : Set (H ⧸ J.subgroupOf H) :=
  {y | ∀ v ∉ T, p v ((y.out : H) : G) ∈ K v}
def shift (v : ι) (g : G) : G := g * (e v (p v g))⁻¹
end
theorem shift_mem {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {H : Subgroup G}
    (he : ∀ v a, e v a ∈ H) (v : ι) {g : G} (hg : g ∈ H) : shift e p v g ∈ H :=
  H.mul_mem hg (H.inv_mem (he _ _))
noncomputable def stepMap (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G)
    (he : ∀ v a, e v a ∈ H) (T : Finset ι) (v : ι) :
    offSet p K J H T × (L v ⧸ K v) → H ⧸ J.subgroupOf H :=
  fun x => ((⟨shift e p v ((x.1.1.out : H) : G) * e v x.2.out,
    H.mul_mem (shift_mem he v (x.1.1.out).2) (he _ _)⟩ : H) : H ⧸ J.subgroupOf H)
section step
variable [DecidableEq ι] {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hJH : J ≤ H) (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
include hJH hpe hpe' he hJ
end step
section ind
variable [DecidableEq ι] {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)}
    {J H : Subgroup G}
    (hJH : J ≤ H) (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
include hJH hJ
include hpe hpe' he
end ind
end GlobalTheory.CosetEuler


