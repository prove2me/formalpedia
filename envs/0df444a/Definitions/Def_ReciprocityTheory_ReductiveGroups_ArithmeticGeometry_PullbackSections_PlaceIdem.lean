-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_PlaceIdem
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_PlaceIdem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:27.364019+00:00
-- url     : https://prove2.me/theorems/790a3f52-c7b0-4366-8250-d3b87e83b23d
-- title:
--   Place Idem
-- statement:
--   Definitions and structural lemmas for Place Idem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/PlaceIdem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open Classical in

def PlaceIdemSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (k : Type) [Field k] [Algebra V k] [IsFractionRing V k]
    (P : Ideal (𝓞 E)), P.IsPrime → P ≠ ⊥ →
    ∃ (n : ℕ) (b : Fin n → 𝓞 E) (a : Fin n → V), ∀ ψ : E →+* k,
      ∑ i, algebraMap V k (a i) * ψ (b i : E) =
        if (∀ x : 𝓞 E, x ∈ P ↔ ψ (x : E) ∈ algebraMap V k '' (IsLocalRing.maximalIdeal V : Set V)) then 1 else 0
end ReciprocityTheory.ChartRestriction.G.PullbackSections


