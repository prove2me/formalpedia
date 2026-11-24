-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherSide
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherSide
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:05.488472+00:00
-- url     : https://prove2.me/theorems/0c01e5a5-69db-4367-ac17-22199359fef7
-- title:
--   Imports Further Side
-- statement:
--   Definitions and structural lemmas for Imports Further Side, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsFurtherSide.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImageVarIdBotTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
def VerticalDegreeAfterAdjoining.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ)
    (i' : ∀ k', ι' k'),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    IsChart (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' →
    ∀ G' : GenFibre v W',
      fnDeg v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' =
        Module.finrank G'.Φ (IntermediateField.adjoin G'.Φ
          (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G'.x' ⟨q.1.1, q.2⟩ / G'.x' ⟨q.1.1, i' q.1.1⟩))
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


