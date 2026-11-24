-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:57.992252+00:00
-- url     : https://prove2.me/theorems/1d2eb069-1e72-472a-b519-3017acee0a88
-- title:
--   Statements Block Trdeg
-- statement:
--   Definitions and structural lemmas for Statements Block Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsBlockTrdeg.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
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
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
def BlockTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
    (L : Type) [Field L] [Algebra ℚ L] (φ : MRing ι' →+* L),
    IsBlockMap κ v → IsMultiProjPrime P' → RingHom.ker φ = P' →
      Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p)))) +
          ((Fintype.card K' - Fintype.card K : ℕ) : Cardinal) ≤
        Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range fun q : Σ k', ι' k' ↦ φ (X q)))
section Examples
abbrev pointBlocks : Unit → Type := fun _ ↦ Unit
def genericPairMap :
    MRing (Sum.elim pointBlocks pointBlocks) →+*
      FractionRing (MvPolynomial (Σ k : Unit ⊕ Unit, Sum.elim pointBlocks pointBlocks k) ℚ) :=
  (algebraMap (MvPolynomial (Σ k : Unit ⊕ Unit, Sum.elim pointBlocks pointBlocks k) ℚ) _).comp
    (MvPolynomial.map (Int.castRingHom ℚ))
end Examples
end GroundTheory.Heights₂.Heights


