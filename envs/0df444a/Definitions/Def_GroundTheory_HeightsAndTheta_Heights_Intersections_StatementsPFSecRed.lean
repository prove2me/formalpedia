-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFSecRed
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFSecRed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:26:22.070848+00:00
-- url     : https://prove2.me/theorems/554d4294-8524-48ee-a836-f3b34e79970b
-- title:
--   Statements PFSec Red
-- statement:
--   Definitions and structural lemmas for Statements PFSec Red, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsPFSecRed.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
def PFSecAt (I : AllFam) (r : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin (r + 1) → HermLine ι')
    (s : MRing ι') (a : K' → ℕ),
    IsBlockMap κ v → IsArithVar P' (d + (r + 1)) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    (∀ k, (N (Fin.last r)).a k = a k) → IsMultiHomog s a → s ∉ P' →
    I K' ι' P' (d + (r + 1)) (Fin.append L' N) =
      (J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L
def PFSecRed.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ r : ℕ, PFSecAt I r → PFAt I (r + 1)
section Inhabitants
def fibreLineDeg : Unit ⊕ Unit → ℕ := Sum.elim (fun _ => 0) fun _ => 1
def fibreCoord : MRing PointLineBlocks := X ⟨Sum.inr (), (0 : Fin 2)⟩
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Inter


