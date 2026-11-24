-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:45.7122+00:00
-- url     : https://prove2.me/theorems/6541b1e3-b78e-4942-9ec2-d1e6e15bd331
-- title:
--   Is Field Intersection No Block Fam
-- statement:
--   Definitions and structural lemmas for Is Field Intersection No Block Fam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsFieldIntersectionNoBlockFam.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
def GenDegAt (I : AllFam) (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι'),
    IsBlockMap κ v → IsArithVar P' d → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    I K' ι' P' d L' = (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * I K ι (imageZ v P') d L
def ArithmeticIntersectionCycle.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ n : ℕ, GenDegAt I n →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
      (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
      (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (s : MRing ι) (α : K → ℕ),
      IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      IsMultiHomog s α → s ∉ imageZ v P' →
      cycR (I K' ι') P' L' (rename v s) =
        (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * cycR (I K ι) (imageZ v P') L s
def ArithmeticIntersectionIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (A : HermLine ι) (A' : HermLine ι') (f g : MRing ι),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → IsSmoothHerm A → IsPullHerm κ v A A' →
    IsRatSectionOn (imageZ v P') A f g →
    ptsIntegral P' (pot L') (logNormRat A' (rename v f) (rename v g)) =
      (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * ptsIntegral (imageZ v P') (pot L) (logNormRat A f g)
section Inhabitants
open IndefiniteRowSideFullHecke.Inter
variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def noBlockFam (F : Type) [Field F] {K : Type} [Fintype K] [IsEmpty K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    IFamily F ι :=
  fun V n _ => if n = 0 then (ptDeg V (fun k => isEmptyElim k) : ℤ) else 0
instance isEmpty_fibreBlock_id : IsEmpty (FibreBlock (id : Unit → Unit)) :=
  ⟨fun k => k.2 ⟨k.1, rfl⟩⟩
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


