-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionChowHeight
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionChowHeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:54.977075+00:00
-- url     : https://prove2.me/theorems/b19f7807-0a79-404e-80a2-efec541b2433
-- title:
--   Statements Section Chow Height
-- statement:
--   Definitions and structural lemmas for Statements Section Chow Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsSectionChowHeight.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemConePointsSpanX0
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt)
open Classical in

def SectionChowHeight.Statement : Prop :=
  ∀ (n e δ : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (P : Ideal (MRing (PBlk n)))
    (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℚ) (u : Fin n → ℤ)
    (g : Ideal (MRing (PBlk n)) → MvPolynomial (Fin (e + 1) × Fin n) ℚ)
    (d : Ideal (MRing (PBlk n)) → ℕ),
    IsUnit S → IsArithVar P (e + 1 + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) (e + 1) δ
      (map (Rat.castHom ℂ) f) →
    IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
    (∀ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u), IsHorizontal W →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) e (d W)
        (map (Rat.castHom ℂ) (g W))) →
      IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (IndefiniteRowSideFullHecke.ArithBezout.specFirst (fun j => (u j : ℚ)) f) δ =
        ∑ᶠ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u),
          (multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
            (if IsHorizontal W then IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g W) (d W) else 0)
end GroundTheory.Heights₂.Heights


