-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemConePointsSpanX0
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MemConePointsSpanX0
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:54.164983+00:00
-- url     : https://prove2.me/theorems/9e6a5d95-8464-4c60-8881-0d92329d8d5e
-- title:
--   Mem Cone Points Span X0
-- statement:
--   Definitions and structural lemmas for Mem Cone Points Span X0, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MemConePointsSpanX0.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
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
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt geoNum charOf arInt)
open Classical in

def ChowHeightRecQ.Holds (n : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) : Prop :=
  (∀ (δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (0 + 1) × Fin n) ℚ) (u : Fin n → ℤ),
    IsArithVar P (0 + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) 0 δ
      (map (Rat.castHom ℂ) f) →
    IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
      IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ =
        IndefiniteRowSideFullHecke.ArithBezout.vertPart P 0 (IndefiniteRowSideFullHecke.ArithBezout.linForm u) -
          arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
            (fun _ : Fin 0 => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)) ∧
  (∀ (e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℚ)
      (u : Fin n → ℤ) (g : Ideal (MRing (PBlk n)) → MvPolynomial (Fin (e + 1) × Fin n) ℚ)
      (d : Ideal (MRing (PBlk n)) → ℕ),
    IsArithVar P (e + 1 + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) (e + 1) δ
      (map (Rat.castHom ℂ) f) →
    IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
    (∀ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u), IsHorizontal W →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) e (d W)
        (map (Rat.castHom ℂ) (g W))) →
      IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ =
        (∑ᶠ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u),
            (multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
              (if IsHorizontal W then IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g W) (d W)
                else (geoNum (e + 1) W (fun _ _ => 1) : ℝ) * Real.log (charOf W))) -
          arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
            (fun _ : Fin (e + 1) => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS))
def ChowHeightRecQ.Statement : Prop :=
  ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S), ChowHeightRecQ.Holds n S hS
def ChowFormExistsRat.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n))), IsArithVar P (e + 1) →
    ∃ (δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
        (map (Rat.castHom ℂ) f)
def ChowHeightRecursionRat.Statement : Prop :=
  ∀ (n e δ : ℕ) (H : ArchData ℚ n) (I : Ideal (MvPolynomial (Fin n) ℚ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ) (u : Fin n → 𝓞 ℚ),
    IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f →
    linForm (fun j => (u j : ℚ)) ∉ I →
      chowHt H (e + 1) δ f =
        chowHt H e δ (specFirst f fun j => (u j : ℚ)) +
          (1 / Module.finrank ℚ ℚ : ℝ) *
            (vertTerm I (e + 1) u -
              ∑ σ : ℚ →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
                (fsLog (H.normAt σ) fun j => σ (u j)))
def RecQOfRecursion.Statement : Prop :=
  ChowHeightRecursionRat.Statement →
    ∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S),
      (∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) →
        ChowHeightRecQ.Holds n S hS
def RecursionOfRecQ.Statement : Prop :=
  (∀ (n : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S),
      (∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) →
        ChowHeightRecQ.Holds n S hS) →
    ChowHeightRecursionRat.Statement
namespace ChowHeightRecQ
end ChowHeightRecQ
end GroundTheory.Heights₂.Heights


