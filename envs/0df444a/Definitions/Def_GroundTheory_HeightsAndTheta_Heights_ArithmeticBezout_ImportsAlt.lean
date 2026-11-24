-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:46.767057+00:00
-- url     : https://prove2.me/theorems/45bdcea3-b93c-4a63-a95a-120e6805f43f
-- title:
--   Imports Alt
-- statement:
--   Definitions and structural lemmas for Imports Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ImportsAlt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
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
namespace ObjectsChow
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal)
def ComplexChowFormToChowForm.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsArithVar P (e + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ g →
      ∃ c : ℂ, c ≠ 0 ∧ ∃ f : MvPolynomial (Fin (e + 1) × Fin n) ℚ,
        g = C c * map (Rat.castHom ℂ) f ∧ IsChowForm (genericIdeal P) (e + 1) f
def ChowFormToComplexChowForm.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
    IsArithVar P (e + 1) → IsChowForm (genericIdeal P) (e + 1) f → IsMultiHomog δ f →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
        (map (Rat.castHom ℂ) f)
open Classical in

def DivCycleGeneric.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ),
    IsArithVar P (e + 1) → IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
      divCycle (genericIdeal P) (fun j => (u j : ℚ)) =
        ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)).filter IsHorizontal).mapDomain
          genericIdeal
def VertPartEq.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ),
    IsArithVar P (e + 1) → IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
      vertTerm (genericIdeal P) (e + 1) (fun j => ((u j : ℤ) : 𝓞 ℚ)) =
        IndefiniteRowSideFullHecke.ArithBezout.vertPart P e (IndefiniteRowSideFullHecke.ArithBezout.linForm u)
end ObjectsChow
end GroundTheory.Heights₂.Heights


