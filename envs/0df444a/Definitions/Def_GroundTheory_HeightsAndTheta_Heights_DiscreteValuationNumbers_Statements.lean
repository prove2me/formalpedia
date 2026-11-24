-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:58.003949+00:00
-- url     : https://prove2.me/theorems/ab94a2ae-18f1-48a6-8b7d-a55a7522f12f
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Statements.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u v
abbrev LengthFormulaDimOne.Statement : Prop := ReciprocityTheory.ChartRestriction.G.AI.LocalLengthAdditivity.{u, v}
abbrev LengthFormulaDimTwo.Statement : Prop := ReciprocityTheory.ChartRestriction.G.AI.LocalLengthMultiplicativity.{u}
def ConservationOfNumber.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      ∀ a : Fin d → K → ℤ,
        cycEval (fun W => vNum W a) (divCycle P (C ϖ)) = gNum P a
open Classical in

def CutByEffectiveDivisor.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
      ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
      (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
      ∀ L : Fin d → K → ℤ,
        cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
          cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
              else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s)
def VerticalDivisorsCommute.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b b' : K → ℤ) (f g f' g' : MRing ι O),
        IsVerticalDivisor P ϖ b f g → IsVerticalDivisor P ϖ b' f' g' →
      ∀ L : Fin d → K → ℤ,
        cycEval (fun G => vNum G (Matrix.vecCons b' L)) (ratDiv P f g) =
          cycEval (fun G => vNum G (Matrix.vecCons b L)) (ratDiv P f' g')
section Examples
def dimTwoExampleIdeal : Ideal (Polynomial ℤ_[2]) :=
  RingHom.ker (Polynomial.eval₂RingHom (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) 0)
instance : dimTwoExampleIdeal.IsPrime := RingHom.ker_isPrime _
abbrev DimTwoExample : Type := Localization.AtPrime dimTwoExampleIdeal
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


