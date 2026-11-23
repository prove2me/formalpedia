-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:17.244091+00:00
-- url     : https://prove2.me/theorems/cd5a3f17-fb92-4e15-85be-f5700eabfc41
-- title:
--   Recursion With Densities
-- statement:
--   Definitions and structural lemmas for Recursion With Densities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_X0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
section gen
variable {α : Type}
noncomputable def restr (X : Finset α) (k : α → α → ℂ) : α → α → ℂ :=
  fun x y => if x ∈ X ∧ y ∈ X then k x y else 0
variable {E : Type} [AddCommGroup E]
noncomputable def G (L : AddSubgroup E) (S : Finset E) (Th : E → α → α → ℂ) (c : E ⧸ L) : α → α → ℂ :=
  if hc : ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c then Th hc.choose else fun _ _ => 0
end gen
section ta
variable {E : Type} [Field E] [DecidableEq E]
end ta
section main
variable {E : Type} [Field E] [DecidableEq E]
noncomputable def D' (D : TA.Data E) (Sg : ℕ → ℕ → Finset E)
    (Th : ℕ → ℕ → E → TA.Pt E → TA.Pt E → ℂ) : TA.Data E :=
  { D with
    K := fun i => restr (PT Sg i) (D.K i)
    Th := fun i s t => restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s)) }
end main
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism.FourierDecayAlt.P.BudgetLiftBounds Formalism.FourierDecayAlt.TC
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
def good (L : AddSubgroup E) (S : Finset E) (c : E ⧸ L) : Prop := ∃ t₁ ∈ S, (t₁ : E ⧸ L) = c
noncomputable def sel (L : AddSubgroup E) (S : Finset E) (c : E ⧸ L) : E :=
  if h : good L S c then h.choose else 0
noncomputable def KrR (D : Data E W) (T : Tower E) : ℕ → Pt E → Pt E → ℂ :=
  fun i p q => if p ∈ T.X i ∧ q ∈ T.X i then D.Kr i p q else 0
noncomputable def ThR (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) :
    ℕ → ℕ → E → Pt E → Pt E → ℂ :=
  fun i s t h h' =>
    if (1 ≤ s ∧ s ≤ i ∧ i ≤ D.r + 1) ∧
        good (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s) then
      (if h ∈ T.X (i - s) ∧ h' ∈ T.X (i - s) then
        Th i s (sel (D.La (i - s + 1) s) (T.Sg (i - s + 1) s) (t : E ⧸ D.La (i - s + 1) s)) h h'
      else 0)
    else 0
noncomputable def Dp (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) : Data E W :=
  { D with
    Kr := KrR D T
    K0 := by simp [KrR, Formalism.FourierDecayAlt.P.OneLevelCoefficients.X0, D.K0]
    Th := ThR D T Th }
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.P.OneLevelCoefficients Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
namespace Formalism.FourierDecayAlt.P
open RecursionWithDensities
end Formalism.FourierDecayAlt.P


