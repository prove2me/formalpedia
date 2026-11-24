-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:09.868217+00:00
-- url     : https://prove2.me/theorems/54869032-ed93-4c17-92d4-a829f41d95bd
-- title:
--   Statements Kleiman Scheme
-- statement:
--   Definitions and structural lemmas for Statements Kleiman Scheme, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsKleimanScheme.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AmpleSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
def KleimanScheme.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι))
    (α : K → ℤ) (b a : ℕ),
    IsFieldIntersection I → IsMultiHomogIdeal V → KH.NefOnF I V α → 1 ≤ b → 1 ≤ a →
    KH.AmpleV F V (b • α + fun _ => (a : ℤ))
section Inhabitants
abbrev lineIdx : Unit → Type := fun _ => Fin 2
def doublePointForm : MRingOver (ZMod 2) lineIdx :=
  monomial (Finsupp.single ⟨(), 0⟩ 2 + Finsupp.single ⟨(), 1⟩ 1) 1
end Inhabitants
section Ample
def KleimanSchemeAmple.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι))
    (α : K → ℤ) (b a : ℕ),
    IsFieldIntersection I → IsMultiHomogIdeal V → KH.NefOnF I V α → 1 ≤ b → 1 ≤ a →
    KH.AmpleV F V (b • α + fun _ => (a : ℤ)) ∧
      ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → KH.GeneratedV F V (e + c • (b • α + fun _ => (a : ℤ)))
end Ample
section InhabitantCurve
abbrev planeIdx : Unit → Type := fun _ => Fin 3
def doubledLinesForm : MRingOver (ZMod 2) planeIdx :=
  monomial (Finsupp.single ⟨(), 0⟩ 2 + Finsupp.single ⟨(), 1⟩ 1) 1
def planeLineX0 : Ideal (MRingOver (ZMod 2) planeIdx) := Ideal.span {X ⟨(), 0⟩}
end InhabitantCurve
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


