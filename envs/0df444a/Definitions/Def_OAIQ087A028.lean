-- Prove2me | Definitions.Def_OAIQ087A028
-- name    : OAIQ087A028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:40:50.963206+00:00
-- url     : https://prove2.me/theorems/ceb15111-752e-4f53-bd17-8a92f2a87b91
-- title:
--   Definitions bundle OAIQ087A028 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 definitions. The definitions and types are `OAI.OptimalMaxCut.LongCode.InstanceAdapter.bits`, `OAI.OptimalMaxCut.LongCode.InstanceAdapter.cubeEquiv`, `OAI.OptimalMaxCut.LongCode.InstanceAdapter.degree`, `OAI.OptimalMaxCut.LongCode.InstanceAdapter.merge`, `OAI.OptimalMaxCut.LongCode.InstanceAdapter.ofInstance`, `OAI.OptimalMaxCut.LongCode.InstanceAdapter.vertexEquiv`, `OAI.OptimalMaxCut.LongCode.InstanceAdapter.words`, `OAI.OptimalMaxCut.LongCode.oddPart`, `OAI.OptimalMaxCut.MISProof.smoothedTruncCoeff`, `OAI.OptimalMaxCut.RawGrid.atom`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`MaxCut_Analysis_CubeEquiv`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Analysis/CubeEquiv.lean), [`MaxCut_Estimates_Clip`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Clip.lean), [`MaxCut_Estimates_Dictator`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/Dictator.lean), [`MaxCut_Estimates_ListSum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Estimates/ListSum.lean).
--
--   **Imports.** It imports the bundles `OAIQ087A016`, `OAIQ087A019` and `OAIQ087A020` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ087A032`; the proof of `OAI.OptimalMaxCut.LongCode.Game.exists_weighted_soundness`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A016
import Definitions.Def_OAIQ087A019
import Definitions.Def_OAIQ087A020

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Clip
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.MISProof
open scoped BigOperators
open Finset Set MaxCutGames.Foundations.Hastad Analytic BooleanFourthMoment GaussianBellman

noncomputable def smoothedTruncCoeff {n : ℕ} (K : ℕ) (u : ℝ) (h : BitCube n → ℝ)
    (s : BitCube n) : ℝ := if degree s ≤ K then u ^ degree s * coefficient h s else 0

end OptimalMaxCut.MISProof

namespace OptimalMaxCut.LongCode

open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad OptimalMaxCut.Analytic
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

noncomputable def oddPart {n : ℕ} (f : Cube (Fin n) → ℝ) (x : Cube (Fin n)) : ℝ :=
  (f x - f (antipode x)) / 2

end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Dictator
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace OptimalMaxCut.LongCode.InstanceAdapter
open scoped BigOperators
open Finset MaxCutGames.Foundations.Target
open MaxCutGames.Explicit.MachineOutputContract
attribute [local instance] Classical.propDecidable

variable {q : ℕ}
noncomputable def ofInstance (g : Instance q) :
    Game (Fin g.vertices) (Fin g.vertices) (Fin g.constraints.length) q := by
  letI : Nonempty (Fin g.constraints.length) := Fin.pos_iff_nonempty.mp g.constraintCount_positive
  exact {
    rightLaw := Law.fiberMarginal (fun e : Fin g.constraints.length => g.constraints[e].target)
    edgeLaw := Law.fiberConditional (fun e : Fin g.constraints.length => g.constraints[e].target)
    source e := g.constraints[e].source
    permutation e := permutationEquiv g.constraints[e].permutation }

noncomputable def merge (g : Instance q) (b : SimpleBipartite g)
    (lx ly : Fin g.vertices → Fin q) : Fin g.vertices → Fin q :=
  fun v => if b.side v then ly v else lx v

end OptimalMaxCut.LongCode.InstanceAdapter

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Analysis_CubeEquiv
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode.InstanceAdapter
open scoped BigOperators
open MaxCutGames.Foundations.Target MaxCutGames.Foundations.Hastad

/-- Fixed binary radix indexing, rather than a chosen `Fintype.equivFin`. -/
def cubeEquiv (q : ℕ) : Cube (Fin q) ≃ Fin (2 ^ q) :=
  (Equiv.arrowCongr (Equiv.refl (Fin q)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Row-major indexing before the explicit finite-field blowup. -/
def vertexEquiv (n q : ℕ) : (Fin n × Cube (Fin q)) ≃ Fin (n * 2 ^ q) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) (cubeEquiv q)).trans finProdFinEquiv

end OptimalMaxCut.LongCode.InstanceAdapter

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_ListSum
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted
attribute [local instance] Classical.propDecidable

namespace InstanceAdapter
variable {q : ℕ}

def degree (g : MaxCutGames.Foundations.Target.Instance q) (y : Fin g.vertices) : ℕ :=
  ∑ e : Fin g.constraints.length, if g.constraints[e].target = y then 1 else 0

end InstanceAdapter
end OptimalMaxCut.LongCode
namespace OptimalMaxCut.LongCode.InstanceAdapter
open scoped BigOperators
open Finset MaxCutGames.Foundations.Target MaxCutGames.Foundations.Hastad
open CounterMachine.Expr
attribute [local instance] Classical.propDecidable

def words {q : ℕ} (g : Instance q) : List ℕ :=
  [g.vertices,q,g.constraints.length] ++ g.constraints.flatMap rowWords
def bits {q : ℕ} (g : Instance q) : List Bool := unaryWords (words g)

end OptimalMaxCut.LongCode.InstanceAdapter

namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open CounterMachine.Expr LongCode
attribute [local instance] Classical.propDecidable

def atom {q : ℕ} (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (s : List Bool) (y e f : ℕ) (x z : Cube (Fin q)) : ℕ :=
  if row q s e 1=y ∧ row q s f 1=y then
    gridSize q K s*degree q s y*((jointLaw t ht q).weight (x,z)).num.toNat /
     (((jointLaw t ht q).weight (x,z)).den*edges s*(degree q s y)^2)
  else 0

end OptimalMaxCut.RawGrid

end

end OAI
end


