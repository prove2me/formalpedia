-- Prove2me | Definitions.Def_OAIQWKERK000
-- name    : OAIQWKERK000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T21:28:07.25788+00:00
-- url     : https://prove2.me/theorems/b66c0125-e0cc-449c-aa3d-131c9c317d14
-- title:
--   Cycle and component counts for permutations (OpenAI Kervaire split)
-- statement:
--   Six small definitions from OpenAI's Lean development for *The Kervaire theorem for groups* (OpenAI Math Release, September 24, 2026, result family 256, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. They serve the proof of the standalone statement `OAI.Kervaire.perm_euler_inequality` (the Euler inequality for a pair of permutations), which does not mention them. For a finite type $D$ with decidable equality, all in `OAI.KervaireRibbon`:
--   - `Cycles σ` is the quotient of $D$ by `Equiv.Perm.SameCycle.setoid σ`, and `numCycles σ` its cardinality, the number of cycles of $\sigma$ with fixed points included;
--   - `classes r` is the number of classes of a setoid $r$ on $D$;
--   - `joinPair r x y` is $r$ joined with the relation identifying $x$ and $y$;
--   - for a list $l$ of pairs, `attachEdges r l` joins the pairs of $l$ into $r$ in order, and `edgePerm σ l` multiplies $\sigma$ on the left by the transpositions of $l$ in order.
--
--   The bundle imports only Mathlib. The definitions bundle of the main Kervaire split imports this bundle instead of repeating these declarations.
-- source:
--   OpenAI, The Kervaire theorem for groups, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 256; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kervaire-Theorem-for-Groups-September-24-2026/The-Kervaire-Theorem-for-Groups-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/Kervaire (PermutationCycles.lean, Components.lean) at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_Kervaire.PermutationCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

abbrev Cycles (σ : Equiv.Perm D) := Quotient (SameCycle.setoid σ)
def numCycles (σ : Equiv.Perm D) : ℕ := Fintype.card (Cycles σ)
end
open Equiv Equiv.Perm
open scoped Classical
end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_Kervaire.Components
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

def classes (r : Setoid D) : ℕ := Fintype.card (Quotient r)
def joinPair (r : Setoid D) (x y : D) : Setoid D := r ⊔ SameCycle.setoid (swap x y)

/-- Successively attach the edges, retaining the component equivalence relation. -/
def attachEdges (r : Setoid D) (l : List (D × D)) : Setoid D :=
  l.foldl (fun r p ↦ joinPair r p.1 p.2) r
def edgePerm (σ : Equiv.Perm D) (l : List (D × D)) : Equiv.Perm D :=
  l.foldl (fun σ p ↦ swap p.1 p.2 * σ) σ

end
open Equiv Equiv.Perm
open scoped Classical
end KervaireRibbon

end

end OAI
end


