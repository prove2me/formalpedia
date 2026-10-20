-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
-- name    : OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:36:39.226876+00:00
-- url     : https://prove2.me/theorems/e19d5d75-079a-41c9-8370-dd0596f2b61f
-- title:
--   Profiles and fibre counts of finite words
-- statement:
--   Let $D$ and $H$ be finite sets; a word is a map $f:D\to H$.
--
--   1. **Profile.** $\mathrm{prof}(f)(h)=\#\{i\in D:f(i)=h\}$.
--   2. **Fibre.** The words on $D$ with a prescribed profile $n:H\to\mathbb{N}$.
--   3. **Word count.** $W_t(n)$ is the number of words of length $t$ with profile $n$:
--   $$
--   W_t(n)=\#\{f:\{1,\dots,t\}\to H:\ \mathrm{prof}(f)=n\}.
--   $$
--   4. **Attained profiles.** The profiles of all words of length $t$.
--
--   $W_t(n)$ is the multinomial coefficient, defined here as an actual count. Grouping words by profile gives the multinomial identity without factorial formulas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingWords.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingWords.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TalagrandExpectationThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding

namespace OAI

/-!
# Counting finite words by their color profiles

The coefficient attached to a profile is the actual cardinality of its fiber
among finite words. Regrouping the weighted sum over words proves the finite
multinomial identity without introducing a factorial formula or a counting
hypothesis.
-/

namespace TalagrandThreshold

open scoped BigOperators

/-- The number of positions of each color in a word on a finite domain. -/
def wordProfile {D H : Type*} [Fintype D] [DecidableEq H] (f : D → H) (h : H) : ℕ :=
  (Finset.univ.filter fun i => f i = h).card

/-- All words on a fixed finite domain having the specified profile. -/
def wordFiber (D : Type*) {H : Type*} [Fintype D] [DecidableEq D]
    [Fintype H] [DecidableEq H] (n : H → ℕ) : Finset (D → H) :=
  Finset.univ.filter fun f => wordProfile f = n

/-- The concrete multinomial coefficient, defined as a finite fiber cardinality. -/
def wordCount {H : Type*} [Fintype H] [DecidableEq H] (t : ℕ) (n : H → ℕ) : ℕ :=
  (wordFiber (Fin t) n).card

/-- The finite set of profiles attained by words of length `t`. -/
def wordProfiles (H : Type*) [Fintype H] [DecidableEq H] (t : ℕ) : Finset (H → ℕ) :=
  Finset.univ.image (fun f : Fin t → H => wordProfile f)

variable {H : Type*} [Fintype H] [DecidableEq H]

@[simp] theorem mem_wordFiber (D : Type*) [Fintype D] [DecidableEq D]
    (n : H → ℕ) (f : D → H) : f ∈ wordFiber D n ↔ wordProfile f = n := by
  simp only [wordFiber, Finset.mem_filter, Finset.mem_univ, true_and]

end TalagrandThreshold

end OAI


