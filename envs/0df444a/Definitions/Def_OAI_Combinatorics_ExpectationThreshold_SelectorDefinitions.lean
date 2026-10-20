-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
-- name    : OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:34:29.499322+00:00
-- url     : https://prove2.me/theorems/f3a6ead5-a12b-40f9-80f9-f5deb82e7cb7
-- title:
--   Moves, profiles, feasibility and capture for the multiscale selector
-- statement:
--   Let $X$ be a finite set and $\mathcal{F}$ a family of subsets of $X$. A family $\mathcal{G}$ covers $\mathcal{F}$ if every $H\in\mathcal{F}$ contains some $S\in\mathcal{G}$; its cost at density $p$ is $\sum_{S\in\mathcal{G}}p^{|S|}$, and $\mathcal{F}$ is $p$-small if some cover has cost at most $\frac12$. A fractional cover is a function $g$ on subsets of $X$ with values in $[0,1]$ such that $\sum_{S\subseteq H}g(S)\ge1$ for every $H\in\mathcal{F}$; its cost is $\sum_{S\subseteq X}g(S)p^{|S|}$. Fix $s\in\mathbb{N}$. Colors are $0,1,\dots,s$ and a coloring is a map $a:X\to\{0,\dots,s\}$. For $i<s$ the prefix of a coloring $z$ is $P_i(z)=\{x:z(x)\le i\}$, and $d_i=2^{-(i+1)}$. A mass family assigns to every member $H\in\mathcal{F}$ a probability vector $\mu_H$ on $X$ supported in $H$.
--
--   1. **Moves.** $z$ is earlier than $a$ if $z(x)\le a(x)$ for all $x$. The changed set is $\{x:z(x)<a(x)\}$, the crossings at $i$ are $|P_i(z)\setminus P_i(a)|$, the movement is $\sum_x(a(x)-z(x))$, and the moved row $i$ is $\{x:z(x)=i<a(x)\}$.
--   2. **Profiles.** $n_{a,z}(i,h)$ counts points with final color $i$ and original color $h>i$. Its row counts, total size and crossing counts are $\sum_hn(i,h)$, $\sum_i\sum_hn(i,h)$ and $\sum_{j\le i<h}n(j,h)$.
--   3. **Feasibility.** $z$ is feasible for $(a,H)$ if for every $i<s$ some cutoff is admissible for $(\mu_H,P_i(z),\text{crossings}_i,d_i)$. The move is feasible if it is earlier and feasible for some member, and bounded for $H_0$ if moreover its changed set lies in $H_0$.
--   4. **Selection.** $z$ is selected for $a$ if, for some member $H_0$, it is a bounded feasible move of minimum movement among those for $H_0$. The selected changed sets form the selector's cover.
--   5. **Capture.** $a$ is captured if some member $H$ has
--   $$
--   \mu_H(P_i(a))\ge1-d_i\quad\text{for all }i<s,
--   $$
--      and bad otherwise. The mean color of $H$ under $a$ is $\sum_x(a(x)+1)\mu_H(x)$.
--   6. **Groups.** For fixed $z$ and profile $n$, the group consists of the bad $a$ that select $z$ with profile $n$.
--
--   The selector shows that, unless $\mathcal{F}$ is $p$-small, a random coloring is captured with probability at least $\frac9{10}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorDefinitions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorDefinitions.lean by skeleton subtraction
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

namespace OAI

/-!
# Actual moves and profiles for the simultaneous selector

We retain all colorings of minimum total movement for at least one original
family member. This avoids an arbitrary tie-breaking order; each retained
coloring still has the member-specific minimality used in reconstruction.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A probability mass for each actual member of the family. -/
structure MassFamily (F : Family α) where
  weight : ↥F → α → ℝ
  nonneg : ∀ H x, 0 ≤ weight H x
  total : ∀ H, ∑ x, weight H x = 1
  supported : ∀ H x, x ∉ H.val → weight H x = 0

/-- Colors have zero-based indices; the actual color level is one larger. -/
def prefixSet {s : ℕ} (z : Coloring α s) (i : Fin s) : Finset α :=
  Finset.univ.filter fun x => (z x).val ≤ i.val

def dscale {s : ℕ} (i : Fin s) : ℝ := ((2 : ℝ) ^ (i.val + 1))⁻¹

/-- `Earlier a z` means that the move from `a` to `z` only lowers colors. -/
def Earlier {s : ℕ} (a z : Coloring α s) : Prop := ∀ x, z x ≤ a x

def changes {s : ℕ} (a z : Coloring α s) : Finset α :=
  Finset.univ.filter fun x => z x < a x

def crossings {s : ℕ} (a z : Coloring α s) (i : Fin s) : ℕ :=
  (prefixSet z i \ prefixSet a i).card

def movement {s : ℕ} (a z : Coloring α s) : ℕ :=
  ∑ x, ((a x).val - (z x).val)

def movedRow {s : ℕ} (a z : Coloring α s) (i : Fin s) : Finset α :=
  Finset.univ.filter fun x => (z x).val = i.val ∧ (z x).val < (a x).val

/-- The full profile retains both final and original colors. -/
abbrev Profile (s : ℕ) := Fin s → Color s → ℕ

def profile {s : ℕ} (a z : Coloring α s) : Profile s :=
  fun i h => (Finset.univ.filter fun x =>
    (z x).val = i.val ∧ a x = h ∧ i.val < h.val).card

def rowCount {s : ℕ} (n : Profile s) (i : Fin s) : ℕ := ∑ h, n i h

def profileSize {s : ℕ} (n : Profile s) : ℕ := ∑ i, rowCount n i

def profileCrossings {s : ℕ} (n : Profile s) (i : Fin s) : ℕ :=
  ∑ j : Fin s, ∑ h : Color s,
    if j.val ≤ i.val ∧ i.val < h.val then n j h else 0

def FeasibleFor {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a z : Coloring α s) (H : ↥F) : Prop :=
  ∀ i : Fin s, ∃ ε : ℝ,
    Admissible (mu.weight H) (prefixSet z i) (crossings a z i : ℝ) (dscale i) ε

def Feasible {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a z : Coloring α s) : Prop :=
  Earlier a z ∧ ∃ H : ↥F, FeasibleFor mu a z H

def BoundedFeasible {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a : Coloring α s) (H₀ : ↥F) (z : Coloring α s) : Prop :=
  Feasible mu a z ∧ changes a z ⊆ H₀.val

def IsMinimalMove {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a : Coloring α s) (H₀ : ↥F) (z : Coloring α s) : Prop :=
  BoundedFeasible mu a H₀ z ∧
    ∀ w, BoundedFeasible mu a H₀ w → movement a z ≤ movement a w

def Selected {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a z : Coloring α s) : Prop := ∃ H₀ : ↥F, IsMinimalMove mu a H₀ z

def selectedMoves {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a : Coloring α s) : Finset (Coloring α s) := by
  classical
  exact Finset.univ.filter (Selected mu a)

/-- An actual bad original coloring, its selected endpoint, and its full profile. -/
def Captured {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a : Coloring α s) : Prop :=
  ∃ H : ↥F, ∀ i : Fin s,
    1 - dscale i ≤ ∑ x ∈ prefixSet a i, mu.weight H x

def Bad {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a : Coloring α s) : Prop := ¬ Captured mu a

def groupOriginals {F : Family α} (mu : MassFamily F) {s : ℕ}
    (z : Coloring α s) (n : Profile s) : Finset (Coloring α s) := by
  classical
  exact Finset.univ.filter fun a => Bad mu a ∧ Selected mu a z ∧ profile a z = n

def meanColor {F : Family α} (mu : MassFamily F) {s : ℕ}
    (H : ↥F) (a : Coloring α s) : ℝ :=
  ∑ x, ((a x).val + 1 : ℝ) * mu.weight H x

end TalagrandThreshold.Selector

end

end OAI


