-- Prove2me | Definitions.Def_RubinsteinBargaining_PEP_Core
-- name    : RubinsteinBargaining_PEP_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:58:44.29979+00:00
-- url     : https://prove2.me/theorems/44ff5711-3348-4ee7-8c06-b72d30ec637e
-- title:
--   Partitions, outcomes, preferences, and axioms (A-1)–(A-5)
-- statement:
--   A partition is a number $s\in[0,1]$ denoting player 1's share of a unit pie; player 2 receives $1-s$. An outcome is either an agreement $(s,t)$ in a natural-number period $t$, including $t=0$ for comparisons, or perpetual disagreement $(0,\infty)$. Each player has a complete, reflexive, transitive preference relation on these outcomes. Strict preference and indifference are derived from that relation.
--
--   The five named predicates encode the paper's assumptions: a strictly larger own share at the same date is better; a positive own share is strictly better sooner and better than perpetual disagreement; adjacent-period comparisons are stationary; upper contour comparisons are sequentially closed in the left share argument; and the own-share compensation required for a one-period delay is nondecreasing in the initial own share. The basic and full bundles make the relevant assumptions explicit in each result.
--
--   **Formalization Note** The disagreement outcome is a distinct constructor, so it cannot be confused with an agreement giving player 1 zero. Axiom (A-4) varies only the left partition argument.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), pp. 100–101, Section 2 and (A-1)–(A-5), https://doi.org/10.2307/1912531

import Mathlib

namespace RubinsteinBargaining.PEP

/-- A partition records player one's share of the unit pie. -/
def S : Set ℝ := Set.Icc 0 1

abbrev Partition := {s : ℝ // s ∈ S}

inductive Player where
  | one | two
  deriving DecidableEq

def other : Player → Player
  | .one => .two
  | .two => .one

def share : Player → Partition → ℝ
  | .one, s => s.val
  | .two, s => 1 - s.val

/-- `none` is perpetual disagreement; `some (s,t)` is agreement in period `t`. -/
abbrev Outcome := Option (Partition × ℕ)

def agreement (s : Partition) (t : ℕ) : Outcome := some (s, t)

abbrev Relation := Outcome → Outcome → Prop

/-- A complete, reflexive, transitive preference relation on outcomes. -/
structure Preference where
  weak : Relation
  complete : ∀ a b, weak a b ∨ weak b a
  reflexive : ∀ a, weak a a
  transitive : ∀ a b c, weak a b → weak b c → weak a c

structure Preferences where
  one : Preference
  two : Preference

def preference (p : Preferences) : Player → Preference
  | .one => p.one
  | .two => p.two

def weak (p : Preferences) (i : Player) (a b : Outcome) : Prop :=
  (preference p i).weak a b

def strict (p : Preferences) (i : Player) (a b : Outcome) : Prop :=
  weak p i a b ∧ ¬ weak p i b a

def indifferent (p : Preferences) (i : Player) (a b : Outcome) : Prop :=
  weak p i a b ∧ weak p i b a

/-- A-1: a larger own share is strictly preferred at the same period. -/
def A1 (p : Preferences) : Prop :=
  ∀ (i : Player) (r s : Partition) (t : ℕ),
    share i s < share i r → strict p i (agreement r t) (agreement s t)

/-- A-2: a positive share is strictly preferred sooner and to perpetual disagreement. -/
def A2 (p : Preferences) : Prop :=
  ∀ (i : Player) (s : Partition) (t₁ t₂ : ℕ),
    0 < share i s → t₁ < t₂ →
      strict p i (agreement s t₁) (agreement s t₂) ∧
      strict p i (agreement s t₂) none

/-- A-3: comparison of adjacent periods is independent of the period number. -/
def A3 (p : Preferences) : Prop :=
  ∀ (i : Player) (r s : Partition) (t₁ t₂ : ℕ),
    (weak p i (agreement r t₁) (agreement s (t₁ + 1)) ↔
     weak p i (agreement r t₂) (agreement s (t₂ + 1)))

/-- A-4: sequential closedness in the left partition argument. -/
def A4 (p : Preferences) : Prop :=
  ∀ (i : Player) (r : ℕ → Partition) (r₀ s : Partition) (t₁ t₂ : ℕ),
    Filter.Tendsto (fun n => (r n : ℝ)) Filter.atTop (nhds (r₀ : ℝ)) →
    ((∀ n, weak p i (agreement (r n) t₁) (agreement s t₂)) →
      weak p i (agreement r₀ t₁) (agreement s t₂)) ∧
    ((∀ n, weak p i (agreement (r n) t₁) none) →
      weak p i (agreement r₀ t₁) none)

/-- A-5: the one-period compensation in own share is nondecreasing in initial own share. -/
def A5 (p : Preferences) : Prop :=
  ∀ (i : Player) (r s r' s' : Partition),
    indifferent p i (agreement r 1) (agreement s 0) →
    indifferent p i (agreement r' 1) (agreement s' 0) →
    share i s < share i s' →
    share i r - share i s ≤ share i r' - share i s'

def BasicAxioms (p : Preferences) : Prop := A1 p ∧ A2 p

def FullAxioms (p : Preferences) : Prop :=
  A1 p ∧ A2 p ∧ A3 p ∧ A4 p ∧ A5 p

end RubinsteinBargaining.PEP


