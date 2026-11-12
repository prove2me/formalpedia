-- Prove2me | Definitions.Def_RobotMP_W1Hard_Bimonotone
-- name    : RobotMP_W1Hard_Bimonotone
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:41:45.638742+00:00
-- url     : https://prove2.me/theorems/fa30d707-8793-4d62-ab68-49dd71661ecb
-- title:
--   Bimonotone subsets of a product of discrete intervals, and grid connectivity (§9.1)
-- statement:
--   Let $I_1, I_2 \subseteq \mathbb Z$ be discrete intervals and $S \subseteq I_1 \times I_2$. Define
--   $$S_1 = \{(x,y) \in I_1 \times I_2 : \exists (x', y') \in S,\ x' \ge x,\ y' \ge y\},\qquad S_2 = \{(x,y) \in I_1 \times I_2 : \exists (x', y') \in S,\ x' \ge x,\ y' \le y\},$$
--   $$S_3 = \{(x,y) \in I_1 \times I_2 : \exists (x', y') \in S,\ x' \le x,\ y' \ge y\},\qquad S_4 = \{(x,y) \in I_1 \times I_2 : \exists (x', y') \in S,\ x' \le x,\ y' \le y\}.$$
--   $S$ is **bimonotone** if $S = S_1 \cap S_2 \cap S_3 \cap S_4$.
--
--   A set $S \subseteq \mathbb Z^2$ is **connected** if any point of $S$ can be reached from any other point of $S$ by a finite sequence of moves, each incrementing or decrementing a single coordinate by one, that stays in $S$. The empty set is connected.
--
--   Bimonotone sets are the constraint relations allowed between two data variables in controlled monotone satisfiability.
--
--   **Formalization Note.** The page prints the condition as $S = S_1 \cap S_2 \cap S_2 \cap S_4$; the intended $S_3$ is used (it is the version repeated on p. 57).
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), pp. 41–42, §9.1

import Mathlib

set_option autoImplicit false

namespace RobotMP.W1Hard

open Set

/-- `S₁ = {(x, y) ∈ I₁ × I₂ : ∃ (x', y') ∈ S, x' ≥ x, y' ≥ y}` (§9.1, p. 41). -/
def bmHull1 (I₁ I₂ : Set ℤ) (S : Set (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {p | p.1 ∈ I₁ ∧ p.2 ∈ I₂ ∧ ∃ q ∈ S, p.1 ≤ q.1 ∧ p.2 ≤ q.2}

/-- `S₂ = {(x, y) ∈ I₁ × I₂ : ∃ (x', y') ∈ S, x' ≥ x, y' ≤ y}`. -/
def bmHull2 (I₁ I₂ : Set ℤ) (S : Set (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {p | p.1 ∈ I₁ ∧ p.2 ∈ I₂ ∧ ∃ q ∈ S, p.1 ≤ q.1 ∧ q.2 ≤ p.2}

/-- `S₃ = {(x, y) ∈ I₁ × I₂ : ∃ (x', y') ∈ S, x' ≤ x, y' ≥ y}`. -/
def bmHull3 (I₁ I₂ : Set ℤ) (S : Set (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {p | p.1 ∈ I₁ ∧ p.2 ∈ I₂ ∧ ∃ q ∈ S, q.1 ≤ p.1 ∧ p.2 ≤ q.2}

/-- `S₄ = {(x, y) ∈ I₁ × I₂ : ∃ (x', y') ∈ S, x' ≤ x, y' ≤ y}`. -/
def bmHull4 (I₁ I₂ : Set ℤ) (S : Set (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {p | p.1 ∈ I₁ ∧ p.2 ∈ I₂ ∧ ∃ q ∈ S, q.1 ≤ p.1 ∧ q.2 ≤ p.2}

/-- `S ⊆ I₁ × I₂` is *bimonotone* (with respect to the discrete intervals `I₁`, `I₂`):
`S = S₁ ∩ S₂ ∩ S₃ ∩ S₄`. -/
def IsBimonotone (I₁ I₂ : Set ℤ) (S : Set (ℤ × ℤ)) : Prop :=
  S = bmHull1 I₁ I₂ S ∩ bmHull2 I₁ I₂ S ∩ bmHull3 I₁ I₂ S ∩ bmHull4 I₁ I₂ S

/-- `q` arises from `p` by incrementing or decrementing a single coordinate by one. -/
def IsUnitStep (p q : ℤ × ℤ) : Prop :=
  (|p.1 - q.1| = 1 ∧ p.2 = q.2) ∨ (p.1 = q.1 ∧ |p.2 - q.2| = 1)

/-- `S ⊆ ℤ²` is *connected*: any point of `S` can be reached from any other point of `S` by a
finite sequence of unit steps (each incrementing or decrementing one coordinate) that stays in
`S`. The empty set is connected. -/
def IsGridConnected (S : Set (ℤ × ℤ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ IsUnitStep a b) p q

end RobotMP.W1Hard


