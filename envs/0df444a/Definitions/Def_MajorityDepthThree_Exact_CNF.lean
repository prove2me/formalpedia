-- Prove2me | Definitions.Def_MajorityDepthThree_Exact_CNF
-- name    : MajorityDepthThree_Exact_CNF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:05.874423+00:00
-- url     : https://prove2.me/theorems/5be9c704-634b-4359-bfed-fb5408d08d6b
-- title:
--   Finite ambient signed CNFs, transversals and extremal counts
-- statement:
--   Let $V$ be a finite set of Boolean variables. An assignment is a subset $S\subseteq V$, its members being set to one. A clause is a pair $(P,N)$ of disjoint subsets of $V$, with width $|P|+|N|$. Its satisfaction condition is
--
--   $$S\cap P\ne\varnothing\quad\text{or}\quad N\setminus S\ne\varnothing.$$
--
--   A CNF $F$ is a finite set of clauses. Validity requires each clause's positive and negative variables to lie in $V$ and be disjoint. Width $k$ means at most $k$ literals per clause; uniformity means exactly $k$. Monotonicity means every negative set is empty. Write $T(F)$ for all satisfying subsets of $V$, $T_t(F)$ for those of size $t$, and $\theta_t(F)=|T_t(F)|$. The threshold condition requires $|S|\ge t$ for every $S\in T(F)$; it does not require the converse. The family $M(F)$ consists of inclusion-minimal satisfying sets. The transversal number $\tau(F)$ is the least satisfying size, represented by an option with no value for an unsatisfiable formula.
--
--   The positive part $H$ contains all and only the all-positive clauses of $F$; the remaining part is $G$. Both retain the same ambient $V$. For $R>0$, define $Z(F,R)=\sum_{U\in M(F)}R^{|U|}$. The clique $K_V^{(k)}$ consists of all positive $k$-subsets of $V$. The extremal count $\Theta(|V|,t,k)$ is the finite maximum of $\theta_t$ over all valid $t$-threshold width-at-most-$k$ CNFs on $V$, including signed formulas. Extremality means attaining that maximum.
--
--   These objects provide the common syntax and counting interface. Empty clauses are false, empty conjunctions are true, and isolated variables remain in $V$. The maximum over an empty candidate family is defined to be zero; every theorem using a positive denominator has nonempty candidates and establishes positivity.
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), pp.6–8, Notation 2.1, Definitions 2.2–2.6 and 3.1; pp.10–11, Section 4

import Mathlib

set_option autoImplicit false

namespace MajorityDepthThree.Exact

abbrev Clause (α : Type) := Finset α × Finset α
abbrev CNF (α : Type) := Finset (Clause α)

variable {α : Type} [DecidableEq α]

def Clause.width (c : Clause α) : ℕ := c.1.card + c.2.card

def Clause.Holds (c : Clause α) (S : Finset α) : Prop :=
  (S ∩ c.1).Nonempty ∨ (c.2 \ S).Nonempty

def ValidCNF (V : Finset α) (F : CNF α) : Prop :=
  ∀ c ∈ F, c.1 ⊆ V ∧ c.2 ⊆ V ∧ Disjoint c.1 c.2

def Width (k : ℕ) (F : CNF α) : Prop := ∀ c ∈ F, c.width ≤ k

def Uniform (k : ℕ) (F : CNF α) : Prop := ∀ c ∈ F, c.width = k

def Monotone (F : CNF α) : Prop := ∀ c ∈ F, c.2 = ∅

noncomputable def transversals (V : Finset α) (F : CNF α) : Finset (Finset α) := by
  classical
  exact V.powerset.filter (fun S => ∀ c ∈ F, c.Holds S)

noncomputable def layer (V : Finset α) (F : CNF α) (t : ℕ) : Finset (Finset α) := by
  classical
  exact (transversals V F).filter (fun S => S.card = t)

noncomputable def theta (V : Finset α) (F : CNF α) (t : ℕ) : ℕ := (layer V F t).card

def Threshold (V : Finset α) (F : CNF α) (t : ℕ) : Prop :=
  ∀ S ∈ transversals V F, t ≤ S.card

noncomputable def minimalSets (V : Finset α) (F : CNF α) : Finset (Finset α) := by
  classical
  exact (transversals V F).filter (fun S => ∀ U ∈ transversals V F, U ⊆ S → U = S)

noncomputable def tau (V : Finset α) (F : CNF α) : Option ℕ := by
  classical
  exact if h : (transversals V F).Nonempty then
    some ((transversals V F).inf' h Finset.card) else none

noncomputable def positivePart (F : CNF α) : CNF α := by
  classical
  exact F.filter (fun c => c.2 = ∅)

noncomputable def remainingPart (F : CNF α) : CNF α := by
  classical
  exact F.filter (fun c => c.2 ≠ ∅)

noncomputable def partitionSum (V : Finset α) (F : CNF α) (r : ℝ) : ℝ :=
  ∑ U ∈ minimalSets V F, r ^ U.card

noncomputable def clique (V : Finset α) (k : ℕ) : CNF α := by
  classical
  exact (V.powerset.filter (fun S => S.card = k)).image (fun S => (S, ∅))

noncomputable def twoClauseCount (F : CNF α) : ℕ := by
  classical
  exact (F.filter (fun c => c.width = 2)).card

variable [Fintype α]

noncomputable def candidates (V : Finset α) (t k : ℕ) : Finset (CNF α) := by
  classical
  exact Finset.univ.filter (fun F => ValidCNF V F ∧ Width k F ∧ Threshold V F t)

noncomputable def thetaMax (V : Finset α) (t k : ℕ) : ℕ :=
  (candidates V t k).sup (fun F => theta V F t)

def Extremal (V : Finset α) (F : CNF α) (t k : ℕ) : Prop :=
  ValidCNF V F ∧ Width k F ∧ Threshold V F t ∧ theta V F t = thetaMax V t k

end MajorityDepthThree.Exact


