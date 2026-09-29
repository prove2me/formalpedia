-- Prove2me | Definitions.Def_diophantine_descent
-- name    : diophantine_descent
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-07T02:28:30.293712+00:00
-- url     : https://prove2.me/theorems/90e874be-2771-40b3-b504-ab5a84bcfedc
-- title:
--   Diophantine triples and finite descent degree
-- statement:
--   An ordered Diophantine triple consists of positive integers $a<b<c$ for which $ab+1$, $ac+1$, and $bc+1$ are squares. It is Euler when $c=a+b+2r$, where $r^2=ab+1$.
--
--   For a non-Euler triple, one descent step replaces the largest entry by
--   $$m=a+b+c+2abc-2rst,$$
--   where $r^2=ab+1$, $s^2=ac+1$, and $t^2=bc+1$, and sorts the three entries increasingly. The step requires $0<m<c$ and that its output is a Diophantine triple. Degree $n$ means a chain of exactly $n$ such steps ending at an Euler triple, with every earlier triple non-Euler.
--
--   These predicates express the classification used in the final proof. Quintuple means five distinct positive integers whose pairwise products plus one are squares; Ordered requires the five entries to increase.
--
--   **Formalization Note** Degree is an inductive relation, so its definition assumes neither termination nor uniqueness. The equation defining $m$ is written without natural-number subtraction. List permutation records the reordering after each step.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 1 (Euler triples); Sections 3–4 (d_minus, partial operator, and degree definition after Proposition 3).

import Init
set_option autoImplicit false

namespace DiophantineDescent

/-- Three positive, increasing integers with the Diophantine property. -/
def Triple (a b c : Nat) : Prop :=
  0 < a ∧ a < b ∧ b < c ∧
  (∃ r : Nat, a * b + 1 = r ^ 2) ∧
  (∃ s : Nat, a * c + 1 = s ^ 2) ∧
  (∃ t : Nat, b * c + 1 = t ^ 2)

def Euler (a b c : Nat) : Prop :=
  ∃ r : Nat, a * b + 1 = r ^ 2 ∧ c = a + b + 2 * r

/-- The paper's partial operator, with the output sorted increasingly.
The equation for m avoids truncated subtraction in the formula for d_minus. -/
def Step (a b c x y z : Nat) : Prop :=
  Triple a b c ∧ ¬ Euler a b c ∧ Triple x y z ∧
  ∃ r s t m : Nat,
    a * b + 1 = r ^ 2 ∧ a * c + 1 = s ^ 2 ∧ b * c + 1 = t ^ 2 ∧
    m + 2 * r * s * t = a + b + c + 2 * a * b * c ∧
    0 < m ∧ m < c ∧ [x, y, z].Perm [a, b, m]

/-- Exactly n descent steps before first reaching an Euler triple. -/
inductive HasDegree : Nat → Nat → Nat → Nat → Prop where
  | zero {a b c : Nat} : Triple a b c → Euler a b c → HasDegree a b c 0
  | succ {a b c x y z n : Nat} :
      Step a b c x y z → HasDegree x y z n → HasDegree a b c (n + 1)

/-- A labelled quintuple; this is the predicate in the headline theorem. -/
def Quintuple (f : Fin 5 → Nat) : Prop :=
  (∀ i, 0 < f i) ∧
  (∀ i j, i ≠ j → f i ≠ f j) ∧
  (∀ i j, i ≠ j → ∃ r : Nat, f i * f j + 1 = r ^ 2)

def Ordered (f : Fin 5 → Nat) : Prop :=
  f 0 < f 1 ∧ f 1 < f 2 ∧ f 2 < f 3 ∧ f 3 < f 4

end DiophantineDescent


