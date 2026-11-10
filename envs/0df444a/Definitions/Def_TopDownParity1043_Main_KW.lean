-- Prove2me | Definitions.Def_TopDownParity1043_Main_KW
-- name    : TopDownParity1043_Main_KW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:18:58.088491+00:00
-- url     : https://prove2.me/theorems/3c382639-9ef1-43cd-b923-292fa0c40b57
-- title:
--   §1.1 — KW search problems, parity and circuit wire counts
-- statement:
--   For Boolean words $x,y\in\{0,1\}^V$, a correct Karchmer–Wigderson output is a coordinate where they differ. A protocol solves $\mathrm{KW}(X,Y)$ if every $x\in X,y\in Y$ reaches such an output:
--   $$\forall x\in X\;\forall y\in Y\;\exists i\in V,\quad \operatorname{run}(P,x,y)=i\quad\text{and}\quad x_i\ne y_i.$$
--
--   The predicate $\operatorname{HasProtocol}(X,Y,d,m)$ asserts the existence of an actual correct tree of at most $d$ rounds and per-message cost at most $m$. For a function $f$, Alice receives a zero-input and Bob a one-input. The parity function on $n$ coordinates is one precisely when the number of one coordinates is odd.
--
--   For a circuit $C$ in the referenced AND/OR DAG model, let
--   $$W(C)=\sum_{i<C.\mathrm{size}}|C.\mathrm{inputs}(i)|,\qquad F(C)=\max_{i<C.\mathrm{size}}|C.\mathrm{inputs}(i)|.$$
--
--   The maximum is zero for a circuit without gates. Each literal or constant input occurrence counts as a wire; the output designation does not. These definitions give the communication and circuit interfaces of Lemma 1 and Theorem 3 without building any lower bound into their meaning.
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), §1.1 and Theorem 3 wire convention, p. 2

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Circuit
import Definitions.Def_TopDownParity1043_Main_Protocol

set_option autoImplicit false

namespace TopDownParity1043.Main

open ParityBarrier563.Trilinear

/-- §1.1, p.2: the KW search relation, including an actual coordinate output. -/
def SolvesKW {V : Type} (P : Protocol (V → Bool) (V → Bool) V)
    (X Y : Set (V → Bool)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∃ i : V, P.run x y = some i ∧ x i ≠ y i

/-- At most d rounds, with at most m bits in each message; no alternation requirement. -/
def HasProtocol {V : Type} (X Y : Set (V → Bool)) (d m : ℕ) : Prop :=
  ∃ P : Protocol (V → Bool) (V → Bool) V,
    P.rounds ≤ d ∧ P.CostBounded m ∧ SolvesKW P X Y

/-- KW(f) gives Alice a zero-input and Bob a one-input. -/
def HasKWProtocol {V : Type} (f : BoolFn V) (d m : ℕ) : Prop :=
  HasProtocol {x | f x = false} {y | f y = true} d m

/-- Parity is one exactly when the number of one coordinates is odd. -/
noncomputable def parity (n : ℕ) : BoolFn (Fin n) := fun x =>
  decide (Odd ((Finset.univ.filter fun i => x i = true).card))

/-- Wire occurrences into all gates, including literal and constant inputs. The output
node designation is free. Unused gates still contribute their wires. -/
def wires {V : Type} (C : Circuit V) : ℕ :=
  ∑ i : Fin C.size, (C.inputs i).length

/-- Largest gate fan-in, zero when there are no gates. -/
def maxFanIn {V : Type} (C : Circuit V) : ℕ :=
  Finset.univ.sup fun i : Fin C.size => (C.inputs i).length

end TopDownParity1043.Main


