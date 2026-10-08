-- Prove2me | Definitions.Def_SchedComplexity_OneMachine_Knapsack
-- name    : SchedComplexity_OneMachine_Knapsack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T22:03:56.589069+00:00
-- url     : https://prove2.me/theorems/506de359-e136-4c9c-9ccc-e36c13ef27ce
-- title:
--   KNAPSACK over positive integers (Theorem 2(b)) and its binary language
-- statement:
--   KNAPSACK, as stated in Theorem 2(b) of Brucker, Lenstra and Rinnooy Kan: *given positive integers $a_1,\dots,a_t,b$, does there exist a subset $S\subset T=\{1,\dots,t\}$ such that*
--
--   $$\sum_{j\in S} a_j = b\,?$$
--
--   (Here $S\subset T$ means an arbitrary subset, possibly empty or all of $T$; the problem is what is now usually called SUBSET SUM.)
--
--   The predicate $\mathrm{KnapsackYes}(a,b)$ says that the list $a=(a_1,\dots,a_t)$ and the target $b$ form a yes-instance. The language $\mathsf{KNAPSACK}$ consists of the binary codes $\langle b\rangle\langle a_1\rangle\cdots\langle a_t\rangle$ of the yes-instances in which **every** number $a_1,\dots,a_t,b$ is positive; each $\langle k\rangle$ is the binary expansion of $k$ (least significant bit first) followed by a separator symbol, so the length of a code is the usual binary size of the instance.
--
--   KNAPSACK is the source problem of every reduction in Theorem 4 of the paper; this language is the left-hand side of the mission's goal.
--
--   **Formalization Note** Indices are 0-based: $T$ is `Fin a.length`. The alphabet `BSym` and the codes `encNat`/`encNats` come from the published definition `ProjSchedTW.Complexity.Encoding` (Neumann, Schwindt and Zimmermann). That file's `subsetSumLang` is not reused because it admits zero sizes and a zero target, whereas the paper's KNAPSACK is over positive integers.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 14, Theorem 2(b)

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace SchedComplexity.OneMachine

open CookPvsNP ProjSchedTW.Complexity

/-- A KNAPSACK instance (Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 14, Theorem 2(b)):
the list `a = [a_1, …, a_t]` (so `T = {1, …, t}` is `Fin a.length`, 0-based) and the target `b`.
It is a yes-instance iff some subset `S ⊆ T` has `∑_{j ∈ S} a_j = b`. Positivity of the data is
not part of this predicate; it is imposed by `knapsackLang`. -/
def KnapsackYes (a : List ℕ) (b : ℕ) : Prop :=
  ∃ S : Finset (Fin a.length), ∑ j ∈ S, a.get j = b

/-- The KNAPSACK language (Theorem 2(b), p. 14): the binary codes `b a_1 … a_t` (each number in
binary by `encNat`, one after the other) of the yes-instances whose data `a_1, …, a_t, b` are all
**positive** integers, as the paper's "Given positive integers a_1, …, a_t, b" requires. -/
def knapsackLang : Lang BSym :=
  { x | ∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ KnapsackYes a b ∧
      x = encNats (b :: a) }

end SchedComplexity.OneMachine


