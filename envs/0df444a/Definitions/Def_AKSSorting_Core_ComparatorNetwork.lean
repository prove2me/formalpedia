-- Prove2me | Definitions.Def_AKSSorting_Core_ComparatorNetwork
-- name    : AKSSorting_Core_ComparatorNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:38:15.204061+00:00
-- url     : https://prove2.me/theorems/a73d12c6-4219-43fb-b038-8b4cbae43fd7
-- title:
--   Comparator networks on n registers: layers of disjoint compare-exchange steps
-- statement:
--   Fix $n$ registers $R_1,\dots,R_n$. A **comparator network** of depth $d$ is a sequence of $d$ **parallel steps**, fixed before the input is seen. Each parallel step is a set of comparators $(i,j)$ with $i\neq j$, and no register occurs in two comparators of the same step; hence a step contains at most $n/2$ comparators. Running the network on an input $x=(x_1,\dots,x_n)$ from a linearly ordered set applies the parallel steps in order, each comparator $(i,j)$ acting as the compare-exchange $\operatorname{ce}_{i,j}$ (minimum to $R_i$, maximum to $R_j$).
--
--   For a network $N$:
--
--   1. its **depth** is the number of parallel steps;
--   2. its **size** is the total number of comparators;
--   3. $N$ **sorts** if for every linearly ordered set $L$ and every input $x\in L^n$ the output $N(x)$ satisfies
--   $$N(x)_1\le N(x)_2\le\cdots\le N(x)_n .$$
--
--   This is the model of Section 1 of Ajtai, Komlós and Szemerédi: "by a parallel step we mean a set of at most $n/2$ disjoint elementary steps", and the goal is that "the least element of $L$ be in $R_1$ the next one in $R_2$ etc. the greatest in $R_n$".
--
--   **Formalization Note** Registers are `Fin n`. A network is a `List` of layers, each a `List (Fin n × Fin n)`; disjointness is stated as "the list of all endpoints of the layer has no duplicates", which also forbids repeating a comparator inside a layer. A layer is evaluated by folding its comparators in list order; by disjointness the order is irrelevant. Comparators may point in either direction ($i<j$ or $i>j$). The paper also allows the other elementary rules (unconditional exchange, reversed comparison); the network model here only has compare-exchange, which is what the paper's construction uses. `Sorts` quantifies over every linearly ordered type and every input, not only permutations; for comparator networks the two notions coincide.
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), p. 1, Abstract and Section 1

import Mathlib
import Definitions.Def_AKSSorting_Core_compareExchange

namespace AKSSorting.Core

/-- A comparator network on the `n` registers `Fin n` (Ajtai–Komlós–Szemerédi 1983, §1 p. 1):
a finite sequence of parallel steps (`layers`), fixed in advance. Each parallel step is a list of
comparators `(i, j)` with `i ≠ j`, and no register occurs twice in one parallel step (the list of
all endpoints of the step has no duplicates), so a step has at most `n / 2` comparators. -/
structure ComparatorNetwork (n : ℕ) where
  layers : List (List (Fin n × Fin n))
  ne : ∀ L ∈ layers, ∀ p ∈ L, p.1 ≠ p.2
  disjoint : ∀ L ∈ layers, (L.flatMap fun p => [p.1, p.2]).Nodup

namespace ComparatorNetwork

variable {n : ℕ}

/-- Apply one parallel step: its comparators, in list order (by disjointness the order does
not matter). The comparator `(i, j)` puts the minimum into `i` and the maximum into `j`. -/
def evalLayer {α : Type} [LinearOrder α] (L : List (Fin n × Fin n)) (x : Fin n → α) :
    Fin n → α :=
  L.foldl (fun y p => compareExchange p.1 p.2 y) x

/-- Run the whole network on the input `x`, parallel step by parallel step. -/
def eval (N : ComparatorNetwork n) {α : Type} [LinearOrder α] (x : Fin n → α) : Fin n → α :=
  N.layers.foldl (fun y L => evalLayer L y) x

/-- Depth: the number of parallel steps. -/
def depth (N : ComparatorNetwork n) : ℕ := N.layers.length

/-- Size: the total number of comparators (elementary steps). -/
def size (N : ComparatorNetwork n) : ℕ := (N.layers.map List.length).sum

/-- The network sorts: for every linearly ordered type and every input, the output is
nondecreasing along the registers `R₁, …, Rₙ`. -/
def Sorts (N : ComparatorNetwork n) : Prop :=
  ∀ (α : Type) [LinearOrder α] (x : Fin n → α), Monotone (N.eval x)

end ComparatorNetwork

end AKSSorting.Core


