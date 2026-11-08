-- Prove2me | Definitions.Def_OneOfManyCC_OneOut
-- name    : OneOfManyCC_OneOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:07.998524+00:00
-- url     : https://prove2.me/theorems/35f094db-074e-4c64-9db9-48c2a4831afe
-- title:
--   Total relations and the 1-out-of-$k$ problem $\mathrm{OneOut}^{\neq}_k(R)$
-- statement:
--   A relation $R\subseteq A\times B\times O$ is **total** if every pair $(x,y)\in A\times B$ has an output $o\in O$ with $(x,y,o)\in R$.
--
--   For $1\le k\le\min\{|A|,|B|\}$, the **1-out-of-$k$ problem** $\mathrm{OneOut}^{\neq}_k(R)$ gives Alice a tuple $X=(x_1,\dots,x_k)\in\mathrm{Inj}_k(A)$ of pairwise distinct elements of $A$, gives Bob a tuple $Y=(y_1,\dots,y_k)\in\mathrm{Inj}_k(B)$, and asks for a pair $(i,o)\in[k]\times O$ with
--
--   $$(x_i,y_i,o)\in R.$$
--
--   The players choose the instance they answer, and the index is the same on both sides. Distinctness is what makes the problem nontrivial: with repeated inputs, $k$ copies of a single input would make it exactly as hard as $R$.
--
--   **Formalization Note** $\mathrm{Inj}_k(A)$ is `Fin k ↪ A` and positions are 0-based. The range of $k$ is a hypothesis of each statement.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3, p.6; §3.2, p.7, Definition 3.4

import Mathlib

namespace OneOfManyCC

/-- **Total relation.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3, p.6:
"A relation R ⊆ A × B × O is total if every pair (x, y) ∈ A × B has an output o ∈ O with
(x, y, o) ∈ R."

**Formalization Note.** A relation is a predicate `R : A → B → O → Prop`. -/
def IsTotal {A B O : Type} (R : A → B → O → Prop) : Prop :=
  ∀ x y, ∃ o, R x y o

/-- **The 1-out-of-k problem** `OneOut≠ₖ(R)`.
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Definition 3.4, p.7:
"For 1 ≤ k ≤ min{|A|, |B|}, the 1-out-of-k problem OneOut≠ₖ(R) gives Alice
X = (x1, . . . , xk) ∈ Injk(A) and Bob Y = (y1, . . . , yk) ∈ Injk(B) and asks for a pair
(i, o) ∈ [k] × O such that (xi, yi, o) ∈ R."

**Formalization Note.** `Inj_k(A)` (§3.2, p.7) is `Fin k ↪ A`: the injective maps `Fin k → A` are
exactly the `k`-tuples of pairwise distinct elements. Positions `[k]` are the `0`-based `Fin k`. The
index `i` is the same on both sides. The range `1 ≤ k ≤ min{|A|, |B|}` is a hypothesis of each
statement that uses this problem. -/
def OneOut {A B O : Type} (k : ℕ) (R : A → B → O → Prop) :
    (Fin k ↪ A) → (Fin k ↪ B) → (Fin k × O) → Prop :=
  fun X Y p => R (X p.1) (Y p.1) p.2

end OneOfManyCC


