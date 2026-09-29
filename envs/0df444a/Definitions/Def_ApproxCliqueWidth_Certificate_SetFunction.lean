-- Prove2me | Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
-- name    : ApproxCliqueWidth_Certificate_SetFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:29:21.874348+00:00
-- url     : https://prove2.me/theorems/266ed2c3-d895-478e-9427-d12a1dfee604
-- title:
--   Submodular and symmetric set functions, matroid rank functions, and well-linked sets
-- statement:
--   Let $V$ be a finite set and $f : 2^V \to \mathbb{Z}$ an integer-valued set function.
--
--   1. $f$ is **submodular** if for all $X, Y \subseteq V$
--   $$f(X) + f(Y) \ge f(X \cap Y) + f(X \cup Y).$$
--   2. $f$ is **symmetric** if $f(X) = f(V \setminus X)$ for all $X \subseteq V$.
--   3. For $E \subseteq V$, a function $r$ is the **rank function of a matroid on $E$** if, for subsets of $E$, it satisfies the axioms (i) $0 \le r(X) \le |X|$ for all $X \subseteq E$; (ii) $r(X) \le r(Y)$ whenever $X \subseteq Y \subseteq E$; (iii) $r$ is submodular on subsets of $E$.
--   4. A set $W \subseteq V$ is **well-linked** with respect to $f$ if for every partition $(X, Y)$ of $W$ and every $Z$ with $X \subseteq Z \subseteq V \setminus Y$,
--   $$f(Z) \ge \min(|X|, |Y|).$$
--
--   These are the basic notions of Oum and Seymour's approximation algorithm for branch-width: well-linked sets are the obstructions whose presence forces large branch-width and whose absence allows a branch-decomposition of small width to be built.
--
--   **Formalization Note** Subsets of $V$ are `Finset V` for a `Fintype V`; $V \setminus X$ is the complement `Xᶜ`. The paper states well-linkedness only for symmetric submodular $f$ with $f(\emptyset) = 0$; the predicate is defined for any $f$, and these assumptions are hypotheses of every theorem that uses it. "$Z \subseteq V \setminus Y$" is written as "$Z$ and $Y$ are disjoint". Values of a matroid rank function on sets not contained in $E$ are not constrained.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 516, Section 2 (submodular, symmetric); p. 517, Section 2 (matroid rank axioms (i)–(iii)); p. 519, Definition 5.1 (well-linked)

import Mathlib

namespace ApproxCliqueWidth.Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Oum–Seymour p. 516: `f : 2^V → ℤ` is submodular if
`f(X) + f(Y) ≥ f(X ∩ Y) + f(X ∪ Y)` for all `X, Y ⊆ V`. -/
def IsSubmodular (f : Finset V → ℤ) : Prop :=
  ∀ X Y : Finset V, f (X ∩ Y) + f (X ∪ Y) ≤ f X + f Y

/-- Oum–Seymour p. 516: `f` is symmetric if `f(X) = f(V \ X)` for all `X ⊆ V`. -/
def IsSymmetric (f : Finset V → ℤ) : Prop :=
  ∀ X : Finset V, f X = f Xᶜ

/-- Oum–Seymour p. 517, matroid rank axioms (i)–(iii), for a rank function on the ground set
`E ⊆ V`: `r` restricted to subsets of `E` satisfies `0 ≤ r(X) ≤ |X|`, is monotone and is
submodular. Values of `r` on sets not contained in `E` are unconstrained. -/
def IsMatroidRankOn (E : Finset V) (r : Finset V → ℤ) : Prop :=
  (∀ X : Finset V, X ⊆ E → 0 ≤ r X ∧ r X ≤ (X.card : ℤ)) ∧
  (∀ X Y : Finset V, X ⊆ Y → Y ⊆ E → r X ≤ r Y) ∧
  (∀ X Y : Finset V, X ⊆ E → Y ⊆ E → r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y)

/-- Oum–Seymour Definition 5.1 (p. 519): `W ⊆ V` is well-linked with respect to `f` if for every
partition `(X, Y)` of `W` and every `Z` with `X ⊆ Z ⊆ V \ Y`, `f(Z) ≥ min(|X|, |Y|)`.
(The paper states the notion for symmetric submodular `f` with `f(∅) = 0`; those assumptions
are hypotheses of the theorems that use it.) -/
def IsWellLinked (f : Finset V → ℤ) (W : Finset V) : Prop :=
  ∀ X Y : Finset V, X ∪ Y = W → Disjoint X Y →
    ∀ Z : Finset V, X ⊆ Z → Disjoint Z Y → (min X.card Y.card : ℤ) ≤ f Z

end ApproxCliqueWidth.Certificate


