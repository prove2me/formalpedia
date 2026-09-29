-- Prove2me | Definitions.Def_Garrido_Equidecomposability
-- name    : Garrido_Equidecomposability
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-23T17:45:26.211489+00:00
-- url     : https://prove2.me/theorems/b7906dde-68c9-4d20-a096-78d35cbe7bc2
-- title:
--   Equidecomposability and paradoxical subsets
-- statement:
--   Three notions for a group $G$ acting on a set $X$, all built on Mathlib's
--   `Equidecomp X G` — a partial bijection of $X$ whose source is cut into finitely many pieces,
--   each moved by a single element of $G$.
--
--   **Equidecomposable.** $A$ and $B$ are $G$-equidecomposable, $A \sim B$, when some
--   equidecomposition has source exactly $A$ and target exactly $B$.
--
--   **EquidecomposableToSubset.** $A \lesssim B$ when $A \sim C$ for some $C \subseteq B$. The relation is written $\lesssim$ in the literature, but the declaration is deliberately not named for an order: nothing here supplies an `LE` instance, and antisymmetry is exactly what Theorem 1.2 has to prove.
--
--   **IsParadoxical.** A subset $E \subseteq X$ is $G$-paradoxical when there are $A, B \subseteq E$
--   with $A \neq E$ and $B \neq E$, disjoint, such that $A \sim E$ and $B \sim E$.
--
--   Note on the third: the source defines paradoxicality for the whole space $X$ ("We say that $X$
--   is (finitely) $G$-paradoxical"), but every later use is for a subset — Theorem 1.11 speaks of
--   $E \subseteq X$, Definition 3.9 of every nonempty $A \subseteq G$, Theorem 3.10(1) of every
--   nonempty $A \subseteq X$. The relativised form is taken as primitive and the source's notion
--   is the case $E = X$. The two proper-subset conditions are written $A \neq E$ and $B \neq E$
--   rather than as strict inclusions, which is equivalent given $A, B \subseteq E$.
--
--   Three further points a reader should not have to discover.
--
--   *The properness clauses exclude $E = \emptyset$, and that is all they add.* Given the other
--   clauses together with $E \neq \emptyset$ they hold automatically: if $A = E$ then disjointness
--   forces $B = \emptyset$, and an equidecomposition with empty source has empty target, so
--   $B \sim E$ would give $E = \emptyset$. Conversely $E$ paradoxical implies $E \neq \emptyset$.
--   This is exactly the work the source's word "proper" does.
--
--   *There is no covering clause.* The definition asks for two disjoint proper subsets each
--   equidecomposable with $E$, and does **not** require $A \cup B = E$. That is the first of the two
--   forms in Corollary 1.3; the source's Definition 1.4 says "any and hence both", and Corollary
--   1.3 is the milestone establishing that the two forms agree.
--
--   *Only a scalar action is assumed.* The three notions are stated for a bare $\mathrm{SMul}$
--   action, with no group, monoid or action axioms, following Mathlib's own `Equidecomp`, which
--   relaxes the group requirement where possible. At that generality $\sim$ is not known to be
--   symmetric or transitive — reflexivity and transitivity need a monoid action and symmetry needs
--   a group — so although the word "equidecomposable" names a symmetric relation, symmetry is
--   neither asserted nor derivable from this definition alone. Every theorem in the mission that
--   uses it does assume a group acting, where the relation is an equivalence relation.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 1-2, Definitions 1.1 and 1.4. Definition 1.4 is stated in the source for the whole space; it is given here for an arbitrary subset, which is the form Theorem 1.11, Definition 3.9 and Theorem 3.10 all use; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib

namespace Garrido

def Equidecomposable (G : Type*) {X : Type*} [SMul G X] (A B : Set X) : Prop :=
  ∃ f : Equidecomp X G, f.source = A ∧ f.target = B

def EquidecomposableToSubset (G : Type*) {X : Type*} [SMul G X] (A B : Set X) : Prop :=
  ∃ C : Set X, C ⊆ B ∧ Equidecomposable G A C

def IsParadoxical (G : Type*) {X : Type*} [SMul G X] (E : Set X) : Prop :=
  ∃ A B : Set X, A ⊆ E ∧ B ⊆ E ∧ A ≠ E ∧ B ≠ E ∧ Disjoint A B ∧
    Equidecomposable G A E ∧ Equidecomposable G B E

end Garrido


