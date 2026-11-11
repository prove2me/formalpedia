-- Prove2me | Definitions.Def_MetaSearch_Heyting_Ideal
-- name    : MetaSearch_Heyting_Ideal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:22:35.900528+00:00
-- url     : https://prove2.me/theorems/96aa89c6-e45f-45cc-adc3-6b151d56c2c2
-- title:
--   Ideals of (Verifiable, ≤), downward closures ↓X, finite joins, and the Heyting arrow of ideals
-- statement:
--   **Ideals (Definition 2.15).** An ideal of the preorder $(\mathsf{Verifiable},\le)$ is a set $I\subseteq\mathsf{Verifiable}$ that is
--   1. nonempty,
--   2. a lower set within $\mathsf{Verifiable}$: if $R\in\mathsf{Verifiable}$, $R\le S$ and $S\in I$, then $R\in I$,
--   3. upwards directed: for $R,S\in I$ there is $T\in I$ with $R\le T$ and $S\le T$.
--
--   The **ideal completion** is the set of ideals ordered by $\subseteq$; `IdealClass` is the type of ideals (a set with a proof that it is an ideal).
--
--   **Downward closure.** For a set $X$ of search problems, $\downarrow X=\{T\in\mathsf{Verifiable}:T\le X_0\text{ for some }X_0\in X\}$, and $\downarrow R=\downarrow\{R\}$.
--
--   **Finite joins.** `JoinClosure U` is the closure of $U$ under finite joins: it contains every member of $U$, the empty join $\mathsf{triv}$, and $S\vee T$ whenever it contains $S$ and $T$.
--
--   **Heyting arrow.** For sets $A,B$ of search problems, $H$ **is the Heyting arrow** $A\to B$ if $H$ is an ideal, $H\cap A\subseteq B$, and $C\subseteq H$ for every ideal $C$ with $C\cap A\subseteq B$; that is, $H$ is the maximum ideal $C$ with $C\cap A\subseteq B$. The **Heyting negation** $\neg A$ is $A\to\mathsf{FP}$, the largest ideal meeting $A$ inside $\mathsf{FP}$.
--
--   **Formalization Note.** Ideals live inside $\mathsf{Verifiable}$ and $\downarrow$ is taken inside $\mathsf{Verifiable}$ (reductions do not preserve verifiability). The Heyting arrow is a predicate given by maximality, not an operation, so that the theorems computing it are not true by definition.
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), pp. 20-21, Definition 2.15; p. 26 (Heyting arrow); p. 27 (↓)

import Mathlib
import Definitions.Def_MetaSearch_Heyting_JoinMeet

namespace MetaSearch.Heyting

/-! # Ideals of `(Verifiable, ≤)` (Definition 2.15), downward closures, finite joins, and the
Heyting arrow of ideals (p. 26) -/

/-- **Definition 2.15** for the preorder `(Verifiable, ≤)`: `I ⊆ Verifiable` is nonempty, a
lower set within `Verifiable`, and upwards directed. -/
def IsIdeal (I : Set SearchProblem) : Prop :=
  I ⊆ Verifiable ∧ I.Nonempty ∧
  (∀ R S, R ∈ Verifiable → Reduces R S → S ∈ I → R ∈ I) ∧
  (∀ R S, R ∈ I → S ∈ I → ∃ T ∈ I, Reduces R T ∧ Reduces S T)

/-- A complexity class: an ideal of `(Verifiable, ≤)`. The ideal completion is this type
ordered by `⊆` of carriers. -/
structure IdealClass where
  carrier : Set SearchProblem
  isIdeal : IsIdeal carrier

/-- `↓X`: the downward closure of a set `X` of search problems within `Verifiable`,
`{T ∈ Verifiable : ∃ X₀ ∈ X, T ≤ X₀}`; `↓R` is `down {R}`. -/
def down (X : Set SearchProblem) : Set SearchProblem :=
  {T | T ∈ Verifiable ∧ ∃ X₀ ∈ X, Reduces T X₀}

/-- The closure of `U` under finite joins: the members of `U`, the empty join `triv`, and
binary joins `S ∨ T` of members. -/
inductive JoinClosure (U : Set SearchProblem) : SearchProblem → Prop
  | mem {S : SearchProblem} : S ∈ U → JoinClosure U S
  | empty : JoinClosure U triv
  | join {S T : SearchProblem} : JoinClosure U S → JoinClosure U T → JoinClosure U (join S T)

/-- `H` is the Heyting arrow `A → B` of ideals: the maximum ideal `C` of `Verifiable` with
`C ∩ A ⊆ B`. The Heyting negation `¬A` is `A → FP`. -/
def IsHeytingArrow (A B H : Set SearchProblem) : Prop :=
  IsIdeal H ∧ H ∩ A ⊆ B ∧ ∀ C, IsIdeal C → C ∩ A ⊆ B → C ⊆ H

end MetaSearch.Heyting


