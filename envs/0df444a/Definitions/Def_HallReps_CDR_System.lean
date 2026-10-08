-- Prove2me | Definitions.Def_HallReps_CDR_System
-- name    : HallReps_CDR_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:49:34.176154+00:00
-- url     : https://prove2.me/theorems/af8d49b7-3ebb-4755-944a-82f46a7876d1
-- title:
--   §2, pp. 26–27, (1)–(3) — complete systems of distinct representatives, Hall's condition, and the meet of all C.D.R.s
-- statement:
--   Let $S$ be any set (possibly infinite) and let
--   $$T_i \subseteq S \qquad (i \in I)$$
--   be a system of subsets of $S$ indexed by a set $I$. The sets $T_i$ may be infinite and need not be distinct from one another: two indices may carry the same set. This file fixes three notions used throughout the mission.
--
--   1. **Complete set of distinct representatives (C.D.R.).** A family $a = (a_i)_{i \in I}$ of elements of $S$ is a C.D.R. of the system when the $a_i$ are pairwise distinct ($a_i \ne a_j$ for $i \ne j$) and
--   $$a_i \in T_i \qquad \text{for every } i \in I.$$
--   One says that $a_i$ *represents* $T_i$.
--
--   2. **Hall's condition.** The system satisfies Hall's condition when any $k$ of the sets contain between them at least $k$ elements: for every finite set $J \subseteq I$ of indices,
--   $$|J| \le \Bigl|\bigcup_{i \in J} T_i\Bigr|,$$
--   where the right-hand side is a cardinality in $\{0, 1, 2, \dots\} \cup \{\infty\}$. A selection of $k$ sets means $k$ indices, so repeated sets are counted with multiplicity.
--
--   3. **The meet of all C.D.R.s.** $R$ is the set of all elements of $S$ that occur as a representative in every C.D.R. of the system:
--   $$R = \{x \in S : x \in \{a_i : i \in I\} \text{ for every C.D.R. } a\}.$$
--   When the system has no C.D.R. at all, the condition is vacuous and $R = S$.
--
--   These are the objects of Hall's 1935 note: Theorem 1 states that Hall's condition is sufficient for a C.D.R. of a finite system, and its proof turns on the set $R$. The paper writes $A \wedge B$ for the intersection and $A \vee B$ for the union of sets; the mission writes $\cap$ and $\cup$.
--
--   **Formalization Note.** The ground set is a type `α`, the system is `T : ι → Set α` (never `Finset α`, since the sets may be infinite), and a C.D.R. is an injective `a : ι → α` with `a i ∈ T i`. Hall's condition quantifies over `s : Finset ι` and compares `s.card` with `Set.encard` of the union in `ℕ∞`, so an infinite union has cardinality `⊤` rather than the junk value `0` of `Set.ncard`. No finiteness of `ι` is built into the definitions; each theorem that needs a finite system assumes `[Finite ι]` or uses `Fin m`.
-- source:
--   P. Hall, On representatives of subsets, J. London Math. Soc. 10 (1935), pp. 26–27, §2, (1)–(3); Theorem 1 (p. 27); definition of R after the Lemma (p. 27)

import Mathlib

namespace HallReps.CDR

variable {ι α : Type*}

/-- (2)–(3), p. 26: `a` is a complete set of distinct representatives (C.D.R.) of the
system `T`: the representatives `a i` are distinct and `a i ∈ T i` for every index `i`. -/
def IsCDR (T : ι → Set α) (a : ι → α) : Prop :=
  Function.Injective a ∧ ∀ i, a i ∈ T i

/-- Theorem 1's condition, p. 27: any `k` of the sets (counted as `k` formally distinct
indices) contain between them at least `k` elements. Cardinalities are in `ℕ∞`, so an
infinite union counts as `⊤`. -/
def HallCondition (T : ι → Set α) : Prop :=
  ∀ s : Finset ι, (s.card : ℕ∞) ≤ (⋃ i ∈ s, T i).encard

/-- p. 27: the meet of all the C.D.R.s of `T`, i.e. the set of elements that occur as a
representative in every C.D.R. of `T` (it is `Set.univ` when `T` has no C.D.R.). -/
def cdrMeet (T : ι → Set α) : Set α :=
  {x | ∀ a : ι → α, IsCDR T a → x ∈ Set.range a}

end HallReps.CDR


