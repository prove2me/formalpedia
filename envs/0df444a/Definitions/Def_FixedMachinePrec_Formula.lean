-- Prove2me | Definitions.Def_FixedMachinePrec_Formula
-- name    : FixedMachinePrec_Formula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:46.528438+00:00
-- url     : https://prove2.me/theorems/681aec9f-efad-424d-bbd5-4f5d68e75a7a
-- title:
--   Atoms, Boolean formulas, leaf counts and the family $\mathcal F_K$
-- statement:
--   Fix the padded set $J=\{1,\dots,N\}$, its order $\prec$, the number of machines $m$, and a rank function $\mathrm{rank}:J\to\{1,\dots,N\}$. For $1\le h\le N+1$ the **rank suffix** is $R_h=\{x\in J:\mathrm{rank}(x)\ge h\}$.
--
--   The **atomic sets** are
--   $$J,\quad \emptyset,\quad R_h\ (1\le h\le N+1),\quad A,\ P_A,\ D_A,\ \hat P_A,\ \hat D_A\quad(|A|=m),$$
--   where $A$ ranges over all $m$-subsets of $J$, antichains or not. A **Boolean formula** is built from atoms by binary union, binary intersection and complement relative to $J$. Its **leaf count** is the number of atomic occurrences, counted with multiplicity; complement adds no leaf. The **family** $\mathcal F_K$ is the set of distinct subsets of $J$ represented by formulas with at most $K$ leaves.
--
--   A rank function is a **bijective topological rank** if it is a bijection onto $\{1,\dots,N\}$ with $x\prec y\Rightarrow\mathrm{rank}(x)<\mathrm{rank}(y)$.
--
--   The algorithm uses $\mathcal F=\mathcal F_{4m+5}$ as candidate node sets and $\mathcal F_{\mathrm{cut}}=\mathcal F_{m+3}$ as candidate cuts; the structural theorem shows these short descriptions suffice.
--
--   **Formalization Note** Atoms are a syntax with a validity predicate ($1\le h\le N+1$ for rank suffixes, $|A|=m$ otherwise). The family is a finite set of subsets of `Fin N`. The algorithm's rank is the smallest-identifier topological order; the theorems take any bijective topological rank.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), §2.2, pp.4–5, Definition 2.2

import Mathlib
import Definitions.Def_FixedMachinePrec_FullSchedule

namespace FixedMachinePrec

/-- **Atoms, Boolean formulas, leaf counts and the family `F_K`.**
Jansen, *Precedence Constraint Scheduling on a Fixed Number of Machines* (manuscript, sha256
08cdf3e1…), §2.2, pp.4–5. "For an m-element set A ⊆ J, define P_A = {x ∈ J : ∃a ∈ A, x ≺ a},
D_A = {x ∈ J : ∃a ∈ A, a ≺ x}, P̂_A = P_A ∪ A, D̂_A = D_A ∪ A. … For 1 ≤ h ≤ N + 1, put
R_h = {x ∈ J : rank(x) ≥ h}." Definition 2.2 (Atoms and the family F_K): "The atomic sets are
J, ∅, R_h, A, P_A, D_A, P̂_A, D̂_A (|A| = m). A Boolean formula uses these atoms, binary union and
intersection, and unary complement relative to J. Its leaf count is the number of atomic
occurrences, counted with multiplicity. Unary complement does not add a leaf. The family F_K
contains the distinct sets represented by formulas with at most K leaves."

`Atom N` names an atomic set; `Atom.Valid m` restricts `R_h` to `1 ≤ h ≤ N + 1` and the boundary
atoms to `|A| = m` (every `m`-set `A`, antichain or not, p.5).

**Formalization Note** `J = Fin N`. The rank is an argument `rank : Fin N → ℕ`; the theorems ask
it to be a bijective topological rank onto `{1, …, N}` (`IsTopoRank`), the algorithm instantiating
it with the smallest-identifier topological order (p.4, p.10). -/
inductive Atom (N : ℕ) where
  | univ
  | empty
  | rankSuffix (h : ℕ)
  | boundary (A : Finset (Fin N))
  | pred (A : Finset (Fin N))
  | succ (A : Finset (Fin N))
  | weakPred (A : Finset (Fin N))
  | weakSucc (A : Finset (Fin N))
  deriving DecidableEq

namespace Atom

variable {N : ℕ}

/-- The admissible atoms: `1 ≤ h ≤ N + 1` for `R_h`, and `|A| = m` for the boundary atoms. -/
def Valid (m : ℕ) : Atom N → Prop
  | univ => True
  | empty => True
  | rankSuffix h => 1 ≤ h ∧ h ≤ N + 1
  | boundary A => A.card = m
  | pred A => A.card = m
  | succ A => A.card = m
  | weakPred A => A.card = m
  | weakSucc A => A.card = m

/-- The rank suffix `R_h = {x ∈ J : rank(x) ≥ h}`. -/
def rankSuffixSet (rank : Fin N → ℕ) (h : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x => h ≤ rank x

/-- The subset of `J` an atom denotes. -/
def eval (prec : Fin N → Fin N → Prop) [DecidableRel prec] (rank : Fin N → ℕ) :
    Atom N → Finset (Fin N)
  | univ => Finset.univ
  | empty => ∅
  | rankSuffix h => rankSuffixSet rank h
  | boundary A => A
  | pred A => predCone prec A
  | succ A => succCone prec A
  | weakPred A => weakPredCone prec A
  | weakSucc A => weakSuccCone prec A

end Atom

/-- Boolean formulas over atoms: atoms, binary union and intersection, unary complement. -/
inductive Formula (N : ℕ) where
  | atom (a : Atom N)
  | union (φ ψ : Formula N)
  | inter (φ ψ : Formula N)
  | compl (φ : Formula N)

namespace Formula

variable {N : ℕ}

/-- All atoms of the formula are admissible. -/
def Valid (m : ℕ) : Formula N → Prop
  | atom a => a.Valid m
  | union φ ψ => φ.Valid m ∧ ψ.Valid m
  | inter φ ψ => φ.Valid m ∧ ψ.Valid m
  | compl φ => φ.Valid m

/-- The leaf count: atomic occurrences with multiplicity; complement adds no leaf. -/
def leaves : Formula N → ℕ
  | atom _ => 1
  | union φ ψ => φ.leaves + ψ.leaves
  | inter φ ψ => φ.leaves + ψ.leaves
  | compl φ => φ.leaves

/-- The subset of `J` a formula represents; complement is relative to `J`. -/
def eval (prec : Fin N → Fin N → Prop) [DecidableRel prec] (rank : Fin N → ℕ) :
    Formula N → Finset (Fin N)
  | atom a => a.eval prec rank
  | union φ ψ => φ.eval prec rank ∪ ψ.eval prec rank
  | inter φ ψ => φ.eval prec rank ∩ ψ.eval prec rank
  | compl φ => Finset.univ \ φ.eval prec rank

end Formula

open Classical in
/-- **The family `F_K`**: the distinct subsets of `J` represented by admissible formulas with at
most `K` leaves (Definition 2.2, p.5). -/
noncomputable def family {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (rank : Fin N → ℕ) (m K : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.filter fun S =>
    ∃ φ : Formula N, φ.Valid m ∧ φ.leaves ≤ K ∧ φ.eval prec rank = S

/-- `rank` is a **bijective topological rank** `J → {1, …, N}`: injective, with values in
`{1, …, N}`, and `x ≺ y ⇒ rank(x) < rank(y)` (§2.2, p.4; §7.1, p.28). -/
def IsTopoRank {N : ℕ} (prec : Fin N → Fin N → Prop) (rank : Fin N → ℕ) : Prop :=
  (∀ x, 1 ≤ rank x ∧ rank x ≤ N) ∧ Function.Injective rank ∧ ∀ x y, prec x y → rank x < rank y

end FixedMachinePrec


