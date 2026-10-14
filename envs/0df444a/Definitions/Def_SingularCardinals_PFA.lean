-- Prove2me | Definitions.Def_SingularCardinals_PFA
-- name    : SingularCardinals_PFA
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T14:47:46.902851+00:00
-- url     : https://prove2.me/theorems/49a6ac39-9273-4e96-bb44-a49daa250299
-- title:
--   Proper posets and the proper forcing axiom (PFA)
-- statement:
--   Forcing notions are preorders $(P,\le)$ with the convention that $q\le p$ means $q$ is **stronger** than $p$. Conditions $p,q$ are **compatible** if some $r$ satisfies $r\le p$ and $r\le q$. A set $S\subseteq P$ is **predense below** $q$ if every $r\le q$ is compatible with some member of $S$; $D\subseteq P$ is **dense** if every $p$ has an extension in $D$. A **filter** is a nonempty, upward-closed $G\subseteq P$ in which any two members have a common extension in $G$.
--
--   **Names for ordinals.** Below a condition $p$, a name for an ordinal is given by a maximal antichain $A$ below $p$ (a set of pairwise incompatible conditions $\le p$ that is predense below $p$) together with an ordinal label $\ell(a)$ for each $a\in A$; for an ordinal set $B$, a condition $q\le p$ forces "the name lies in $B$" iff $\{a\in A:\ell(a)\in B\}$ is predense below $q$.
--
--   **Properness game.** Fix $p$. In round $n$ player I plays a name $\dot a_n$ for an ordinal below $p$, and player II answers with an ordinal $\beta_n$. A strategy for II is winning if for every sequence of moves of I there is $q\le p$ such that
--   $$q\Vdash\ \forall n\ \exists m\ \ \dot a_n=\beta_m .$$
--   $P$ is **proper** if, for every $p\in P$, player II has a winning strategy in this game.
--
--   **PFA.** The **proper forcing axiom** states: for every nonempty proper poset $P$ and every family $(D_i)_{i\in I}$ of dense subsets of $P$ with $|I|=\aleph_1$, there is a filter $G\subseteq P$ with $G\cap D_i\neq\emptyset$ for every $i$.
--
--   **Formalization Note** The usual definition of properness (via countable elementary submodels of $H_\theta$, or via preservation of stationary subsets of $[\lambda]^{\omega}$) needs a formalized forcing relation or model theory of set theory, which Mathlib lacks. This definition uses instead the game characterization of properness (Gray; Shelah, *Proper and Improper Forcing*), with names for ordinals given in antichain form and the forcing relation unfolded into predensity; this equivalence is a ZFC theorem but is not itself checked here, so this definition should be reviewed with particular care. Posets, index types and ordinal labels live in one fixed universe.
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, last paragraph: "the proper forcing axiom, which implies 2^ℵ0 = ℵ2 and hence is incompatible with GCH also implies SCH". Definition of properness via the properness game: S. Shelah, Proper and Improper Forcing, Springer 1998; C. Gray, PhD thesis, Berkeley 1980.

import Mathlib

universe u

namespace SingularCardinals

open Cardinal

/-! Forcing convention throughout: in a poset `P`, `q ≤ p` means `q` is a stronger condition. -/

/-- Two conditions are compatible if they have a common extension. -/
def Compatible {P : Type u} [Preorder P] (p q : P) : Prop := ∃ r, r ≤ p ∧ r ≤ q

/-- `S` is predense below `q`: every extension of `q` is compatible with some member of `S`. -/
def PredenseBelow {P : Type u} [Preorder P] (S : Set P) (q : P) : Prop :=
  ∀ r ≤ q, ∃ s ∈ S, Compatible r s

/-- `D` is dense: every condition has an extension in `D`. -/
def IsDense {P : Type u} [Preorder P] (D : Set P) : Prop := ∀ p : P, ∃ d ∈ D, d ≤ p

/-- A filter in the forcing sense: nonempty, upward closed, and any two members have a common
extension inside it. -/
def IsForcingFilter {P : Type u} [Preorder P] (G : Set P) : Prop :=
  G.Nonempty ∧ (∀ p ∈ G, ∀ q, p ≤ q → q ∈ G) ∧ ∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, r ≤ p ∧ r ≤ q

/-- A name for an ordinal below `p`, in antichain form: a maximal antichain below `p` whose
members are labelled by ordinals (the name takes the value `label a` on generic filters
containing `a`). -/
structure OrdinalNameBelow (P : Type u) [Preorder P] (p : P) where
  antichain : Set P
  le : ∀ a ∈ antichain, a ≤ p
  pairwise_incompatible : antichain.Pairwise fun a b => ¬ Compatible a b
  predense : PredenseBelow antichain p
  label : P → Ordinal.{u}

/-- The properness game below `p`: in round `n` player I plays a name `ȧₙ` for an ordinal and
player II answers with an ordinal `βₙ` (computed by the strategy `σ` from I's moves so far).
`σ` is winning if for every play of I there is `q ≤ p` forcing `∀ n ∃ m, ȧₙ = βₘ`, i.e. for
every `n` the members of the `n`-th antichain whose label is some `βₘ` are predense below `q`. -/
def IsWinningProperStrategy {P : Type u} [Preorder P] {p : P}
    (σ : List (OrdinalNameBelow P p) → Ordinal.{u}) : Prop :=
  ∀ x : ℕ → OrdinalNameBelow P p, ∃ q ≤ p, ∀ n : ℕ,
    PredenseBelow {a ∈ (x n).antichain |
      ∃ m : ℕ, (x n).label a = σ (List.ofFn fun i : Fin (m + 1) => x i)} q

/-- A poset is proper if, below every condition, player II has a winning strategy in the
properness game (Gray–Shelah game characterization of properness). -/
def IsProper (P : Type u) [Preorder P] : Prop :=
  ∀ p : P, ∃ σ : List (OrdinalNameBelow P p) → Ordinal.{u}, IsWinningProperStrategy σ

/-- The proper forcing axiom: for every nonempty proper poset `P` and every family of `ℵ₁`
dense subsets of `P`, some filter meets every member of the family. -/
def PFA : Prop :=
  ∀ (P : Type u) [Preorder P] [Nonempty P], IsProper P →
    ∀ (ι : Type u), #ι = aleph 1 → ∀ D : ι → Set P, (∀ i, IsDense (D i)) →
      ∃ G : Set P, IsForcingFilter G ∧ ∀ i, (G ∩ D i).Nonempty

end SingularCardinals


