-- Prove2me | Definitions.Def_GroupIsoDepth_LowerBounds_Circuits
-- name    : GroupIsoDepth_LowerBounds_Circuits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:40:41.774901+00:00
-- url     : https://prove2.me/theorems/c6aa5e19-6bf7-4c0a-8f2b-0eab8a272987
-- title:
--   Depth-2 circuits: terms, DNFs, CNF/DNF evaluation, size and deciding a language
-- statement:
--   Let $V$ be a finite set of Boolean input variables. A **literal** is $x_v$ or $\bar x_v$; a **clause** is an OR of literals and a **CNF** an AND of clauses (the published `LiftSAParity` objects: a literal is a pair $(v,b)$, true at $a\in\{0,1\}^V$ iff $a_v=b$). A **term** is an AND of literals and a **DNF** an OR of terms. A CNF is true at $a$ when no clause is falsified; a DNF is true at $a$ when some term has all its literals true.
--
--   A **depth-2 circuit** over $V$ is a CNF or a DNF; its **size** is its number of clauses (CNF) or terms (DNF). A depth-2 circuit $\varphi$ **decides** a language $L\subseteq\{0,1\}^V$ if $\varphi(a)=1\iff a\in L$ for **every** $a\in\{0,1\}^V$.
--
--   **Formalization Note** Clauses, terms, CNFs and DNFs are `Finset`s, so a repeated clause or term is counted once. `Depth2 V := CNF V ⊕ DNF V`. Truth values are propositions (`CNF.Holds`, `DNF.Holds`, `Depth2.Holds`).
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), §3.1 (p. 14, PDF 15); Theorem 5.2 (p. 36, PDF 37); proof of Theorem 5.3 (p. 40, PDF 41)

import Mathlib
import Definitions.Def_LiftSAParity_CNF

namespace GroupIsoDepth.LowerBounds

/-! Grochow, Kardeş, Levet, *Group Isomorphism: Depth-2½ Circuits and Lower Bounds*, STOC 2027
submission (manuscript sha256 cd6cacd4…), §3.1 (printed p. 14, PDF 15), Theorem 5.2 (p. 36,
PDF 37) and the proof of Theorem 5.3 (p. 40, PDF 41).

Depth-2 Boolean circuits over a variable set `V`. Literals, clauses and CNFs are the published
`LiftSAParity` objects: a literal is a pair `(v, b) : V × Bool`, true under `a : V → Bool` iff
`a v = b`; a clause is a `Finset` of literals (their OR); a CNF is a `Finset` of clauses (their
AND). A term is a `Finset` of literals read as their AND, and a DNF is a `Finset` of terms read
as their OR. The size of a CNF (resp. DNF) is its number of clauses (resp. terms). -/

open LiftSAParity

/-- A term over `V`: a finite set of literals, read as their conjunction. -/
abbrev Term (V : Type*) := Finset (V × Bool)

/-- A DNF over `V`: a finite set of terms, read as their disjunction. -/
abbrev DNF (V : Type*) := Finset (Term V)

/-- The CNF `φ` is true (outputs 1) at `a`: no clause of `φ` is falsified by `a`. -/
def CNF.Holds {V : Type*} (φ : CNF V) (a : V → Bool) : Prop :=
  ∀ C ∈ φ, ¬ Falsifies a C

/-- The term `t` is true at `a`: every literal of `t` is true, i.e. `a v = b` for `(v, b) ∈ t`. -/
def Term.Holds {V : Type*} (t : Term V) (a : V → Bool) : Prop :=
  ∀ l ∈ t, a l.1 = l.2

/-- The DNF `ψ` is true (outputs 1) at `a`: some term of `ψ` is true at `a`. -/
def DNF.Holds {V : Type*} (ψ : DNF V) (a : V → Bool) : Prop :=
  ∃ t ∈ ψ, Term.Holds t a

/-- A depth-2 circuit over `V`: a CNF (AND of ORs of literals) or a DNF (OR of ANDs of literals). -/
abbrev Depth2 (V : Type*) := CNF V ⊕ DNF V

/-- The depth-2 circuit `φ` outputs 1 at `a`. -/
def Depth2.Holds {V : Type*} : Depth2 V → (V → Bool) → Prop
  | Sum.inl φ, a => CNF.Holds φ a
  | Sum.inr ψ, a => DNF.Holds ψ a

/-- The size of a depth-2 circuit: the number of clauses of a CNF, the number of terms of a DNF. -/
def Depth2.size {V : Type*} : Depth2 V → ℕ
  | Sum.inl φ => φ.card
  | Sum.inr ψ => ψ.card

/-- The depth-2 circuit `φ` decides the language `L ⊆ {0,1}^V`: it is correct on **every**
assignment of its input variables. -/
def Depth2.Decides {V : Type*} (φ : Depth2 V) (L : (V → Bool) → Prop) : Prop :=
  ∀ a : V → Bool, Depth2.Holds φ a ↔ L a

end GroupIsoDepth.LowerBounds


