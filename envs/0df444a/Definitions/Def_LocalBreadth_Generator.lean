-- Prove2me | Definitions.Def_LocalBreadth_Generator
-- name    : LocalBreadth_Generator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:59.375097+00:00
-- url     : https://prove2.me/theorems/633be85a-1d17-4c93-be18-0be1f0754ab0
-- title:
--   Generators, full enumerations, freshness and eventual validity
-- statement:
--   A **generator** receives an enumeration $(x_t)$ of a target language one element at a time and, after each input, produces one integer $o_t$. A **full enumeration** of $K\subseteq\mathbb Z$ is a sequence of elements of $K$ whose range is exactly $K$; repetitions are permitted.
--
--   A generator is **fresh** on a family $\mathcal X$ if on every full enumeration of every $K\in\mathcal X$ and at every time $t$,
--   $$o_t\notin S_t\cup O_{t-1},\qquad S_t=\{x_1,\dots,x_t\},\quad O_{t-1}=\{o_1,\dots,o_{t-1}\}.$$
--   Such a point is called available. A later input may equal an earlier output. The generator is **universally eventually valid** on $\mathcal X$ if for every $K\in\mathcal X$ and every full enumeration of $K$, all but finitely many outputs belong to $K$. The output set $O$ is the set of all outputs of the run.
--
--   These are the model conventions under which every result of Part I of the paper is stated.
--
--   **Formalization Note** A generator is a function `List ℤ → ℤ` of the inputs so far, oldest first, with no computability clause. Time is 0-indexed, so the paper's $x_{t+1}$ is `x t`.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), model conventions, p.13

import Mathlib

namespace LocalBreadth

/-- A **generator** answers the inputs received so far (oldest first) with one integer.
Kleinberg, Wei, *Characterizing Local Breadth in Language Generation*, STOC 2027 submission
(manuscript sha256 f924cbfc…), model conventions, p.13.

**Formalization Note.** A generator is a deterministic function of the input history with no
computability clause: the paper places no computational restriction on it (p.1, p.16), and its
own earlier outputs are determined by the inputs. Time is 0-indexed. -/
abbrev Generator := List ℤ → ℤ

/-- The inputs `x 0, …, x t`, oldest first. The paper's `x_{t+1}` is `x t`. -/
def inputsUpTo (x : ℕ → ℤ) (t : ℕ) : List ℤ := (List.range (t + 1)).map x

/-- The output at time `t`: it sees the inputs up to and including `x t`. -/
def output (G : Generator) (x : ℕ → ℤ) (t : ℕ) : ℤ := G (inputsUpTo x t)

/-- The output set `O` of the run of `G` on the enumeration `x`. -/
def outputSet (G : Generator) (x : ℕ → ℤ) : Set ℤ := Set.range (output G x)

/-- A **full enumeration** of `K` (p.13): a sequence of elements of `K` whose range is exactly
`K`; repetitions are permitted. -/
def IsFullEnumeration (K : Set ℤ) (x : ℕ → ℤ) : Prop := Set.range x = K

/-- **Global freshness** (p.13): `o_t ∉ S_t ∪ O_{t-1}`, the condition "every output is available".

**Formalization Note.** Required on full enumerations of members of `X`, the only runs the paper
ever considers; a later input may equal an earlier output. -/
def IsFresh (X : Set (Set ℤ)) (G : Generator) : Prop :=
  ∀ K ∈ X, ∀ x, IsFullEnumeration K x → ∀ t,
    output G x t ∉ {y | ∃ s ≤ t, x s = y} ∪ {y | ∃ s < t, output G x s = y}

/-- **Universal eventual validity on `X`** (p.13): for every `K ∈ X` and every full enumeration of
`K`, all but finitely many outputs belong to `K`. -/
def IsEventuallyValid (X : Set (Set ℤ)) (G : Generator) : Prop :=
  ∀ K ∈ X, ∀ x, IsFullEnumeration K x → {t | output G x t ∉ K}.Finite

end LocalBreadth


