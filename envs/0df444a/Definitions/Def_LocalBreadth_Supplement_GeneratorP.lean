-- Prove2me | Definitions.Def_LocalBreadth_Supplement_GeneratorP
-- name    : LocalBreadth_Supplement_GeneratorP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:18:10.86375+00:00
-- url     : https://prove2.me/theorems/b562cd92-7ccf-4a5a-bfa6-647899d3c2a6
-- title:
--   Generators over $\mathbb Z^d$: full enumerations, freshness, eventual validity
-- statement:
--   This is the model of the paper (p.13), used unchanged in Part II (p.51), over an arbitrary universe of strings $P$; Part II takes $P=\mathbb Z^d$ (§§6–9; in §6 the languages lie in $\mathbb N^d\subseteq\mathbb Z^d$).
--
--   A **generator** receives an enumeration $(x_t)$ of a target language $K\subseteq P$ one element at a time and after each input produces one point $o_t\in P$. A **full enumeration** of $K$ is a sequence of elements of $K$ whose range is exactly $K$; repetitions are permitted. The output set $O$ is the set of all outputs.
--
--   A generator is **fresh** on a family $\mathcal X$ if on every full enumeration of every $K\in\mathcal X$ and at every time $t$,
--   $$o_t\notin S_t\cup O_{t-1},\qquad S_t=\{x_1,\dots,x_t\},\quad O_{t-1}=\{o_1,\dots,o_{t-1}\}.$$
--   It is **universally eventually valid** on $\mathcal X$ if for every $K\in\mathcal X$ and every full enumeration of $K$, all but finitely many outputs belong to $K$.
--
--   These are the higher-dimensional counterparts of the published one-dimensional model `LocalBreadth.Generator`.
--
--   **Formalization Note** A generator is a function `List P → P` of the inputs so far, oldest first; it is causal by construction and has no computability clause. Time is 0-indexed, so the paper's $x_{t+1}$ is `x t`.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), model conventions, p.13; Part II conventions, p.51

import Mathlib

namespace LocalBreadth.Supplement

/-- A **generator** over a universe of strings `P`: it answers the inputs received so far (oldest
first) with one point of `P`. Kleinberg, Wei, *Characterizing Local Breadth in Language Generation*,
STOC 2027 submission (manuscript sha256 f924cbfc…), model conventions, p.13, used unchanged in
Part II ("We use the model conventions from Part I", p.51).

**Formalization Note.** This is the published `LocalBreadth.Generator` (fixed to `ℤ`) with the
universe of strings made a parameter: Part II uses `P = Fin d → ℤ` (§§6–9; in §6 the languages
lie in `ℕ^d ⊆ ℤ^d`). A generator is a deterministic function of the input history, with no
computability clause, and is causal by construction. Time is 0-indexed. -/
abbrev GeneratorP (P : Type) := List P → P

variable {P : Type}

/-- The inputs `x 0, …, x t`, oldest first. The paper's `x_{t+1}` is `x t`. -/
def inputsUpToP (x : ℕ → P) (t : ℕ) : List P := (List.range (t + 1)).map x

/-- The output at time `t`: it sees the inputs up to and including `x t`. -/
def outputP (G : GeneratorP P) (x : ℕ → P) (t : ℕ) : P := G (inputsUpToP x t)

/-- The output set `O` of the run of `G` on the enumeration `x`. -/
def outputSetP (G : GeneratorP P) (x : ℕ → P) : Set P := Set.range (outputP G x)

/-- A **full enumeration** of `K` (p.13): a sequence of elements of `K` whose range is exactly `K`;
repetitions are permitted. -/
def IsFullEnumerationP (K : Set P) (x : ℕ → P) : Prop := Set.range x = K

/-- **Global freshness** (p.13): `o_t ∉ S_t ∪ O_{t-1}` ("every output is available").

**Formalization Note.** Required on full enumerations of members of `X`, the only runs the paper
considers; a later input may equal an earlier output. -/
def IsFreshP (X : Set (Set P)) (G : GeneratorP P) : Prop :=
  ∀ K ∈ X, ∀ x, IsFullEnumerationP K x → ∀ t,
    outputP G x t ∉ {y | ∃ s ≤ t, x s = y} ∪ {y | ∃ s < t, outputP G x s = y}

/-- **Universal eventual validity on `X`** (p.13): for every `K ∈ X` and every full enumeration of
`K`, all but finitely many outputs belong to `K`. -/
def IsEventuallyValidP (X : Set (Set P)) (G : GeneratorP P) : Prop :=
  ∀ K ∈ X, ∀ x, IsFullEnumerationP K x → {t | outputP G x t ∉ K}.Finite

end LocalBreadth.Supplement


