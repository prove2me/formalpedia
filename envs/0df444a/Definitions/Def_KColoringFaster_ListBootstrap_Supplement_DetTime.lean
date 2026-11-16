-- Prove2me | Definitions.Def_KColoringFaster_ListBootstrap_Supplement_DetTime
-- name    : KColoringFaster_ListBootstrap_Supplement_DetTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:24:48.278564+00:00
-- url     : https://prove2.me/theorems/cf6a7ba9-5137-4d54-97b3-8e16718707ae
-- title:
--   §3, Lemma 3.3, Theorem 4.4 — deterministic $O^*(T)$ time, palettes, short lists and the table of induced list subinstances
-- statement:
--   This definition adds to the published definitions `Instances` and `Algorithms` the objects that Lemma 3.3 (p. 9) and Theorem 4.4 (p. 19) of the paper need.
--
--   1. **Deterministic $O^*(T)$ time.** A property $\mathrm{Good}$ of outputs is *computed deterministically in time $O^*(T)$* on a class $\mathrm{Dom}$ of inputs if there are one program $P$ of the published integer RAM and polynomials $p,q$ with natural coefficients, all fixed before the input, such that on every input $a\in\mathrm{Dom}$ with encoding $x$ and budget
--   $$B=\big\lceil p(\sigma(x))\cdot T(a)\big\rceil,$$
--   the run without coins and without oracle halts with cost at most $B$, keeps every register within $q(\sigma(x))$ bits, and its output satisfies $\mathrm{Good}(a,\cdot)$. Here $\sigma(x)$ is the bit size of the input. *Deciding* a property $\mathrm{Yes}$ means outputting $[1]$ on yes-instances and $[0]$ on no-instances, without error; *finding* a solution means that whenever a solution exists, the output is one.
--   2. **Instances over a palette.** For a finite set $P\subseteq\mathbb N$ of colors, a list instance $(G,L)$ is *over* $P$ if $L(v)\subseteq P$ for every vertex $v$.
--   3. **Short lists.** $b(G,L)=\#\{v : |L(v)|\le 2\}$, the number of vertices whose list has at most two colors (sizes $0$, $1$, $2$ all count).
--   4. **Induced list subinstances.** For $X\subseteq V(G)$, $G[X]$ is *list colorable* if some map $c$ satisfies $c(v)\in L(v)$ for every $v\in X$ and $c(u)\ne c(v)$ for every edge $uv$ with $u,v\in X$. The *subset table* of $(G,L)$ on $n$ vertices is the word of length $2^n$ whose $i$-th entry ($0\le i<2^n$) is $1$ if $G[X_i]$ is list colorable and $0$ otherwise, where $X_i=\{v : \text{bit } v \text{ of } i \text{ is } 1\}$.
--
--   These objects let Lemma 3.3 and Theorem 4.4 be stated on the same machine, budget and encodings as the rest of the mission.
--
--   **Formalization Note** The deterministic predicate is the coin-free run of the published machine with the published budget `budget p x T`; it is the deterministic analogue of `RandDecides`/`RandFinds` of `Algorithms`, which has only a polynomial-time deterministic predicate (`DetPolyComputes`). $X_\emptyset$ ($i=0$) is the empty set, whose induced instance is colorable.
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 7 (§3, O* convention), p. 9 (Lemma 3.3), p. 19 (Theorem 4.4)

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Algorithms

open Classical

namespace KColoringFaster.ListBootstrap.Supplement

open CongruencyTU
open KColoringFaster.ListBootstrap

/-! # Deterministic `O*(T)` time, fixed palettes, short lists, and the induced-subinstance table

Zamir, *k-Coloring is Faster than Computing the Chromatic Number*, arXiv:2607.25973 (revision of
9 Sep 2026), §3 (p. 7), Lemma 3.3 (p. 9) and Theorem 4.4 (p. 19).

The machine, the budget `⌈p(σ(x)) · T⌉` and the instance encodings are the published base
definitions `Algorithms` and `Instances`; this file adds only the deterministic `O*(T)` analogue
of their randomized predicates, and the objects of Lemma 3.3 and Theorem 4.4. -/

/-- A deterministic computation in time `O*(T)`: one program `P` and polynomials `p q`, fixed before
the input, such that on every input `a` of `Dom`, with budget `B = ⌈p(σ(enc a)) · T a⌉`, the run
without coins and without oracle halts with cost at most `B`, keeps every register within
`q(σ(enc a))` bits, and its output satisfies `Good a`. -/
def DetComputes {α : Type*} (enc : α → List ℤ) (Dom : α → Prop)
    (Good : α → List ℤ → Prop) (T : α → ℝ) : Prop :=
  ∃ (P : Program) (p q : Polynomial ℕ), ∀ a, Dom a →
    RunBounded P noOracle noCoins (enc a) (budget p (enc a) (T a)) q 0 ∧
    Good a (outputAfter P noOracle noCoins (enc a) (budget p (enc a) (T a)))

/-- Deterministic decision in time `O*(T)`, without error: the output is `[1]` on yes-instances and
`[0]` on no-instances. -/
def DetDecides {α : Type*} (enc : α → List ℤ) (Dom Yes : α → Prop) (T : α → ℝ) : Prop :=
  DetComputes enc Dom (fun a out => out = if Yes a then [1] else [0]) T

/-- Deterministic search in time `O*(T)`: on every input of `Dom` the run is within the budget, and
whenever a solution exists the output is one. Nothing is required of the output otherwise. -/
def DetFinds {α : Type*} (enc : α → List ℤ) (Dom : α → Prop) (Sol : α → List ℤ → Prop)
    (T : α → ℝ) : Prop :=
  DetComputes enc Dom (fun a out => (∃ y, Sol a y) → Sol a out) T

/-- The list instance `I` is **over the palette** `P` (§3.1, p. 7; Lemma 3.3, p. 9; Theorem 4.4,
p. 19): every list is contained in `P`. Lists may be empty, and not every color of `P` need occur. -/
def OverPalette (P : Finset ℕ) (I : ListInstance) : Prop :=
  ∀ v, I.L v ⊆ P

/-- Theorem 4.4, p. 19: `b`, the number of vertices whose list has size **at most two** (sizes `0`,
`1` and `2` all count). -/
noncomputable def binaryCount (I : ListInstance) : ℕ :=
  (Finset.univ.filter fun v : Fin I.n => (I.L v).card ≤ 2).card

/-- Lemma 3.3, p. 9: the induced subinstance `G[X]` (with the lists restricted to `X`) is list
colorable. -/
def InducedListColorable (I : ListInstance) (X : Finset (Fin I.n)) : Prop :=
  ∃ c : Fin I.n → ℕ, (∀ v ∈ X, c v ∈ I.L v) ∧ ∀ u ∈ X, ∀ v ∈ X, I.G.Adj u v → c u ≠ c v

/-- The vertex set coded by the number `i`: the vertices `v` such that bit `v` of `i` is `1`
(so `i = ∑_{v ∈ X} 2^v`). -/
def subsetOfIndex (n : ℕ) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v : Fin n => i.testBit v.val

/-- The output of Lemma 3.3: the table over all `2^n` vertex subsets, whose `i`-th entry
(`i = 0, …, 2^n − 1`) is `1` if `G[X_i]` is list colorable and `0` otherwise, with
`X_i = subsetOfIndex n i`. -/
noncomputable def encSubsetTable (I : ListInstance) : List ℤ :=
  (List.range (2 ^ I.n)).map fun i =>
    if InducedListColorable I (subsetOfIndex I.n i) then 1 else 0

end KColoringFaster.ListBootstrap.Supplement


