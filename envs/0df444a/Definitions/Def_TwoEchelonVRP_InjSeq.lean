-- Prove2me | Definitions.Def_TwoEchelonVRP_InjSeq
-- name    : TwoEchelonVRP_InjSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:25:53.842981+00:00
-- url     : https://prove2.me/theorems/bd1b569e-5288-4369-a8fd-021ece63245e
-- title:
--   Nonempty injective sequences (route orders) and their canonical orientation
-- statement:
--   A route of either level is a cycle through a base vertex (the depot, or a satellite) and a nonempty set of further vertices, visited in some order without repetition. This file defines the **nonempty injective sequences** $c_0, c_1, \dots, c_m$ of elements of $\{0, \dots, n-1\}$ ($m + 1 \le n$, the $c_j$ pairwise distinct), the set $\{c_0, \dots, c_m\}$ they visit, and their **canonical orientation**: the sequence is canonical when $m = 0$ or
--
--   $$
--   c_0 < c_m .
--   $$
--
--   A sequence and its reversal describe the same cycle (the same set of traversed edges); for $m \ge 1$ exactly one of the two is canonical, so canonical sequences index the cycles through the base vertex one to one.
--
--   **Formalization Note** A sequence is a pair `⟨m, c⟩` with `c : Fin (m+1) ↪ Fin n`; injectivity makes every route elementary. The module declares `InjSeq`, `InjSeq.toFinset`, `InjSeq.IsCanonical` and its decidability instance.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §2 and §2.1, unnumbered, pp. 299–300 (routes as cycles through the depot and a subset of satellites, or 'a simple cycle in G passing through a satellite and a subset of customers'; routes identified by their edge sets E(R_r), E(R_kl))

import Mathlib

namespace TwoEchelonVRP

/-- **Nonempty injective sequences** of elements of `Fin n`, used to describe the order in which a
route visits its satellites (first level) or its customers (second level).
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §2 and §2.1, unnumbered, pp. 299–300: a route passes
through the depot and a subset of satellites, or is "a simple cycle in G passing through a
satellite and a subset of customers".

An element `⟨m, c⟩` is the sequence `c 0, c 1, …, c m` of `m + 1` pairwise distinct elements.

**Formalization Note.** Injectivity makes every route elementary (no vertex visited twice). -/
abbrev InjSeq (n : ℕ) : Type := Σ m : Fin n, Fin (m.val + 1) ↪ Fin n

/-- The set `{c 0, …, c m}` of elements visited by an injective sequence. -/
def InjSeq.toFinset {n : ℕ} (c : InjSeq n) : Finset (Fin n) := Finset.univ.map c.2

/-- **Canonical orientation of a cycle.** A route is a cycle through a fixed base vertex (the
depot or the satellite) and the vertices `c 0, …, c m`; the sequence and its reversal describe the
same cycle (the same set of traversed edges). The sequence is *canonical* when it has one element
or its first element is smaller than its last; exactly one of the two orientations of a cycle with
at least two visited vertices is canonical, so canonical sequences index the cycles one to one.

Baldacci et al., Operations Research 61(2) (2013), §2.1, unnumbered, pp. 299–300: a route is
identified by its set `E(R_r)` (resp. `E(R_kl)`) of traversed edges. -/
def InjSeq.IsCanonical {n : ℕ} (c : InjSeq n) : Prop :=
  c.1.val = 0 ∨ c.2 0 < c.2 (Fin.last c.1.val)

instance {n : ℕ} : DecidablePred (InjSeq.IsCanonical (n := n)) := fun c => by
  unfold InjSeq.IsCanonical; infer_instance

end TwoEchelonVRP


