-- Prove2me | Definitions.Def_LocalSearchFL_MultiSwap_capture
-- name    : LocalSearchFL_MultiSwap_capture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:37:10.208903+00:00
-- url     : https://prove2.me/theorems/897b43d3-4e27-491b-95fd-feeb00d40e66
-- title:
--   Neighbourhoods $N_A(a)$, $N_A(T)$, capture of a set, and good facilities
-- statement:
--   Let $S$ and $O$ be two solutions, and let $\sigma_S, \sigma_O : C \to F$ assign every client to the facility serving it in $S$ and in $O$ respectively.
--
--   1. **Neighbourhoods.** For a facility $a$, $N_S(a) = \{ j \in C : \sigma_S(j) = a\}$ is the set of clients that $a$ serves; for a set $T$ of facilities, $N_S(T) = \bigcup_{a \in T} N_S(a)$. The same notation is used with $O$ and $\sigma_O$.
--   2. **Capture of a set.** For $A \subseteq S$,
--   $$\mathrm{capture}(A) = \{ o \in O \mid |N_S(A) \cap N_O(o)| > |N_O(o)|/2 \}.$$
--   3. **Good and bad facilities.** A facility $s$ captures $o \in O$ if $|N_S(s) \cap N_O(o)| > \tfrac12 |N_O(o)|$, i.e. $o \in \mathrm{capture}(\{s\})$. The facility $s$ is **bad** if it captures some $o \in O$ and **good** otherwise.
--
--   Capture is the bookkeeping device of the analysis: it decides which facilities of $O$ may be swapped in against a set $A$ of facilities of $S$ without losing control of the clients of $A$.
--
--   **Formalization Note** The strict inequality $|N_S(A) \cap N_O(o)| > |N_O(o)|/2$ is written in integers as $|N_O(o)| < 2\,|N_S(A) \cap N_O(o)|$. "Good" is encoded as $\mathrm{capture}(\{s\}) = \emptyset$. The assignments are arbitrary functions; in the paper they are nearest-facility assignments, but the definitions do not need that.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 548 (N_A(a), N_A(T)), p. 549 (Definition 3.1, good/bad), p. 551 (§3.4, capture(A))

import Mathlib

namespace LocalSearchFL.MultiSwap

/-- The **neighbourhood** `N_A(a)` of a facility `a` under an assignment `σ` of clients to
facilities (p. 548): the set of clients that `a` serves. -/
def nbhd {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa] (σ : Cl → Fa) (a : Fa) : Finset Cl :=
  Finset.univ.filter (fun j => σ j = a)

/-- The neighbourhood `N_A(T) = ⋃_{a ∈ T} N_A(a)` of a set `T` of facilities (p. 548): the set of
clients served by some facility of `T`. -/
def nbhdSet {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa] (σ : Cl → Fa) (T : Finset Fa) :
    Finset Cl :=
  Finset.univ.filter (fun j => σ j ∈ T)

/-- **Capture of a set** (§3.4, p. 551). Given the assignment `σS` of the clients to the
facilities of a solution `S` and the assignment `σO` to those of a solution `O`,
`capture(A) = {o ∈ O | |N_S(A) ∩ N_O(o)| > |N_O(o)|/2}`, stated in integers as
`|N_O(o)| < 2 |N_S(A) ∩ N_O(o)|`. -/
def capture {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (O A : Finset Fa) : Finset Fa :=
  O.filter (fun o => (nbhd σO o).card < 2 * (nbhdSet σS A ∩ nbhd σO o).card)

/-- A facility `s` is **good** (p. 549) if it captures no facility of `O`, i.e.
`capture({s}) = ∅`, and **bad** otherwise (Definition 3.1: `s` captures `o` iff
`|N_S(s) ∩ N_O(o)| > ½ |N_O(o)|`). -/
def IsGood {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (O : Finset Fa) (s : Fa) : Prop :=
  capture σS σO O {s} = ∅

end LocalSearchFL.MultiSwap


