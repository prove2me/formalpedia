-- Prove2me | Definitions.Def_HHRControl_PV_Construction428
-- name    : HHRControl_PV_Construction428
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:34.770507+00:00
-- url     : https://prove2.me/theorems/0245f1ce-fe9b-4d1e-aed2-ee0b0929a2fc
-- title:
--   Construction 4.28, p. 24 — the election built from a Hitting Set instance (B, S, k)
-- statement:
--   Construction 4.28 builds an election from a Hitting Set instance $(B,S,k)$, where $B=\{b_1,\dots,b_m\}$, $S=\{S_1,\dots,S_n\}$ is a family of subsets of $B$, and $k\le m$ is a positive integer.
--
--   The candidates are $C=B\cup\{c,w\}$. The voters are:
--   1. $2(m-k)+2n(k+1)+4$ voters of the form $c>w>\cdots$;
--   2. $2n(k+1)+5$ voters of the form $w>c>\cdots$;
--   3. for each $i$, $1\le i\le n$, $2(k+1)$ voters of the form $S_i>c>\cdots$, where "$S_i$" denotes the elements of $S_i$ in some order;
--   4. for each $j$, $1\le j\le m$, two voters of the form $b_j>w>\cdots$.
--
--   Here "$\cdots$" means that the remaining candidates follow in some arbitrary order. The predicate $\mathrm{IsConstruction428}(m,n,k,S,P)$ says that the profile $P$ is such an election: $1\le k\le m$, and its voters can be labelled with the four kinds so that the kinds have the stated numbers of voters and every ballot has the form of its kind.
--
--   This election is the source of Claims 4.29, 4.30, 4.40 and 4.41, which give the NP-hardness of plurality control by partition of voters in model TP.
--
--   **Formalization Note** The candidates are `Fin (m + 2)`: $b_j$ is $j$ (0-based), $c$ is $m$ and $w$ is $m+1$. A voter $S_i>c>\cdots$ ranks exactly the elements of $S_i$ in the first $|S_i|$ positions and $c$ in position $|S_i|$. Since the construction leaves orders arbitrary, the predicate admits every order of the remaining candidates, every order of the elements of $S_i$, and any order of the voters.
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 24, Construction 4.28

import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

/-! # Construction 4.28: the election built from a Hitting Set instance

Hemaspaandra, Hemaspaandra & Rothe, *Anyone but Him*, arXiv:cs/0507027v5, p. 24, Construction 4.28.

The candidates are `Fin (m + 2)`: `b j = j` for `j : Fin m` (the set `B`), `c = m` and `w = m + 1`.
The construction leaves the order of the remaining candidates in every ballot, and the order of
the elements of `S i`, arbitrary; `IsConstruction428` therefore holds for every profile of the
stated shape. -/

/-- The candidate `b j` (`j : Fin m`) of Construction 4.28. -/
def candB {m : ℕ} (j : Fin m) : Fin (m + 2) := Fin.castAdd 2 j

/-- The candidate `c` of Construction 4.28. -/
def candC (m : ℕ) : Fin (m + 2) := ⟨m, by omega⟩

/-- The candidate `w` of Construction 4.28. -/
def candW (m : ℕ) : Fin (m + 2) := ⟨m + 1, by omega⟩

/-- The four kinds of voters of Construction 4.28. -/
inductive VoterType (m n : ℕ) where
  /-- a voter `c > w > ⋯` -/
  | cw
  /-- a voter `w > c > ⋯` -/
  | wc
  /-- a voter `Sᵢ > c > ⋯` -/
  | set (i : Fin n)
  /-- a voter `bⱼ > w > ⋯` -/
  | elem (j : Fin m)
  deriving DecidableEq

/-- The ballot `r` has the form its type `t` prescribes:
`c > w > ⋯`, `w > c > ⋯`, `Sᵢ > c > ⋯` (the elements of `Sᵢ` in the first `|Sᵢ|` positions, in some
order, then `c`), or `bⱼ > w > ⋯`. -/
def BallotForm {m n : ℕ} (S : Fin n → Finset (Fin m)) : VoterType m n → Ranking (m + 2) → Prop
  | .cw, r => (r (candC m) : ℕ) = 0 ∧ (r (candW m) : ℕ) = 1
  | .wc, r => (r (candW m) : ℕ) = 0 ∧ (r (candC m) : ℕ) = 1
  | .set i, r => (∀ j : Fin m, j ∈ S i ↔ (r (candB j) : ℕ) < (S i).card) ∧
      (r (candC m) : ℕ) = (S i).card
  | .elem j, r => (r (candB j) : ℕ) = 0 ∧ (r (candW m) : ℕ) = 1

/-- `P` is an election of Construction 4.28 for the Hitting Set instance `(B, S, k)` with
`B = Fin m`, `S : Fin n → Finset (Fin m)` and a positive integer `k ≤ m`: its voters can be labelled
so that there are `2(m − k) + 2n(k + 1) + 4` voters `c > w > ⋯`, `2n(k + 1) + 5` voters `w > c > ⋯`,
for each `i` exactly `2(k + 1)` voters `Sᵢ > c > ⋯`, and for each `j` exactly two voters
`bⱼ > w > ⋯`. -/
def IsConstruction428 (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ}
    (P : Fin N → Ranking (m + 2)) : Prop :=
  1 ≤ k ∧ k ≤ m ∧
    ∃ τ : Fin N → VoterType m n,
      (Finset.univ.filter fun v => τ v = .cw).card = 2 * (m - k) + 2 * n * (k + 1) + 4 ∧
      (Finset.univ.filter fun v => τ v = .wc).card = 2 * n * (k + 1) + 5 ∧
      (∀ i, (Finset.univ.filter fun v => τ v = .set i).card = 2 * (k + 1)) ∧
      (∀ j, (Finset.univ.filter fun v => τ v = .elem j).card = 2) ∧
      ∀ v, BallotForm S (τ v) (P v)

end HHRControl.PV


