-- Prove2me | Definitions.Def_PctDistortion_Supplement_c1Maximal
-- name    : PctDistortion_Supplement_c1Maximal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:29:01.831521+00:00
-- url     : https://prove2.me/theorems/9fb88233-14d7-4b3e-a444-897e43c1bf88
-- title:
--   Majority tournaments, the Condorcet game and C1-maximal lotteries
-- statement:
--   Let $\mathcal E=(V,\mathcal C,\vec\succ)$ be an election with $n$ voters. A **majority tournament** of $\mathcal E$ is a digraph $T$ on $\mathcal C$ with no loops, containing exactly one of the arcs $(i,j)$, $(j,i)$ for every pair $i\ne j$, such that every arc $(i,j)$ is supported by at least $n/2$ voters who prefer $i$ to $j$ (pairwise ties are oriented arbitrarily).
--
--   The **Condorcet game** $\mathcal G^C_T$ is the zero-sum game in which Alice and Bob choose candidates $i,j$, with Alice's payoff
--   $$p^C_A(i,j)=\begin{cases}0,& i=j,\\ +1,& (i,j)\in T,\\ -1,& (j,i)\in T,\end{cases}$$
--   and Bob's payoff $-p^C_A(i,j)$.
--
--   **C1-Maximal Lotteries** outputs the lottery $a\in\Delta\mathcal C$ for which $(a,a)$ is the equilibrium of $\mathcal G^C_T$ (Definition 9); the set `c1Maximal T` collects every $a$ for which $(a,a)$ is a mixed Nash equilibrium.
--
--   **Formalization Note** Nash equilibria are the published `BlottoLP.Flow.IsNashEq` (Alice the row player). Existence and uniqueness of the equilibrium (Laslier; Proposition 6 of the paper, cited) are not built in: by that result the set is the singleton of the C1-maximal lottery.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), App. B, p.30 (majority tournament), Definitions 8–9, p.30

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_PctDistortion_Election

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

open Classical in
/-- `T` is a **majority tournament** of the election `E` (with `n` voters), pairwise ties
oriented arbitrarily: `T` has no loops, for every pair `i ≠ j` exactly one of `(i, j)`,
`(j, i)` is an arc, and every arc `(i, j)` is supported by at least `n/2` voters who prefer
`i` to `j`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), App. B, p.30: "let T = (C, E) be the majority tournament of an election E = (V, C, ≻⃗), with
pairwise ties oriented arbitrarily. Thus, every arc (i, j) ∈ E is supported by at least n/2 voters
who prefer i to j."

**Formalization Note.** "At least `n/2` voters" is `n ≤ 2 · #{v | i ≻_v j}` in `ℕ`. -/
def IsMajorityTournament {V C : Type} [Fintype V] (E : Election V C) (T : Digraph C) : Prop :=
  (∀ i, ¬ T.Adj i i) ∧ (∀ i j, i ≠ j → (T.Adj i j ↔ ¬ T.Adj j i)) ∧
    ∀ i j, T.Adj i j →
      Fintype.card V ≤ 2 * (Finset.univ.filter (fun v => E.prefers v i j)).card

open Classical in
/-- Alice's payoff in the **Condorcet game** `𝒢^C_T` over the tournament `T` when Alice
chooses `i` and Bob chooses `j`: `0` if `i = j`, `+1` if `(i, j)` is an arc, `−1` if
`(j, i)` is an arc. Bob receives the opposite payoff.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 8, p.30.

**Formalization Note.** For `i ≠ j` in a tournament exactly one of the two arcs exists, so
"not `(i, j)`" means "`(j, i)`". -/
noncomputable def condorcetPayoff {C : Type} (T : Digraph C) (i j : C) : ℝ :=
  if i = j then 0 else if T.Adj i j then 1 else -1

/-- The **C1-maximal lotteries** of the tournament `T`: the lotteries `a ∈ ∆C` for which
`(a, a)` is a (mixed) Nash equilibrium of the Condorcet game `𝒢^C_T`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 9, p.30: "Given a tournament T, C1-Maximal Lotteries outputs the lottery a ∈ ∆C
for which (a, a) is the unique equilibrium of 𝒢^C_T. … The lotteries … of an election E are defined
as the lotteries … of E's majority tournament T."

**Formalization Note.** Nash equilibria are the published `BlottoLP.Flow.IsNashEq` (Alice the
row player; both strategies mixed). Existence and uniqueness of the equilibrium (Laslier,
Proposition 6 of the paper, cited) are not part of the definition: the set is all symmetric
equilibrium strategies, which is the singleton of the C1-maximal lottery by Proposition 6. -/
def c1Maximal {C : Type} [Fintype C] (T : Digraph C) : Set (C → ℝ) :=
  {a | BlottoLP.Flow.IsNashEq (condorcetPayoff T) a a}

end PctDistortion.Supplement


