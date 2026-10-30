-- Prove2me | Definitions.Def_SubsamplingSM_Offline_alg2Step
-- name    : SubsamplingSM_Offline_alg2Step
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:54:32.020138+00:00
-- url     : https://prove2.me/theorems/957902c1-a697-4e1f-8405-c85ce9cbeae3
-- title:
--   One iteration of Algorithm 2
-- statement:
--   Algorithm 2 runs the greedy algorithm over all of $N$ and flips the coin of each chosen element on the spot. With the coins fixed in advance ($b_u=1$ if and only if $u\in b$), one iteration does the following. If no $u\in N'$ has $S\cup\{u\}\in\mathcal I$ and $f(u\mid S)>0$, the state is unchanged (the loop has terminated). Otherwise let $u=\operatorname{pick}(S,C(N',S))$ and set $S_u\leftarrow S$.
--   1. If $b_u=1$: add $u$ to $S$ and to $O$, let $O_u=\mathrm{sel}(O,S)$ be a smallest subset of $O\setminus S$ with $O\setminus O_u\in\mathcal I$ (for the updated $O$ and $S$), and record $Y_u=1$ if $u\notin O$ at the beginning of the iteration.
--   2. If $b_u=0$: let $O_u=\{u\}$ if $u\in O$ and $O_u=\emptyset$ otherwise.
--
--   In both cases remove the elements of $O_u$ from $O$ and remove $u$ from $N'$.
--
--   **Formalization Note** The smallest set of Line 6 is given by a selection rule $\mathrm{sel}$, constrained in the lemmas by the minimum-removal property. The greedy choice uses the same tie rule as SampleGreedy.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 2, Lines 2–11, p. 9, and the tie-breaking rule of p. 10

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_cands
import Definitions.Def_SubsamplingSM_Offline_pick
import Definitions.Def_SubsamplingSM_Offline_Alg2State

namespace SubsamplingSM.Offline

/-- **One iteration of the while loop of Algorithm 2.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 2, Lines 2–11, p. 9: "while there exists an element `u ∈ N′` such that
`S + u ∈ I` and `f(u | S) > 0` do / Let `u ∈ N′` be the element of this kind maximizing
`f(u | S)`, and let `Su ← S`. / with probability `q` do / Add `u` to `S` and `O`. / Let
`Ou ⊆ O \ S` be the smallest set such that `O \ Ou ∈ I`. / otherwise / if `u ∈ O` then let
`Ou ← {u}`. / else let `Ou ← ∅`. / Remove the elements of `Ou` from `O`. / Remove `u` from
`N′`." Ties are broken by the fixed order of p. 10.

The coin flips are fixed in advance (p. 10: "we may assume for the sake of the proof that these
bits are chosen before the execution of the algorithms"): `u ∈ b` means `b_u = 1`. If there is
no candidate, the state is unchanged (the loop has terminated). Otherwise `u` is chosen by
`pick` (the same rule as in SampleGreedy), `S_u` is set to `S`, and

1. if `u ∈ b`: `u` is added to `S` and `O`, `O_u` is `sel (O ∪ {u}) (S ∪ {u})`, which is
   removed from `O`, and `u` is recorded in `Ys` when `u ∉ O` at the beginning of the
   iteration (`Y_u = 1`, p. 15);
2. if `u ∉ b`: `O_u = {u}` if `u ∈ O` and `O_u = ∅` otherwise, and `O_u` is removed from
   `O`;

and in both cases `u` is removed from `N′`.

**Formalization Note.** The smallest set of Line 6 is given by the selection rule `sel`, which
statements constrain by `IsMinRemoval` (paper.md generalization 8). -/
noncomputable def alg2Step {α : Type*} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (sel : Finset α → Finset α → Finset α) (b : Finset α)
    (st : Alg2State α) : Alg2State α :=
  if h : (cands f I st.N' st.S).Nonempty then
    let u := pick f st.S (cands f I st.N' st.S) h
    if u ∈ b then
      let S' := insert u st.S
      let O1 := insert u st.O
      let R := sel O1 S'
      { S := S', O := O1 \ R, N' := st.N'.erase u, Ou := Function.update st.Ou u R,
        Su := Function.update st.Su u st.S,
        Ys := if u ∉ st.O then insert u st.Ys else st.Ys }
    else
      let R : Finset α := if u ∈ st.O then {u} else ∅
      { S := st.S, O := st.O \ R, N' := st.N'.erase u, Ou := Function.update st.Ou u R,
        Su := Function.update st.Su u st.S, Ys := st.Ys }
  else st

end SubsamplingSM.Offline


