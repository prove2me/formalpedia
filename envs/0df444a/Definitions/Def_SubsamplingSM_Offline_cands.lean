-- Prove2me | Definitions.Def_SubsamplingSM_Offline_cands
-- name    : SubsamplingSM_Offline_cands
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:48:35.016926+00:00
-- url     : https://prove2.me/theorems/20ccaf2f-fa6b-406f-b225-c3ec9883568b
-- title:
--   Candidate set of the greedy while-test
-- statement:
--   Given a set function $f$, a collection $\mathcal I$, a pool $T\subseteq N$ and a current solution $S$, the **candidates** are the elements of the pool that can be added feasibly and with positive gain:
--   $$C(T,S)=\{u\in T : S\cup\{u\}\in\mathcal I \text{ and } f(u\mid S)>0\}.$$
--
--   This is the condition of the while loop of SampleGreedy (Algorithm 1, Line 6, with $T=N'$) and of Algorithm 2 (Line 2, with $T$ the set $N'$ of elements not yet considered). The loop runs while $C(T,S)\neq\emptyset$. Elements of $S$ are never candidates, since their marginal gain is $0$.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 1, Line 6, and Algorithm 2, Line 2, p. 9

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_marg

namespace SubsamplingSM.Offline

open Classical in
/-- **Candidate set of the greedy while-test.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 1, Line 6, p. 9: "while there exists `u ∈ N′` such that `S + u ∈ I` and
`f(u | S) > 0` do"; the same test is Line 2 of Algorithm 2, p. 9.

`cands f I T S = {u ∈ T : S ∪ {u} ∈ I and f(u | S) > 0}`, where `T` is the current pool
(`N′`). Elements of `S` are excluded automatically, since their marginal gain is `0`.

**Formalization Note.** Decidability of `I` and of `<` on `ℝ` is classical. -/
noncomputable def cands {α : Type*} [DecidableEq α] (f : Finset α → ℝ) (I : Finset α → Prop)
    (T S : Finset α) : Finset α :=
  T.filter (fun u => I (insert u S) ∧ 0 < marg f S u)

end SubsamplingSM.Offline


