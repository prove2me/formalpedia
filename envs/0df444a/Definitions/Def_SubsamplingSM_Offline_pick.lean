-- Prove2me | Definitions.Def_SubsamplingSM_Offline_pick
-- name    : SubsamplingSM_Offline_pick
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:49:03.822248+00:00
-- url     : https://prove2.me/theorems/00cb4483-8295-412d-adfd-75285a700a61
-- title:
--   Greedy choice with ties broken by a fixed order
-- statement:
--   Let the ground set be ordered, $N=\{u_1,\dots,u_n\}$. For a nonempty candidate set $C$ and a current solution $S$, the **greedy choice** is the element of $C$ maximizing $f(u\mid S)$; when several elements attain the maximum, the one appearing earliest in the order is taken:
--   $$\operatorname{pick}(S,C)=\min\Big\{u\in C : f(u\mid S)=\max_{v\in C}f(v\mid S)\Big\}.$$
--
--   SampleGreedy (Line 7) and Algorithm 2 (Line 3) both use this rule, which is the tie-breaking assumption under which the paper proves that the two algorithms are equivalent.
--
--   **Formalization Note** The order of the ground set is the `LinearOrder α` instance, and every statement quantifies over an arbitrary one.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 1, Line 7, p. 9, and the tie-breaking rule of p. 10

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_marg

namespace SubsamplingSM.Offline

open Classical in
/-- **The greedy choice with ordered tie-breaking.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 1, Line 7, p. 9: "Let `u ∈ N′` be the element of this kind maximizing
`f(u | S)`" (likewise Algorithm 2, Line 3), with the tie rule of p. 10: "suppose that the
ground set is (arbitrarily) ordered `N = {u1, u2 . . . un}` and that both algorithms break ties
in favor of the element appearing earlier in this order."

For a nonempty set `C` of candidates, `pick f S C hC` is the earliest element, in the linear
order of `α`, among the elements of `C` whose marginal gain `f(u | S)` equals the maximum
over `C`.

**Formalization Note.** The ordering of the ground set is the `LinearOrder α` instance; every
statement quantifies over an arbitrary one (paper.md Reading 2). Algorithm 1 and Algorithm 2 use
this same helper, as Lemma 4 requires. -/
noncomputable def pick {α : Type*} [LinearOrder α] (f : Finset α → ℝ) (S C : Finset α)
    (hC : C.Nonempty) : α :=
  (C.filter (fun u => marg f S u = C.sup' hC (marg f S))).min' (by
    obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hC (marg f S)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, he.symm⟩⟩)

end SubsamplingSM.Offline


