-- Prove2me | Definitions.Def_OnlineCRS_Combine_GreedyOCRS
-- name    : OnlineCRS_Combine_GreedyOCRS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:15:45.09161+00:00
-- url     : https://prove2.me/theorems/41ec212e-c74e-4b77-afcd-af49afb58f28
-- title:
--   Greedy OCRS (Definition 1.3)
-- statement:
--   Let $P\subseteq[0,1]^N$ be a relaxation for the feasible sets $\mathcal F\subseteq 2^N$. A **greedy OCRS** $\pi$ for $P$ fixes, for each input point $x$, a down-closed subfamily $\mathcal F_{\pi,x}\subseteq\mathcal F$, possibly at random; the elements then arrive one by one, and an active element is selected if, together with the elements already selected, it forms a set in $\mathcal F_{\pi,x}$. The OCRS is *randomized* if the choice of $\mathcal F_{\pi,x}$ is random and *deterministic* otherwise.
--
--   Here a greedy OCRS for $\mathcal F$ is given by the **law** of $\mathcal F_{\pi,x}$: for every $x$, a probability distribution on families of subsets of $N$ whose support consists of down-closed families $\mathcal G\subseteq\mathcal F$ with $\emptyset\in\mathcal G$. A deterministic greedy OCRS is one whose law at every $x$ is a point mass.
--
--   **Formalization Note**
--   1. The random choice of $\mathcal F_{\pi,x}$ depends on $x$ only and is independent of the active set $R(x)$ (it is made before any element is revealed); its law is all that selectability and efficiency depend on, so the online selection process itself is not modelled.
--   2. The law is defined for every $x\in\mathbb R^N$, not only $x\in P$; any paper OCRS extends this way (for instance with $\mathcal F_x=\{\emptyset\}$), and selectability and efficiency only evaluate it on $b\cdot P$ and $P$.
--   3. The relaxation $P$ is not part of the structure; statements carry "$P$ is a relaxation of $P_{\mathcal F}$" as a hypothesis or conclusion.
--   4. Every family in the support contains $\emptyset$ (a nonempty down-closed family). The greedy rule starts from the empty selection, and the paper reads selectability as a guarantee that $e$ is selected with probability at least $c$ (p. 3); with the empty family every element would be vacuously "selectable" while none is ever selected.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.3, p. 3

import Mathlib
import Definitions.Def_OnlineCRS_Combine_DownClosed

namespace OnlineCRS.Combine

/-- **Greedy OCRS (Definition 1.3), through the law of `F_{π,x}`.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.3, p. 3: "Let `P ⊆ [0,1]^N` be a relaxation for the feasible sets `F ⊆ 2^N`.
A greedy OCRS `π` for `P` is an OCRS that for any `x ∈ P` defines a down-closed subfamily of
feasible sets `F_{π,x} ⊆ F`, and an element `e` is selected when it arrives if, together with
the already selected elements, the obtained set is in `F_{π,x}`. If the choice of `F_{π,x}`
given `x` is randomized, we talk about a randomized greedy OCRS; otherwise, we talk about a
deterministic greedy OCRS."

A `GreedyOCRS F` is a map `law` sending each `x` to a probability distribution on families of
subsets of `N`, supported on nonempty (`∅ ∈ G`) down-closed subfamilies `G` of `F`: `law x` is
the law of `F_{π,x}`.
A deterministic greedy OCRS is one with `law x = PMF.pure F_x`.

**Formalization Note.**
* Reading 2: the random choice of `F_{π,x}` depends on `x` only and is independent of the active
  set `R(x)`; only its law matters for selectability and efficiency.
* Reading 5 (encoding): `law` is defined for every `x : N → ℝ`, not only for `x ∈ P`. A paper
  OCRS extends to all `x` (e.g. by `F_x = {∅}`); selectability and efficiency only evaluate `law`
  at `x ∈ b · P` and `x ∈ P`.
* Reading (nonempty family): each `F_{π,x}` contains `∅`, i.e. is a nonempty down-closed family.
  The greedy rule starts from the empty selection, and the paper reads selectability as "it
  guarantees that an element is selected with probability at least `c`" (p. 3); with the empty
  family `F_x = ∅` every element would be vacuously selectable (`χ_e(A, ∅, ∅)` holds) while none
  is ever selected, and Theorem 1.9's existential would be witnessed by that family alone.
* Reading 9 (encoding): the online selection process itself (order, irrevocable decisions,
  almighty adversary) is not modelled; it is determined by `F_x`.
* The relaxation `P` of Definition 1.3 is not a field: statements carry `IsRelaxation F P`
  as a hypothesis or conclusion. -/
structure GreedyOCRS {N : Type*} [DecidableEq N] (F : Finset (Finset N)) where
  /-- The law of the random down-closed family `F_{π,x}`, for each input `x`. -/
  law : (N → ℝ) → PMF (Finset (Finset N))
  /-- Every family in the support is down-closed, contains `∅`, and is contained in `F`. -/
  law_support : ∀ x, ∀ G ∈ (law x).support, DownClosed G ∧ ∅ ∈ G ∧ G ⊆ F

end OnlineCRS.Combine


