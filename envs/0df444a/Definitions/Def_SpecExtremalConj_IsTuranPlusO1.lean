-- Prove2me | Definitions.Def_SpecExtremalConj_IsTuranPlusO1
-- name    : SpecExtremalConj_IsTuranPlusO1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:11.824577+00:00
-- url     : https://prove2.me/theorems/7fcb2787-ddc1-4a83-a9df-289b34e6a3b2
-- title:
--   Hypothesis of Theorem 1.2: $\mathrm{Ex}(n,F)$ is $T_{n,r}$ plus $O(1)$ edges
-- statement:
--   Let $F$ be a graph and $r$ a natural number. Write $\mathrm{ex}(n,F)$ for the maximum number of edges of an $F$-free graph on $n$ vertices and $\mathrm{Ex}(n,F)$ for the set of $F$-free graphs on $n$ vertices with $\mathrm{ex}(n,F)$ edges.
--
--   **The graphs in $\mathrm{Ex}(n,F)$ are obtained from $T_{n,r}$ by adding $O(1)$ edges** if there are constants $A$ and $n_1$ such that for every $n\ge n_1$, every $H\in\mathrm{Ex}(n,F)$ contains a (relabelled) spanning copy of $T_{n,r}$ and
--
--   $$e(H)\le e(T_{n,r})+A.$$
--
--   This is the hypothesis of Theorem 1.2 and of Conjecture 1.1 (Cioabă–Desai–Tait).
--
--   **Formalization Note** $O(1)$ is read as a bound $A$ independent of $n$; the number of added edges may vary with $n$. "The graphs in $\mathrm{Ex}(n,F)$" is read as every member, for all $n$ beyond a threshold $n_1$. Membership in $\mathrm{Ex}(n,F)$ is Mathlib's `H.IsExtremal F.Free` on `Fin n`.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, Theorem 1.2, p. 2 ("the graphs in Ex(n, F) are obtained from T_{n,r} by adding O(1) edges"); Ex(n, F), ex(n, F): §1, p. 1

import Mathlib
import Definitions.Def_SpecExtremalConj_ContainsSpanningTuran
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **Hypothesis of Theorem 1.2: Ex(n, F) is T_{n,r} plus O(1) edges.** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, Theorem 1.2, p. 2:
"F be any graph such that the graphs in Ex(n, F) are obtained from T_{n,r} by adding O(1) edges".
Ex(n, F) is the set of n-vertex F-free graphs with ex(n, F) edges (p. 1).

`IsTuranPlusO1 F r` says: there are `A` and `n₁` such that for every `n ≥ n₁`, every extremal
`F`-free graph `H` on `Fin n` (Mathlib's `H.IsExtremal F.Free`) contains a spanning copy of
`turanGraph n r` and has at most `e(T_{n,r}) + A` edges.

**Formalization Note.** O(1) is read as a bound `A` independent of `n`: the number of added edges
may vary with `n`, which is the weakest hypothesis and hence the strongest theorem. "The graphs in
Ex(n, F)" is read as every member of Ex(n, F), for all large `n` (`n ≥ n₁`). -/
def IsTuranPlusO1 {W : Type*} (F : SimpleGraph W) (r : ℕ) : Prop :=
  ∃ A n₁ : ℕ, ∀ n ≥ n₁, ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H.IsExtremal F.Free →
    ContainsSpanningTuran r H ∧ #H.edgeFinset ≤ #(turanGraph n r).edgeFinset + A

end SpecExtremalConj


