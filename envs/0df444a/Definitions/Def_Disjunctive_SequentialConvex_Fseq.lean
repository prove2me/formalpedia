-- Prove2me | Definitions.Def_Disjunctive_SequentialConvex_Fseq
-- name    : Disjunctive_SequentialConvex_Fseq
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:24:39.417988+00:00
-- url     : https://prove2.me/theorems/b627782c-bb77-4b81-a46b-f6532a0ec2d0
-- title:
--   The sequential-convexification recursion $F_j$
-- statement:
--   This definition builds the "partial convex hull" recursion Theorem 3.1 is about: imposing the
--   disjunctions of a disjunctive program one at a time.
--
--   Fix an ordering of $S$, given as a bijection $\sigma : \{0,\dots,|S|-1\} \to S$. Define
--   $F_0$ (step zero) to be the base polyhedron itself, and recursively, for $k =
--   0,\dots,|S|-1$,
--
--   $$
--   F_{k+1} := \mathrm{conv}\Big[\bigcup_{i \in Q_{\sigma(k)}} \big(F_k \cap \{x : d_i x \ge
--   d_{i0}\}\big)\Big],
--   $$
--
--   imposing the $\sigma(k)$-th disjunction and taking the convex hull of the resulting union.
--   Theorem 3.1 asks whether $F_{|S|}$, built this way, equals the convex hull of the *whole*
--   constraint set $F$ imposed all at once.
--
--   **Formalization Note.** `Fseq` is total on all of `ℕ` for definitional convenience (steps past
--   `|S|` are held constant); Theorem 3.1's claim is only about the value at `Fintype.card S`. The
--   ordering `σ` is a parameter of `Fseq` itself, not fixed once and for all, so that Theorem 3.1
--   can quantify over an arbitrary choice of it.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 42, Theorem 3.1

import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic

namespace Disjunctive.SequentialConvex

/-- The recursive sequential-convexification construction `F_j` (Balas §3.1, p. 42, Theorem 3.1):
`F_0 := F₀`, and for `j = 1, …, |S|` (given an arbitrary ordering `σ` of `S`), `F_j := conv[⋃_{i ∈
Q_{σ(j-1)}} (F_{j-1} ∩ {x : d_i x ≥ d_{i0}})]`. Steps past `|S|` leave the set unchanged. -/
def Fseq {n : ℕ} {S : Type*} [Fintype S] (Qidx : S → Type*) [∀ j, Fintype (Qidx j)]
    (F0 : Set (Fin n → ℝ)) (d : (j : S) → Qidx j → Fin n → ℝ) (d0 : (j : S) → Qidx j → ℝ)
    (σ : Fin (Fintype.card S) ≃ S) : ℕ → Set (Fin n → ℝ)
  | 0 => F0
  | k + 1 =>
    if h : k < Fintype.card S then
      convexHull ℝ
        (⋃ i : Qidx (σ ⟨k, h⟩),
          Fseq Qidx F0 d d0 σ k ∩ HalfspaceGE (d (σ ⟨k, h⟩) i) (d0 (σ ⟨k, h⟩) i))
    else
      Fseq Qidx F0 d d0 σ k

end Disjunctive.SequentialConvex


