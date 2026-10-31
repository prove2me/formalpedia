-- Prove2me | Definitions.Def_AdaDiscRL_encounters
-- name    : AdaDiscRL_encounters
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:54.023622+00:00
-- url     : https://prove2.me/theorems/70404c6f-2dd8-4871-af01-bbee786459ce
-- title:
--   Encounter episodes $k_1<\dots<k_t$ of a ball and its ancestors
-- statement:
--   For a ball $B$, a step $h$ and an episode $k$, the **encounter episodes** $k_1<\dots<k_t\le k$ are the episodes at which $B$ or one of its ancestors was the selected ball $B^{j}_h$ at step $h$. `selAt … j h` is $B^j_h$ and `encEp … i` is $k_{i+1}$.
--
--   These index the weighted sums in Lemmas 3.2, B.3, C.1, C.3 and D.1–D.2.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma 3.2, p.18; Lemma B.3, p.38; Lemma C.1, p.39

import Mathlib
import Definitions.Def_AdaDiscRL_AlgState

namespace AdaDiscRL

open Classical

variable {S A ι : Type*} [MeasurableSpace S] [MeasurableSpace A]
  {D : S × A → S × A → ℝ} {dS Lmax H : ℕ}

/-- The episodes `k₁ < ⋯ < k_t ≤ k` at which the ball `B` or one of its ancestors was selected at
step `h` (arXiv:2110.15843v3, Lemma 3.2, p.18; Lemmas B.3, C.1, p.38–39): the `j ∈ {1, …, k}` with
`B_h^j` an ancestor of `B` or `B` itself, where `B_h^j` is selected with the state `alg data (j−1)`
and the state `X_h^j`. -/
noncomputable def encounters (P : HierPartition S A ι D dS Lmax)
    (choose : Finset ι → (ι → ℝ) → ι) (alg : (ℕ → EpData S A H) → ℕ → AlgState S ι H)
    (data : ℕ → EpData S A H) (k : ℕ) (h : Fin H) (B : ι) : Finset ℕ :=
  (Finset.Icc 1 k).filter (fun j =>
    P.IsAncestorOrSelf (selBall P choose (alg data (j - 1)) h ((data j).1 h.castSucc)) B)

/-- The `i`-th encounter episode `k_{i+1}` (0-based `i`), in increasing order. -/
noncomputable def encEp (P : HierPartition S A ι D dS Lmax)
    (choose : Finset ι → (ι → ℝ) → ι) (alg : (ℕ → EpData S A H) → ℕ → AlgState S ι H)
    (data : ℕ → EpData S A H) (k : ℕ) (h : Fin H) (B : ι)
    (i : Fin (encounters P choose alg data k h B).card) : ℕ :=
  (encounters P choose alg data k h B).orderEmbOfFin rfl i

/-- The ball selected at step `h` of episode `j`, `B_h^j`. -/
noncomputable def selAt (P : HierPartition S A ι D dS Lmax)
    (choose : Finset ι → (ι → ℝ) → ι) (alg : (ℕ → EpData S A H) → ℕ → AlgState S ι H)
    (data : ℕ → EpData S A H) (j : ℕ) (h : Fin H) : ι :=
  selBall P choose (alg data (j - 1)) h ((data j).1 h.castSucc)

end AdaDiscRL


