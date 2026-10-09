-- Prove2me | Definitions.Def_WassTwoStage_Copositive_Cones
-- name    : WassTwoStage_Copositive_Cones
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:54:56.096995+00:00
-- url     : https://prove2.me/theorems/4c986596-1343-4feb-bf9c-52ebcb5b0a8f
-- title:
--   Strictly copositive matrices $M \succ_{\mathcal C} 0$ and the completely positive cone $\mathcal C^*$
-- statement:
--   Let $\iota$ be a finite index set and $M$ a real square matrix indexed by $\iota$. Vector inequalities are componentwise.
--
--   1. $M$ is **strictly copositive**, written $M \succ_{\mathcal C} 0$, if
--   $$v^\top M v > 0 \qquad \text{for every } v \in \mathbb R^{\iota}_+ \text{ with } v \neq 0.$$
--   2. $M$ is **completely positive**, written $M \succeq_{\mathcal C^*} 0$, if there is an entrywise nonnegative matrix $B \in \mathbb R^{\iota \times m}_+$, for some finite number $m$ of columns, with
--   $$M = BB^\top .$$
--
--   Together with the copositive cone $\mathcal C = \{M : \xi^\top M \xi \ge 0\ \forall \xi \ge 0\}$ (reused from the platform definition of copositivity), these are the cones in which the copositive programs (10), (24), (28) and the completely positive programs (14), (25) of Hanasusanto and Kuhn are posed, and in which Lemmas 3 and 4 are stated.
--
--   **Formalization Note** The paper calls $M \succ_{\mathcal C} 0$ membership in the interior of $\mathcal C$; on symmetric matrices this interior is exactly the set described in item 1, which is also the property the paper's proofs of Lemmas 3 and 4 establish. The paper fixes $m = g(K) = \max\{\binom{K+1}{2} - 4, K\}$ columns; allowing any finite $m$ gives the same cone (the paper's reference [50]) and matches the "finite index set $\mathcal L_i$" of decomposition (16). A product $BB^\top$ is automatically symmetric.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 5 (Notation: C, C*), p. 15 (Lemma 3: ≻_C, interior of C)

import Mathlib

namespace WassTwoStage.Copositive

open Matrix

/-- Strict copositivity, Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 15 (Lemma 3 and its proof):
`M ≻_C 0` means that `M` lies in the interior of the copositive cone
`C = {M ∈ 𝕊^K : ξᵀMξ ≥ 0 ∀ ξ ≥ 0}` (Notation, p. 5). On symmetric matrices this interior is
exactly the set of matrices with `vᵀMv > 0` for every nonzero `v ≥ 0`, which is the property
the paper's proofs of Lemmas 3 and 4 establish ("This implies that `WWᵀ` lies in the interior of
the copositive cone"); that property is the definition used here. -/
def StrictlyCopositive {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ v : ι → ℝ, 0 ≤ v → v ≠ 0 → 0 < v ⬝ᵥ (M *ᵥ v)

/-- The completely positive cone, Hanasusanto–Kuhn, arXiv:1609.07505v3, Notation, p. 5:
`C* = {M ∈ 𝕊^K : M = BBᵀ for some entrywise nonnegative B}`. The paper fixes the number of
columns of `B` to `g(K) = max{binom(K+1,2) − 4, K}`; any finite number of columns gives the same
cone (a sum of finitely many nonnegative rank-one matrices can be rewritten with `g(K)` of them,
the paper's reference [50]), and the proofs work with "a finite index set `L_i`" (eq. (16),
p. 11). Here `B` may have any finite number `m` of columns. Every `BBᵀ` is symmetric, so the
symmetry requirement of `𝕊^K` is automatic. -/
def CompletelyPositive {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∃ (m : ℕ) (B : Matrix ι (Fin m) ℝ), (∀ a b, 0 ≤ B a b) ∧ M = B * Bᵀ

end WassTwoStage.Copositive


