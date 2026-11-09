-- Prove2me | Definitions.Def_AgnosticTNS_IsRootedSubtreeSeq
-- name    : AgnosticTNS_IsRootedSubtreeSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:19.900201+00:00
-- url     : https://prove2.me/theorems/9526895c-d90a-4b5a-b629-02cb522b59cf
-- title:
--   Rooted-subtree learning sequence of a tree
-- statement:
--   A learning sequence is a **rooted-subtree learning sequence** of a tree $T$ rooted at $\ell$ if its steps correspond bijectively to the vertices, step $k$ introduces its vertex $v_k$ ($F_k=\{v_k\}$), $S_k$ is the subtree of $v_k$ (the vertices whose path to $\ell$ passes through $v_k$), and the children of step $k$ are the steps of the children of $v_k$. Steps are processed from the leaves towards the root; every such order is allowed.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.8, p.25; proof of Corollary 5.1, p.39

import Mathlib
import Definitions.Def_AgnosticTNS_LearningSequence

namespace AgnosticTNS

/-- **The rooted-subtree learning sequence of a tree**, Proposition 3.8, p.25, and the proof of
Corollary 5.1, p.39 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): root `T` at `ℓ`; there is one step per vertex (`σ` maps steps to
vertices), step `k` introduces its vertex (`F_k = {σ k}`), `S_k` is the subtree of `σ k`
(the vertices `u` with `σ k` on the path from `ℓ` to `u`), and the children `I_k` are the steps of the
children of `σ k`. Any processing order allowed by Definition 2.3 (leaves towards the root) is
covered. -/
def IsRootedSubtreeSeq {n : ℕ} (T : SimpleGraph (Fin n)) (ℓ : Fin n) (Ls : LearningSequence n) :
    Prop :=
  ∃ σ : Fin Ls.L ≃ Fin n, ∀ k : Fin Ls.L,
    Ls.F k = {σ k} ∧
    (∀ u, u ∈ Ls.S k ↔ T.dist ℓ u = T.dist ℓ (σ k) + T.dist (σ k) u) ∧
    ∀ j, j ∈ Ls.I k ↔ (T.Adj (σ k) (σ j) ∧ T.dist ℓ (σ j) = T.dist ℓ (σ k) + 1)

end AgnosticTNS


