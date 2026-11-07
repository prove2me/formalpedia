-- Prove2me | Definitions.Def_DynHaussler_rank
-- name    : DynHaussler_rank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:48.751533+00:00
-- url     : https://prove2.me/theorems/f9f9d663-7c38-42c5-9365-92aaeaadad1f
-- title:
--   Rank $\mathrm{sfat}_\eta(V)$ with the convention $\mathrm{sfat}_\eta(\emptyset)=-1$
-- statement:
--   Let $X$ be a set, $\eta\in\mathbb R$ and $V\subseteq\mathbb R^X$ a class of functions. The **rank** of $V$ at scale $\eta$ is its sequential fat-shattering dimension (Definition 3), with the paper's convention for the empty class:
--   $$
--   \operatorname{rank}_\eta(V)=\begin{cases}\mathrm{sfat}_\eta(V), & V\neq\emptyset,\\ -1, & V=\emptyset.\end{cases}
--   $$
--   Here $\mathrm{sfat}_\eta(V)\in\{0,1,2,\dots\}\cup\{\infty\}$ is the largest depth of an instance tree that $V$ sequentially fat-shatters at scale $\eta$ (margin $\eta/2$ around a node-dependent threshold), and $\infty$ if these depths are unbounded.
--
--   The rank is the potential that every correction step of the paper's schedule construction decreases (Lemmas 11–13); the value $-1$ for the empty class is what makes "rank at most $r-1$" force emptiness when $r=0$.
--
--   **Formalization Note** The published `NondualOpt.sfat` gives the empty class the value $0$. This wrapper is valued in `WithBot ℕ∞`: it is $\bot$ (playing $-1$) on the empty class and `NondualOpt.sfat V η` on a nonempty class. Two structural lemmas record both cases.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Definition 3, p.13 (PDF p.15); "The rank of a class V means sfat_η(V)", Section 4.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

namespace DynHaussler

/-- The **rank** of a class `V ⊆ [0,1]^X` at scale `η`: its sequential fat-shattering dimension
`sfat_η(V)` (Definition 3), with the paper's convention `sfat_η(∅) = −1`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Definition 3, p.13 (PDF p.15): "A nonempty class has dimension at least zero; we set
`sfat_η(∅) = −1`"; "The rank of a class `V` means `sfat_η(V)`", Section 4.1, p.18 (PDF p.20).

**Formalization Note** The published `NondualOpt.sfat` gives the empty class the value `0`. This
wrapper restores the paper's `−1`: it is `⊥` on the empty class and `sfat_η(V)` (in `ℕ∞`, with
`⊤` for unbounded depths) on a nonempty class. So `⊥` plays the role of `−1`, and "rank at most
`r − 1`" for an integer `r ≥ 0` reads `rank η V < r`. -/
noncomputable def rank {X : Type*} (η : ℝ) (V : Set (X → ℝ)) : WithBot ℕ∞ :=
  open Classical in
  if V.Nonempty then ((NondualOpt.sfat V η : ℕ∞) : WithBot ℕ∞) else ⊥

theorem rank_empty {X : Type*} (η : ℝ) : rank η (∅ : Set (X → ℝ)) = ⊥ := by
  simp [rank]

theorem rank_of_nonempty {X : Type*} (η : ℝ) {V : Set (X → ℝ)} (hV : V.Nonempty) :
    rank η V = ((NondualOpt.sfat V η : ℕ∞) : WithBot ℕ∞) := by
  simp [rank, hV]

end DynHaussler


