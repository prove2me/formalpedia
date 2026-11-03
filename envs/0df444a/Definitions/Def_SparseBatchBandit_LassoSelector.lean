-- Prove2me | Definitions.Def_SparseBatchBandit_LassoSelector
-- name    : SparseBatchBandit_LassoSelector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:30:07.557605+00:00
-- url     : https://prove2.me/theorems/c9f9f855-26b0-4478-8278-becaac0328f0
-- title:
--   Selection rule of the Lasso step
-- statement:
--   A selection rule assigns to each step $m$ and each pair (design on $T^{(m)}$, rewards on $T^{(m)}$) a vector of $\mathbb R^d$. The rounds of $T^{(m)}$ are listed in increasing order, so a design is a function on $\mathrm{Fin}\,|T^{(m)}|$. By its type the rule sees neither $\theta^\star$ nor the noise nor any round outside $T^{(m)}$.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_sample

namespace SparseBatchBandit

/-- A selection rule for the Lasso step of Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Algorithm 1, p.16 (PDF 16): at step `m` it reads
only the design and the rewards on `T^{(m)}` and returns a vector. The rounds of `T^{(m)}` are
listed in increasing order, so a design is indexed by `Fin |T^{(m)}|`. -/
def LassoSelector (T s₀ M d : ℕ) : Type :=
  (m : ℕ) → (Fin (sample T s₀ M m).card → Fin d → ℝ) → (Fin (sample T s₀ M m).card → ℝ) → Fin d → ℝ

end SparseBatchBandit


