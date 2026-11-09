-- Prove2me | Definitions.Def_GevreyGibbsSep_Answer
-- name    : GevreyGibbsSep_Answer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:48.848317+00:00
-- url     : https://prove2.me/theorems/f4ebfaa8-e829-4530-9157-0dcfd5c6c077
-- title:
--   Answer space of the derivative oracles
-- statement:
--   An oracle answer lists, for every order $j\ge0$ and every tuple of coordinates $(i_1,\dots,i_j)$, a real number: the entry $\partial_{i_1}\cdots\partial_{i_j}\log\bar p(x)$ of the derivative tensor $\nabla^{\otimes j}\log\bar p(x)$.
--
--   **Formalization Note** One answer space serves every order $k\in\mathbb N\cup\{\infty\}$: an order-$k$ answer has its entries of order $j>k$ equal to $0$. The space carries the product Borel $\sigma$-algebra.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.2, Eq. (B2), p.34

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The answer space of the derivative oracles (arXiv:2608.24527 (sha256 d4fd40eb…),
Definition B.2, Eq. (B2), p.34): for every order `j` and every index tuple `(i₁, …, iⱼ)` a real
number, the entry `∂_{i₁} ⋯ ∂_{iⱼ} log p̄(x)` of `∇^{⊗j} log p̄(x)`.

**Formalization Note** One type for every order `k`: an order-`k` answer has its entries of
order `j > k` set to `0`. It carries the product Borel σ-algebra. -/
abbrev Answer (d : ℕ) : Type := (j : ℕ) → (Fin j → Fin d) → ℝ

end GevreyGibbsSep


