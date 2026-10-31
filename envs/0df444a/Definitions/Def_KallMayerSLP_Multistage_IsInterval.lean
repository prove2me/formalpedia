-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_IsInterval
-- name    : KallMayerSLP_Multistage_IsInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:59.193988+00:00
-- url     : https://prove2.me/theorems/15982845-5098-4419-9281-f29e416cfbca
-- title:
--   Interval of $\mathbb R^k$
-- statement:
--   A subset of $\mathbb R^k$ is an **interval** if it is a product $I_1\times\dots\times I_k$ of one-dimensional intervals.
--
--   The book bounds the distributions within intervals $\Xi^t\subset\mathbb R^{r_t}$ and partitions them into subintervals.
--
--   **Formalization Note** Each factor is an order-connected subset of $\mathbb R$, so open, closed and half-open factors are allowed: a partition into disjoint subintervals needs half-open ones, as in the book's Example 3.1 with $[0,\tfrac12)$ and $[\tfrac12,1]$. The empty set counts as an interval.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, p.261 (PDF 270); half-open cells p.259 (PDF 268)

import Mathlib

namespace KallMayerSLP.Multistage

/-- An **interval** of `ℝ^k`, the book's word for a product of one-dimensional intervals (Kall &
Mayer, *Stochastic Linear Programming* (2005), Chapter 3, p.261, PDF 270: "intervals
`Ξ^t ⊂ ℝ^{r_t}`", "a partition of `Ξ^{ν+1}` into subintervals").

**Formalization Note.** Each factor is an order-connected subset of `ℝ`: open, closed and half-open
factors are all allowed, because a partition into disjoint subintervals needs half-open ones (the
book's own Example 3.1 uses `[0, 1/2)` and `[1/2, 1]`, p.259, PDF 268). The empty set counts as an
interval. -/
def IsInterval {k : ℕ} (S : Set (Fin k → ℝ)) : Prop :=
  ∃ I : Fin k → Set ℝ, (∀ i, (I i).OrdConnected) ∧ S = Set.univ.pi I

end KallMayerSLP.Multistage


