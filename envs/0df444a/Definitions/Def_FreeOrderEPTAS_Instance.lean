-- Prove2me | Definitions.Def_FreeOrderEPTAS_Instance
-- name    : FreeOrderEPTAS_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:34.682484+00:00
-- url     : https://prove2.me/theorems/b8ec6ee8-203a-4669-b299-4b048a306e43
-- title:
--   An instance of Free-Order Prophets
-- statement:
--   An instance of **Free-Order Prophets** is a family of $n$ independent random variables $X_1,\dots,X_n$, given by their laws $\mu_1,\dots,\mu_n$. Each $\mu_i$ is a probability measure on $\mathbb R$ carried by $[0,\infty)$ with a finite mean.
--
--   The goal of the problem is to choose an inspection order and a stopping rule so as to maximize the expected value of the variable at which one stops. Every statement of the mission is about such an instance.
--
--   **Formalization Note** Independence is not a field: the values are the coordinates under the product measure `Measure.pi μ`. Variables are indexed by `Fin n`.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.1, p.16; non-negative variables, §1, p.3

import Mathlib

open MeasureTheory

namespace FreeOrderEPTAS

/-- An instance of Free-Order Prophets (Segev & Singla, arXiv:2007.13121v3, §3.1, p.16, with the
non-negative variables of §1, p.3): the laws `μ i` of `n` independent random variables `X_i`.

**Formalization Note.** Each `μ i` is a probability measure on `ℝ` carried by `[0, ∞)` with a finite
mean. Independence is not a field: the values are the coordinates under `Measure.pi μ`. -/
structure Instance (n : ℕ) where
  /-- The law of `X_i`. -/
  μ : Fin n → Measure ℝ
  /-- Each law is a probability measure. -/
  prob : ∀ i, IsProbabilityMeasure (μ i)
  /-- `X_i ≥ 0` almost surely. -/
  nonneg : ∀ i, μ i (Set.Iio 0) = 0
  /-- `X_i` has a finite mean. -/
  integrable : ∀ i, Integrable id (μ i)

attribute [instance] Instance.prob

end FreeOrderEPTAS


