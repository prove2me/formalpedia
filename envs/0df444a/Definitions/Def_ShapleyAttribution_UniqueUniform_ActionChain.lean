-- Prove2me | Definitions.Def_ShapleyAttribution_UniqueUniform_ActionChain
-- name    : ShapleyAttribution_UniqueUniform_ActionChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:06.070628+00:00
-- url     : https://prove2.me/theorems/0758d083-8ab7-4fa0-806d-b7818de6881a
-- title:
--   §2.1 — finite action-dependent absorbing chain
-- statement:
--   An action-dependent finite Markov chain has transient states $\mathbb S=\{1,\ldots,m\}$, actions $\mathbb A=\{1,\ldots,n\}$, and two absorbing destinations: conversion $c$ and quit $q$. It specifies an initial-state distribution $\lambda$, action frequencies $\beta_s^a$, transitions $p^a_{ss'}$ among transient states, and exit probabilities $p^a_{sc}$ and $p^a_{sq}$.
--
--   Validity means $\lambda_s\ge0$ and $\sum_s\lambda_s=1$; for each $s$, $\beta_s^a\ge0$ and $\sum_a\beta_s^a=1$; and for every $(s,a)$ all transition probabilities are nonnegative and $\sum_{s'}p^a_{ss'}+p^a_{sc}+p^a_{sq}=1$. The average transient matrix is $P^\beta_{ss'}=\sum_a\beta_s^a p^a_{ss'}$. Absorption means $(P^\beta)^k\to0$ as $k\to\infty$, equivalently eventual exit from every transient state under these finite stochastic assumptions.
--
--   This chain is reusable independently of the attribution game. **Formalization Note** States and actions use `Fin m` and `Fin n`; paper index $k$ is Lean index $k-1$. All probabilities are real, with nonnegativity imposed by validity.
-- source:
--   Singal, Besbes, Desir, Goyal & Iyengar, Shapley Meets Uniform: An Axiomatic Framework for Attribution in Online Advertising, SSRN 3392721 (version of August 21, 2021), pp. 6–8, §2.1, Assumption 1

import Mathlib

namespace ShapleyAttribution.UniqueUniform

/-- A finite action-dependent absorbing-chain specification, before an attribution
game chooses which action-state pairs are players. -/
structure ActionChain (m n : ℕ) where
  lam : Fin m → ℝ
  β : Fin m → Fin n → ℝ
  P : Fin n → Fin m → Fin m → ℝ
  pc : Fin n → Fin m → ℝ
  pq : Fin n → Fin m → ℝ

/-- The initial distribution, action frequencies, and each transition row are
probability distributions. -/
def ActionChain.Valid {m n : ℕ} (C : ActionChain m n) : Prop :=
  (∀ s, 0 ≤ C.lam s) ∧ (∑ s, C.lam s) = 1 ∧
  (∀ s a, 0 ≤ C.β s a) ∧ (∀ s, (∑ a, C.β s a) = 1) ∧
  (∀ a s s', 0 ≤ C.P a s s') ∧ (∀ a s, 0 ≤ C.pc a s) ∧
  (∀ a s, 0 ≤ C.pq a s) ∧
  (∀ a s, (∑ s', C.P a s s') + C.pc a s + C.pq a s = 1)

/-- The averaged transient-state transition matrix. -/
def ActionChain.Pβ {m n : ℕ} (C : ActionChain m n) : Matrix (Fin m) (Fin m) ℝ :=
  fun s s' => ∑ a, C.β s a * C.P a s s'

/-- Absorption from every transient state, expressed by convergence of the
transient transition powers to zero. -/
def ActionChain.Absorbing {m n : ℕ} (C : ActionChain m n) : Prop :=
  Filter.Tendsto (fun k : ℕ => C.Pβ ^ k) Filter.atTop (nhds 0)

end ShapleyAttribution.UniqueUniform


