-- Prove2me | Definitions.Def_MNLStability_IsSpaced
-- name    : MNLStability_IsSpaced
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:24.351644+00:00
-- url     : https://prove2.me/theorems/75b399d2-90d8-467f-aa4f-6d7fffcf09a0
-- title:
--   $(1+\varepsilon)$-spaced level sets and $\lfloor c\rfloor_H$
-- statement:
--   For a finite set $H$ of natural numbers, $\lfloor c\rfloor_H$ is the largest element of $H$ that is at most $c$.
--
--   A set $H$ is **$(1+\varepsilon)$-spaced in $[C]$ with $0$ added** when $H\subseteq\{0,1,\dots,C\}$, $0\in H$, and
--
--   $$\lfloor c\rfloor_H\ \ge\ \frac{c}{1+\varepsilon}\qquad\text{for every }c\in[C]=\{1,\dots,C\}.$$
--
--   Rounding inventory levels down into such a set loses at most a factor $1/(1+\varepsilon)$ per product (Lemma 7) and leaves only $O(\varepsilon^{-1}\log C)$ levels.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §4.2, p.19

import Mathlib

namespace MNLStability

/-- `⌊c⌋_H`, the largest element of `H` that is at most `c` (SSRN:3498325, §4.2, p.19), and `0` if
there is none. -/
def floorH (H : Finset ℕ) (c : ℕ) : ℕ := (H.filter (· ≤ c)).sup id

/-- `H` is a `(1 + ε)`-spaced subset of `[C]` with `0` added (SSRN:3498325, §4.2, p.19): `H ⊆ {0, …, C}`,
`0 ∈ H`, and `⌊c⌋_H ≥ c / (1 + ε)` for every `c ∈ [C] = {1, …, C}`. -/
def IsSpaced (ε : ℝ) (C : ℕ) (H : Finset ℕ) : Prop :=
  0 ∈ H ∧ (∀ h ∈ H, h ≤ C) ∧ ∀ c : ℕ, 1 ≤ c → c ≤ C → (c : ℝ) / (1 + ε) ≤ floorH H c

end MNLStability


