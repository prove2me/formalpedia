-- Prove2me | Definitions.Def_GeoSemialgCSP_msWeight
-- name    : GeoSemialgCSP_msWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:56.750783+00:00
-- url     : https://prove2.me/theorems/f4d015e9-f844-45b7-bfa5-40d00061de3c
-- title:
--   Weights of the multiscale template $\tilde I$
-- statement:
--   On the leaves of the complete ordered $k$-ary tree of height $h$, the **multiscale template** $\tilde I$ (Guruswami–Håstad–Manokaran–Raghavendra–Charikar) gives each ordered $k$-tuple of leaves the probability that the following process outputs it: choose a depth $p$ uniformly in $\{0,\dots,h-1\}$, then a node $u$ uniformly among the $k^p$ nodes at that depth; let $u_1,\dots,u_k$ be its children in order, and independently choose $a_j$ uniformly among the $k^{h-1-p}$ leaves below $u_j$. A tuple output from depth $p$ has weight
--   $$\frac1h\cdot k^{-p}\cdot\bigl(k^{-(h-1-p)}\bigr)^k .$$
--
--   Every tuple of positive weight consists of distinct leaves that are cousins. For $h\ge1$ the weights sum to $1$.
--
--   **Formalization Note** A tuple can be output from at most one depth (the first position where the words differ), so the weight is a sum over depths with at most one nonzero term. For $h=0$ all weights are $0$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.1, p.10 (PDF p.11)

import Mathlib

namespace GeoSemialgCSP

open Classical in
/-- **Weights of the multiscale template `Ĩ`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.1, printed p.10 (PDF p.11): choose a
depth uniformly from `{0, …, h−1}`, then a node `u` uniformly at that depth; let `u₁, …, u_k` be its
children in order, and independently choose `a_j` uniformly among the leaves below `u_j`. The
weight of a tuple of leaves is the probability that this process outputs it.

**Formalization Note.** Leaves are words `Fin h → Fin k`. A tuple is output from depth `p` iff all
words agree before position `p` and word `i` has letter `i` at `p`; that depth is unique. Its
probability is `(1/h)·k^{−p}·(k^{−(h−1−p)})^k`. For `h = 0` all weights are `0`. -/
noncomputable def msWeight {k : ℕ} (h : ℕ) (l : Fin k → (Fin h → Fin k)) : ℝ :=
  ∑ p : Fin h,
    if (∀ i j : Fin k, ∀ s : Fin h, s < p → l i s = l j s) ∧ (∀ i, l i p = i) then
      (1 / (h : ℝ)) * (1 / (k : ℝ)) ^ (p : ℕ) * ((1 / (k : ℝ)) ^ (h - 1 - (p : ℕ))) ^ k
    else 0

end GeoSemialgCSP


