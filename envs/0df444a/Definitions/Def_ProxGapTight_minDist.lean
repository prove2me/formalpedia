-- Prove2me | Definitions.Def_ProxGapTight_minDist
-- name    : ProxGapTight_minDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:17.800659+00:00
-- url     : https://prove2.me/theorems/3f5b2be5-e2f7-463e-991f-71ace7290779
-- title:
--   Minimum distance $d(C)$ of a linear code
-- statement:
--   Let $R$ be a semiring and $\iota$ a finite index set of size $n$. A **linear code** is a submodule $C\subseteq R^{\iota}$. For a word $x$, its Hamming weight $\mathrm{wt}(x)$ is the number of nonzero coordinates. The **minimum distance** of $C$ is
--   $$
--   d(C)=\min_{0\neq c\in C}\mathrm{wt}(c).
--   $$
--
--   It is the basic parameter of a code and enters the relative distance $\delta(C)=d(C)/n$, which is the quantity the mission's main theorem controls.
--
--   **Formalization Note** The minimum is the infimum of a set of natural numbers. For the zero code the set is empty and the infimum is $0$ by convention; the paper's $d(C)$ is undefined there, and every statement of the mission about a code it produces asserts that the code is nonzero.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §2, p.6, display

import Mathlib

namespace ProxGapTight

/-- **Minimum distance** `d(C) := min_{0≠c∈C} wt(c)` of a linear code, Kominers, Thaler, Zheng,
*The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes*, manuscript
(Sept. 2026), §2, p.6, display.

A code is a submodule `C` of `ι → R` (coordinates indexed by a finite type `ι`, length
`n = Fintype.card ι`); `wt` is Mathlib's `hammingNorm` (number of nonzero coordinates).

**Formalization Note.** The minimum is the natural-number `sInf` of the weights of the nonzero
codewords. For `C = ⊥` that set is empty and `sInf ∅ = 0`; the paper's `d(C)` is undefined there,
and every statement of this mission that uses `minDist` of a code it produces asserts `C ≠ ⊥`. -/
noncomputable def minDist {R ι : Type} [Semiring R] [DecidableEq R] [Fintype ι]
    (C : Submodule R (ι → R)) : ℕ :=
  sInf {w : ℕ | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = w}

end ProxGapTight


