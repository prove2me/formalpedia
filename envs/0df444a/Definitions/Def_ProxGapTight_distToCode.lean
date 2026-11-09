-- Prove2me | Definitions.Def_ProxGapTight_distToCode
-- name    : ProxGapTight_distToCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:27.656483+00:00
-- url     : https://prove2.me/theorems/7e66d60f-515a-41fc-9699-acae20c8d4c5
-- title:
--   Relative distance $\delta(x,C)$ of a word to a code
-- statement:
--   For a linear code $C\subseteq R^{\iota}$ of length $n$ and a word $x\in R^{\iota}$, the **relative distance of $x$ to $C$** is
--   $$
--   \delta(x,C)=\frac1n\min_{c\in C}\mathrm{wt}(x-c),
--   $$
--   the smallest fraction of coordinates in which $x$ differs from a codeword.
--
--   This is the notion of closeness in the proximity-gaps property: a word is $\rho$-close to $C$ when $\delta(x,C)\le\rho$.
--
--   **Formalization Note** $\mathrm{wt}(x-c)$ is the Hamming distance between $x$ and $c$. The minimum is the infimum of a nonempty set of natural numbers (it contains $\mathrm{wt}(x-0)$), so it is attained.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §2, p.6, display

import Mathlib

namespace ProxGapTight

/-- **Relative distance of a word to a code** `δ(x, C) := (1/n) min_{c∈C} wt(x − c)`, Kominers,
Thaler, Zheng, manuscript (Sept. 2026), §2, p.6, display.

**Formalization Note.** `wt(x − c)` is the Hamming distance `hammingDist x c`. The minimum is the
natural-number `sInf` of these distances; the set is nonempty because `0 ∈ C`, so the `sInf` is
attained and equals the paper's minimum. The result is divided by `n = Fintype.card ι` in `ℝ`. -/
noncomputable def distToCode {R ι : Type} [Semiring R] [DecidableEq R] [Fintype ι]
    (x : ι → R) (C : Submodule R (ι → R)) : ℝ :=
  (sInf {w : ℕ | ∃ c ∈ C, hammingDist x c = w} : ℕ) / (Fintype.card ι : ℝ)

end ProxGapTight


