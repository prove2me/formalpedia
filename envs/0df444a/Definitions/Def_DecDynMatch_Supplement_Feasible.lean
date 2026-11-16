-- Prove2me | Definitions.Def_DecDynMatch_Supplement_Feasible
-- name    : DecDynMatch_Supplement_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:23:08.823193+00:00
-- url     : https://prove2.me/theorems/694c2b3d-bb57-401a-a1cb-541ebed17957
-- title:
--   Feasible growth function $g$ (non-decreasing, positive, $g(t)=\Omega(t)$)
-- statement:
--   A function $g:\mathbb N\to\mathbb N$ is **feasible** if
--
--   1. $g(t)\ge 1$ for every integer $t\ge 1$;
--   2. $g$ is non-decreasing on the positive integers: $g(s)\le g(t)$ whenever $1\le s\le t$;
--   3. $g(t)=\Omega(t)$: there are $c>0$ and $t_0$ with $c\,t\le g(t)$ for all $t\ge t_0$.
--
--   Feasible functions are the growth rates of the replay rules $F_g$ (eq. (5)) of the protocol family $\Pi_g$; examples are $g(t)=t$ (SC-DA), $t\log t$ and $t^\alpha$ with $\alpha>1$.
--
--   **Formalization Note** The paper also requires $g$ to be polynomial-time computable; no bound uses this (it only serves the running time of evaluating $F_g$), so it is not required here and every feasible function in the paper's sense satisfies this predicate. The value $g(0)$ is unconstrained and never read.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), §3.2, p.8; App. A.5, p.20

import Mathlib

namespace DecDynMatch.Supplement

/-- **Feasible growth function.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), §3.2, p.8: "let function g : ℕ≥1 → ℕ≥1 be
non-decreasing and polynomial-time computable, with g(t) = Ω(t). We call such a function
feasible."

`Feasible g` says: `g t ≥ 1` for every `t ≥ 1`; `g` is non-decreasing on the positive integers;
and `g(t) = Ω(t)`, i.e. there are `c > 0` and `t₀` with `c·t ≤ g t` for all `t ≥ t₀`.

**Formalization Note.**
* `g : ℕ → ℕ`; its value at `0` is unconstrained and never read (the sequence `s_j` of eq. (5)
  starts at `s₀ = H ≥ 1` and every argument of `g` in the paper is a positive integer).
* Polynomial-time computability is **not** required: no bound of the paper uses it (App. A.5, p.21,
  uses it only for the running time of evaluating `F_g`). Every feasible function in the paper's
  sense satisfies this predicate. -/
def Feasible (g : ℕ → ℕ) : Prop :=
  (∀ t, 1 ≤ t → 1 ≤ g t) ∧ (∀ s t, 1 ≤ s → s ≤ t → g s ≤ g t) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → c * (t : ℝ) ≤ (g t : ℝ)

end DecDynMatch.Supplement


