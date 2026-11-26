-- Prove2me | Definitions.Def_StreamSubmod_Supplement_IsRounding
-- name    : StreamSubmod_Supplement_IsRounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:42:45.925195+00:00
-- url     : https://prove2.me/theorems/8dbf477a-21a9-551a-9cd9-bff16e43d8e6
-- title:
--   A rounding procedure for line 4 of Algorithm 3
-- statement:
--   Let $V$ be a finite ground set, $f:2^V\to\mathbb R$ and $k$ a natural number. A (randomized) rounding procedure is given by a finite set of seeds $\Omega'$ with probabilities $\nu(\omega')$ and a map $R$ assigning to every seed $\omega'$ and every vector $x$ a set $R(\omega',x)\subseteq V$. It is a rounding procedure for $f$ and $k$ if $\nu$ is a probability vector and, for every $x\in[0,1]^V$ with $\|x\|_1\le k$:
--
--   1. every $R(\omega',x)$ has at most $k$ elements;
--   2. every $R(\omega',x)$ lies in $\operatorname{supp}(x)$;
--   3. the expected value is at least the value of the multilinear extension:
--
--   $$
--   \sum_{\omega'}\nu(\omega')\,f\bigl(R(\omega',x)\bigr)\ \ge\ F(x).
--   $$
--
--   Line 4 of Algorithm 3 produces its set $S_1$ with such a procedure; Pipage Rounding and Swap Rounding are examples. The results about Algorithm 3 hold for every rounding procedure with these properties.
--
--   **Formalization Note** Requirement 2 is taken from the proof of Observation 21, where the algorithm needs access only to the elements of $\operatorname{supp}(x)$ to calculate $S_1$ and $S_2$.
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Algorithm 3, line 4, and the paragraph before it, p.22; proof of Observation 21, p.23

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_StreamSubmod_Supplement_Basic

namespace StreamSubmod.Supplement

open NonmonotoneSubmod.Shared

/-- `R` is a rounding procedure for `f` under the cardinality constraint `k`, as used in line 4 of
Algorithm 3 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, Algorithm 3, line 4, p.22:
"Round the vector `x` to yield a feasible solution `S₁` such that `E[f(S₁)] ≥ F(x)`"; p.22: the
rounding procedures of [13, 18] "guarantee that the output set `S₁` of the rounding is always
feasible, and that its expected value with respect to `f` is at least the value `F(x)` of the
fractional solution `x`"; proof of Observation 21, p.23: "To calculate the sets `S₁` and `S₂`,
Algorithm 3 needs access only to the elements of `V` that appear in the support of `x`").

**Formalization Note.** The randomness of the rounding is a finite seed type `Ω'` with the
probability vector `ν`, and `R ω' x` is the rounded set for the seed `ω'`. The guarantees are
required for every fractional solution `x ∈ [0,1]^V` with `‖x‖₁ ≤ k`: every output has at most `k`
elements and lies in `supp(x)`, and its expected value is at least `F(x)`. Pipage rounding and swap
rounding are such procedures. -/
structure IsRounding {E Ω' : Type} [Fintype E] [DecidableEq E] [Fintype Ω'] (f : Finset E → ℝ)
    (k : ℕ) (ν : Ω' → ℝ) (R : Ω' → (E → ℝ) → Finset E) : Prop where
  /-- `ν` is non-negative. -/
  prob_nonneg : ∀ ω', 0 ≤ ν ω'
  /-- `ν` has total mass one. -/
  prob_sum : ∑ ω', ν ω' = 1
  /-- Every rounded set is feasible: it has at most `k` elements. -/
  card_le : ∀ x : E → ℝ, (∀ e, 0 ≤ x e) → (∀ e, x e ≤ 1) → l1 x ≤ (k : ℝ) →
    ∀ ω', (R ω' x).card ≤ k
  /-- Every rounded set lies in the support of `x`. -/
  subset_supp : ∀ x : E → ℝ, (∀ e, 0 ≤ x e) → (∀ e, x e ≤ 1) → l1 x ≤ (k : ℝ) →
    ∀ ω', R ω' x ⊆ supp x
  /-- The expected value of the rounded set is at least `F(x)`. -/
  approx : ∀ x : E → ℝ, (∀ e, 0 ≤ x e) → (∀ e, x e ≤ 1) → l1 x ≤ (k : ℝ) →
    F f x ≤ ∑ ω', ν ω' * f (R ω' x)

end StreamSubmod.Supplement


