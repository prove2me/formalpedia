-- Prove2me | Definitions.Def_MetricMatchingDistortion_IsPartialFractionalMatching
-- name    : MetricMatchingDistortion_IsPartialFractionalMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:40.915848+00:00
-- url     : https://prove2.me/theorems/c1ba69ce-c9e9-441d-bbf7-f43f1b5fc40d
-- title:
--   Partial and perfect fractional matchings, their cost and unmatched mass
-- statement:
--   A **partial fractional matching** is a matrix $X=(X_{a,b})_{a\in A,b\in B}$ with nonnegative entries whose row sums and column sums are at most $1$; it is **perfect** if all row and column sums equal $1$. Its **cost** under $d$ is
--   $$\mathrm{cost}(X,d)=\sum_{a\in A}\sum_{b\in B}X_{a,b}\,d(a,b),$$
--   and its **unmatched mass** is the real number $k=n-\sum_{a,b}X_{a,b}$.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §2, p.9–10 (PDF pp.11–12); §3.1, p.12 (PDF p.14)

import Mathlib

namespace MetricMatchingDistortion

/-- **Fractional matching.** Charikar et al., *Sublinear Metric Distortion for Matching*,
arXiv:2611.05777 (held version, sha256 fdf3452b…), §2, p.9 (PDF p.11): "A fractional matching is
any matrix indexed by A and B … with nonnegative entries such that each row sum and each column sum
is in [0, 1]. If all the row sums and column sums are equal to 1, we say that the fractional
matching is perfect; otherwise, we say that it is partial."

`IsPartialFractionalMatching X`: `X a b ≥ 0`, every row sum and every column sum is at most `1`
(§3.1, p.12: "a partial fractional matching is a nonnegative matrix X indexed by A × B whose row and
column sums are at most one"; perfect ones included). -/
def IsPartialFractionalMatching {n : ℕ} (X : Fin n → Fin n → ℝ) : Prop :=
  (∀ a b, 0 ≤ X a b) ∧ (∀ a, ∑ b, X a b ≤ 1) ∧ ∀ b, ∑ a, X a b ≤ 1

/-- A **perfect fractional matching** (§2, p.9): nonnegative entries, every row sum and every
column sum equal to `1` (a doubly stochastic matrix). -/
def IsPerfectFractionalMatching {n : ℕ} (X : Fin n → Fin n → ℝ) : Prop :=
  (∀ a b, 0 ≤ X a b) ∧ (∀ a, ∑ b, X a b = 1) ∧ ∀ b, ∑ a, X a b = 1

/-- **Cost of a fractional matching** (§2, p.10 = PDF p.12): "cost(X, d) := ∑_{a∈A} ∑_{b∈B}
X_{a,b} · d(a, b)". Agent `a` is the point `Sum.inl a`, item `b` the point `Sum.inr b`. The same
formula is used for any matrix (§6.2, p.51: "we write cost(Z, d) = ∑ Z_{a,b} · d(a, b) for any
nonnegative matrix Z"). -/
def fracCost {n : ℕ} (X : Fin n → Fin n → ℝ) (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, X a b * d (Sum.inl a) (Sum.inr b)

/-- **Unmatched mass** (§3.1, p.12 = PDF p.14): "Let k := n − ∑_{a,b} X_{a,b} be the total unmatched
mass on each side". A real number. -/
def unmatchedMass {n : ℕ} (X : Fin n → Fin n → ℝ) : ℝ :=
  (n : ℝ) - ∑ a, ∑ b, X a b

end MetricMatchingDistortion


