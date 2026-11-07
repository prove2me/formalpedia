-- Prove2me | Definitions.Def_DoublingMST_ddimOn
-- name    : DoublingMST_ddimOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:24:18.242519+00:00
-- url     : https://prove2.me/theorems/ca36abaf-e1c3-4e7d-8713-f08ae058b901
-- title:
--   Doubling dimension $\operatorname{ddim}(S)$ of a point set (Definition 2.2)
-- statement:
--   The **doubling dimension** of a point set $S\subseteq X$ is the doubling dimension of the metric space $(S,d)$: the smallest $t\ge0$ such that for every $x\in S$ and $r>0$ the ball $B(x,r)\cap S$ is covered by at most $2^t$ balls of radius $r/2$ centred at points of $S$.
--
--   **Formalization Note** Defined as the infimum of the admissible $t$; the set is nonempty, bounded below and closed, so the infimum is attained. The empty set has dimension $0$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Definition 2.2, p.12 (PDF p.14)

import Mathlib
open scoped Classical

namespace DoublingMST

/-- **Doubling dimension of a point set.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 2.2, p.12 (PDF p.14): "The doubling dimension of a metric space (X, d) is the
smallest t ≥ 0 such that every metric ball can be covered by at most 2^t balls of half the radius.
The doubling dimension of a point set S ⊆ X is the doubling dimension of the metric space (S, d),
and is denoted by ddim(S)."

`ddimOn d S` is the infimum of the `t ≥ 0` such that for every `x ∈ S` and `r > 0` there is a set
`C ⊆ S` of at most `2^t` centres whose balls of radius `r/2` cover `B(x, r) ∩ S`.

**Formalization Note.** Balls and centres are those of the metric space `(S, d)`: centres lie in
`S`. The set of admissible `t` is nonempty (`t = log₂ |S|` works with `C = S`), bounded below by
`0` and closed, so the infimum is attained: it is the smallest such `t`. For `S = ∅` the value is
`0`. Balls are closed, as on p.11. -/
noncomputable def ddimOn {n : ℕ} (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∀ x ∈ S, ∀ r : ℝ, 0 < r → ∃ C : Finset (Fin n), C ⊆ S ∧
    (C.card : ℝ) ≤ (2 : ℝ) ^ t ∧ ∀ y ∈ S, d x y ≤ r → ∃ c ∈ C, d c y ≤ r / 2}

end DoublingMST


