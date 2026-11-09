-- Prove2me | Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
-- name    : MetricMatchingDistortion_IsConsistentPseudometric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:20:07.310211+00:00
-- url     : https://prove2.me/theorems/73f6f007-8830-435a-8ac1-42a8e5011a3f
-- title:
--   Pseudometrics on agents and items consistent with the rankings, $\rho(\sigma)$
-- statement:
--   Let $d$ be a real function on pairs of points of $A\cup B$ (agents and items as disjoint points). It is a **pseudometric** if
--   1. $d(x,y)\ge 0$,
--   2. $d(x,x)=0$,
--   3. $d(x,y)=d(y,x)$,
--   4. $d(x,y)\le d(x,z)+d(z,y)$.
--
--   Distinct points may be at distance $0$ (collocation is allowed). It is **consistent** with the rankings if for every agent $a$ and items $b,b'$,
--   $$b\succ_a b'\implies d(a,b)\le d(a,b').$$
--   $\rho(\sigma)$ is the set of consistent pseudometrics: the metrics a mechanism must handle without seeing them.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_Ranking

namespace MetricMatchingDistortion

/-- **Pseudometric on agents and items.** Charikar et al., *Sublinear Metric Distortion for
Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), §2, p.9 (PDF p.11): "Distances are
conveyed by an unknown pseudometric d : (A ∪ B) × (A ∪ B) → R≥0. … (i) Indiscernibility of
Identicals: d(x, y) = 0 if x = y, (ii) Symmetry: d(x, y) = d(y, x), (iii) Triangle inequality:
d(x, y) ≤ d(x, z) + d(z, y). Note that our definition allows collocation of distinct vertices."

The points are `Fin n ⊕ Fin n`: agent `a` is `Sum.inl a`, item `b` is `Sum.inr b`.

**Formalization Note.** Nonnegativity is the codomain `R≥0` of the page. Distinct points may be at
distance `0` (collocation), as the page allows. -/
def IsPseudometric {n : ℕ} (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) : Prop :=
  (∀ x y, 0 ≤ d x y) ∧ (∀ x, d x x = 0) ∧ (∀ x y, d x y = d y x) ∧
    ∀ x y z, d x y ≤ d x z + d z y

/-- **Consistency** (§2, p.9): "A metric d is consistent with an instance σ if, for every agent
a ∈ A and all items bi, bj ∈ B, bi ≻a bj implies d(a, bi) ≤ d(a, bj)." -/
def IsConsistent {n : ℕ} (rk : Ranking n) (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) : Prop :=
  ∀ a b b', Prefers rk a b b' → d (Sum.inl a) (Sum.inr b) ≤ d (Sum.inl a) (Sum.inr b')

/-- `d ∈ ρ(σ)`: `d` is a pseudometric on agents and items consistent with the rankings `rk`
(§2, p.9: "We let ρ(σ) denote the set of all metrics consistent with σ"). -/
def IsConsistentPseudometric {n : ℕ} (rk : Ranking n)
    (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) : Prop :=
  IsPseudometric d ∧ IsConsistent rk d

end MetricMatchingDistortion


