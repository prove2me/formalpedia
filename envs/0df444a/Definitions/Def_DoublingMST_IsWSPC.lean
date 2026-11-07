-- Prove2me | Definitions.Def_DoublingMST_IsWSPC
-- name    : DoublingMST_IsWSPC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:30:25.445825+00:00
-- url     : https://prove2.me/theorems/76cd04b4-842b-4bf1-9628-80c27f9f042c
-- title:
--   Well-separated pair cover (Definition 3.1)
-- statement:
--   A **$t$-well-separated pair cover** of $X$ is a finite collection $\Phi$ of pairs $(A,B)$ of nonempty subsets of $X$ such that
--
--   1. (separation) every $(A,B)\in\Phi$ is $t$-separated;
--   2. (covering) for any two distinct points $p,q$ there is $(A,B)\in\Phi$ with one of $p,q$ in $A$ and the other in $B$.
--
--   **Formalization Note** The page's "for $t\ge2$" is a hypothesis of the statements that use a $t$-WSPC.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Definition 3.1, pp.13–14 (PDF pp.15–16)

import Mathlib
import Definitions.Def_DoublingMST_IsSeparated

namespace DoublingMST

/-- **Well-separated pair cover.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 3.1, pp.13–14 (PDF pp.15–16): "For t ≥ 2, a t-well-separated pair cover of X is
a collection of pairs Φ = {(A_1, B_1), …, (A_k, B_k)} of nonempty subsets of X satisfying the
following: (1) Separation: Each pair (A, B) ∈ Φ is t-separated … (2) Covering: For any two distinct
points p, q ∈ X, there exists at least one pair (A, B) ∈ Φ such that p lies in either A or B and q
in the other set."

**Formalization Note.** `Φ` is a finite set of ordered pairs of finite sets. The page's "for
t ≥ 2" is a hypothesis of each statement that uses a t-WSPC, not part of this predicate. -/
def IsWSPC {n : ℕ} (d : Fin n → Fin n → ℝ) (Φ : Finset (Finset (Fin n) × Finset (Fin n)))
    (t : ℝ) : Prop :=
  (∀ AB ∈ Φ, AB.1.Nonempty ∧ AB.2.Nonempty ∧ IsSeparated d AB.1 AB.2 t) ∧
    ∀ p q : Fin n, p ≠ q → ∃ AB ∈ Φ, (p ∈ AB.1 ∧ q ∈ AB.2) ∨ (q ∈ AB.1 ∧ p ∈ AB.2)

end DoublingMST


