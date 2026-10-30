-- Prove2me | Definitions.Def_GarberOLO_Alg3_IsApproxOracle
-- name    : GarberOLO_Alg3_IsApproxOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:48:45.803873+00:00
-- url     : https://prove2.me/theorems/cc0f158b-5a62-4430-9c49-233ddd896a47
-- title:
--   $\alpha$-approximate linear optimization oracle $\mathcal O_K$
-- statement:
--   Given a setting, a map $\mathcal O_K : \mathbb R^d \to \mathbb R^d$ is an **$\alpha$-approximation oracle** for $K$ if for every $c \in \mathbb R^d_+$:
--
--   1. $\mathcal O_K(c) \in K$;
--   2. if $\alpha \ge 1$: $\ \mathcal O_K(c) \cdot c \le \alpha \min_{x \in K} x \cdot c$;
--   3. if $\alpha < 1$: $\ \mathcal O_K(c) \cdot c \ge \alpha \max_{x \in K} x \cdot c$.
--
--   This is the only access the player has to $K$; for NP-hard problems with an $\alpha$-approximation algorithm (MAX-CUT, vertex cover, metric TSP) such an oracle is available.
--
--   **Formalization Note** The comparisons with the min and max are written for every $x \in K$, which is equivalent because $K$ is compact and (by item 1 at $c = 0$) nonempty. Values of the map outside $\mathbb R^d_+$ are unconstrained and never used.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, §2.1, p. 4 (unnumbered display)

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting

open scoped RealInnerProductSpace

namespace GarberOLO.Alg3

/-- **The α-approximate linear optimization oracle O_K** (§2.1).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, §2.1, p. 4 (unnumbered display):
"∀ c ∈ ℝᵈ₊ : O_K(c) ∈ K and O_K(c) · c ≤ α min_{x∈K} x · c if α ≥ 1;
O_K(c) · c ≥ α max_{x∈K} x · c if α < 1."

`IsApproxOracle S OK` says: for every `c` with nonnegative coordinates, `OK c ∈ K`; if
`1 ≤ α` then `⟪OK c, c⟫ ≤ α ⟪x, c⟫` for every `x ∈ K`; if `α < 1` then
`α ⟪x, c⟫ ≤ ⟪OK c, c⟫` for every `x ∈ K`.

**Formalization Note.** The oracle is any function `ℝᵈ → ℝᵈ`; only its values on ℝᵈ₊ are
constrained (the paper's O_K is defined on ℝᵈ₊ only, and the algorithms never query it
elsewhere). The bounds against min/max are written pointwise ("for every x ∈ K"), which is
equivalent to the min/max form because K is compact and, by the first clause at `c = 0`,
nonempty, so the min and max are attained. -/
def IsApproxOracle {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ c : EuclideanSpace ℝ (Fin d), (∀ i, 0 ≤ c i) →
    OK c ∈ S.K ∧
    (1 ≤ S.α → ∀ x ∈ S.K, ⟪OK c, c⟫ ≤ S.α * ⟪x, c⟫) ∧
    (S.α < 1 → ∀ x ∈ S.K, S.α * ⟪x, c⟫ ≤ ⟪OK c, c⟫)

end GarberOLO.Alg3


