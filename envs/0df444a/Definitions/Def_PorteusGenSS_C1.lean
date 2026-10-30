-- Prove2me | Definitions.Def_PorteusGenSS_C1
-- name    : PorteusGenSS_C1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:14:05.302933+00:00
-- url     : https://prove2.me/theorems/59983685-7c39-4516-b525-3733cd974d73
-- title:
--   Tangent parameters $C_1(z)$
-- statement:
--   For an ordering cost $c$ and $z>0$,
--
--   $$
--   C_1(z)=\{(a,K)\in\mathbb R^2:\ az+K=c(z)\ \text{and}\ ay+K\ge c(y)\ \text{for all }y\ge0\},
--   $$
--
--   the slopes and intercepts of the lines that touch $c$ at $z$ and lie above $c$ on $[0,\infty)$.
--
--   **Formalization Note** The set is defined for every real $z$; it is used only for $z>0$.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §II, p. 412

import Mathlib

namespace PorteusGenSS

/-- **Tangent parameters C₁(z) of the ordering cost (§II).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §II, p. 412: "Let, for z > 0, C1(z) = {(c, K) ∈ R²; cz + K = c(z) and cy + K ≥ c(y) for
all y ≥ 0}."

`C1 c z` is the set of pairs `(a, K)` with `a z + K = c z` and `c y ≤ a y + K` for every `y ≥ 0`:
the slopes and intercepts of the lines that touch `c` at `z` and lie above `c` on `[0, ∞)`.

**Formalization Note.** The pair is written `(a, K)` (the paper reuses the letter `c` for the
slope). The set is defined for every real `z`; the paper and every use in the mission take
`z > 0`. -/
def C1 (c : ℝ → ℝ) (z : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 * z + p.2 = c z ∧ ∀ y : ℝ, 0 ≤ y → c y ≤ p.1 * y + p.2}

end PorteusGenSS


