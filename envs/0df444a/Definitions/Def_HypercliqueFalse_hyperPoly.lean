-- Prove2me | Definitions.Def_HypercliqueFalse_hyperPoly
-- name    : HypercliqueFalse_hyperPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:29:55.067825+00:00
-- url     : https://prove2.me/theorems/4bf563e6-0a29-4667-8e93-065127c6efcd
-- title:
--   The $(k,h)$-hyperclique polynomial $H_{k,h}$
-- statement:
--   Let $k, h, m \in \mathbb N$. Given an integer array $A_S$ over $[m]^h$ for every $h$-element subset $S \subseteq [k]$, the **$(k,h)$-hyperclique polynomial** is
--   $$
--   H_{k,h} = \sum_{x \in [m]^k} \ \prod_{S \in \binom{[k]}{h}} A_{S;\,x_S},
--   $$
--   where, for $S = \{s_1 < \dots < s_h\}$, $x_S = (x_{s_1},\dots,x_{s_h})$ is the restriction of $x$ to the entries in $S$.
--
--   Theorem 2.1 evaluates this polynomial in time $O(m^{(1-\epsilon_h)k})$; with all arrays equal to the indicator array of a hypergraph it is $k!$ times the number of $k$-hypercliques.
--
--   **Formalization Note** Positions are `Fin k`, values `Fin m` (0-based); the restriction $x_S$ is read through the increasing enumeration of $S$ (`Finset.orderEmbOfFin`). The arrays are indexed by the subtype of $h$-element subsets.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, Hyperclique Polynomials, p.4

import Mathlib

set_option autoImplicit false

namespace HypercliqueFalse

/-- **The `(k, h)`-hyperclique polynomial.** Fischer, *The Hyperclique Hypothesis is False*,
arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, "Hyperclique Polynomials", p.4:
"given integer-valued arrays A_S over [n]^h, for all S ∈ ([k] choose h), the goal is to compute the
(k, h)-hyperclique polynomial H_{k,h} = Σ_{x∈[n]^k} Π_{S∈([k] choose h)} A_{S;x_S}", where `x_S` is
"the restriction of x to the entries in S".

Here the variables range over `[m]`: `A S` is an integer array over `[m]^h` for every `h`-element
subset `S` of the `k` positions, and
`hyperPoly A = Σ_{x : [k] → [m]} Π_S A_S(x_S)`.

**Formalization Note.** Positions are `Fin k`, values `Fin m` (0-based). The restriction `x_S` is
read through the increasing enumeration of `S` (`S.orderEmbOfFin`): `x_S = (x_{s₁}, …, x_{s_h})` for
`S = {s₁ < ⋯ < s_h}`, as in the paper's `S = {s₁, …, s_h}`. -/
def hyperPoly {k h m : ℕ} (A : {S : Finset (Fin k) // S.card = h} → (Fin h → Fin m) → ℤ) : ℤ :=
  ∑ x : Fin k → Fin m, ∏ S : {S : Finset (Fin k) // S.card = h},
    A S (fun t => x (S.1.orderEmbOfFin S.2 t))

end HypercliqueFalse


