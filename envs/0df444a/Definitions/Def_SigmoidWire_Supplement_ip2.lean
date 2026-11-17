-- Prove2me | Definitions.Def_SigmoidWire_Supplement_ip2
-- name    : SigmoidWire_Supplement_ip2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:39:38.255005+00:00
-- url     : https://prove2.me/theorems/17ee421b-e292-43ca-81d6-edaadd519cae
-- title:
--   Inner product mod 2, $\mathrm{IP2}$
-- statement:
--   For $x,y\in\{0,1\}^n$,
--   $$\mathrm{IP2}(x,y)=\sum_{i=1}^n x_iy_i \bmod 2,$$
--   a Boolean function of $2n$ input bits.
--
--   It is a classical lower-bound target: threshold circuits need $\Omega(n)$ gates and ReLU circuits $\Omega(n/\log n)$ gates to compute it, while Theorems 1.7 and 6.10 give sublinear sigmoidal circuits.
--
--   **Formalization Note** An input is a string of $2n$ bits whose first $n$ bits are $x$ and last $n$ bits are $y$.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), §6.3, p.41

import Mathlib

namespace SigmoidWire.Supplement

/-- **Inner product mod 2** on `2n` input bits.

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), §6.3, p.41 (PDF p.43):
"Given inputs x, y ∈ {0,1}^n, IP2 computes Σ_{i∈[n]} x_i y_i mod 2"; "Let n be the length of x
(and y), i.e., 2n be the input length."

**Formalization Note.** An input is `z : Fin (n + n) → Bool`; `x_i = z i` (the first `n`
coordinates, `Fin.castAdd`) and `y_i = z (n + i)` (`Fin.natAdd`). The value is `true` iff the number
of `i` with `x_i = y_i = 1` is odd. -/
def ip2 (n : ℕ) (z : Fin (n + n) → Bool) : Bool :=
  decide (Odd (Finset.univ.filter fun i : Fin n =>
    z (Fin.castAdd n i) = true ∧ z (Fin.natAdd n i) = true).card)

end SigmoidWire.Supplement


