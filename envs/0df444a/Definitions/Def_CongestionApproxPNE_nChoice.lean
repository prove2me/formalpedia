-- Prove2me | Definitions.Def_CongestionApproxPNE_nChoice
-- name    : CongestionApproxPNE_nChoice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:06.128221+00:00
-- url     : https://prove2.me/theorems/4e3c8365-2088-43bb-9f16-ffc0ff3f9b4a
-- title:
--   The number of light players of the parameter choice, $n=\lfloor 1/(d^{1/(2(k+1))}w)\rfloor$
-- statement:
--   For an integer $d$, with $k=k_d$ and $w=\ln d/(2d)$, the number of light players in the parameter choice of the proof of Theorem 1 is
--
--   $$
--   n=\left\lfloor\frac{1}{d^{\frac{1}{2(k+1)}}\,w}\right\rfloor.
--   $$
--
--   **Formalization Note** $d^{1/(2(k+1))}$ is `Real.rpow`; $\lfloor\cdot\rfloor$ is `Nat.floor`, equal to the integer floor on the positive argument (for $d\ge 2$).
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, p.6 (PDF p.7), choice of n

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **The number of light players of the parameter choice, `n = ⌊1 / (d^{1/(2(k+1))} w)⌋`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, arXiv:2002.07466v3, proof of Theorem 1,
p.6, with `k = k_d` and `w = ln d/(2d)`.

**Formalization Note** `d^{1/(2(k+1))}` is `Real.rpow`; `⌊·⌋` is `Nat.floor`, which agrees with
the integer floor on the (positive, for `d ≥ 2`) argument. -/
noncomputable def nChoice (d : ℕ) : ℕ :=
  ⌊1 / ((d : ℝ) ^ (1 / (2 * ((kd d : ℝ) + 1))) * wChoice d)⌋₊

end CongestionApproxPNE


