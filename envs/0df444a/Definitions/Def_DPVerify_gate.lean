-- Prove2me | Definitions.Def_DPVerify_gate
-- name    : DPVerify_gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:28.908599+00:00
-- url     : https://prove2.me/theorems/6d88e30c-2149-4453-9b95-56a6b7b2b22b
-- title:
--   Smooth consistency gate $G(p,u)=\kappa^2p^2/(u^2+\kappa^2p^2)$
-- statement:
--   For a constant $\kappa>0$, the **smooth consistency gate** is
--
--   $$
--   G(p,u)=\frac{\kappa^2p^2}{u^2+\kappa^2p^2},
--   $$
--
--   evaluated at $p=p_S(m)$, the probability that the original verifier sends the message $m$ on the sample $S$, and $u=U_m(r)$, the public hash value of $m$. The new verifier of Theorem 4.1 accepts a claimed transcript $(m,a)$ with probability $G(p_S(m),U_m(r))\,b_S(m,a)$, where $b_S(m,a)$ is the original conditional acceptance probability.
--
--   **Formalization Note** At $p=u=0$ the formula reads $0/0$, which Lean evaluates to $0$; the proof only uses $u\ge 1/L>0$.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Theorem 4.1's proof, p.11 (PDF p.14)

import Mathlib

set_option autoImplicit false

namespace DPVerify

/-- The smooth consistency gate `G(p, u) = κ²p² / (u² + κ²p²)` (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Theorem 4.1's proof, p.11 =
PDF p.14), with `p = p_S(m)` the probability that the original verifier sends `m` and
`u = U_m(r)` the public hash value of `m`.

**Formalization Note** At `p = u = 0` Lean's division gives `G = 0`; the proof only evaluates
`G` at `u ≥ 1/L > 0`. -/
noncomputable def gate (κ p u : ℝ) : ℝ :=
  κ ^ 2 * p ^ 2 / (u ^ 2 + κ ^ 2 * p ^ 2)

end DPVerify


