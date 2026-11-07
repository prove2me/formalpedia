-- Prove2me | Definitions.Def_QPACLarge_sgn
-- name    : QPACLarge_sgn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:22.330196+00:00
-- url     : https://prove2.me/theorems/5ae6ae31-2313-409e-9983-197fbdb91d98
-- title:
--   Sign representation $(-1)^b$
-- statement:
--   The **sign representation** of a bit $b$ is $(-1)^b$: $0 \mapsto 1$, $1 \mapsto -1$. A Boolean target $f$ has sign representation $F(x) = (-1)^{f(x)}$ and a hypothesis $h$ has $H(x) = (-1)^{h(x)}$.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.1, p.14

import Mathlib

namespace QPACLarge

/-- **Sign representation of a bit.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.1, p.14: "a target `f : {0,1}ⁿ → {0,1}` has sign representation
`F : {0,1}ⁿ → {−1,1}`, `F(x) = (−1)^{f(x)}`".

`sgn b = (−1)^b`: `sgn false = 1`, `sgn true = −1`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

end QPACLarge


