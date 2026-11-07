-- Prove2me | Definitions.Def_QPACLarge_Zcorr
-- name    : QPACLarge_Zcorr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:07:20.804984+00:00
-- url     : https://prove2.me/theorems/b49a8fa5-1a16-43b1-86a4-bd4b8f14d6fa
-- title:
--   Normalized correlation $Z_a$
-- statement:
--   For a target $f$ with $F = (-1)^f$ and a seed $a$,
--   $$
--   Z_a = \frac{1}{\sqrt N} \sum_{x} F(x) H_a(x) = \sqrt N \,\mathrm{corr}(H_a, F), \qquad N = 2^n .
--   $$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.5, p.17; Section 3.2.2, p.25

import Mathlib
import Definitions.Def_QPACLarge_qa
import Definitions.Def_QPACLarge_sgn

namespace QPACLarge

open QAlgorithms

/-- **The normalized correlation `Z_a`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.5, p.17 and Section 3.2.2, p.25: "`Z_a = (1/√N) Σₓ F(x)H_a(x) = √N corr(H_a, F)`",
with `N = 2ⁿ`, `F = (−1)^f` and `H_a = (−1)^{q_a}`. -/
noncomputable def Zcorr {n : ℕ} (f : Qubits n → Bool) (a : Seed n) : ℝ :=
  (Real.sqrt (2 ^ n))⁻¹ * ∑ x : Qubits n, sgn (f x) * sgn (qa a x)

end QPACLarge


