-- Prove2me | Definitions.Def_QPACLarge_PF
-- name    : QPACLarge_PF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:09:42.818143+00:00
-- url     : https://prove2.me/theorems/e78f26b6-2ffe-49ec-81fb-a539b2c30cd8
-- title:
--   Measurement law $P_F(a)=(1+Z_a)^2/(2M)$, Eq. (5)
-- statement:
--   The law of the seed measured by the correlation-biased quantum sampler is
--   $$
--   P_F(a) = \frac{(1 + Z_a)^2}{2M}, \tag{5}
--   $$
--   where $M = |A| = 2^r$ is the number of seeds.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.2, Step 4, p.25, Eq. (5)

import Mathlib
import Definitions.Def_QPACLarge_Zcorr

namespace QPACLarge

open QAlgorithms

/-- **The measurement law `P_F` of the quantum sampler.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.2, Step 4, p.25, Eq. (5): "`P_F(a) ≜ (1 + Z_a)²/(2M)`", with `M = |A| = 2^r`
the number of seeds. -/
noncomputable def PF {n : ℕ} (f : Qubits n → Bool) (a : Seed n) : ℝ :=
  (1 + Zcorr f a) ^ 2 / (2 * Fintype.card (Seed n))

end QPACLarge


