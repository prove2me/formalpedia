-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_utility
-- name    : SeqPostedPricing_MatroidSPM_utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:28:23.771283+00:00
-- url     : https://prove2.me/theorems/b8ee86ec-1a0f-4255-8a94-92a659a187c2
-- title:
--   Quasi-linear utility $u_i = v_i\cdot\mathbf 1[i\in M(\mathbf b)]-\pi_i(\mathbf b)$
-- statement:
--   For a mechanism $M$, an agent $i$ with true value $v_i$, and a profile $\mathbf b$ of reported values, the **utility** of agent $i$ is
--
--   $$
--   u_i(v_i;\mathbf b)=v_i\cdot\mathbf 1[i\in M(\mathbf b)]-\pi_i(\mathbf b),
--   $$
--
--   its value if it is served minus the price it pays. Truthfulness and individual rationality are stated in terms of this utility.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §1, p. 1 and §2.1, p. 4

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_Mechanism

namespace SeqPostedPricing.MatroidSPM

/-- **Quasi-linear utility of an agent.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §1, unnumbered, p. 1 (PDF p. 3) and §2.1, p. 4 (PDF p. 6): agent `i` has value `v_i` "for
getting served" and pays the price `π_i`.

`utility M i vi b` is the utility of agent `i`, whose true value is `vi`, when the mechanism `M`
runs on the reported profile `b`: `vi` if `i` is served at `b`, minus the payment `M.pay b i`.

**Formalization Note.** Single-parameter quasi-linear utility, the standard reading of the
paper's model. -/
noncomputable def utility {n : ℕ} (M : Mechanism n) (i : Fin n) (vi : ℝ) (b : Fin n → ℝ) : ℝ :=
  (if i ∈ M.alloc b then vi else 0) - M.pay b i

end SeqPostedPricing.MatroidSPM


