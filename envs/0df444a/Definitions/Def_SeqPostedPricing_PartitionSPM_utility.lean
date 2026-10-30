-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_utility
-- name    : SeqPostedPricing_PartitionSPM_utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:03:10.295821+00:00
-- url     : https://prove2.me/theorems/e0cf0cbe-a851-40e3-a5f9-69f9bbf1159f
-- title:
--   Quasi-linear utility of an agent
-- statement:
--   Let $M$ be a mechanism, $i$ an agent with true value $v_i$ for being served, and $b$ the profile of reports. The **utility** of agent $i$ is
--
--   $$
--   u_i(v_i; b) = v_i \cdot \mathbf 1[i \in M(b)] - \pi_i(b).
--   $$
--
--   It is the utility of a quasi-linear single-parameter agent, on which truthfulness and individual rationality are defined.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §1, p. 1 (PDF p. 3), and §2.1, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_Mechanism

namespace SeqPostedPricing.PartitionSPM

/-- **Quasi-linear utility of an agent** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §1, p. 1 = PDF p. 3, and §2.1, p. 4 = PDF p. 6:
agent `i` has value `v_i` for getting served and pays `π_i`). Agent `i` with true value `vi`, when the
bid profile is `b`, gets `vi − π_i(b)` if served and `−π_i(b)` otherwise.

**Formalization Note** The standard quasi-linear utility of single-parameter mechanism design;
the paper uses it implicitly in "truthful" and "individually rational". -/
def utility {n : ℕ} (M : Mechanism n) (i : Fin n) (vi : ℝ) (b : Fin n → ℝ) : ℝ :=
  (if i ∈ M.alloc b then vi else 0) - M.pay b i

end SeqPostedPricing.PartitionSPM


