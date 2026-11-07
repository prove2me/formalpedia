-- Prove2me | Definitions.Def_ReplicableOL_hazardAt
-- name    : ReplicableOL_hazardAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:25.032269+00:00
-- url     : https://prove2.me/theorems/5bf50efd-b7ac-4449-84ec-b00cb1d52700
-- title:
--   Disagreement hazard given $\mu$
-- statement:
--   Given the past and the epoch mean $\mu$, the probability that the two rules $\Phi_j(h;\cdot)$ and $\Phi_j(h';\cdot)$ differ on two independent blocks from $\nu_\mu$.
--
--   **Formalization Note** A finite sum over the two blocks, at a fixed mean `μ` and fixed prefixes `h`, `h'`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 4.2, p.15–16

import Mathlib
import Definitions.Def_ReplicableOL_EpochRule
import Definitions.Def_ReplicableOL_blockWeight

namespace ReplicableOL

/-- **Disagreement hazard given $\mu$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 4.2, p.15–16. `P[D^{12}_j | G_{j−1} ∨ σ(μ_j)] = ∫ 1{F(s) ≠ F′(s′)} ν^{⊗2}(ds ds′)`.

**Formalization Note.** A finite sum over the two blocks, at a fixed mean `μ` and fixed prefixes `h`, `h'`. -/
noncomputable def hazardAt {k L : ℕ} (Φ : EpochRule k L) (j : Fin k) (h h' : Fin j → Block L) (μ : ℝ) : ℝ :=
  ∑ s : Block L, ∑ s' : Block L,
    blockWeight μ s * blockWeight μ s' * (if Φ j h s ≠ Φ j h' s' then 1 else 0)

end ReplicableOL


