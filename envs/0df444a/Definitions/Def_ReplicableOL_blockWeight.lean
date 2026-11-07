-- Prove2me | Definitions.Def_ReplicableOL_blockWeight
-- name    : ReplicableOL_blockWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:14.139049+00:00
-- url     : https://prove2.me/theorems/62ed02ad-6a48-44ae-9513-dd05681d00dd
-- title:
--   Block probability $b_s(\mu)=\nu_\mu(s)$
-- statement:
--   The probability of a block $s$ under $\nu_\mu=\mathrm{Bern}(1/2+\mu)^{\otimes L}$,
--   $$
--   b_s(\mu)=(1/2+\mu)^{|s|}(1/2-\mu)^{L-|s|}.
--   $$
--
--   **Formalization Note** A real polynomial in `μ`, read as a probability for `|μ| ≤ 1/2`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 4.1, p.15; Appendix A.3, p.28

import Mathlib
import Definitions.Def_ReplicableOL_Block

namespace ReplicableOL

/-- **Block probability $b_s(\mu)=\nu_\mu(s)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 4.1, p.15; Appendix A.3, p.28. `ν_μ := Bern(1/2 + μ)^{⊗L}` and `b_s(μ) := (1/2 + μ)^{|s|} (1/2 − μ)^{L−|s|} = P[S = s | μ]`.

**Formalization Note.** A real polynomial in `μ`, read as a probability for `|μ| ≤ 1/2`. -/
noncomputable def blockWeight {L : ℕ} (μ : ℝ) (s : Block L) : ℝ :=
  ∏ i, if s i then 1 / 2 + μ else 1 / 2 - μ

end ReplicableOL


