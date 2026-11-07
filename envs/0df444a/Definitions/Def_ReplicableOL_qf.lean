-- Prove2me | Definitions.Def_ReplicableOL_qf
-- name    : ReplicableOL_qf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:51.753367+00:00
-- url     : https://prove2.me/theorems/638914b1-7326-4e35-8826-0d9dc9a99b5a
-- title:
--   Acceptance curve $q_f(\mu)$
-- statement:
--   For a fixed function $f$ of a block, $q_f(\mu)=\mathbb E[f(S)\mid\mu]=\sum_sf(s)b_s(\mu)$.
--
--   **Formalization Note** A real function on all of `ℝ`, read as an expectation for `|μ| ≤ 1/2`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Appendix A.3, p.28

import Mathlib
import Definitions.Def_ReplicableOL_blockWeight

namespace ReplicableOL

/-- **Acceptance curve $q_f(\mu)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Appendix A.3, p.28. `q_f(μ) := E[f(S) | μ] = Σ_s f(s) b_s(μ)`, a polynomial in `μ`.

**Formalization Note.** A real function on all of `ℝ`, read as an expectation for `|μ| ≤ 1/2`. -/
noncomputable def qf {L : ℕ} (f : Block L → ℝ) (μ : ℝ) : ℝ :=
  ∑ s : Block L, f s * blockWeight μ s

end ReplicableOL


