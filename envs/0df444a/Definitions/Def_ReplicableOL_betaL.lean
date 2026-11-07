-- Prove2me | Definitions.Def_ReplicableOL_betaL
-- name    : ReplicableOL_betaL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:33.078731+00:00
-- url     : https://prove2.me/theorems/7d3f6c53-be8f-434e-ad99-1317ea2b6802
-- title:
--   The Lipschitz constant $\beta_L$
-- statement:
--   The bound $\beta_L=\frac2{\sqrt3}\sqrt L$ on the derivative of $q_f$ on $[-1/4,1/4]$.
--
--   **Formalization Note** `L` is a natural number cast to `ℝ`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Appendix A.3, p.28

import Mathlib

namespace ReplicableOL

/-- **The Lipschitz constant $\beta_L$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Appendix A.3, p.28. `β_L := (2/√3) √L`.

**Formalization Note.** `L` is a natural number cast to `ℝ`. -/
noncomputable def betaL (L : ℕ) : ℝ := 2 / √3 * √(L : ℝ)

end ReplicableOL


