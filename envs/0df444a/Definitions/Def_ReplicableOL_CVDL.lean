-- Prove2me | Definitions.Def_ReplicableOL_CVDL
-- name    : ReplicableOL_CVDL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:38.213105+00:00
-- url     : https://prove2.me/theorems/f021c660-c04c-4a3b-acde-b6a36a17ad2d
-- title:
--   The constant $C_V(\Delta,L)$
-- statement:
--   The constant $C_V(\Delta,L)=\max\{\frac43,\frac{16}3\Delta\beta_L\}$; in the regime $\Delta\sqrt L\ge\sqrt3/8$ it equals $C_B\Delta\sqrt L$.
--
--   **Formalization Note** Exact. Since `(16/3)Δβ_L = C_B Δ√L`, this is the factor printed after Lemma 2.4 on p.8.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Appendix A.3, p.28

import Mathlib
import Definitions.Def_ReplicableOL_betaL

namespace ReplicableOL

/-- **The constant $C_V(\Delta,L)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Appendix A.3, p.28. `C_V(Δ, L) := max{4/3, (16/3) Δ β_L}`.

**Formalization Note.** Exact. Since `(16/3)Δβ_L = C_B Δ√L`, this is the factor printed after Lemma 2.4 on p.8. -/
noncomputable def CVDL (Δ : ℝ) (L : ℕ) : ℝ := max (4 / 3) (16 / 3 * Δ * betaL L)

end ReplicableOL


