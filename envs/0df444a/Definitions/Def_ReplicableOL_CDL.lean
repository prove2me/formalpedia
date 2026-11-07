-- Prove2me | Definitions.Def_ReplicableOL_CDL
-- name    : ReplicableOL_CDL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:26.875022+00:00
-- url     : https://prove2.me/theorems/021b7929-aac6-478d-89b5-af5c01a56670
-- title:
--   The constant $C(\Delta,L)$
-- statement:
--   The constant $C(\Delta,L)=\frac43\Delta\max\{1,4\Delta\beta_L\}$; in the regime $\Delta\sqrt L\ge\sqrt3/8$ it equals $C_B\Delta^2\sqrt L$.
--
--   **Formalization Note** Exact. Since `4Δβ_L = (8/√3)Δ√L`, this is the factor printed after Lemma 2.4 on p.8.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Appendix A.3, p.28

import Mathlib
import Definitions.Def_ReplicableOL_betaL

namespace ReplicableOL

/-- **The constant $C(\Delta,L)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Appendix A.3, p.28. `C(Δ, L) := (4/3) Δ max{1, 4Δβ_L}`.

**Formalization Note.** Exact. Since `4Δβ_L = (8/√3)Δ√L`, this is the factor printed after Lemma 2.4 on p.8. -/
noncomputable def CDL (Δ : ℝ) (L : ℕ) : ℝ := 4 / 3 * Δ * max 1 (4 * Δ * betaL L)

end ReplicableOL


