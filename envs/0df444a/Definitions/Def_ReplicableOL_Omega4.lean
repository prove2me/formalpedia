-- Prove2me | Definitions.Def_ReplicableOL_Omega4
-- name    : ReplicableOL_Omega4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:44.149495+00:00
-- url     : https://prove2.me/theorems/3804308d-88b4-4d6f-b033-fddc033b737f
-- title:
--   The four-run sample space
-- statement:
--   The sample space of Section 4: the epoch means and four data sequences. Runs 1 and 2 use $S$ and $S'$; $S''$ and $S'''$ serve only to define phantom runs.
--
--   **Formalization Note** A product type: `ω.1` is `θ`, then `ω.2.1`, `ω.2.2.1`, `ω.2.2.2.1`, `ω.2.2.2.2` are `S, S′, S″, S‴`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_Bits

namespace ReplicableOL

/-- **The four-run sample space.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 4.1, p.15. `θ` and the four data sequences `S, S′, S″, S‴`.

**Formalization Note.** A product type: `ω.1` is `θ`, then `ω.2.1`, `ω.2.2.1`, `ω.2.2.2.1`, `ω.2.2.2.2` are `S, S′, S″, S‴`. -/
abbrev Omega4 (k L : ℕ) : Type :=
  (Fin k → ℝ) × Bits k L × Bits k L × Bits k L × Bits k L

end ReplicableOL


