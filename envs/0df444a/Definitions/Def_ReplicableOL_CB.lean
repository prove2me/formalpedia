-- Prove2me | Definitions.Def_ReplicableOL_CB
-- name    : ReplicableOL_CB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:18.304509+00:00
-- url     : https://prove2.me/theorems/4d4c9cd2-8299-4f72-aec1-8866de2caf6a
-- title:
--   The constant $C_B$
-- statement:
--   The constant $C_B=32/(3\sqrt3)$ of the gain-weighted coin lemma.
--
--   **Formalization Note** The exact value.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 2.4, p.8

import Mathlib

namespace ReplicableOL

/-- **The constant $C_B$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 2.4, p.8. `C_B = 32/(3√3)`.

**Formalization Note.** The exact value. -/
noncomputable def CB : ℝ := 32 / (3 * √3)

end ReplicableOL


