-- Prove2me | Definitions.Def_ReplicableOL_selfHazard
-- name    : ReplicableOL_selfHazard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:49:42.547501+00:00
-- url     : https://prove2.me/theorems/37348a39-eb50-4391-a8f1-c783abe3039a
-- title:
--   Phantom hazards $h^{14}_j$, $h^{23}_j$
-- statement:
--   The hazard of a **phantom run**: the probability that one epoch rule, at a fixed prefix, gives different action strings on two independent blocks.
--
--   **Formalization Note** `selfHazard Δ Φ j h` is `hazard` with both prefixes equal to `h`: at `h = S_{<j}` it is `h^{14}_j`, at `h = S′_{<j}` it is `h^{23}_j`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_hazard

namespace ReplicableOL

/-- **Phantom hazards $h^{14}_j$, $h^{23}_j$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 4.1, p.15. `h^{14}_j := P[D^{14}_j | G_{j−1}]` and `h^{23}_j := P[D^{23}_j | G_{j−1}]`, where a phantom run compares an epoch rule with itself on two independent blocks.

**Formalization Note.** `selfHazard Δ Φ j h` is `hazard` with both prefixes equal to `h`: at `h = S_{<j}` it is `h^{14}_j`, at `h = S′_{<j}` it is `h^{23}_j`. -/
noncomputable def selfHazard {k L : ℕ} (Δ : ℝ) (Φ : EpochRule k L) (j : Fin k) (h : Fin j → Block L) : ℝ :=
  hazard Δ Φ j h h

end ReplicableOL


