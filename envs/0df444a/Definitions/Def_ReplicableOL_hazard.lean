-- Prove2me | Definitions.Def_ReplicableOL_hazard
-- name    : ReplicableOL_hazard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:09.312544+00:00
-- url     : https://prove2.me/theorems/ab87f593-408b-4256-97a7-fe051057486e
-- title:
--   First-disagreement hazard $h_j$
-- statement:
--   The **hazard** $h_j=\mathbb P[D^{12}_j\mid\mathcal G_{j-1}]$ that the runs differ in epoch $j$, given both runs' past data.
--
--   **Formalization Note** The explicit version as a function of the two prefixes. Lemma 4.1 (`lemma_4_1`) ties it to Mathlib's `condExp`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8; Sec. 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_hazardAt
import Definitions.Def_ReplicableOL_uniformPrior
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **First-disagreement hazard $h_j$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8; Sec. 4.1, p.15. `h_j := P[the runs differ in E_j | G_{j−1}]`.

**Formalization Note.** The explicit version as a function of the two prefixes. Lemma 4.1 (`lemma_4_1`) ties it to Mathlib's `condExp`. -/
noncomputable def hazard {k L : ℕ} (Δ : ℝ) (Φ : EpochRule k L) (j : Fin k) (h h' : Fin j → Block L) : ℝ :=
  ∫ μ, hazardAt Φ j h h' μ ∂(uniformPrior Δ)

end ReplicableOL


