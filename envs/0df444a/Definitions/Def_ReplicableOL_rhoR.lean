-- Prove2me | Definitions.Def_ReplicableOL_rhoR
-- name    : ReplicableOL_rhoR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:43.665028+00:00
-- url     : https://prove2.me/theorems/74bedc59-6c81-4346-b08c-078be784a04a
-- title:
--   Per-seed disagreement $\rho(r)$ on Construction C
-- statement:
--   At a fixed seed $r$, $\rho(r)=\mathbb P_{\theta,S,S'}[M_k=0]$ is the probability that the two runs disagree somewhere in the first $kL$ rounds, with $\theta$ shared.
--
--   **Formalization Note** The seed is implicit in the rule `Φ`. `1 − M_k` is the indicator of `{M_k = 0}`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8

import Mathlib
import Definitions.Def_ReplicableOL_E2
import Definitions.Def_ReplicableOL_M

namespace ReplicableOL

/-- **Per-seed disagreement $\rho(r)$ on Construction C.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8. `ρ(r) := P_{θ,S,S′}[M_k = 0]`.

**Formalization Note.** The seed is implicit in the rule `Φ`. `1 − M_k` is the indicator of `{M_k = 0}`. -/
noncomputable def rhoR {k L : ℕ} (Δ : ℝ) (Φ : EpochRule k L) : ℝ :=
  E2 Δ fun _ S S' => 1 - M Φ k S S'

end ReplicableOL


