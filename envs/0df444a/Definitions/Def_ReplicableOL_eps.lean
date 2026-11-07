-- Prove2me | Definitions.Def_ReplicableOL_eps
-- name    : ReplicableOL_eps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:26.552198+00:00
-- url     : https://prove2.me/theorems/1125da9d-987c-46a4-a48e-9004cc6de315
-- title:
--   Centred noise $\varepsilon_t$
-- statement:
--   The **centred noise** $\varepsilon_t=B_t-\frac12-\mu_j$ of a round $t$ in epoch $j$.
--
--   **Formalization Note** Position `i` of epoch `j`, with the bit `S j i` read as a real number.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8

import Mathlib
import Definitions.Def_ReplicableOL_Bits

namespace ReplicableOL

/-- **Centred noise $\varepsilon_t$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8. `ε_t := B_t − 1/2 − μ_j`.

**Formalization Note.** Position `i` of epoch `j`, with the bit `S j i` read as a real number. -/
noncomputable def eps {k L : ℕ} (θ : Fin k → ℝ) (S : Bits k L) (j : Fin k) (i : Fin L) : ℝ :=
  (if S j i then 1 else 0) - 1 / 2 - θ j

end ReplicableOL


