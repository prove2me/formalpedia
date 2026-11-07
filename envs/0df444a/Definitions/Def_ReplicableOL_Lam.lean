-- Prove2me | Definitions.Def_ReplicableOL_Lam
-- name    : ReplicableOL_Lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:49:24.004219+00:00
-- url     : https://prove2.me/theorems/5864c843-d302-456d-99c0-2f2d891b4ca8
-- title:
--   Accumulated hazard $\Lambda_k$
-- statement:
--   The **accumulated first-disagreement hazard** $\Lambda_k=\sum_{j\le k}M_{j-1}h_j$, whose expectation is exactly $\rho(r)$.
--
--   **Formalization Note** In 0-based form, `Σ_{j : Fin k} M Φ j * hazard Δ Φ j …`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8

import Mathlib
import Definitions.Def_ReplicableOL_M
import Definitions.Def_ReplicableOL_hazard
import Definitions.Def_ReplicableOL_hist

namespace ReplicableOL

/-- **Accumulated hazard $\Lambda_k$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8. `Λ_k := Σ_j M_{j−1} h_j`.

**Formalization Note.** In 0-based form, `Σ_{j : Fin k} M Φ j * hazard Δ Φ j …`. -/
noncomputable def Lam {k L : ℕ} (Δ : ℝ) (Φ : EpochRule k L) (S S' : Bits k L) : ℝ :=
  ∑ j : Fin k, M Φ j S S' * hazard Δ Φ j (hist S j) (hist S' j)

end ReplicableOL


