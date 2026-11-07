-- Prove2me | Definitions.Def_ReplicableOL_Nterm
-- name    : ReplicableOL_Nterm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:08.371661+00:00
-- url     : https://prove2.me/theorems/f0efd2d7-c122-487b-b709-fd7722aa20fa
-- title:
--   Noise term $N$
-- statement:
--   The **noise term** $N=\sum_{t\le kL}\sigma_t\varepsilon_t$, with $\sigma_t=2\cdot\mathbf 1\{a_t=1\}-1$. For a causal learner it is a martingale.
--
--   **Formalization Note** `σ_t` is `1` when Lean's action is `0`, the paper's expert 1, and `−1` otherwise.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8

import Mathlib
import Definitions.Def_ReplicableOL_EpochRule
import Definitions.Def_ReplicableOL_eps
import Definitions.Def_ReplicableOL_hist

namespace ReplicableOL

/-- **Noise term $N$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8. `N := Σ_{t≤kL} σ_t ε_t` with `σ_t := 2·1{a_t = 1} − 1`.

**Formalization Note.** `σ_t` is `1` when Lean's action is `0`, the paper's expert 1, and `−1` otherwise. -/
noncomputable def Nterm {k L : ℕ} (Φ : EpochRule k L) (θ : Fin k → ℝ) (S : Bits k L) : ℝ :=
  ∑ j : Fin k, ∑ i : Fin L, (if Φ j (hist S j) (S j) i = 0 then 1 else -1) * eps θ S j i

end ReplicableOL


