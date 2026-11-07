-- Prove2me | Definitions.Def_ReplicableOL_Xterm
-- name    : ReplicableOL_Xterm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:09.841129+00:00
-- url     : https://prove2.me/theorems/2446ff02-a917-473c-9abe-f54a78255eef
-- title:
--   The comparator's edge $X$ on bits
-- statement:
--   The comparator's edge $X=\sum_{j\le k}(L\mu_j+Z_j)$ as a function of the means and the bits. It does not actually depend on $\theta$: it equals the number of ones minus $kL/2$.
--
--   **Formalization Note** The form on block sequences of `comparatorEdge`; the two agree through `embed`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8

import Mathlib
import Definitions.Def_ReplicableOL_eps

namespace ReplicableOL

/-- **The comparator's edge $X$ on bits.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8. `X := Σ_{j≤k} x_j`, `x_j := Lμ_j + Z_j`, `Z_j := Σ_{t∈E_j} ε_t`.

**Formalization Note.** The form on block sequences of `comparatorEdge`; the two agree through `embed`. -/
noncomputable def Xterm {k L : ℕ} (θ : Fin k → ℝ) (S : Bits k L) : ℝ :=
  ∑ j : Fin k, ((L : ℝ) * θ j + ∑ i : Fin L, eps θ S j i)

end ReplicableOL


