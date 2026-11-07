-- Prove2me | Definitions.Def_ReplicableOL_lawP
-- name    : ReplicableOL_lawP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:04.853061+00:00
-- url     : https://prove2.me/theorems/196c9691-4e8c-4591-8300-bbfe1019a604
-- title:
--   The law $P_\theta$ of Construction C
-- statement:
--   **Construction C.** Split $[T]$ into $k=\lfloor T/L\rfloor$ epochs of length $L$. Given $\theta=(\mu_1,\dots,\mu_k)$, the losses are independent, with $\ell_t=(B_t,1-B_t)$, $B_t\sim\mathrm{Bern}(1/2+\mu_j)$ in epoch $j$, and $\ell_t=(1/2,1/2)$ on the trailing rounds. $P_\theta$ is the resulting law of $S$.
--
--   **Formalization Note** `k = T / L` (natural-number division). The measure is a product over `Fin T` of `roundLaw`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7

import Mathlib
import Definitions.Def_ReplicableOL_roundLaw
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **The law $P_\theta$ of Construction C.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7. "For each θ the law P_θ of S is a product law, with point masses on the trailing rounds."

**Formalization Note.** `k = T / L` (natural-number division). The measure is a product over `Fin T` of `roundLaw`. -/
noncomputable def lawP (T L : ℕ) (θ : Fin (T / L) → ℝ) : Measure (Fin T → Fin 2 → ℝ) :=
  Measure.pi fun t : Fin T => roundLaw (T / L) L θ t

end ReplicableOL


