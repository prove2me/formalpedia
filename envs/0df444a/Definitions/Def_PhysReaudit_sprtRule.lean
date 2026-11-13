-- Prove2me | Definitions.Def_PhysReaudit_sprtRule
-- name    : PhysReaudit_sprtRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:45:47.243525+00:00
-- url     : https://prove2.me/theorems/1ba54edd-53d8-4456-a166-16a63a013570
-- title:
--   The two-sided sequential likelihood-ratio rule of Theorem 4
-- statement:
--   The **two-sided SPRT** of Theorem 4 traverses full episodes, restarting after every navigation failure, until each next target observation $Y_i$ is obtained. After the $n$-th target observation ($n\ge1$) it computes
--
--   $$
--   S_n=\sum_{i=1}^{n}\{Y_iz_-+(1-Y_i)z_+\},\qquad A=\log(1/\delta),
--   $$
--
--   accepts when $S_n\ge A$ (upper boundary), stops without a certificate when $S_n\le -A$ (lower boundary), and continues otherwise. It never stops before its first target observation and ignores old data.
--
--   **Formalization Note** It is the full-traversal rule whose stopping decision is this two-sided boundary test on the target outcomes seen so far; the thresholds are given by $q_0$, $t$ and $\delta$.
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), proof of Theorem 4, p.4 (PDF p.5): "Traverse full episodes until each next target observation Yi is obtained … Accept at the upper boundary; at the lower boundary stop without a certificate."

import Mathlib
import Definitions.Def_PhysReaudit_Rule
import Definitions.Def_PhysReaudit_fullTraversalRule
import Definitions.Def_PhysReaudit_sprtS

namespace PhysReaudit

/-- The SPRT's stopping decision on the target outcomes seen so far (any order): continue on the empty list;
otherwise, with `S` the sum of the increments and `A = log(1/δ)`, accept if `S ≥ A`, stop without a
certificate if `S ≤ −A`, continue otherwise. -/
noncomputable def sprtStop (q₀ t δ : ℝ) (ys : List Bool) : Option Bool :=
  if ys = [] then none
  else if Real.log (1 / δ) ≤ (ys.map (sprtIncr q₀ t)).sum then some true
  else if (ys.map (sprtIncr q₀ t)).sum ≤ -Real.log (1 / δ) then some false
  else none

/-- The two-sided sequential likelihood-ratio rule of the proof of Theorem 4
(Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), proof of Theorem 4, p.4 (PDF p.5)): "Set A = log(1/δ) and z− = log(q0/t) < 0. Traverse full episodes
until each next target observation Yi is obtained, and form Sn = Σ_{i=1}^n {Yi z− + (1 − Yi) z+},
τ = inf{n ≥ 1 : Sn ≥ A or Sn ≤ −A}. Accept at the upper boundary; at the lower boundary stop without a
certificate."

It is the full-traversal rule with stopping decision `sprtStop q₀ t δ`; it ignores the side variable and
never stops before its first target observation. -/
noncomputable def sprtRule (W : Type) [MeasurableSpace W] (q₀ t δ : ℝ) : Rule W :=
  fullTraversalRule W (sprtStop q₀ t δ)

end PhysReaudit


