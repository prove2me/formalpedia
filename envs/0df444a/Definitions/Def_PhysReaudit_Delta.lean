-- Prove2me | Definitions.Def_PhysReaudit_Delta
-- name    : PhysReaudit_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:42:20.586073+00:00
-- url     : https://prove2.me/theorems/cccb29a3-08eb-48cb-bada-6ba24f2bc582
-- title:
--   Advantage $\Delta_q=b-\kappa pq$ and the thresholds $t$, $q_0$, $z_\pm$
-- statement:
--   Let $p=a^d$ be the reach probability of the target. A candidate policy receives a known root bonus $b$ and enters the chain with probability $1-\kappa$, so its advantage over the reference under target parameter $q$ is
--
--   $$
--   \Delta_q=b-\kappa p q .
--   $$
--
--   With $0<\varepsilon<b<\kappa p$ the module also fixes the two thresholds and the two log-likelihood increments of the paper:
--
--   $$
--   t=\frac{b}{\kappa p},\qquad q_0=\frac{b-\varepsilon}{\kappa p},\qquad z_+=\log\frac{1-q_0}{1-t},\qquad z_-=\log\frac{q_0}{t}.
--   $$
--
--   Then $0<q_0<t<1$, $\Delta_q<0$ exactly when $q>t$ and $\Delta_q\ge\varepsilon$ exactly when $q\le q_0$; $z_+>0>z_-$.
--
--   **Formalization Note** $z_\pm$ are written as functions of the pair $(q_0,t)$ and are used only for $0<q_0<t<1$, where every logarithm has a positive argument.
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), §4, pp.2–3 (PDF pp.3–4): display "∆q = b − κpq", the definitions of t and q0; Theorem 4 (z+), p.3; proof of Theorem 4 (z−), p.4

import Mathlib

namespace PhysReaudit

/-- The candidate's advantage `Δ_q = b − κ p q` with reach probability `p = a^d`
(Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), §4, p.2 (PDF p.3), display "∆q = b − κpq"). -/
noncomputable def Delta (a : ℝ) (d : ℕ) (b κ q : ℝ) : ℝ :=
  b - κ * a ^ d * q

/-- The soundness threshold `t = b / (κ p)`, `p = a^d` (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), §4, p.3 (PDF p.4)).
`Δ_q < 0` iff `q > t`. -/
noncomputable def tThr (a : ℝ) (d : ℕ) (b κ : ℝ) : ℝ :=
  b / (κ * a ^ d)

/-- The completeness threshold `q₀ = (b − ε) / (κ p)`, `p = a^d` (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), §4, p.3 (PDF p.4)).
`Δ_q ≥ ε` iff `q ≤ q₀`. -/
noncomputable def q0 (a : ℝ) (d : ℕ) (b κ ε : ℝ) : ℝ :=
  (b - ε) / (κ * a ^ d)

/-- `z₊ = log((1 − q₀)/(1 − t))` (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), Theorem 4, p.3 (PDF p.4)), the log-likelihood-ratio increment of
a target observation `Y = 0`.

**Formalization Note** Written as a function of the pair `(q₀, t)`; it is used only for `0 < q₀ < t < 1`,
where the argument of the logarithm is positive. -/
noncomputable def zPlus (q₀ t : ℝ) : ℝ :=
  Real.log ((1 - q₀) / (1 - t))

/-- `z₋ = log(q₀/t)` (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), proof of Theorem 4, p.4 (PDF p.5)), the log-likelihood-ratio increment of a
target observation `Y = 1`.

**Formalization Note** Used only for `0 < q₀ < t < 1`, where `z₋ < 0`. -/
noncomputable def zMinus (q₀ t : ℝ) : ℝ :=
  Real.log (q₀ / t)

end PhysReaudit


