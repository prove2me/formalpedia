-- Prove2me | Definitions.Def_PhysReaudit_Supplement_certL
-- name    : PhysReaudit_Supplement_certL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:24:10.89125+00:00
-- url     : https://prove2.me/theorems/19b0ef2d-081e-4eb6-af3c-a93d552f21b9
-- title:
--   The fixed-target-budget family certificate $L(\kappa)=b-\kappa pU$, $U=\min\{1,\hat q+r\}$ (Theorem 6)
-- statement:
--   This file defines the audit and the certificate of Theorem 6.
--
--   1. **The fixed-budget audit** $R_n$: it traverses full root-started episodes (one root setup, then navigation attempts until a failure or the target, then one target observation) and halts as soon as $n$ target outcomes have been recorded.
--   2. **The target mean** $\hat q$: the number of successes among the target outcomes recorded by $R_n$ when it halts, divided by $n$.
--   3. **The radius and the upper value**
--   $$
--   r=\sqrt{\frac{\log(2/\delta)}{2n}},\qquad U=\min\{1,\hat q+r\}.
--   $$
--   4. **The certificate** for the policy $\pi_\kappa$, with reach probability $p=a^d$:
--   $$
--   L(\kappa)=b-\kappa pU .
--   $$
--   The certificate accepts $\pi_\kappa$ precisely when $L(\kappa)\ge0$.
--
--   One batch of $n$ target observations serves every policy of the family $\{\pi_\kappa:0\le\kappa\le\kappa_{\max}\}$ at once; Theorem 6 states that it is simultaneously sound and $\varepsilon$-complete.
--
--   **Formalization Note** The audit is the published full-traversal rule with the stopping decision "halt once $n$ target outcomes are recorded" (it halts with `accept`; the certificate does not depend on the halting action). On the null set of paths where the audit never halts, the recorded list is empty and $\hat q=0$.
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), Theorem 6, p.5 (PDF p.6): "take exactly n = ⌈2(κmax p/ε)² log(2/δ)⌉ target observations through full root-started episodes. With target mean q̂, set r = √(log(2/δ)/(2n)), U = min{1, q̂ + r}, L(κ) = b − κpU. Accept precisely when L(κ) ≥ 0."

import Mathlib
import Definitions.Def_PhysReaudit_Rule
import Definitions.Def_PhysReaudit_run
import Definitions.Def_PhysReaudit_fullTraversalRule

namespace PhysReaudit.Supplement

open PhysReaudit

/-- The fixed-target-budget audit of Theorem 6 (Q. Li, *When Can Physical Evidence Survive a World-Model
Update?*, review revision of 3 November 2026 (sha256 a20c437b…), Theorem 6, p.5 (PDF p.6): "take exactly n
target observations through full root-started episodes").

It traverses full root-started episodes (`fullTraversalRule`) and halts as soon as `n` target outcomes have
been recorded; until then it continues.

**Formalization Note** The halting action is `accept`; whether the audit halts with `accept` or `stop` is
immaterial, since the family certificate is a function of the recorded target outcomes only (`certL`). -/
def budgetRule (W : Type) [MeasurableSpace W] (n : ℕ) : Rule W :=
  fullTraversalRule W (fun ys => if n ≤ ys.length then some true else none)

open Classical in
/-- The target outcomes recorded by rule `R` when it halts (most recent first): the target outcomes of the
history at the first decision time at which the run is halted. On a path where `R` never halts this is the
empty list.

**Formalization Note** For `budgetRule W n` with `a > 0` the audit halts almost surely, and then this list
has length exactly `n`. -/
noncomputable def haltTargets {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (ω : Omega W) :
    List Bool :=
  if h : stops R d ω then targets (run R d ω (Nat.find h)).hist else []

/-- The target mean `q̂` of the fixed-budget audit (Theorem 6, p.5 (PDF p.6): "With target mean q̂"):
the number of successful target outcomes recorded by `budgetRule W n`, divided by `n`. -/
noncomputable def qhat {W : Type} [MeasurableSpace W] (d n : ℕ) (ω : Omega W) : ℝ :=
  ((haltTargets (budgetRule W n) d ω).count true : ℝ) / n

/-- The radius `r = √(log(2/δ)/(2n))` of Theorem 6 (p.5, PDF p.6). -/
noncomputable def certR (n : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt (Real.log (2 / δ) / (2 * n))

/-- The upper confidence value `U = min{1, q̂ + r}` of Theorem 6 (p.5, PDF p.6). -/
noncomputable def certU {W : Type} [MeasurableSpace W] (d n : ℕ) (δ : ℝ) (ω : Omega W) : ℝ :=
  min 1 (qhat d n ω + certR n δ)

/-- The family certificate of Theorem 6 (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*,
review revision of 3 November 2026 (sha256 a20c437b…), Theorem 6, p.5 (PDF p.6), display
"L(κ) = b − κpU"): `L(κ) = b − κ p U` with `p = a^d`, computed from the `n` target outcomes of the
fixed-budget audit on the outcome `ω`. The certificate accepts the policy `π_κ` precisely when `L(κ) ≥ 0`.

**Formalization Note** `q̂`, hence `U` and `L`, are read from the recorded target outcomes of
`budgetRule W n` (`haltTargets`); on the null set of paths where the audit never halts the list is empty. -/
noncomputable def certL {W : Type} [MeasurableSpace W] (a : ℝ) (d n : ℕ) (b δ κ : ℝ) (ω : Omega W) : ℝ :=
  b - κ * a ^ d * certU (W := W) d n δ ω

end PhysReaudit.Supplement


