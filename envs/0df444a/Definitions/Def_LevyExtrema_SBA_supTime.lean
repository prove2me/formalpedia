-- Prove2me | Definitions.Def_LevyExtrema_SBA_supTime
-- name    : LevyExtrema_SBA_supTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:37.769984+00:00
-- url     : https://prove2.me/theorems/dde98ee1-87ad-4b92-a9c9-1b7688e1f972
-- title:
--   First time $\tau_t(f)=\inf\{s\in[0,t]:\overline f_s=\overline f_t\}$ the supremum is attained
-- statement:
--   For a path $f:[0,\infty)\to\mathbb R$ and $t\ge0$, the **time of the supremum** is
--
--   $$\tau_t(f)=\inf\{s\in[0,t] : \overline f_s=\overline f_t\},$$
--
--   the first time at which the running supremum $\overline f$ reaches its final value $\overline f_t$. The condition is on $\overline f_s$, not on $f_s$: the set always contains $t$, and for a path that reaches its supremum only as a left limit, $\tau_t(f)$ is the time of that left limit.
--
--   For a Lévy process $X$, $\tau_T(X)$ is the third coordinate of the target vector $\chi=(X_T,\overline X_T,\tau_T)$.
--
--   **Formalization Note** The infimum is taken in $\mathbb R_{\ge0}$ over a set that contains $t$, so it is never the junk value of an empty set.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, §1.1, p. 3 (notation before Theorem 1)

import Mathlib
import Definitions.Def_LevyExtrema_SBA_runSup

open scoped NNReal

namespace LevyExtrema.SBA

/-- **First time τ_t(f) at which the supremum f̄_t is attained.**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, §1.1, p. 3:
"τ_t(f) = inf{s ∈ [0, t] : f̄_s = f̄_t} the first time the supremum f̄_t is attained".

`supTime f t = sInf {s ∈ [0, t] | runSup f s = runSup f t}`.

**Formalization Note.** The condition is on the running supremum `f̄_s`, exactly as printed, not
on `f_s`: the set always contains `t`, so it is nonempty and the infimum (in `ℝ≥0`) is never the
junk value of an empty set. For a càdlàg path that reaches its supremum only as a left limit this
is the time of that left limit. -/
noncomputable def supTime (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ≥0 :=
  sInf {s : ℝ≥0 | s ∈ Set.Icc 0 t ∧ runSup f s = runSup f t}

end LevyExtrema.SBA


