-- Prove2me | Definitions.Def_FrechetPrefs_InadaUtility
-- name    : FrechetPrefs_InadaUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:17.2984+00:00
-- url     : https://prove2.me/theorems/d22b7296-9af0-4749-bbd5-77199483e6fe
-- title:
--   Assumption 1: a $C^2$ utility with the Inada conditions and $|u''|$ decreasing
-- statement:
--   A utility $u:(0,\infty)\to\mathbb R$ satisfies **Assumption 1** when it is $C^2$, satisfies the Inada conditions
--   $$\lim_{x\to0}u'(x)=+\infty,\qquad \lim_{x\to\infty}u'(x)=0,$$
--   and $x\mapsto|u''(x)|$ is decreasing.
--
--   Logarithmic and CRRA utilities with $\gamma>1$ satisfy it. It is the hypothesis on preferences behind every result of the mission.
--
--   **Formalization Note** $u$ is a total function on $\mathbb R$ constrained on $(0,\infty)$ only; that set is open, so `deriv u` and `deriv (deriv u)` are the true derivatives there. "Decreasing" is read weakly, the more general reading. Neither $u'>0$ nor concavity is assumed; their weak forms follow.
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), Assumption 1, p.10

import Mathlib

open Set Filter Topology

namespace FrechetPrefs

/-- Assumption 1, p.10 of Petracou–Xepapadeas–Yannacopoulos, manuscript MS-DEC-19-01009-REV: the
utility `u : ℝ₊ → ℝ` is `C²`, satisfies the Inada conditions `u′(0) = lim_{x→0} u′(x) = +∞` and
`u′(∞) = lim_{x→∞} u′(x) = 0`, and `|u″|` is decreasing.

**Formalization Note.** `u` is a total function on `ℝ` and only its values on `(0,∞)` are
constrained. Since `(0,∞)` is open, `deriv u` and `deriv (deriv u)` are the true derivatives there.
"Decreasing" is read as weakly decreasing, the more general reading. Neither `u′ > 0` nor concavity is
assumed: the weak forms follow (`inada_consequences`). -/
def IsInadaUtility (u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Ioi 0) ∧
    Tendsto (deriv u) (𝓝[>] 0) atTop ∧
    Tendsto (deriv u) atTop (𝓝 0) ∧
    AntitoneOn (fun x => |deriv (deriv u) x|) (Ioi 0)

end FrechetPrefs


