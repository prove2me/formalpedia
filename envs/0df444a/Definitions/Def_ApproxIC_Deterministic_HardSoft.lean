-- Prove2me | Definitions.Def_ApproxIC_Deterministic_HardSoft
-- name    : ApproxIC_Deterministic_HardSoft
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:44.017566+00:00
-- url     : https://prove2.me/theorems/57348fa5-21a6-4e13-bd14-b70bf3583793
-- title:
--   Theorem 2, p. 24 — the hard/soft floor mechanism m_d(p, s) and the posted price at p
-- statement:
--   The **hard/soft floor mechanism** with hard floor $p$ and soft floor $s$ (Theorem 2 of Balseiro, Besbes and Castro) is the deterministic mechanism $m_d(p,s)=(x_d,t_d)$ with
--   $$x_d(v)=\mathbf 1\{v\ge p\},\qquad t_d(v)=v\,\mathbf 1\{v\in[p,s)\}+s\,\mathbf 1\{v\ge s\}.$$
--   A buyer who reports below the hard floor gets nothing and pays nothing; between the hard and the soft floor he receives the item and pays his own report; above the soft floor he receives the item and pays $s$.
--
--   The **posted-price mechanism** at price $p$ is the case $s=p$: $x(v)=\mathbf 1\{v\ge p\}$ and $t(v)=p\,\mathbf 1\{v\ge p\}$.
--
--   Theorem 2 shows that among deterministic $\varepsilon$-incentive-compatible mechanisms a hard/soft floor mechanism with $s=p+\varepsilon$ is optimal; the posted price at an optimal price $p^\star$ is the classical optimum at $\varepsilon=0$.
--
--   **Formalization Note** The theorem's display prints $t_d(v)=v\,\mathbf 1\{v\in[p,s]\}+s\,\mathbf 1\{v\in[s,\bar v]\}$, which counts $2s$ at $v=s$; the proof (p. 52) has $[p,s)$, which is used here. The mechanism is defined on all of $\mathbb R$ by the same formulas; only its values on $S=[0,\bar v]$ enter feasibility and revenue. It does not depend on the value distribution.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 24, Theorem 2 (hard/soft floor mechanism), read with Appendix B, p. 52; p. 13, §2.1 (posted-price mechanism)

import Mathlib
import Definitions.Def_ApproxIC_Deterministic_Setting

namespace ApproxIC.Deterministic

/-- The hard/soft floor mechanism `m_d(p, s)` of Theorem 2 (p. 24; payment region read as in the
proof, p. 52): `x_d(v) = 1{v ≥ p}` and
`t_d(v) = v · 1{v ∈ [p, s)} + s · 1{v ≥ s}`. A buyer reporting below the hard floor `p` gets
nothing and pays nothing; between the hard floor and the soft floor `s` he gets the item and pays
his report; above the soft floor he gets the item and pays `s`. -/
noncomputable def hardSoft (p s : ℝ) : Mech where
  x v := if p ≤ v then 1 else 0
  t v := if v < p then 0 else if v < s then v else s

/-- The posted-price mechanism at price `p` (p. 13): `x(v) = 1{v ≥ p}`, `t(v) = p · 1{v ≥ p}`.
It is the hard/soft floor mechanism with `s = p`. -/
noncomputable def postedPrice (p : ℝ) : Mech := hardSoft p p

end ApproxIC.Deterministic


