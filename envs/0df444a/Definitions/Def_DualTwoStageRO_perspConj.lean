-- Prove2me | Definitions.Def_DualTwoStageRO_perspConj
-- name    : DualTwoStageRO_perspConj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:44.973152+00:00
-- url     : https://prove2.me/theorems/92f80f9f-8223-4096-9642-7eb48a10e1ad
-- title:
--   Closed perspective $v\,g^*(u/v)$ of the conjugate
-- statement:
--   For $g:\mathbb R^n\to\mathbb R$, $u\in\mathbb R^n$ and $v\in\mathbb R$, the **perspective of the conjugate** $g^*$ is
--
--   $$v\,g^*\!\Big(\frac uv\Big)=\begin{cases} v\,g^*(u/v), & v>0,\\ 0, & v=0,\ u=0,\\ +\infty, & v=0,\ u\neq 0,\\ +\infty, & v<0.\end{cases}$$
--
--   The paper uses the notation $t f(\nu/t)$ for the perspective $h(\nu,t)$, defined as $tf(\nu/t)$ for $t>0$ and as the lower limit $\liminf_{(\nu',t')\to(\nu,0)}t'f(\nu'/t')$ at $t=0$ (Rockafellar 1970, p. 67). For $f=g^*$ with $g$ finite on $\mathbb R^n$ this closure at $t=0$ is the recession function of $g^*$, i.e. the support function of $\operatorname{dom}g=\mathbb R^n$: $0$ at $u=0$ and $+\infty$ otherwise.
--
--   This is the function in the constraints $v_i(g_i)^*(u_i/v_i)\le z_i$ of the set $\mathcal V$ of Theorem 1.
--
--   **Formalization Note** Values are in `EReal`. A weight $v=0$ with $u\neq0$ gives $+\infty$, not $0\cdot g^*(u/0)$; the latter convention would enlarge $\mathcal V$. Negative $v$ lies outside the perspective's domain $\mathbb R^n\times\mathbb R_+$ and gets $+\infty$.
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), §1.4, p.1795 (perspective, citing Rockafellar 1970, p.67); Theorem 1, p.1796 (the set V)

import Mathlib
import Definitions.Def_DualTwoStageRO_conj

namespace DualTwoStageRO

/-- **Perspective of the conjugate**, `v (g)^*(u / v)`, in its closed form.
de Ruiter, Zhen, den Hertog, Operations Research 71(5), 2023, §1.4, p.1795: the perspective of `f`
is `h(ν,t) = t f(ν/t)` for `t > 0` and `h(ν,0) = liminf_{(ν′,t′)→(ν,0)} t′ f(ν′/t′)`
(Rockafellar 1970, p.67); "we use tf(ν/t) to denote the perspective function h(ν,t)". It enters
the set `V` of Theorem 1, p.1796, as `v_i (g_i)^*(u_i / v_i) ≤ z_i`.

* `v > 0`: `v · g^*(u / v)`;
* `v = 0`: `0` if `u = 0` and `+∞` otherwise;
* `v < 0`: `+∞` (outside the perspective's domain `ℝⁿ × ℝ₊`).

**Formalization Note.** The page's definition of the perspective is for a real-valued `f`, while
`g^*` is extended-valued. At `v = 0` the value is read as Rockafellar's closure, i.e. the recession
function of `g^*`, which is the support function of `dom g = ℝⁿ`: `0` at `u = 0` and `+∞` otherwise.
The naive `0 · g^*(u/0) = 0` would be wrong for `u ≠ 0`. -/
noncomputable def perspConj {n : ℕ} (h : (Fin n → ℝ) → ℝ) (u : Fin n → ℝ) (v : ℝ) : EReal :=
  if 0 < v then (v : EReal) * conj h (v⁻¹ • u)
  else if v = 0 ∧ u = 0 then 0 else ⊤

end DualTwoStageRO


