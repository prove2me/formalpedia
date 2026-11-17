-- Prove2me | Definitions.Def_ABPOnline_Supplement_dpH
-- name    : ABPOnline_Supplement_dpH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:35:12.913449+00:00
-- url     : https://prove2.me/theorems/74272289-98e1-495b-a96d-a70b4dba6b81
-- title:
--   Piecewise-constant weights and the heat-semigroup recursion $H_{m-1},\dots,H_0$ of (38)–(39)
-- statement:
--   Let $0=t_0<t_1<\dots<t_m=1$ be a grid, $a_0,\dots,a_{m-1}>0$ weights and $\Delta_i=t_{i+1}-t_i$. The **piecewise-constant weight** is $\eta(t)=a_i$ for $t_i\le t<t_{i+1}$. With $P_s$ the one-dimensional heat semigroup, $P_sf(x)=\int f(x+y)\,dN(0,s)(y)$, define backwards
--   $$
--   H_{m-1}:=P_{\Delta_{m-1}}\mathbf 1_{[\kappa,\infty)},\qquad H_i:=P_{\Delta_i}\big(H_{i+1}^{a_{i+1}/a_i}\big)\quad(i=m-2,\dots,0).
--   $$
--
--   These functions take values in $(0,1]$, and $-2a_0\log H_0(0)$ is the value of the weighted relaxation (Theorem 5.3).
--
--   **Formalization Note** The grid and the weights are sequences indexed by $\mathbb N$, of which $t_0,\dots,t_m$ and $a_0,\dots,a_{m-1}$ are used. The weight is the sum $\sum_{i<m}a_i\mathbf 1_{[t_i,t_{i+1})}$, which is $0$ outside $[0,1)$. $H_i$ is computed by a recursion on $m-1-i$; the power is the real power.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Theorem 5.3, (38)–(39), p.20 (PDF p.21)

import Mathlib
import Definitions.Def_ABPOnline_heatSG

set_option autoImplicit false

namespace ABPOnline.Supplement

/-- The **piecewise-constant weight** `η(s) = a_i` for `t_i ≤ s < t_{i+1}`, `0 ≤ i < m`
(Jo–Lee, arXiv:2609.02124, Theorem 5.3, printed p.20, PDF p.21).

**Formalization Note** The grid `t` and the values `a` are sequences indexed by `ℕ`; only
`t 0, …, t m` and `a 0, …, a (m-1)` are used. For a strictly increasing grid the intervals
`[t_i, t_{i+1})` are disjoint, so the sum has at most one nonzero term and equals `a_i` on
`[t_i, t_{i+1})`; outside `[t_0, t_m)` (in particular at `s = t_m`) it is `0`, which does not
matter for an integral over `(0,1)`. -/
noncomputable def pcWeight (m : ℕ) (t a : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, if t i ≤ s ∧ s < t (i + 1) then a i else 0

/-- Auxiliary backward recursion: `dpHaux κ m t a j = H_{m-1-j}` (arXiv:2609.02124, (38)–(39),
p.20). Step `0` is `H_{m-1} = P_{Δ_{m-1}} 1_{[κ,∞)}`; step `j+1` is, with `i = m-(j+2)`,
`H_i = P_{Δ_i}(H_{i+1}^{a_{i+1}/a_i})`, `Δ_i = t_{i+1} − t_i`. -/
noncomputable def dpHaux (κ : ℝ) (m : ℕ) (t a : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => heatSG (t m - t (m - 1)) (Set.indicator (Set.Ici κ) (fun _ => (1 : ℝ)))
  | j + 1 => heatSG (t (m - (j + 2) + 1) - t (m - (j + 2)))
      (fun x => dpHaux κ m t a j x ^ (a (m - (j + 2) + 1) / a (m - (j + 2))))

/-- The functions `H_i`, `0 ≤ i ≤ m-1`, of the dynamic-programming recursion of Theorem 5.3
(Jo–Lee, arXiv:2609.02124, (38)–(39), printed p.20, PDF p.21):
`H_{m-1} := P_{Δ_{m-1}} 1_{[κ,∞)}` and, for `i = m-2, …, 0`, `H_i := P_{Δ_i}(H_{i+1}^{a_{i+1}/a_i})`,
with `P_s` the published heat semigroup `ABPOnline.heatSG` and `Δ_i = t_{i+1} − t_i`.

**Formalization Note** `dpH κ m t a i = dpHaux κ m t a (m-1-i)`; meaningful for `i ≤ m-1`. The
indicator is of the closed half-line `[κ,∞)`. The power is `Real.rpow`; the base takes values in
`[0,1]` for the paper's data, where `Real.rpow` is the usual power. -/
noncomputable def dpH (κ : ℝ) (m : ℕ) (t a : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  dpHaux κ m t a (m - 1 - i)

end ABPOnline.Supplement


