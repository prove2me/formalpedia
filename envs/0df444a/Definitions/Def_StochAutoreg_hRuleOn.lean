-- Prove2me | Definitions.Def_StochAutoreg_hRuleOn
-- name    : StochAutoreg_hRuleOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:25.938168+00:00
-- url     : https://prove2.me/theorems/2c2aff33-62b6-4f20-9f91-8862bc457fa1
-- title:
--   Active rules $h_{b,s}$ of the family $H_D$
-- statement:
--   For $b\in\{0,1\}$ and $s\in\{-1,1\}^D$, the active generator $h_{b,s}$ sets, for $0\le j\le D$ and $|z|<M$,
--
--   $$p_{h_{b,s}}(x_jz)=\begin{cases}1,&|z|=0,\\ b,&|z|=1\text{ or }(j=0,\ |z|=M-1),\\ \tfrac12+t_Hs_j,&j\ge1,\ 2\le|z|<J+2,\\ \mathbf 1\{\sum_{t=3}^{J+2}z_t>J/2\},&j\ge1,\ |z|=M-1,\\ \tfrac12,&\text{otherwise.}\end{cases}$$
--
--   The root $x_0$ is the anchor.
--
--   **Formalization Note** The token $z_t$ is generated at depth $t-1$. In Lean the anchor is index `0` and $x_{i+1}$ is index `Fin.succ i`, with sign `s i`.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §7, "The second family H_D", p.15

import Mathlib
import Definitions.Def_StochAutoreg_clampI

namespace StochAutoreg

/-- The active generators `h_{b,s}` of the family `H_D`, in the order of the display:
`1` if `|z| = 0`; `b` if `|z| = 1` or (`j = 0` and `|z| = M-1`); `1/2 + t_H s_j` if `j ≥ 1` and `2 ≤ |z| < J+2`;
`1{∑_{t=3}^{J+2} z_t > J/2}` if `j ≥ 1` and `|z| = M-1`; `1/2` otherwise.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §7 "The second family `H_D`", p.15.

**Formalization Note.** Tokens are 1-indexed in the paper and `z_t` is generated at depth `t-1`, so
`(z.drop 2).take J` is `z₃, …, z_{J+2}`. Root `0` is the anchor `x₀`; `s : Fin D → ℤˣ` indexes `j ∈ [D]`, and root
`Fin.succ i` is `x_{i+1}` with sign `s i`. -/
noncomputable def hRuleOn (J M : ℕ) (tH : ℝ) {D : ℕ} (b : Bool) (s : Fin D → ℤˣ)
    (j : Fin (D + 1)) (z : List Bool) : unitInterval :=
  clampI <|
    if z.length = 0 then 1
    else if z.length = 1 ∨ (j = 0 ∧ z.length = M - 1) then (if b then 1 else 0)
    else Fin.cases (motive := fun _ => ℝ) (1 / 2)
      (fun i =>
        if 2 ≤ z.length ∧ z.length < J + 2 then 1 / 2 + tH * ((s i : ℤ) : ℝ)
        else if z.length = M - 1 then
          (if J < 2 * ((z.drop 2).take J).count true then 1 else 0)
        else 1 / 2) j

end StochAutoreg


