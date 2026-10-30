-- Prove2me | Definitions.Def_PorteusGenSS_valueFn
-- name    : PorteusGenSS_valueFn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:17:02.442861+00:00
-- url     : https://prove2.me/theorems/be6919a7-a8cd-435d-bffe-93ac48daa44f
-- title:
--   Value functions $f_n$
-- statement:
--   The value functions of the finite-horizon inventory problem: $f_0$ is the terminal cost and, for $n\ge1$,
--
--   $$
--   f_n(x)=\inf_{y\ge x}\{c(y-x)+h_n(y)\},\qquad h_n=(m+\alpha f_{n-1})*\varphi,
--   $$
--
--   where $m$ is the one-period holding and shortage cost, $\alpha\in[0,1]$ the discount factor and $\varphi$ the demand density.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), eqs. (2)–(4), p. 413

import Mathlib
import Definitions.Def_PorteusGenSS_conv
import Definitions.Def_PorteusGenSS_valueOp

namespace PorteusGenSS

/-- **The value functions fₙ, equations (2)–(4).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §III, eqs. (2)–(4), p. 413: "(2) fn(x) = inf_{y≥x} {c(y − x) + L(y) + αfn−1∗φ(y)}.
Let (3) hn = L + αfn−1∗φ = (m + αfn−1)∗φ. Then (4) fn(x) = inf_{y≥x} {c(y − x) + hn(y)}."
"Let f0(x) denote the cost associated with having x units left over … at the end of the last
period."

`valueFn c α φ m f0 n` is `fₙ`: `f₀` is the terminal cost and
`f_{n+1} = valueOp c ((m + α fₙ) ∗ φ)`.

**Formalization Note.** `hₙ` is written in the paper's second form of (3), `(m + αf_{n−1})∗φ`.
The index of `valueFn` is the paper's period index (`valueFn … 0 = f₀`). -/
noncomputable def valueFn (c : ℝ → ℝ) (α : ℝ) (φ m f0 : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f0
  | n + 1 => valueOp c (conv (fun x => m x + α * valueFn c α φ m f0 n x) φ)

end PorteusGenSS


