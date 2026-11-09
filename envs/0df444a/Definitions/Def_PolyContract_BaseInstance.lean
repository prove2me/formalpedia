-- Prove2me | Definitions.Def_PolyContract_BaseInstance
-- name    : PolyContract_BaseInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:48:30.483132+00:00
-- url     : https://prove2.me/theorems/c0ec7bdf-97f2-4b55-b75a-80d62d5e8adb
-- title:
--   The base instance $(f_0,m,\beta)$ of Proposition C.10
-- statement:
--   On $E_0=\{C_0,C_1,C_2\}$ let $m:=(5,12,4)$, $\beta:=(1,4,4)$, and
--   $$f_0(\emptyset)=0,\ f_0(C_0)=\tfrac13,\ f_0(C_1)=\tfrac76,\ f_0(C_2)=\tfrac23,\ f_0(C_0C_1)=\tfrac76,\ f_0(C_0C_2)=1,\ f_0(C_1C_2)=\tfrac43,\ f_0(E_0)=\tfrac43.$$
--   The module also defines the cut form with arcs $C_0\to C_1$ of capacity $1/3$ and $C_1\to C_2$ of capacity $1/2$ and weights $0,2/3,2/3$, and the line $L_0(\alpha)=10+7\alpha$.
--
--   This is level 0 of the comb gadget: a three-element instance whose reward touches $L_0$ at two shares.
--
--   **Formalization Note** $C_0,C_1,C_2$ are the elements $0,1,2$ of a three-element type.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Proposition C.10, p.56 (PDF p.57)

import Mathlib
import Definitions.Def_PolyContract_QuadInstance
import Definitions.Def_PolyContract_CutForm

set_option autoImplicit false

namespace PolyContract

/-- The rank function `f₀` of the base (Klimm, Lippke, Warode, arXiv:2611.04934, version of
November 3, 2026, sha256 18cfc0a5…, Proposition C.10, p.56) on `E₀ = {C₀, C₁, C₂}`:
`f₀(∅) = 0`, `f₀(C₀) = 1/3`, `f₀(C₁) = 7/6`, `f₀(C₂) = 2/3`, `f₀(C₀C₁) = 7/6`, `f₀(C₀C₂) = 1`,
`f₀(C₁C₂) = 4/3`, `f₀(E₀) = 4/3`.

**Formalization Note** `C₀, C₁, C₂` are `0, 1, 2 : Fin 3`; the last branch is `S = E₀`. -/
noncomputable def f0 (S : Finset (Fin 3)) : ℝ :=
  if S = ∅ then 0
  else if S = {0} then 1 / 3
  else if S = {1} then 7 / 6
  else if S = {2} then 2 / 3
  else if S = {0, 1} then 7 / 6
  else if S = {0, 2} then 1
  else if S = {1, 2} then 4 / 3
  else 4 / 3

/-- The base instance `(f₀, m, β)` with `m := (5, 12, 4)` and `β := (1, 4, 4)`
(arXiv:2611.04934, Proposition C.10, p.56). -/
noncomputable def baseInstance : QuadInstance (Fin 3) where
  f := f0
  m := ![5, 12, 4]
  β := ![1, 4, 4]

/-- The cut form of Proposition C.10 (arXiv:2611.04934, p.56): the arcs `C₀ → C₁` of capacity
`1/3` and `C₁ → C₂` of capacity `1/2`, and the weights `0, 2/3, 2/3` on `C₀, C₁, C₂`. -/
def baseCutForm : CutForm (Fin 3) where
  arcs := [(0, 1, 1 / 3), (1, 2, 1 / 2)]
  ω := ![0, 2 / 3, 2 / 3]

/-- The line `L₀(α) := p₀ + q₀α` with `p₀ := 10` and `q₀ := 7` (arXiv:2611.04934,
Proposition C.10, p.56). -/
def baseLine (α : ℝ) : ℝ := 10 + 7 * α

end PolyContract


