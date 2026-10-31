-- Prove2me | Definitions.Def_AdaDiscRL_nearOptSet
-- name    : AdaDiscRL_nearOptSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:33.149326+00:00
-- url     : https://prove2.me/theorems/521b3140-487c-40dd-931e-3a4bdd2bfa03
-- title:
--   Near-optimal set $Z^r_h$
-- statement:
--   For a step $h$ and a scale $r$, the **near-optimal set** is
--   $$
--   Z^r_h=\{(x,a)\in\mathcal S\times\mathcal A:\ \mathrm{gap}_h(x,a)\le C_L(H+1)r\},
--   $$
--   where $C_L$ is a constant depending on the Lipschitz constants of the problem. The zooming dimension measures how fast its packing numbers grow as $r\to0$.
--
--   **Formalization Note** $C_L$ is a parameter; the theorems instantiate it as $aL$ with $L=1+L_r+L_V+L_VL_T$ and a universal $a$. The Lean step $h$ is the paper's $h+1$; $H+1$ is the paper's literal.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Definition 2.6, p.11

import Mathlib
import Definitions.Def_AdaDiscRL_gap

namespace AdaDiscRL

/-- **Near-optimal set** (arXiv:2110.15843v3, Definition 2.6, p.11):
`Z_h^r = {(x, a) ∈ S × A | gap_h(x, a) ≤ C_L (H + 1) r}`, where `C_L` is a constant depending on the
Lipschitz constants. `h : Fin H` is the paper's step `h + 1`; `H + 1` is the paper's literal. -/
def nearOptSet {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] {H : ℕ}
    (M : EpisodicMDP S A H) (CL : ℝ) (h : Fin H) (r : ℝ) : Set (S × A) :=
  {p | gap M h p ≤ CL * ((H : ℝ) + 1) * r}

end AdaDiscRL


