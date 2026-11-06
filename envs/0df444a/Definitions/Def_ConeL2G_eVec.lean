-- Prove2me | Definitions.Def_ConeL2G_eVec
-- name    : ConeL2G_eVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:36.459954+00:00
-- url     : https://prove2.me/theorems/de84340a-1553-4229-be95-e25f5ab43b14
-- title:
--   The normalized centered indicator $e_{i,c}$
-- statement:
--   For a vertex $i$, a color $c$ and an assignment $x$,
--   $$e_{i,c}(x)=\begin{cases}\dfrac{\mathbb 1\{x_i=c\}-p_{i,c}}{\sqrt{p_{i,c}(1-p_{i,c})}}, & c\in L_i^{-x_{N_H(i)}},\\[2mm] 0, & \text{otherwise.}\end{cases}$$
--   Given $X_{-i}=x_{-i}$, $e_{i,c}$ has conditional mean $0$ and conditional second moment $1$.
--
--   **Formalization Note** When only one color is available ($p_{i,c}=1$) the printed formula is $0/0$; Lean's convention $x/0=0$ gives $e_{i,c}=0$ there. On such a fiber $D_i=0$, so nothing depends on this value.
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Section 2.1, pp.7–8

import Mathlib
import Definitions.Def_ConeL2G_pMarg

namespace ConeL2G

/-- **The normalized centered indicator** `e_{i,c}`. Li–Oveis Gharan, arXiv:2610.37721,
Section 2.1, pp.7–8: for `c ∈ L_i^{−x_{N_H(i)}}`,
"`e_{i,c}(x) = (1{xᵢ = c} − p_{i,c}) / √(p_{i,c}(1 − p_{i,c}))`", and "Otherwise, if
`c ∉ L_i^{−x_{N_H(i)}}`, we define `e_{i,c} = 0`".

**Formalization Note.** When only one color is available (`ℓ_i^{−x_{N_H(i)}} = 1`, so
`p_{i,c} = 1`) the printed formula is `0/0`; Lean's `x / 0 = 0` makes `e_{i,c} = 0` there. This
is harmless: on such a fiber `Dᵢ` is `0`, and every statement of the mission is unaffected. -/
noncomputable def eVec {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {K : ℕ} (L : V → Finset (Fin K)) (i : V) (c : Fin K)
    (x : V → Fin K) : ℝ :=
  if c ∈ avail H L i x then
    ((if x i = c then (1 : ℝ) else 0) - pMarg H L i x) /
      Real.sqrt (pMarg H L i x * (1 - pMarg H L i x))
  else 0

end ConeL2G


