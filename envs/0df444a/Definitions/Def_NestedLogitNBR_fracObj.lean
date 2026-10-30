-- Prove2me | Definitions.Def_NestedLogitNBR_fracObj
-- name    : NestedLogitNBR_fracObj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:40:06.367857+00:00
-- url     : https://prove2.me/theorems/4b0ca373-aae6-49d9-808b-4eac4f381ab0
-- title:
--   Objective of the fractional nest problem (8)
-- statement:
--   For nest $i$, a level $x\in\mathbb R$ and a fractional assortment $z\in[0,1]^n$, the objective of problem (8) (p. 21), the inner maximization of problem (7), is
--
--   $$
--   \Big(\sum_{j\in N}v_{ij}z_j\Big)^{\gamma_i}\left[\frac{\sum_{j\in N}r_{ij}v_{ij}z_j}{\sum_{j\in N}v_{ij}z_j}-x\right].
--   $$
--
--   At the indicator vector of an assortment $S$ it equals $V_i(S)^{\gamma_i}(R_i(S)-x)$, so problem (7) relaxes the choice of assortments to fractional ones.
--
--   **Formalization Note** When $\sum_j v_{ij}z_j=0$ the power is taken as $0$ (and the quotient is $0$ by $x/0=0$), so the objective is $0$, the same convention as for $V_i(S)^{\gamma_i}$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), eq. (8), p. 21; problem (7), p. 20

import Mathlib

namespace NestedLogitNBR

/-- **Objective of the fractional nest problem (8).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), eq. (8), p. 21 (also the inner maximization of problem (7), p. 20):
`max_{z_i∈[0,1]^n} { (Σ_{j∈N} v_ij z_ij)^{γ_i} [ Σ_{j∈N} r_ij v_ij z_ij / Σ_{j∈N} v_ij z_ij − x ] }`.

`fracObj r v γ i z x = (Σ_j v_ij z_j)^{γ_i} · ((Σ_j r_ij v_ij z_j) / (Σ_j v_ij z_j) − x)`.

**Formalization Note.** The power is `Real.rpow`, replaced by `0` when `Σ_j v_ij z_j = 0`
(the same convention as `nestAttraction`: a nest with no weight offered contributes `0`; this
also avoids `0 ^ 0 = 1` at `γ_i = 0`). With this convention, at the indicator vector of a set
`S` the value is `V_i(S)^{γ_i}(R_i(S) − x)`. -/
noncomputable def fracObj {m n : ℕ} (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (i : Fin m)
    (z : Fin n → ℝ) (x : ℝ) : ℝ :=
  (if ∑ j, v i j * z j = 0 then 0 else (∑ j, v i j * z j) ^ γ i) *
    ((∑ j, r i j * v i j * z j) / (∑ j, v i j * z j) - x)

end NestedLogitNBR


