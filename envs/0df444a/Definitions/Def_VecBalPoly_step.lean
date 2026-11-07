-- Prove2me | Definitions.Def_VecBalPoly_step
-- name    : VecBalPoly_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:13:17.030249+00:00
-- url     : https://prove2.me/theorems/2c109907-8ef1-4610-af6e-8ba706100f73
-- title:
--   One iteration of Algorithm 2.2
-- statement:
--   Given a state and a direction $h$: let
--   $$t_*=\min_{j\in V:\,h_j\ne0}\frac{1-|x_j|}{|h_j|},\qquad t=\min\{\tau,t_*\}.$$
--   If $t=\tau$ set $\xi=1$; otherwise let $j_*$ be the smallest index attaining $t_*$ and set $\xi=1$ if $x_{j_*}h_{j_*}\ge0$ and $\xi=-1$ otherwise. Update $x_V\leftarrow x_V+\xi t h$ and perform cleanup.
--
--   **Formalization Note** When no $j\in V$ has $h_j\ne0$, $t_*$ is taken to be $\tau$, so that $t=\tau$.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Algorithm 2.2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_VecBalPoly_cleanup

namespace VecBalPoly

open Classical

variable {m n : ℕ}

/-- `t⋆ = min_{j∈V : hⱼ≠0} (1 − |xⱼ|)/|hⱼ|`; when no `j ∈ V` has `hⱼ ≠ 0` the value `τ`
is used, so that `min{τ, t⋆} = τ`. -/
noncomputable def tstar (st : St m n) (h : Fin n → ℝ) : ℝ :=
  if hne : (st.V.filter (fun j => h j ≠ 0)).Nonempty then
    (st.V.filter (fun j => h j ≠ 0)).inf' hne (fun j => (1 - |st.x j|) / |h j|)
  else tau n

/-- The step length `t = min{τ, t⋆}`. -/
noncomputable def tstep (st : St m n) (h : Fin n → ℝ) : ℝ :=
  min (tau n) (tstar st h)

/-- The sign `ξ`: `1` if `t = τ`; otherwise, with `j⋆` the smallest index attaining `t⋆`,
`ξ = 1` if `x_{j⋆}h_{j⋆} ≥ 0` and `ξ = −1` otherwise. -/
noncomputable def xi (st : St m n) (h : Fin n → ℝ) : ℝ :=
  if tstep st h = tau n then 1 else
    if hne : (st.V.filter (fun j => h j ≠ 0 ∧ (1 - |st.x j|) / |h j| = tstar st h)).Nonempty then
      (let jstar := (st.V.filter
          (fun j => h j ≠ 0 ∧ (1 - |st.x j|) / |h j| = tstar st h)).min' hne
        if 0 ≤ st.x jstar * h jstar then 1 else -1)
    else 1

/-- The state after the update `x_V ← x_V + ξth` of Algorithm 2.2, before cleanup. -/
noncomputable def preState (st : St m n) (h : Fin n → ℝ) : St m n :=
  { st with x := fun j => if j ∈ st.V then st.x j + xi st h * tstep st h * h j else st.x j }

/-- **One iteration of Algorithm 2.2** for a given direction `h`: steps 2 and 3 (step length,
sign choice, update `x_V ← x_V + ξth`, then cleanup).
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Algorithm 2.2, p.6 (PDF p.7).

**Formalization Note** The helpers `tstar`, `tstep`, `xi`, `preState` are steps 2–3 as printed,
with the tie-break "the smallest index attaining `t⋆`". -/
noncomputable def step (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (h : Fin n → ℝ) : St m n :=
  cleanup A false (preState st h)

end VecBalPoly


