-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_eta
-- name    : GradSuffice_Thm8Data_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:08.141471+00:00
-- url     : https://prove2.me/theorems/f552e75d-7bd4-49cf-b88b-afec1e484ebf
-- title:
--   Block averages $\eta_{t,k}$
-- statement:
--   For each copy $k$, write the sampled branch as $\sigma_k=(\sigma_{k,1},\dots,\sigma_{k,DL})$ and set
--   $$\eta_{t,k}:=-\frac1L\sum_{i=(t-1)L+1}^{tL}\sigma_{k,i}\,\xi_i(\sigma_{k,1},\dots,\sigma_{k,i-1}),$$
--   the negated average of the signed labels along block $t$ of the branch.
--
--   **Formalization Note** 0-based: block $t$ is the set of positions $i$ with $tL\le i<(t+1)L$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, p.19

import Mathlib
import Definitions.Def_NondualOpt_histPrefix
import Definitions.Def_GradSuffice_signR
import Definitions.Def_GradSuffice_Thm8Data

namespace GradSuffice

/-- **The block averages `η_{t,k}`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, p.19:
`η_{t,k} := −(1/L) ∑_{i=(t−1)L+1}^{tL} σ_{k,i} ξᵢ(σ_{k,1}, …, σ_{k,i−1})`.

**Formalization Note.** 0-based: block `t` consists of the positions `i` with `tL ≤ i < (t+1)L`
of the branch `σ_k`. -/
noncomputable def Thm8Data.eta {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (t : Fin c.D) (k : Fin c.κ) :
    StrongDual ℝ X :=
  -(1 / (thm8L c.θ c.D : ℝ)) •
    ∑ i ∈ Finset.univ.filter (fun i : Fin (c.D * thm8L c.θ c.D) =>
        (t : ℕ) * thm8L c.θ c.D ≤ i ∧ (i : ℕ) < ((t : ℕ) + 1) * thm8L c.θ c.D),
      signR (c.σ k i) • c.ξ i (NondualOpt.histPrefix (c.σ k) i)

end GradSuffice


