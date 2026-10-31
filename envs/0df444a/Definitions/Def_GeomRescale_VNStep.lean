-- Prove2me | Definitions.Def_GeomRescale_VNStep
-- name    : GeomRescale_VNStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:02.781621+00:00
-- url     : https://prove2.me/theorems/d008e3f5-326a-43c5-b399-b051de550d38
-- title:
--   One iteration of Algorithm 1
-- statement:
--   One iteration of the `while` loop of the sliding von Neumann algorithm runs when $\|y\|_Q > \varepsilon$. It picks an order sorted by $Qy$ and takes the greedy vector $g_k$ of $f_{\mu'}$.
--
--   1. If $y^{\mathsf T} Q g_k \le 0$, lines 11–15 run on $g_k$.
--   2. If $y^{\mathsf T} Q g_k > 0$, the algorithm slides: $W' := \mathrm{MinSet}(f_{\mu'}, Qy)$ for that same order, $\delta := -f_{\mu'}(W')$ with the old $\mu'$, $\mu' := -f(W')$, and line 9 patches $g_k$ at the first and last elements of that same order. Lines 11–15 then run on the patched vector.
--
--   **Formalization Note** This is a relation: every tie-break and every argmin is a separate step. An iteration is charged $n$ evaluations and $c(n) + n^2$ operations for lines 4–6, $n$ operations more for lines 7–9, and the charge of lines 11–15.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, lines 4–15, p.8

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_IsSortedBy
import Definitions.Def_GeomRescale_IsMinSet
import Definitions.Def_GeomRescale_enlarge
import Definitions.Def_GeomRescale_sortCost
import Definitions.Def_GeomRescale_vnUpdate
import Definitions.Def_GeomRescale_patch

namespace GeomRescale

/-- One iteration of the `while` loop of Algorithm 1, lines 4–15 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, p.8).

The guard of line 4 is `ε < ‖y‖_Q`. Line 5 picks an order `σ` sorted by `Qy` and takes the greedy
vector `g_k` of `f_μ′`. If `yᵀQg_k ≤ 0` (`plain`) lines 11–15 run on `g_k`. If `yᵀQg_k > 0` (`slide`),
line 7 sets `W′` to a `MinSet(f_μ′, Qy)` for that same order, `δ := −f_μ′(W′)` with the old `μ′`, and
`μ′ := −f(W′)`; line 9 patches `g_k` at the first and last elements of that same order; lines 11–15
run on the patched vector.

**Formalization Note.** Every tie-break and every argmin is allowed, one order per iteration: line 8
does not sort again. The test of line 6 reads the unpatched `g_k`. An iteration is charged `n`
evaluations and `c(n) + n²` operations for lines 4–6, `n` more operations when lines 7–9 run, and the
charge of `vnUpdate`; the values of `f` used in lines 7–9 are prefix values already paid for. -/
inductive VNStep {n : ℕ} (f : Finset (Fin n) → ℤ) (Q : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    VN n → VN n → Prop
  | plain (v : VN n) (σ : Equiv.Perm (Fin n)) :
      ε < qnorm Q v.y →
      IsSortedBy (Q.mulVec v.y) σ →
      ¬ 0 < qdot Q v.y (SchrijverSFM.Alg.greedy (enlarge (fR f) (v.μ : ℝ)) σ) →
      VNStep f Q ε v
        (vnUpdate Q (SchrijverSFM.Alg.greedy (enlarge (fR f) (v.μ : ℝ)) σ)
          { v with evals := v.evals + n, ops := v.ops + sortCost n + n ^ 2 })
  | slide (v : VN n) (σ : Equiv.Perm (Fin n)) (W' : Finset (Fin n)) :
      ε < qnorm Q v.y →
      IsSortedBy (Q.mulVec v.y) σ →
      0 < qdot Q v.y (SchrijverSFM.Alg.greedy (enlarge (fR f) (v.μ : ℝ)) σ) →
      IsMinSet (enlarge (fR f) (v.μ : ℝ)) σ W' →
      VNStep f Q ε v
        (vnUpdate Q
          (patch σ (-(enlarge (fR f) (v.μ : ℝ) W'))
            (SchrijverSFM.Alg.greedy (enlarge (fR f) (v.μ : ℝ)) σ))
          { v with
            μ := -f W'
            W := W'
            evals := v.evals + n
            ops := v.ops + sortCost n + n ^ 2 + n })

end GeomRescale


