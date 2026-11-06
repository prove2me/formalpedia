-- Prove2me | Definitions.Def_ConstrSOSP_BoxProblem
-- name    : ConstrSOSP_BoxProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:04:37.815399+00:00
-- url     : https://prove2.me/theorems/4fe8c1cb-2d41-483c-a7fd-114e9213d103
-- title:
--   White-box stationarity problem on the unit square
-- statement:
--   For a stationarity notion $P$, the search problem whose instances are the valid instances above and whose answers are rational points $x$ at which the machines' data satisfy $P$.
--
--   **Formalization Note** The paper's total problems also accept violation certificates. On a valid instance there is none: the promises rule out every Lipschitz and Taylor violation, and the KKT margin rules out a boundary SOSP1. So the answer sets agree.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definitions 4.6, 4.8, 4.10, pp.19–22

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_ConstrSOSP_Evals
import Definitions.Def_ConstrSOSP_encInst
import Definitions.Def_ConstrSOSP_ValidBox

namespace ConstrSOSP

open CardinalMatching

/-- **White-box stationarity search problem on `[0, 1]²`** (arXiv:2604.02285, 2 Nov 2026,
Definitions 4.6, 4.8 and 4.10, pp.19–22, restricted as in Theorem 5.1, p.22), for a
stationarity notion `P ϵG ϵH x g H`.

* The instances are the valid ones of `ValidBox K` (box, `L = L₁ = L₂ = 1`, accuracy
  `(ϵ, √ϵ)`, all regularity promises, the KKT margin `[1/12, 11/12]²`).
* An answer is the code `encRatVec 2 x` of a rational point `x` at which the machines return
  data `(f(x), ∇f(x), ∇²f(x)) = (v, g, H)` satisfying `P ϵG ϵH x g H`.

**Formalization Note** The violation outputs of the paper's total problems are not answers: on a
valid instance the promises exclude every Lipschitz and Taylor violation, and the KKT margin
excludes a boundary SOSP1, so the answer sets coincide with the paper's. -/
def BoxProblem (K : ℕ)
    (P : ℝ → ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ → Prop) :
    TetrisHard.Rows.SearchProblem where
  valid := ValidBox K
  answer s t := ∃ (ϵG ϵH : ℚ) (T : ℕ) (cf cg cH : List Bool) (x : Fin 2 → ℚ) (v : ℚ)
    (g : Fin 2 → ℚ) (H : Fin 2 → Fin 2 → ℚ),
    s = encInst ϵG ϵH T cf cg cH ∧ t = encRatVec 2 x ∧ Evals K T cf cg cH x v g H ∧
    P (ϵG : ℝ) (ϵH : ℝ) (fun i => (x i : ℝ)) (fun i => (g i : ℝ))
      (Matrix.of fun i j => (H i j : ℝ))

end ConstrSOSP


