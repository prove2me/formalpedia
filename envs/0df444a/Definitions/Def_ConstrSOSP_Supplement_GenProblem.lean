-- Prove2me | Definitions.Def_ConstrSOSP_Supplement_GenProblem
-- name    : ConstrSOSP_Supplement_GenProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:24:37.063899+00:00
-- url     : https://prove2.me/theorems/f4bde309-79af-4e78-81c7-6293f19a14b4
-- title:
--   Total white-box stationarity search problem on a general polytope
-- statement:
--   Fix a clock exponent $K$, a dimension restriction $D$ and a stationarity notion $P$. The search problem has the valid instances described above. On an instance with data $\epsilon_G,\epsilon_H,A,B,L,L_1,L_2$ and machines for $f,\nabla f,\nabla^2 f$, an answer is either
--
--   1. a rational point $x$ such that the machines' data $(f(x),\nabla f(x),\nabla^2 f(x))$ satisfy $P$ (which includes $x\in\mathcal X$); or
--   2. two rational points $x,y\in\mathcal X$ whose machine data form a regularity violation with constants $L,L_1,L_2$.
--
--   This is the common shape of Sosp1 and Fixed-Dimensions-Sosp2, which differ only in the stationarity test and the dimension.
--
--   **Formalization Note** The first bit of an answer tags its kind (`false` for a point, `true` for a violation pair).
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definitions 4.6 and 4.8, pp.19–21

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_ConstrSOSP_Poly
import Definitions.Def_ConstrSOSP_Supplement_encInstGen
import Definitions.Def_ConstrSOSP_Supplement_EvalsD
import Definitions.Def_ConstrSOSP_Supplement_Violation
import Definitions.Def_ConstrSOSP_Supplement_ValidGen

namespace ConstrSOSP.Supplement

open CardinalMatching ConstrSOSP

/-- **Total white-box stationarity search problem on a general polytope** (Kontogiannis, Panageas
& Pollatos, arXiv:2604.02285, 2 Nov 2026, Definitions 4.6 and 4.8, pp.19–21), for a dimension
restriction `D` and a stationarity notion `P m d A B L₁ ϵG ϵH x g H`.

* The instances are those of `ValidGen K D`.
* An answer on `s = encInstGen ϵG ϵH m d A B L L₁ L₂ T cf cg cH` is either
  1. `false :: encRatVec d x` for a rational point `x` at which the machines return data
     `(f(x), ∇f(x), ∇²f(x)) = (v, g, H)` satisfying `P m d A B L₁ ϵG ϵH x g H` ("Find a point
     x* ∈ X such that …"), or
  2. `true :: (encRatVec d x ++ encRatVec d y)` for rational points `x, y ∈ X` at which the
     machines return data `(vx, gx, Hx)`, `(vy, gy, Hy)` exhibiting a `Violation` with the
     instance's constants `L, L₁, L₂` ("Alternatively, we also accept one of the following
     violations as a solution").

**Formalization Note** The leading bit tags the answer kind. Membership of `x` in `X` for a
stationarity answer is part of `P` (`IsSOSP1`, `IsSOSP2` both require `x ∈ X`). -/
def GenProblem (K : ℕ) (D : ℕ → Prop)
    (P : (m d : ℕ) → (Fin m → Fin d → ℝ) → (Fin m → ℝ) → ℝ → ℝ → ℝ → (Fin d → ℝ) →
      (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ → Prop) :
    TetrisHard.Rows.SearchProblem where
  valid := ValidGen K D
  answer s t := ∃ (ϵG ϵH : ℚ) (m d : ℕ) (A : Fin m → Fin d → ℚ) (B : Fin m → ℚ) (L L1 L2 : ℚ)
    (T : ℕ) (cf cg cH : List Bool),
    s = encInstGen ϵG ϵH m d A B L L1 L2 T cf cg cH ∧
    ((∃ (x : Fin d → ℚ) (v : ℚ) (g : Fin d → ℚ) (H : Fin d → Fin d → ℚ),
        t = false :: encRatVec d x ∧ EvalsD d K T cf cg cH x v g H ∧
        P m d (fun j i => (A j i : ℝ)) (fun j => (B j : ℝ)) (L1 : ℝ) (ϵG : ℝ) (ϵH : ℝ)
          (fun i => (x i : ℝ)) (fun i => (g i : ℝ)) (Matrix.of fun i j => (H i j : ℝ))) ∨
      (∃ (x y : Fin d → ℚ) (vx vy : ℚ) (gx gy : Fin d → ℚ) (Hx Hy : Fin d → Fin d → ℚ),
        t = true :: (encRatVec d x ++ encRatVec d y) ∧
        (fun i => (x i : ℝ)) ∈ Poly (fun j i => (A j i : ℝ)) (fun j => (B j : ℝ)) ∧
        (fun i => (y i : ℝ)) ∈ Poly (fun j i => (A j i : ℝ)) (fun j => (B j : ℝ)) ∧
        EvalsD d K T cf cg cH x vx gx Hx ∧ EvalsD d K T cf cg cH y vy gy Hy ∧
        Violation (L : ℝ) (L1 : ℝ) (L2 : ℝ) (fun i => (x i : ℝ)) (vx : ℝ) (fun i => (gx i : ℝ))
          (Matrix.of fun i j => (Hx i j : ℝ)) (fun i => (y i : ℝ)) (vy : ℝ)
          (fun i => (gy i : ℝ)) (Matrix.of fun i j => (Hy i j : ℝ))))

end ConstrSOSP.Supplement


