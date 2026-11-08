-- Prove2me | Definitions.Def_EuclidDiamStream_hardDist
-- name    : EuclidDiamStream_hardDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:41.521573+00:00
-- url     : https://prove2.me/theorems/ed442818-cdd7-4ccc-9261-018f8f58a274
-- title:
--   The hard distribution $\mathcal D$ (Definition 3.1)
-- statement:
--   Fix positive integers $P,U$, and let $d,\tau$ be as in the definition of $d(n,c)$. A draw of $\mathcal D$ is a frequency vector $v$ on the grid obtained as follows:
--   1. draw $x,y$ uniformly from $\{0,1\}^d$, viewed as a subset of the grid;
--   2. set $v_y=P$ with probability $1/2$ and $v_y=0$ otherwise;
--   3. for each $z\in\mathcal B(x,\tau)$, draw $v_z$ uniformly from $\{1,\dots,PU\}$, and set all remaining coordinates to $0$.
--
--   Also defined here are the error $\Pr_{v\sim\mathcal D}[\mathrm{Dec}(Tv)\ne\mathrm{diam}_{r,c,n}(v)]$ and the success probability $\Pr_{v\sim\mathcal D}[\mathrm{Dec}(Tv)=\mathrm{diam}_{r,c,n}(v)]$ of a sketch. All sketch lower bounds of the mission are stated against this distribution.
--
--   **Formalization Note** If $y\in\mathcal B(x,\tau)$, the ball draw determines $v_y$, following the order of the page. All draws form one uniform draw on a product, and the values drawn outside the ball are ignored, so the law of $v$ is unchanged. The value $*$ always counts as an error of a sketch.
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), pp.7–8, Def. 3.1; p.8, (2); p.7, Theorem 2

import Mathlib
import Definitions.Def_EuclidDiamStream_hamBall
import Definitions.Def_EuclidDiamStream_diamGap
import Definitions.Def_EuclidDiamStream_hardDim

namespace EuclidDiamStream

open Classical in
/-- The frequency vector that the hard distribution of Definition 3.1 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.8, builds from a draw
`(x, y, b, w)`: `v_z = w z + 1 ∈ {1,…,PU}` for `z ∈ B(x,τ)`; `v_y = P` if `b` holds and `v_y = 0` otherwise,
when `y ∉ B(x,τ)`; and all remaining coordinates are `0`.

**Formalization Note.** If `y ∈ B(x,τ)`, the ball draw determines `v_y`, following the order of the page. The
witness `z` of a grid point in the embedded ball is unique when `Δ ≥ 1`, the only case the mission uses. -/
noncomputable def hardVec {d K : ℕ} (Δ τ P : ℕ) (x y : Cube d) (b : Bool) (w : Cube d → Fin K) :
    Point d Δ → ℤ :=
  fun p =>
    if h : ∃ z, embed Δ z = p ∧ ham x z ≤ τ then ((w h.choose : ℕ) : ℤ) + 1
    else if p = embed Δ y ∧ b = true then (P : ℤ) else 0

/-- Definition 3.1 (Hard Distribution `D`), pp.7–8, for `d = d(n,c)` and `τ = ⌊d/(12c²)⌋`: draw `x, y`
uniformly from `{0,1}^d`, draw `v_y = P` with probability 1/2 and `v_y = 0` otherwise, and draw each `v_z`,
`z ∈ B(x,τ)`, uniformly from `{1,…,PU}`; all other coordinates are `0`.

**Formalization Note.** The positive integers `P, U` are `ℕ+`. All draws are one uniform draw on the product
`Cube d × Cube d × Bool × (Cube d → Fin (PU))`, that is, independent uniform draws. The values at `z` outside
the ball are drawn and then ignored, which leaves the law of `v` unchanged. -/
noncomputable def hardDist (n : ℕ) (c : ℝ) (Δ : ℕ) (P U : ℕ+) :
    PMF (Point (hardDim n c) Δ → ℤ) :=
  haveI : Nonempty (Fin ((P : ℕ) * (U : ℕ))) := ⟨⟨0, Nat.mul_pos P.pos U.pos⟩⟩
  (PMF.uniformOfFintype
      (Cube (hardDim n c) × Cube (hardDim n c) × Bool × (Cube (hardDim n c) → Fin ((P : ℕ) * (U : ℕ))))).map
    (fun t => hardVec Δ (hardTau n c) (P : ℕ) t.1 t.2.1 t.2.2.1 t.2.2.2)

/-- The error `Pr_{v∼D}[Dec(Tv) ≠ diam_{r,c,n}(v)]` of a sketch on the hard distribution, as in (2), p.8, at
`r = hardScale n c`.

**Formalization Note.** `Dec` outputs a bit and `diamGap` is `none` on `∗`, so a vector with
`diam_{r,c,n}(v) = ∗` always counts as an error. -/
noncomputable def hardError {s : ℕ} (n : ℕ) (c : ℝ) (Δ : ℕ) (P U : ℕ+)
    (T : Matrix (Fin s) (Point (hardDim n c) Δ) ℤ) (Dec : (Fin s → ℤ) → Bool) : ENNReal :=
  (hardDist n c Δ P U).toOuterMeasure
    {v | some (Dec (T.mulVec v)) ≠ diamGap (hardScale n c) c n v}

/-- The success probability `Pr_{v∼D}[Dec(Tv) = diam_{r,c,n}(v)]` of a sketch on the hard distribution, as
in Theorem 2, p.7. -/
noncomputable def hardSuccess {s : ℕ} (n : ℕ) (c : ℝ) (Δ : ℕ) (P U : ℕ+)
    (T : Matrix (Fin s) (Point (hardDim n c) Δ) ℤ) (Dec : (Fin s → ℤ) → Bool) : ENNReal :=
  (hardDist n c Δ P U).toOuterMeasure
    {v | some (Dec (T.mulVec v)) = diamGap (hardScale n c) c n v}

end EuclidDiamStream


