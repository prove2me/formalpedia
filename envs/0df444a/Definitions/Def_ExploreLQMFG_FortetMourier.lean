-- Prove2me | Definitions.Def_ExploreLQMFG_FortetMourier
-- name    : ExploreLQMFG_FortetMourier
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:44.390486+00:00
-- url     : https://prove2.me/theorems/2c8d2606-5903-47d0-8277-45e27a5d9551
-- title:
--   The path space $\mathcal C([0,T];\mathbb R^d\times\mathbb R^d)$ and the Fortet–Mourier class of (2.13)
-- statement:
--   Let $\mathcal C([0,T];\mathbb R^d\times\mathbb R^d)$ be the continuous paths, with the uniform distance
--   $$\rho(x,y)=\sup_{0\le t\le T}|x_t-y_t|,$$
--   where $|\cdot|$ is the Euclidean norm of $\mathbb R^d\times\mathbb R^d=\mathbb R^{2d}$. A function $F$ on this space is in the Fortet–Mourier class when it is bounded by $1$ and $1$-Lipschitz:
--   $$|F(x)|\le1,\qquad |F(x)-F(y)|\le\rho(x,y).$$
--   For processes $X,Y$ with continuous paths, $(X,Y)$ denotes the path $t\mapsto(X_t(\omega),Y_t(\omega))$, the argument of $F$ in (2.13).
--
--   The supremum over this class of $|\mathbb E[F(\cdot)]-\mathbb E[F(\cdot)]|$ is the Fortet–Mourier (bounded-Lipschitz) distance in which the weak error of the scheme is measured.
--
--   **Formalization Note** The paper does not name the norm on $\mathbb R^d\times\mathbb R^d$; any other product norm changes the class by at most a factor $\sqrt2$.
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), Theorem 2.4, (2.13) p.21

import Mathlib
import Definitions.Def_ExploreLQMFG_Model

open MeasureTheory Filter Topology
open scoped NNReal Matrix

namespace ExploreLQMFG

/-- The path space `𝒞([0, T]; ℝᵈ × ℝᵈ)` of continuous maps from `[0, T]` to `ℝᵈ × ℝᵈ`
(arXiv:2107.00839v2, Theorem 2.4, (2.13), p.21). -/
abbrev PathSpace (d : ℕ) (T : ℝ≥0) : Type :=
  C(Set.Icc (0 : ℝ) T, (Fin d → ℝ) × (Fin d → ℝ))

/-- The uniform distance `sup_{t ∈ [0, T]} |x_t − y_t|` on `𝒞([0, T]; ℝᵈ × ℝᵈ)`, where `|·|` is
the Euclidean norm of `ℝᵈ × ℝᵈ = ℝ^{2d}`.

**Formalization Note.** The paper does not name the norm on `ℝᵈ × ℝᵈ`; the Euclidean norm of
`ℝ^{2d}` is the natural one, and any other product norm changes the Fortet–Mourier class by at
most a factor `√2`, which the constant `C` of (2.13) absorbs. The supremum is over the compact,
nonempty `[0, T]` of a continuous function, so it is finite and attained. -/
noncomputable def pathDist {d : ℕ} {T : ℝ≥0} (x y : PathSpace d T) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) T, Real.sqrt (eSq ((x t).1 - (y t).1) + eSq ((x t).2 - (y t).2))

/-- `F` is in the Fortet–Mourier class of arXiv:2107.00839v2, Theorem 2.4, (2.13), p.21: a
function on `𝒞([0, T]; ℝᵈ × ℝᵈ)` "bounded by 1 and 1-Lipschitz continuous", that is,
`|F(x)| ≤ 1` and `|F(x) − F(y)| ≤ sup_t |x_t − y_t|`. -/
def IsFortetMourier {d : ℕ} {T : ℝ≥0} (F : PathSpace d T → ℝ) : Prop :=
  (∀ x, |F x| ≤ 1) ∧ ∀ x y, |F x - F y| ≤ pathDist x y

open Classical in
/-- The path `t ↦ (X_t(ω), Y_t(ω))`, `t ∈ [0, T]`, of a pair of `ℝᵈ`-valued processes, as an
element of `𝒞([0, T]; ℝᵈ × ℝᵈ)` (the argument of `F` in (2.13), p.21).

**Formalization Note.** If the path is not continuous the value is the zero path; every pair
to which the mission applies `pathOf` has continuous paths for every `ω`, so the default is
never used. -/
noncomputable def pathOf {Ω : Type*} {d : ℕ} (T : ℝ≥0) (X Y : ℝ≥0 → Ω → Fin d → ℝ)
    (ω : Ω) : PathSpace d T :=
  if hc : Continuous (fun t : Set.Icc (0 : ℝ) T => (X (t : ℝ).toNNReal ω, Y (t : ℝ).toNNReal ω))
  then ⟨_, hc⟩ else 0

end ExploreLQMFG


