-- Prove2me | Definitions.Def_BSUMConv_BSCA_Setting
-- name    : BSUMConv_BSCA_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:55.72569+00:00
-- url     : https://prove2.me/theorems/bf6675b6-f4bf-4aef-a2a2-5ce68583a871
-- title:
--   §VI, pp. 16–17 — BSCA feasible set, first-order agreement and Armijo run
-- statement:
--   Let $X=\prod_{i=1}^{N}X_i$ be a Cartesian feasible set and let $f:X\to\mathbb R$ be an objective. The approximation $h_i(y_i,x)$ is used when block $i$ is selected. The definitions specify first-order agreement at feasible one-block directions,
--   $$h_i'(x_i,x;d_i)=f'(x;(0,\ldots,d_i,\ldots,0)),$$
--   strict convexity in the trial block, and joint continuity on feasible pairs.
--
--   A BSCA run starts at $x^0\in X$. At step $r$ it chooses a minimizing block value $y^r_i$, leaves other blocks unchanged, and sets $d^r=y^r-x^r$. Among the steps $\alpha^{\rm init}\beta^j$, it selects the largest that satisfies Armijo's decrease test and sets $x^{r+1}=x^r+\alpha^r d^r$. This model is reused in the convergence statements.
--
--   **Formalization Note** The algorithm's mixed indices in Figure 4 are resolved using the accompanying text and proof. The objective is extended by $+\infty$ off $X$ for the stationary-point predicate. Blocks and iterations are indexed from zero; the published Tseng block space and lower directional derivative are reused.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, pp. 4, 8, 16–17, §II, (12), (30), Fig. 4

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSUM_Setting

namespace BSUMConv.BSCA

open Filter Topology TsengBCD.Stationary

variable {N : ℕ} {n : Fin N → ℕ}

/-- Extend the real objective by +∞ off the feasible set, as in the paper's effective-domain
convention on p. 4. -/
noncomputable def fext (f : X n → ℝ) (S : Set (X n)) : X n → EReal :=
  by
    classical
    exact fun x => if x ∈ S then (f x : EReal) else ⊤

/-- First-order agreement (30), for a feasible one-block displacement. -/
def FirstOrderAgreement
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (f : X n → ℝ)
    (h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) : Prop :=
  ∀ x ∈ BSUMConv.BSUM.Xset Xs, ∀ (i : Fin N) (di : EuclideanSpace ℝ (Fin (n i))),
    x i + di ∈ Xs i →
      dirDeriv (fun yi => (h i yi x : EReal)) (x i) di =
        ((fderiv ℝ f x (Pi.single i di) : ℝ) : EReal)

/-- Strict convexity of each approximation in its own block, on that block's feasible set. -/
def StrictApprox
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) : Prop :=
  ∀ (i : Fin N) (y : X n), y ∈ BSUMConv.BSUM.Xset Xs →
    StrictConvexOn ℝ (Xs i) (fun xi => h i xi y)

/-- Continuity of the block approximation jointly in the trial block and feasible base point. -/
def ContinuousApprox
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) : Prop :=
  ∀ i, ContinuousOn (fun p => h i p.1 p.2) (Xs i ×ˢ BSUMConv.BSUM.Xset Xs)

/-- Figure 4, p. 17, with its mixed indices resolved using the surrounding text: step `r`
minimizes at `x r`, and moves from `x r` to `x (r+1)`. The chosen backtracking index is
minimal, so its step is the largest Armijo-admissible member of the geometric sequence. -/
def IsBSCARun
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (f : X n → ℝ)
    (h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ)
    (s : ℕ → Fin N) (σ β αinit : ℝ)
    (x y : ℕ → X n) (j : ℕ → ℕ) : Prop :=
  x 0 ∈ BSUMConv.BSUM.Xset Xs ∧
    ∀ r : ℕ,
      let i := s r
      let d := y r - x r
      let α := αinit * β ^ (j r)
      y r i ∈ Xs i ∧
      (∀ w ∈ Xs i, h i (y r i) (x r) ≤ h i w (x r)) ∧
      (∀ k, k ≠ i → y r k = x r k) ∧
      f (x r) - f (x r + α • d) ≥ -σ * α * fderiv ℝ f (x r) d ∧
      (∀ j' : ℕ, j' < j r →
        let α' := αinit * β ^ j'
        ¬ (f (x r) - f (x r + α' • d) ≥ -σ * α' * fderiv ℝ f (x r) d)) ∧
      x (r + 1) = x r + α • d

end BSUMConv.BSCA


