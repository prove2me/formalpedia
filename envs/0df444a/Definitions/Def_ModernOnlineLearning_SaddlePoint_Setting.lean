-- Prove2me | Definitions.Def_ModernOnlineLearning_SaddlePoint_Setting
-- name    : ModernOnlineLearning_SaddlePoint_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:38:48.326982+00:00
-- url     : https://prove2.me/theorems/5632c8af-2bc8-415a-99ca-9e191b8ffb52
-- title:
--   Algorithms 7.8 and 15.6 — optimistic FTRL runs, partial-gradient smoothness, averages and attained extrema
-- statement:
--   Let $X$ and $Y$ be feasible sets in two real normed spaces. A minimum or maximum on a set means an attained extremum. For a fixed regularizer $\psi$ and dual-vector sequence $g_t$ with $g_0=0$, an optimistic FTRL run chooses $z_t$ to minimize
--   $$
--   \psi(z)+g_{t-1}(z)+\sum_{i=1}^{t-1}g_i(z)
--   $$
--   over the feasible set in every round $t=1,\ldots,T$. Algorithm 15.6 uses two such runs: the $X$-player's vector is $g_{X,t}=\nabla_x f(x_t,y_t)$, while the $Y$-player's is $g_{Y,t}=-\nabla_y f(x_t,y_t)$. The returned points are the averages $\bar x_T=T^{-1}\sum_{t=1}^T x_t$ and $\bar y_T=T^{-1}\sum_{t=1}^T y_t$.
--
--   The smoothness predicate supplies partial derivatives on an open neighborhood of $X\times Y$ and the four bounds (15.7)–(15.10), with constants $L_{XX}$, $L_{XY}$ and $L_{YY}$. These shared definitions let the regret and duality-gap statements refer to exactly the same algorithm.
--
--   **Formalization Note** Gradients are continuous linear functionals, so their operator norm is the book's dual norm. Losses and regularizers are real-valued on ambient spaces and only evaluated on the feasible sets. The run predicate carries the horizon $T$ and constrains exactly the rounds $1,\ldots,T$; index zero only supplies the zero hint.
-- source:
--   Orabona, arXiv:1912.13213v10, Algorithm 7.8, p. 129; Algorithm 15.6 and (15.7)–(15.10), p. 261

import Mathlib

set_option autoImplicit false

namespace ModernOnlineLearning.SaddlePoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point attaining the minimum on a feasible set. -/
def IsMinOn (V : Set E) (h : E → ℝ) (z : E) : Prop :=
  z ∈ V ∧ ∀ w ∈ V, h z ≤ h w

/-- A point attaining the maximum on a feasible set. -/
def IsMaxOn (V : Set E) (h : E → ℝ) (z : E) : Prop :=
  z ∈ V ∧ ∀ w ∈ V, h w ≤ h z

/-- Algorithm 7.8 with a fixed regularizer, linear losses, and the previous gradient as hint,
run for the rounds `t = 1, …, T`. -/
def IsOptFTRLRun (V : Set E) (ψ : E → ℝ) (g : ℕ → E →L[ℝ] ℝ)
    (z : ℕ → E) (T : ℕ) : Prop :=
  g 0 = 0 ∧ ∀ t ∈ Finset.Icc 1 T,
    IsMinOn V (fun w => ψ w + g (t - 1) w +
      ∑ i ∈ Finset.Ico 1 t, g i w) (z t)

variable {EX EY : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY]

/-- The two partial gradients on an open neighborhood of the feasible product,
with the four Lipschitz conditions (15.7)–(15.10). -/
def IsSmoothSaddleOn (X : Set EX) (Y : Set EY) (f : EX → EY → ℝ)
    (gx : EX → EY → EX →L[ℝ] ℝ) (gy : EX → EY → EY →L[ℝ] ℝ)
    (LXX LXY LYY : ℝ) : Prop :=
  ∃ U : Set (EX × EY), IsOpen U ∧ Set.prod X Y ⊆ U ∧
    (∀ p ∈ U, HasFDerivAt (fun x => f x p.2) (gx p.1 p.2) p.1 ∧
      HasFDerivAt (f p.1) (gy p.1 p.2) p.2) ∧
    (∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y,
      ‖gx x y - gx x' y‖ ≤ LXX * ‖x - x'‖) ∧
    (∀ x ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y,
      ‖gx x y - gx x y'‖ ≤ LXY * ‖y - y'‖) ∧
    (∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y,
      ‖gy x y - gy x' y‖ ≤ LXY * ‖x - x'‖) ∧
    (∀ x ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y,
      ‖gy x y - gy x y'‖ ≤ LYY * ‖y - y'‖)

/-- Algorithm 15.6 over the rounds `t = 1, …, T`: each player's linearized losses have the previous observed
partial gradient as the next hint. The Y-player minimizes minus the Y-gradient. -/
def IsOptFTRLSaddleRun (X : Set EX) (Y : Set EY)
    (ψX : EX → ℝ) (ψY : EY → ℝ)
    (gx : EX → EY → EX →L[ℝ] ℝ) (gy : EX → EY → EY →L[ℝ] ℝ)
    (x : ℕ → EX) (y : ℕ → EY) (T : ℕ) : Prop :=
  IsOptFTRLRun X ψX (fun t => if t = 0 then 0 else gx (x t) (y t)) x T ∧
  IsOptFTRLRun Y ψY (fun t => if t = 0 then 0 else -gy (x t) (y t)) y T

/-- The 1-indexed arithmetic average returned by Algorithms 15.1 and 15.6. -/
noncomputable def avg (T : ℕ) (z : ℕ → E) : E :=
  ((T : ℝ)⁻¹) • ∑ t ∈ Finset.Icc 1 T, z t

end ModernOnlineLearning.SaddlePoint


