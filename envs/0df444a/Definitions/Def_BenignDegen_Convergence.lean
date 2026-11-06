-- Prove2me | Definitions.Def_BenignDegen_Convergence
-- name    : BenignDegen_Convergence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:50.308331+00:00
-- url     : https://prove2.me/theorems/d3ec3f34-235f-4b15-9892-b1138abe1ee0
-- title:
--   $G$-metrics, $\alpha$-averaged and firmly nonexpansive maps, R-linear and eventual Q-linear convergence
-- statement:
--   Let $E$ be a real inner product space and $G:E\to E$ a linear operator, with $\|z\|_G^2=\langle z,Gz\rangle$ and $\operatorname{dist}_G(z,W)=\inf_{w\in W}\|z-w\|_G$.
--
--   1. $T$ is **$\alpha$-averaged** in $\|\cdot\|_G$ ($0<\alpha<1$) if $\|Tz-Tw\|_G^2\le\|z-w\|_G^2-\frac{1-\alpha}{\alpha}\|(z-Tz)-(w-Tw)\|_G^2$ for all $z,w$.
--   2. $T$ is **firmly nonexpansive** in $\|\cdot\|_G$ if $\|Tz-Tw\|_G^2\le\langle Tz-Tw,G(z-w)\rangle$ for all $z,w$.
--   3. $u_k\to\bar u$ **R-linearly** if $\|u_k-\bar u\|\le c\rho^k$ for all $k$, some $c\ge0$, $0\le\rho<1$.
--   4. A sequence of distances $d_k$ **contracts eventually Q-linearly** if $d_{k+1}\le\rho d_k$ for all $k\ge K$, some $K$ and $0\le\rho<1$.
--
--   These are the notions in which Lemma F.1, Propositions F.2 and F.4 and Corollaries 5.1–5.2 are stated.
--
--   **Formalization Note** The averagedness inequality is the one of [BC17] used on pp.28–29. `dist_G` is only applied to nonempty sets.
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix F.1, Lemma F.1 and its proof, pp.27–28; §5, pp.10–11

import Mathlib

namespace BenignDegen

open scoped RealInnerProductSpace

noncomputable section

/-! # Metrics, averagedness and linear rates (Appendix F)

Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*,
arXiv:2610.20270v1, Appendix F.1, pp.27–28 (Lemma F.1 and its proof: the averagedness inequality
of [BC17], `dist_G`, Q-linear and R-linear convergence), §5, p.10–11.

**Formalization Note** A metric `G` on a real inner product space `E` is a continuous linear map
`G : E → E`; its squared norm is `‖z‖²_G = ⟨z, Gz⟩` and `dist_G(z, W) = inf_{w∈W} ‖z − w‖_G`
(only used for nonempty `W`). `α`-averagedness in `‖·‖_G` is the [BC17] inequality used on
pp.28–29; firm nonexpansiveness is `‖Tz − Tw‖²_G ≤ ⟨Tz − Tw, z − w⟩_G`. R-linear convergence
`u_k → ū` means `‖u_k − ū‖ ≤ c ρ^k` for all `k`, some `c ≥ 0` and `0 ≤ ρ < 1`; eventual Q-linear
contraction of a sequence of distances `d_k` means `d_{k+1} ≤ ρ d_k` for all `k ≥ K`, some `K` and
`0 ≤ ρ < 1`. These notions are not in Mathlib. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `‖z‖²_G := ⟨z, Gz⟩`. -/
def gSq (G : E →L[ℝ] E) (z : E) : ℝ := ⟪z, G z⟫

/-- `‖z‖_G := √⟨z, Gz⟩`. -/
def gNorm (G : E →L[ℝ] E) (z : E) : ℝ := Real.sqrt (gSq G z)

/-- `dist_G(z, W) := inf_{w ∈ W} ‖z − w‖_G`. -/
def gDist (G : E →L[ℝ] E) (z : E) (W : Set E) : ℝ := sInf ((fun w => gNorm G (z - w)) '' W)

/-- `T` is `α`-averaged in `‖·‖_G` (`0 < α < 1`), via the [BC17] inequality
`‖Tz − Tw‖²_G ≤ ‖z − w‖²_G − ((1 − α)/α)‖(z − Tz) − (w − Tw)‖²_G` for all `z, w`. -/
def IsAveragedIn (G : E →L[ℝ] E) (α : ℝ) (T : E → E) : Prop :=
  0 < α ∧ α < 1 ∧ ∀ z w : E,
    gSq G (T z - T w) ≤ gSq G (z - w) - ((1 - α) / α) * gSq G ((z - T z) - (w - T w))

/-- `T` is firmly nonexpansive in `‖·‖_G`: `‖Tz − Tw‖²_G ≤ ⟨Tz − Tw, G(z − w)⟩`. -/
def IsFirmlyNonexpansiveIn (G : E →L[ℝ] E) (T : E → E) : Prop :=
  ∀ z w : E, gSq G (T z - T w) ≤ ⟪T z - T w, G (z - w)⟫

/-- `Fix T`. -/
def fixedPts (T : E → E) : Set E := {z | T z = z}

/-- `u_k → ū` R-linearly: `‖u_k − ū‖ ≤ c ρ^k` for all `k`, with `c ≥ 0` and `0 ≤ ρ < 1`. -/
def RLinearTo {F : Type*} [NormedAddCommGroup F] (u : ℕ → F) (ubar : F) : Prop :=
  ∃ c ≥ (0 : ℝ), ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k, ‖u k - ubar‖ ≤ c * ρ ^ k

/-- A sequence of distances `d_k` contracts eventually Q-linearly: for some `K` and
`0 ≤ ρ < 1`, `d_{k+1} ≤ ρ d_k` for all `k ≥ K`. -/
def EventuallyQLinear (d : ℕ → ℝ) : Prop :=
  ∃ K : ℕ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k ≥ K, d (k + 1) ≤ ρ * d k

end

end BenignDegen


