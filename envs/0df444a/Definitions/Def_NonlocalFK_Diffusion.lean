-- Prove2me | Definitions.Def_NonlocalFK_Diffusion
-- name    : NonlocalFK_Diffusion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:48.222279+00:00
-- url     : https://prove2.me/theorems/e45f74cd-bbb2-47cc-a850-314b596c1371
-- title:
--   Bounded smooth domain, the cylinder $Q$, $\bar Q$, $\partial_pQ$, and the local data with the assumptions of §2.1
-- statement:
--   Fix a dimension $d\ge 1$ and write $E=\mathbb R^d$. A **bounded smooth domain** is an open, connected, bounded set $\mathcal O\subset\mathbb R^d$ with $C^\infty$ boundary.
--
--   The local data are $\mathcal O$, a horizon $T>0$, coefficients $b:[0,T]\times\mathbb R^d\to\mathbb R^d$ and $\sigma:[0,T]\times\mathbb R^d\to\mathbb R^{d\times d}$, a rate $r>0$ and a running payoff $f$. They determine the sets
--
--   $$
--   Q=[0,T)\times\mathcal O,\qquad \bar Q=[0,T]\times\bar{\mathcal O},\qquad \partial_pQ=(\{T\}\times\bar{\mathcal O})\cup([0,T)\times\partial\mathcal O).
--   $$
--
--   The assumptions are: $b,\sigma$ continuous on $[0,T]\times\mathbb R^d$; for some $\bar K$ and all $(t,x),(\hat t,\hat x)$,
--
--   $$
--   |b(t,x)-b(\hat t,\hat x)|+|\sigma(t,x)-\sigma(\hat t,\hat x)|\le\bar K(|x-\hat x|+|t-\hat t|),\qquad |b(t,x)|+|\sigma(t,x)|\le\bar K(1+|x|);
--   $$
--
--   uniform ellipticity $\sum_{i,j}a_{ij}(t,x)\xi_i\xi_j\ge\Lambda|\xi|^2$ on $Q$ with $a=\sigma\sigma^{\mathsf T}$ and some $\Lambda>0$; and $f$ uniformly Hölder on $\bar Q$.
--
--   These objects are shared by the local problem of Proposition A.1 and the nonlocal problem of the main theorem.
--
--   **Formalization Note** The smooth boundary is expressed by a global defining function $\rho$ with $\mathcal O=\{\rho<0\}$, $\partial\mathcal O=\{\rho=0\}$, $d\rho\ne0$ on $\partial\mathcal O$. Hölder continuity uses the metric of $\mathbb R\times\mathbb R^d$ with an existential exponent, and $|\sigma|$ is the Frobenius norm; with existential constants these choices are immaterial.
-- source:
--   Dai, Kou, Yang, A Stochastic Representation for Nonlocal Parabolic PDEs with Applications, SSRN 3541591, §1.1, pp.1-2; §2.1, eq. (2.1)-(2.3), p.6

import Mathlib

open MeasureTheory Set
open scoped ContDiff NNReal

noncomputable section

namespace NonlocalFK

/-- Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Bounded smooth domain `𝒪 ⊂ ℝᵈ` (Dai, Kou, Yang, A Stochastic Representation for Nonlocal
Parabolic PDEs with Applications, SSRN 3541591, §1.1, p.1): open, connected, bounded, with `C^∞`
boundary.

**Formalization Note.** The `C^∞` boundary is expressed by a global defining function `ρ`, with
`𝒪 = {ρ < 0}`, `∂𝒪 = {ρ = 0}` and `dρ ≠ 0` on `∂𝒪`. The paper gives no degree of smoothness; for
bounded domains the defining-function form is equivalent to the chart form. -/
structure IsBoundedSmoothDomain {d : ℕ} (O : Set (E d)) : Prop where
  isOpen : IsOpen O
  isConnected : IsConnected O
  isBounded : Bornology.IsBounded O
  defining : ∃ ρ : E d → ℝ, ContDiff ℝ ∞ ρ ∧ O = {x | ρ x < 0} ∧ frontier O = {x | ρ x = 0} ∧
    ∀ x ∈ frontier O, fderiv ℝ ρ x ≠ 0

/-- The local part of the problem (Dai, Kou, Yang, SSRN 3541591, §1.1, p.2, and §2.1, p.6): the
domain `𝒪`, the horizon `T`, the coefficients `b`, `σ`, the discount rate `r` and the running data
`f`. All functions take the pair `(t, x)`. -/
structure Diffusion (d : ℕ) where
  O : Set (E d)
  T : ℝ
  b : ℝ × E d → E d
  σ : ℝ × E d → Matrix (Fin d) (Fin d) ℝ
  r : ℝ
  f : ℝ × E d → ℝ

namespace Diffusion

variable {d : ℕ} (c : Diffusion d)

/-- `Q := [0, T) × 𝒪` (SSRN 3541591, p.2). It contains `t = 0`. -/
def Q : Set (ℝ × E d) := Ico 0 c.T ×ˢ c.O

/-- `Q̄ := [0, T] × 𝒪̄`. -/
def Qbar : Set (ℝ × E d) := Icc 0 c.T ×ˢ closure c.O

/-- The parabolic boundary `∂ₚQ := ({T} × 𝒪̄) ∪ ([0, T) × ∂𝒪)` (SSRN 3541591, p.2). -/
def bdry : Set (ℝ × E d) := ({c.T} ×ˢ closure c.O) ∪ (Ico 0 c.T ×ˢ frontier c.O)

/-- The Frobenius norm used for the size `|σ|` of a matrix.

**Formalization Note.** The paper does not name the matrix norm in (2.1)–(2.2). All norms on
`d × d` matrices are equivalent, and the constant `K̄` is existential, so the choice is immaterial. -/
def matAbs (M : Matrix (Fin d) (Fin d) ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The standing assumptions on the local data (SSRN 3541591, §2.1, p.6): `d ≥ 1`, `T > 0`, a
bounded smooth domain, continuous `b`, `σ` on `[0, T] × ℝᵈ` with the Lipschitz bound (2.1) and the
linear growth bound (2.2), uniform ellipticity (2.3) of `a = σσᵀ` on `Q`, a positive rate `r`, and
`f` uniformly Hölder on `Q̄`.

**Formalization Note.** Hölder continuity is stated for the metric of `ℝ × ℝᵈ`. On the bounded set
`Q̄` this implies the parabolic Hölder condition with the same exponent and is implied by it with
half the exponent, so with `α` existential the two classes coincide. -/
structure Assumptions : Prop where
  one_le_d : 1 ≤ d
  T_pos : 0 < c.T
  domain : IsBoundedSmoothDomain c.O
  continuous_b : ContinuousOn c.b (Icc 0 c.T ×ˢ univ)
  continuous_σ : ContinuousOn c.σ (Icc 0 c.T ×ˢ univ)
  bounds : ∃ K : ℝ,
    (∀ p ∈ Icc 0 c.T ×ˢ (univ : Set (E d)), ∀ q ∈ Icc 0 c.T ×ˢ (univ : Set (E d)),
      ‖c.b p - c.b q‖ + matAbs (c.σ p - c.σ q) ≤ K * (‖p.2 - q.2‖ + |p.1 - q.1|)) ∧
    (∀ p ∈ Icc 0 c.T ×ˢ (univ : Set (E d)), ‖c.b p‖ + matAbs (c.σ p) ≤ K * (1 + ‖p.2‖))
  elliptic : ∃ Λ : ℝ, 0 < Λ ∧ ∀ ξ : E d, ∀ p ∈ c.Q,
    Λ * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, (c.σ p * (c.σ p).transpose) i j * ξ i * ξ j
  r_pos : 0 < c.r
  holder_f : ∃ α : ℝ≥0, 0 < α ∧ α ≤ 1 ∧ ∃ C : ℝ≥0, HolderOnWith C α c.f c.Qbar

end Diffusion

end NonlocalFK


