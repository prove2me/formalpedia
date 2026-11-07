-- Prove2me | Definitions.Def_PolySampIso_LogBarrier
-- name    : PolySampIso_LogBarrier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:24.173457+00:00
-- url     : https://prove2.me/theorems/c7c4eae2-c41f-44c6-a41b-d37fcbb7e60b
-- title:
--   The polytope, its slacks and log barrier, the uniform measure π and the cooled measures π_t
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rows $a_1,\dots,a_m$ and let $b\in\mathbb R^m$. The **polytope** is $X=\{x\in\mathbb R^n: Ax<b\}$, assumed nonempty and bounded (hence full-dimensional, with $A$ of full column rank). At $x\in X$ the **slacks** are $s(x)=b-Ax\in\mathbb R^m_{>0}$ and the **log barrier** is
--
--   $$\psi(x)=-\sum_{i=1}^m\log s_i(x),$$
--
--   with gradient $\nabla\psi(x)=A^\top s(x)^{-1}$ and Hessian $H(x)=A^\top S(x)^{-2}A$, $S(x)=\mathrm{diag}(s(x))$. The **local norms** are $\|v\|_x=\sqrt{v^\top H(x)v}$ and $\|v\|_{x,*}=\sqrt{v^\top H(x)^{-1}v}$.
--
--   The **uniform measure** $\pi$ is Lebesgue measure on $X$ normalized to mass one. For $t\ge0$ the **cooled measure** is
--
--   $$\pi_t\propto e^{-t\psi}\pi,\qquad Z(t)=\int e^{-t\psi(x)}\,\pi(dx),$$
--
--   so $\pi_0=\pi$; $t$ is an inverse temperature.
--
--   **Formalization Note** Points are `EuclideanSpace ℝ (Fin n)`. The gradient and Hessian are the formulas above, which are the derivatives of $\psi$ on $X$. `StandingAssumption A b` is "$X$ nonempty and bounded".
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), §2.3, pp.9–10 (PDF pp.11–12), eqs. (6)–(8); §4.1, p.30 (PDF p.32), eq. (43)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolySampIso

/-!
# The polytope, its log barrier, the uniform measure and the cooled measures

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), §2.3, pp.9–10 (PDF pp.11–12), eqs. (6)–(8):
"We now specialize the FSL framework to the setting of the logarithmic barrier (log barrier) over
a nonempty, full-dimensional, bounded polytope. … Let A ∈ Rm×n be a full-rank matrix with rows
{ai}i∈[m], and let b ∈ Rm. Define the polytope X := {x ∈ Rn | Ax < b} . (6) We reserve the
notation π for the uniform measure over X. At a point x ∈ X, we define its vector of slacks
s(x) := b − Ax ∈ Rm>0, and the corresponding diagonal matrix S(x) := diag (s(x)). The log barrier
is defined as ψ(x) := −Σ_{i∈[m]} log (si(x)) . (7) Observe that ∇ψ(x) = A⊤s(x)−1 … H(x) :=
∇²ψ(x) = A⊤S(x)−2A, ∥v∥x := ∥v∥H(x) , ∥v∥x,∗ := ∥v∥H(x)−1 . (8)"
§4.1, p.30 (PDF p.32), eq. (43): "πt ∝ exp(−tψ)π, Z(t) := ∫ exp(−tψ(x))π(x)dx."

**Formalization Note.**
* Points are `EuclideanSpace ℝ (Fin n)`; `A : Matrix (Fin m) (Fin n) ℝ`, `b : Fin m → ℝ`.
* `StandingAssumption A b` is the section's standing assumption: `X` nonempty and bounded (`X` is
  open, so nonempty means full-dimensional; nonempty and bounded imply that `A` has full column
  rank, which the paper calls "full-rank").
* `logBarrier`, `gradLogBarrier`, `hessLogBarrier` are the formulas (7), `A⊤s(x)⁻¹` and
  `A⊤S(x)⁻²A`; they are the gradient and Hessian of `ψ` on `X` (off `X` the values are not used:
  `Real.log` of a nonpositive slack is a junk value).
* `dualLocalNorm A b x v = ‖v‖_{x,∗} = √(v⊤H(x)⁻¹v)`; `H(x)` is positive definite on `X` under the
  standing assumption, so the matrix inverse is the true inverse there.
* `uniform A b = π` is Lebesgue measure conditioned on `X` (`ProbabilityTheory.cond`).
* `cooled A b t = π_t` has density `exp(−tψ)/Z(t)` with respect to `π`; `π_0 = π`.
-/

/-- The polytope `X = {x ∈ ℝⁿ | Ax < b}` (6). -/
def polytope {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, ∑ j, A i j * x j < b i}

/-- The standing assumption of §2.3: the polytope is nonempty and bounded. -/
def StandingAssumption {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  (polytope A b).Nonempty ∧ Bornology.IsBounded (polytope A b)

/-- The slack vector `s(x) = b − Ax`. -/
def slack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Fin m → ℝ :=
  fun i => b i - ∑ j, A i j * x j

/-- The log barrier `ψ(x) = −Σᵢ log sᵢ(x)` (7). -/
noncomputable def logBarrier {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -∑ i, Real.log (slack A b x i)

/-- The gradient `∇ψ(x) = A⊤s(x)⁻¹`. -/
noncomputable def gradLogBarrier {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => ∑ i, A i j / slack A b x i

/-- The Hessian `H(x) = A⊤S(x)⁻²A` (8). -/
noncomputable def hessLogBarrier {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  A.transpose * Matrix.diagonal (fun i => 1 / slack A b x i ^ 2) * A

/-- The local norm `‖v‖_x = √(v⊤H(x)v)` (8). -/
noncomputable def localNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∑ j, ∑ k, v j * hessLogBarrier A b x j k * v k)

/-- The dual local norm `‖v‖_{x,∗} = √(v⊤H(x)⁻¹v)` (8). -/
noncomputable def dualLocalNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∑ j, ∑ k, v j * (hessLogBarrier A b x)⁻¹ j k * v k)

/-- The uniform probability measure `π` on `X`. -/
noncomputable def uniform {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  ProbabilityTheory.cond volume (polytope A b)

/-- The normalizing constant `Z(t) = ∫ exp(−tψ) dπ` (43). -/
noncomputable def partitionZ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-t * logBarrier A b x) ∂(uniform A b)

/-- The cooled measure `π_t ∝ exp(−tψ)π` (43), with density `exp(−tψ)/Z(t)` against `π`. -/
noncomputable def cooled {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (t : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (uniform A b).withDensity fun x =>
    ENNReal.ofReal (Real.exp (-t * logBarrier A b x) / partitionZ A b t)

end PolySampIso


