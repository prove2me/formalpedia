-- Prove2me | Definitions.Def_ZonotopeContainment_AdaptiveSampling_Geometry
-- name    : ZonotopeContainment_AdaptiveSampling_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:11:34.375803+00:00
-- url     : https://prove2.me/theorems/ead2562d-b344-4c14-8e57-604ac1ddfcc3
-- title:
--   Euclidean zonotopes, support and approximate Lewis position
-- statement:
--   For a family $v_1,\ldots,v_n\in\mathbb R^d$, define its origin-centred zonotope and support by
--   $$Z(v)=\left\{\sum_{i=1}^n t_iv_i: |t_i|\le1\right\},\qquad h_{Z(v)}(b)=\sup_{x\in Z(v)}\langle b,x\rangle.$$
--   The supremum is taken over the actual zonotope, including $Z(\varnothing)=\{0\}$, rather than defined by a closed-form support identity. The finite zonotope is compact and nonempty.
--
--   The Lewis matrix is
--   $$L(v)=\sum_i\frac{v_iv_i^\top}{\|v_i\|}.$$
--   An approximate Lewis map for $w$ is an invertible real matrix $T$ with $\tfrac14 I\preceq L(Tw)\preceq I$, in the Loewner order. Zero generators contribute zero to the Lewis matrix.
--
--   These are the reusable geometric objects needed for the sampling algorithm. Vectors carry the Euclidean norm; generator coefficients are scalars in a finite family.
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), equation (3) and §1.1, p. 2; §2.1, p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib

noncomputable section
open scoped BigOperators MatrixOrder

namespace ZonotopeContainment.AdaptiveSampling

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The matrix acts on Euclidean coordinates, with their ℓ₂ norm. -/
def act {d : ℕ} (M : Mat d) (x : E d) : E d := M.toEuclideanLin x

/-- Equation (3), p. 2: the origin-centred zonotope with its generators as data. -/
def zonotope {d n : ℕ} (v : Fin n → E d) : Set (E d) :=
  {x | ∃ t : Fin n → ℝ, (∀ i, |t i| ≤ 1) ∧ x = ∑ i, t i • v i}

/-- Only used on a finite zonotope: the image is nonempty and compact, even if n = 0. -/
def support {d n : ℕ} (v : Fin n → E d) (b : E d) : ℝ :=
  sSup ((fun x => inner ℝ b x) '' zonotope v)

/-- The summand is zero for a zero generator (Lean's division convention). -/
def rankOne {d : ℕ} (v : E d) : Mat d := fun k l => v k * v l

def lewis {d n : ℕ} (v : Fin n → E d) : Mat d :=
  ∑ i, (‖v i‖⁻¹ : ℝ) • rankOne (v i)

/-- The preprocessing map is an input; no properties of later iterates are assumed. -/
def ApproxLewis {d n : ℕ} (w : Fin n → E d) (T : Mat d) : Prop :=
  IsUnit T ∧ (1 / 4 : ℝ) • (1 : Mat d) ≤ lewis (fun i => act T (w i)) ∧
    lewis (fun i => act T (w i)) ≤ (1 : Mat d)

end ZonotopeContainment.AdaptiveSampling


