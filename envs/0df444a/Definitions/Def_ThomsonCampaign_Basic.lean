-- Prove2me | Definitions.Def_ThomsonCampaign_Basic
-- name    : ThomsonCampaign_Basic
-- status  : Definition
-- author  : @vatsj
-- created : 2026-10-13T22:05:28.99238+00:00
-- url     : https://prove2.me/theorems/5cd81dc7-c42a-44a3-9553-824755a67d7c
-- title:
--   Sphere configurations and Coulomb energy
-- statement:
--   Let $\mathbb{R}^3$ carry its Euclidean norm. A **sphere configuration** of $n$ points is a map $x : \{0,\dots,n-1\} \to \mathbb{R}^3$ with $\lVert x_i \rVert = 1$ for every $i$ and $x$ injective, so the points lie on the unit sphere and are pairwise distinct. Its **Coulomb energy** is
--   $$E(x) = \sum_{i<j} \frac{1}{\lVert x_i - x_j \rVert}.$$
--   Distinctness matters in Lean, where $1/0 = 0$: without it, coincident points would cost nothing.
--   `cyl ρ θ h` is the point with cylindrical coordinates $(\rho\cos\theta, \rho\sin\theta, h)$.
-- source:
--   Definitions copied from the Thomson N = 7 Lean proof package (Hung Tran), https://github.com/huwngtran/thomson-n7-lean, ComparatorChallenges/ThomsonN7.lean.

import Mathlib

open Real

namespace ThomsonCampaign

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- `n` pairwise distinct points on the unit sphere of `ℝ³`. -/
def SphereConfig (n : ℕ) : Set (Fin n → R3) :=
  {x | (∀ i, ‖x i‖ = 1) ∧ Function.Injective x}

/-- Coulomb energy `∑_{i<j} 1 / ‖x i - x j‖`. -/
noncomputable def coulombEnergy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹

/-- The point with cylindrical coordinates `(ρ, θ, h)`. -/
noncomputable def cyl (ρ θ h : ℝ) : R3 := !₂[ρ * cos θ, ρ * sin θ, h]

end ThomsonCampaign


