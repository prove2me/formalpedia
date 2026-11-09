-- Prove2me | Definitions.Def_ModLatSVP_IsShortest
-- name    : ModLatSVP_IsShortest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:49.802715+00:00
-- url     : https://prove2.me/theorems/affdc1a2-e51c-473e-91b3-f2381eab72c3
-- title:
--   Solutions of SVP and CVP in the Gram-matrix input model
-- statement:
--   Let $G\in\mathbb Q^{N\times N}$ be the Gram matrix of a lattice $L=B_L\mathbb Z^N$, so that $\|B_Lx\|^2=x^TGx$.
--
--   1. $x\in\mathbb Z^N$ is a **shortest vector** (a solution of SVP) if $x\neq0$ and $x^TGx\le y^TGy$ for every nonzero $y\in\mathbb Z^N$.
--   2. For a rational target $t\in\mathbb Q^N$, representing $u=B_Lt$, $x\in\mathbb Z^N$ is a **closest vector** (a solution of CVP) if
--   $$(x-t)^TG(x-t)\le(y-t)^TG(y-t)\qquad\text{for every }y\in\mathbb Z^N .$$
--
--   These are the output conditions of every algorithm of the mission.
--
--   **Formalization Note** The condition $x\ne0$ is part of SVP: without it $x=0$ would be "shortest".
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §2.1, p.11 (PDF p.11)

import Mathlib

open Matrix

namespace ModLatSVP

/-- The squared length `xᵀ G x` over `ℚ`. Kim, Lee, Son, *Exact SVP and CVP in Structured Lattices:
Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256 e7151fad…), §2.1,
p.11: "∥B_L x∥² = xᵀGx, ∥B_L x − u∥² = (x − t)ᵀG(x − t)". -/
def qfQ {N : ℕ} (G : Matrix (Fin N) (Fin N) ℚ) (x : Fin N → ℚ) : ℚ :=
  x ⬝ᵥ (G *ᵥ x)

/-- `x` is a solution of SVP (§2.1, p.11): "find a nonzero vector v ∈ L satisfying ∥v∥ = λ₁(L) =
min_{x ∈ ℤ^m∖{0}} ∥B_L x∥", in the Gram-matrix input model: `x ≠ 0` and `xᵀGx ≤ yᵀGy` for every nonzero
`y ∈ ℤ^N`. -/
def IsShortest {N : ℕ} (G : Matrix (Fin N) (Fin N) ℚ) (x : Fin N → ℤ) : Prop :=
  x ≠ 0 ∧ ∀ y : Fin N → ℤ, y ≠ 0 →
    qfQ G (fun i => (x i : ℚ)) ≤ qfQ G (fun i => (y i : ℚ))

/-- `x` is a closest vector to the rational target `t` (§2.1, p.11): "find a vector v ∈ L satisfying
∥v − u∥ = dist(u, L) = min_{x ∈ ℤ^m} ∥B_L x − u∥", with `u = B_L t`: `(x − t)ᵀG(x − t) ≤ (y − t)ᵀG(y − t)`
for every `y ∈ ℤ^N`. -/
def IsClosest {N : ℕ} (G : Matrix (Fin N) (Fin N) ℚ) (t : Fin N → ℚ) (x : Fin N → ℤ) : Prop :=
  ∀ y : Fin N → ℤ, qfQ G ((fun i => (x i : ℚ)) - t) ≤ qfQ G ((fun i => (y i : ℚ)) - t)

end ModLatSVP


