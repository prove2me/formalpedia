-- Prove2me | Definitions.Def_RovelliLQG_Defs
-- name    : RovelliLQG_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T19:16:21.383466+00:00
-- url     : https://prove2.me/theorems/34193ba8-ab0e-4521-92b1-0c131e01778c
-- title:
--   Rovelli 2011: half-space polyhedra, face areas, cross product, and the LQG area spectrum
-- statement:
--   Shared definitions for the mission, all in the namespace `RovelliLQG`.
--
--   1. $\mathbb E^3$ (`E3`) is Euclidean three-space $\mathbb R^3$ with its standard inner product.
--   2. For a family of vectors $u_l$ and reals $h_l$, the **half-space polyhedron** is
--   $$P(u,h)=\{x\in\mathbb E^3:\langle u_l,x\rangle\le h_l\ \text{for all } l\}.$$
--   3. Its $l$-th **face** is $F_l(u,h)=P(u,h)\cap\{x:\langle u_l,x\rangle=h_l\}$.
--   4. For a vector $u$ and a set $S$, the **planar area** $\operatorname{area}_u(S)\in[0,\infty]$ is the Lebesgue (Haar) measure on the subspace $u^\perp$ of the orthogonal projection of $S$ onto $u^\perp$. For $S$ contained in a plane orthogonal to $u\neq0$ this is the usual area of $S$.
--   5. The **direction** of $n$ is $\hat n=n/\|n\|$ (and $\hat 0=0$).
--   6. The **cross product** $a\times b$ on $\mathbb E^3$.
--   7. $\operatorname{cas}(j)=\sqrt{j(j+1)}$, the square root of the $SU(2)$ Casimir eigenvalue in spin $j$.
--   8. The **area spectrum** (Rovelli, eq. (26)):
--   $$\mathcal A(\gamma,\hbar,G)=\Big\{8\pi\gamma\hbar G\sum_{n}\sqrt{j_n(j_n+1)}\ :\ (j_n)\ \text{a finite family in}\ \{0,\tfrac12,1,\tfrac32,\dots\}\Big\}.$$
--
--   These objects are the classical polyhedral geometry behind Penrose's spin–geometry theorem and the numerical area spectrum of loop quantum gravity.
--
--   **Formalization Note** Spins are encoded as $k/2$, $k\in\mathbb N$, and finite families as multisets. Areas take values in $[0,\infty]$.
-- source:
--   C. Rovelli, Loop quantum gravity: the first 25 years, Class. Quantum Grav. 28 (2011) 153002, doi:10.1088/0264-9381/28/15/153002, arXiv:1012.4707, §2.1 (eqs. (4)-(13)), §2.3 (eqs. (17)-(18)), §4.3 (eq. (26))

import Mathlib

namespace RovelliLQG

open scoped InnerProductSpace

/-- Euclidean three-space `ℝ³` with its standard inner product. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The (possibly empty or unbounded) polyhedron cut out by the half-spaces
`⟪u l, x⟫ ≤ h l`. -/
def halfspacePolyhedron {ι : Type*} (u : ι → E3) (h : ι → ℝ) : Set E3 :=
  {x | ∀ l, ⟪u l, x⟫_ℝ ≤ h l}

/-- The face of `halfspacePolyhedron u h` lying on the supporting plane `⟪u l, x⟫ = h l`. -/
def polyhedronFace {ι : Type*} (u : ι → E3) (h : ι → ℝ) (l : ι) : Set E3 :=
  halfspacePolyhedron u h ∩ {x | ⟪u l, x⟫_ℝ = h l}

/-- Two-dimensional area of a set `S` lying in a plane orthogonal to the nonzero vector `u`:
the Lebesgue (inner-product Haar) measure, on the plane `u^⊥`, of the orthogonal
projection of `S` onto `u^⊥`. -/
noncomputable def planarArea (u : E3) (S : Set E3) : ENNReal :=
  MeasureTheory.volume ((ℝ ∙ u)ᗮ.orthogonalProjection '' S)

/-- The unit vector in the direction of `n` (equal to `0` when `n = 0`). -/
noncomputable def unitDir (n : E3) : E3 := ‖n‖⁻¹ • n

/-- The cross product on `ℝ³`. -/
noncomputable def cross3 (a b : E3) : E3 :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))

/-- The quantity `√(j (j+1))`, the square root of the `SU(2)` Casimir eigenvalue
in the spin-`j` representation. -/
noncomputable def casimirRoot (j : ℝ) : ℝ := Real.sqrt (j * (j + 1))

/-- The area spectrum of eq. (26): all numbers `8 π γ ħ G ∑ₙ √(jₙ (jₙ+1))` for finite
families of spins `jₙ ∈ {0, 1/2, 1, 3/2, …}` (encoded as `jₙ = kₙ / 2`, `kₙ ∈ ℕ`). -/
noncomputable def areaSpectrum (γ ħ G : ℝ) : Set ℝ :=
  {A | ∃ ks : Multiset ℕ,
    A = 8 * Real.pi * γ * ħ * G * (ks.map (fun k : ℕ => casimirRoot ((k : ℝ) / 2))).sum}

end RovelliLQG


