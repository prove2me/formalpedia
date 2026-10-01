-- Prove2me | Definitions.Def_ThomsonProblem_defs
-- name    : ThomsonProblem_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T20:11:51.44427+00:00
-- url     : https://prove2.me/theorems/e124251d-ff90-44c1-b27a-c1158529ad37
-- title:
--   Thomson problem: configurations on the unit sphere, Coulomb energy, and the candidate optimal configurations
-- statement:
--   This file sets up the **Thomson problem**: place $N$ electrons on the unit sphere $S^2\subset\mathbb R^3$ so that their total Coulomb energy is as small as possible.
--
--   1. **Admissible configuration.** An $N$-point configuration is a map $x:\{0,\dots,N-1\}\to\mathbb R^3$. It is *admissible* if every point lies on the unit sphere, $\|x_i\|=1$, and the points are pairwise distinct, $x_i\neq x_j$ for $i\neq j$.
--   2. **Coulomb energy.** In units with $e=1$ and Coulomb constant $k_e=1$,
--   $$
--   U(x)=\sum_{0\le i<j\le N-1}\frac{1}{\|x_i-x_j\|}.
--   $$
--   3. **Energy minimiser.** A configuration $x$ *solves the Thomson problem for $N$ electrons* if it is admissible and $U(x)\le U(y)$ for every admissible $N$-point configuration $y$.
--   4. **Candidate configurations** (explicit coordinates, all on the unit sphere):
--      - $N=2$: the antipodal pair $(0,0,\pm1)$;
--      - $N=3$: the equilateral triangle $(1,0,0)$, $(-\tfrac12,\pm\tfrac{\sqrt3}{2},0)$ on the equator (a great circle);
--      - $N=4$: the regular tetrahedron $\tfrac1{\sqrt3}(1,1,1),\tfrac1{\sqrt3}(1,-1,-1),\tfrac1{\sqrt3}(-1,1,-1),\tfrac1{\sqrt3}(-1,-1,1)$;
--      - $N=5$: the triangular bipyramid: the poles $(0,0,\pm1)$ together with the equatorial equilateral triangle above;
--      - $N=6$: the regular octahedron $\pm e_1,\pm e_2,\pm e_3$;
--      - $N=7$: the pentagonal bipyramid: the poles $(0,0,\pm1)$ together with the regular pentagon $p_k=(\cos\tfrac{2\pi k}{5},\sin\tfrac{2\pi k}{5},0)$, $k=0,\dots,4$;
--      - $N=12$: the regular icosahedron: the twelve points $(0,\pm1,\pm\varphi)$, $(\pm1,\pm\varphi,0)$, $(\pm\varphi,0,\pm1)$, each divided by $\sqrt{1+\varphi^2}$, where $\varphi=\tfrac{1+\sqrt5}{2}$ is the golden ratio.
--
--   These definitions are shared by every statement of the mission. The energy is invariant under rotations and reflections of the sphere and under relabelling of the points, so fixing one particular orientation of each candidate polyhedron loses no generality.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin 3)`, configurations are functions `Fin N → EuclideanSpace ℝ (Fin 3)`, and the pairwise sum runs over $j\in(i,N-1]$ via `Finset.Ioi i`. Lean's convention $1/0=0$ only affects non-admissible configurations with coincident points, which are excluded by the admissibility hypothesis.
-- source:
--   Wikipedia, "Thomson problem" (as uploaded, PDF snapshot retrieved 2026-09-29/30), sections "Mathematical statement", "Example" and "Known exact solutions".

import Mathlib

namespace ThomsonProblem

/-- Euclidean three-space `ℝ³` with its usual (Euclidean) distance. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- An admissible `N`-electron configuration: `N` pairwise distinct points on the unit
sphere `{v ∈ ℝ³ : ‖v‖ = 1}`. -/
def IsAdmissible {N : ℕ} (x : Fin N → Space) : Prop :=
  (∀ i, ‖x i‖ = 1) ∧ Function.Injective x

/-- The Coulomb (Riesz `s = 1`) energy `∑_{i < j} 1 / ‖x i - x j‖` of a configuration,
in units with `e = 1` and `kₑ = 1`. -/
noncomputable def coulombEnergy {N : ℕ} (x : Fin N → Space) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, 1 / dist (x i) (x j)

/-- `x` solves the Thomson problem for `N` electrons: it is admissible and its Coulomb
energy is at most that of every admissible `N`-point configuration. -/
def IsEnergyMinimizer {N : ℕ} (x : Fin N → Space) : Prop :=
  IsAdmissible x ∧ ∀ y : Fin N → Space, IsAdmissible y → coulombEnergy x ≤ coulombEnergy y

/-- `N = 2`: two antipodal points (the poles). -/
noncomputable def antipodalPair : Fin 2 → Space :=
  ![!₂[0, 0, 1], !₂[0, 0, -1]]

/-- `N = 3`: vertices of an equilateral triangle inscribed in the equator (a great circle). -/
noncomputable def equilateralTriangle : Fin 3 → Space :=
  ![!₂[1, 0, 0], !₂[-1 / 2, Real.sqrt 3 / 2, 0], !₂[-1 / 2, -(Real.sqrt 3 / 2), 0]]

/-- `N = 4`: vertices of a regular tetrahedron inscribed in the unit sphere. -/
noncomputable def regularTetrahedron : Fin 4 → Space :=
  fun i => (1 / Real.sqrt 3) •
    ![!₂[1, 1, 1], !₂[1, -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]] i

/-- `N = 5`: vertices of a triangular bipyramid (the two poles and an equilateral triangle
on the equator). -/
noncomputable def triangularBipyramid : Fin 5 → Space :=
  ![!₂[0, 0, 1], !₂[0, 0, -1],
    !₂[1, 0, 0], !₂[-1 / 2, Real.sqrt 3 / 2, 0], !₂[-1 / 2, -(Real.sqrt 3 / 2), 0]]

/-- `N = 6`: vertices of a regular octahedron (`±e₁, ±e₂, ±e₃`). -/
noncomputable def regularOctahedron : Fin 6 → Space :=
  ![!₂[1, 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0], !₂[0, -1, 0], !₂[0, 0, 1], !₂[0, 0, -1]]

/-- The `k`-th vertex `(cos (2πk/5), sin (2πk/5), 0)` of a regular pentagon inscribed in
the equator. -/
noncomputable def pentagonVertex (k : ℕ) : Space :=
  !₂[Real.cos (2 * Real.pi * k / 5), Real.sin (2 * Real.pi * k / 5), 0]

/-- `N = 7`: vertices of a pentagonal bipyramid (the two poles and a regular pentagon on
the equator). -/
noncomputable def pentagonalBipyramid : Fin 7 → Space :=
  ![!₂[0, 0, 1], !₂[0, 0, -1],
    pentagonVertex 0, pentagonVertex 1, pentagonVertex 2, pentagonVertex 3, pentagonVertex 4]

/-- `N = 12`: vertices of a regular icosahedron inscribed in the unit sphere: the twelve
points `(0, ±1, ±φ)`, `(±1, ±φ, 0)`, `(±φ, 0, ±1)` (with `φ` the golden ratio), each
scaled by `1 / √(1 + φ²)`. -/
noncomputable def regularIcosahedron : Fin 12 → Space :=
  fun i => (1 / Real.sqrt (1 + Real.goldenRatio ^ 2)) •
    ![!₂[0, 1, Real.goldenRatio], !₂[0, 1, -Real.goldenRatio],
      !₂[0, -1, Real.goldenRatio], !₂[0, -1, -Real.goldenRatio],
      !₂[1, Real.goldenRatio, 0], !₂[1, -Real.goldenRatio, 0],
      !₂[-1, Real.goldenRatio, 0], !₂[-1, -Real.goldenRatio, 0],
      !₂[Real.goldenRatio, 0, 1], !₂[Real.goldenRatio, 0, -1],
      !₂[-Real.goldenRatio, 0, 1], !₂[-Real.goldenRatio, 0, -1]] i

end ThomsonProblem


