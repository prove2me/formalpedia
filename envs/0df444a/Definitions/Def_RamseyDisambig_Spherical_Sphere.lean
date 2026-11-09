-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_Sphere
-- name    : RamseyDisambig_Spherical_Sphere
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:25:12.302861+00:00
-- url     : https://prove2.me/theorems/c0560b06-72f4-4e11-a813-433721f94eb4
-- title:
--   Spherical margin matrices and their disambiguations
-- statement:
--   For a natural dimension $d$, let $S^d$ be the full unit sphere in $\mathbb R^{d+1}$. Write $d_S(x,y)=\arccos\langle x,y\rangle$ for angular distance. For $0<\varepsilon<\pi/2$, define
--   $$M_\varepsilon^d[x,y]=\begin{cases}0&d_S(x,y)\le\varepsilon,\\1&d_S(x,y)\ge\pi-\varepsilon,\\\star&\text{otherwise}.\end{cases}$$
--   A spherical disambiguation is any binary matrix preserving these specified entries. It has no symmetry, measurability or continuity requirement. The predicate $\operatorname{SphericalFamilyUniversal}(\varepsilon)$ means that $(M_\varepsilon^d)_{d\ge1}$ is disambiguation-universal in the preceding sense.
--
--   These definitions give the geometric object and the universality conclusion of Theorem 1.
--
--   **Formalization Note** The carrier is the sphere subtype of `EuclideanSpace ℝ (Fin (d+1))`, and angular distance is `InnerProductGeometry.angle` of the underlying vectors. The family index is a positive natural number. Outside the stated angular range, the total partial-matrix function gives precedence to the near case; no theorem here uses that unsupported range.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), §1 and §2.4, pp. 3, 13 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Matrices

set_option autoImplicit false

noncomputable section

namespace RamseyDisambig.Spherical

/-- The full sphere S^d in R^(d+1), pp. 3, 13. -/
abbrev Sphere (d : ℕ) :=
  {x : EuclideanSpace ℝ (Fin (d + 1)) // x ∈ Metric.sphere 0 1}

/-- Angular, rather than chordal, distance on the unit sphere. -/
def sphericalDistance {d : ℕ} (x y : Sphere d) : ℝ :=
  InnerProductGeometry.angle x.val y.val

/-- The spherical margin partial matrix, for use with 0 < ε < π/2. -/
def sphericalMarginMatrix (ε : ℝ) (d : ℕ) : PartialMatrix (Sphere d) (Sphere d) :=
  fun x y => if sphericalDistance x y ≤ ε then some false
    else if Real.pi - ε ≤ sphericalDistance x y then some true else none

/-- No symmetry or regularity is imposed on a completion. -/
def IsSphericalDisambiguation (ε : ℝ) (d : ℕ) (c : Sphere d → Sphere d → Bool) : Prop :=
  IsDisambiguation (sphericalMarginMatrix ε d) c

/-- The family in Theorem 1 contains precisely the positive-dimensional spheres. -/
def SphericalFamilyUniversal (ε : ℝ) : Prop :=
  DisambiguationUniversal (fun d : ℕ+ => Sphere d) (fun d : ℕ+ => Sphere d)
    (fun d => sphericalMarginMatrix ε d)

end RamseyDisambig.Spherical


