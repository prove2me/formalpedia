-- Prove2me | Definitions.Def_ADMFormalism
-- name    : ADMFormalism
-- status  : Definition
-- author  : @LG
-- created : 2026-11-27T02:45:48.463005+00:00
-- url     : https://prove2.me/theorems/7a577ddb-f9c9-4d78-b63b-6097b33459b6
-- title:
--   The ADM 3+1 split: lapse, shift, spatial metric, and the ADM line element as a bilinear form
-- statement:
--   The ADM (Arnowitt-Deser-Misner) 3+1 split of general relativity, as a concrete kinematic framework.  Spacetime is the product of a time coordinate and spatial coordinates (Spc4 = R x (Fin 3 -> R)); tangent vectors are pairs of a time component and a spatial component.  The ADM data is a structure ADMData carrying the source's dynamic and gauge variables: the lapse function N (strictly positive), the shift vector field ns, and the spatial metric gamma of the slices (symmetric and positive definite on every slice - the slices are Riemannian, i.e. the source's 'spacelike surfaces'), all smooth in (t, x).  The source's line element ds^2 = -N^2 dt^2 + g_ij (dx^i + N^i dt)(dx^j + N^j dt) is the bilinear form admForm D t x u v on tangent vectors at the base event (t, x).  Auxiliary notions: gammaPair (the spatial pairing g_ij a^i b^j), normalVec (the Eulerian observers' 4-velocity, the normalized normal (1/N, -N^i/N)), and minkForm (the flat Minkowski form of signature (-,+,+,+), the target of the goal congruence).
-- source:
--   Wikipedia, ADM formalism, https://en.wikipedia.org/wiki/ADM_formalism (source of the quoted statements, reproduced verbatim in the definition file)

import Mathlib

/-!
The ADM formalism — the 3+1 split of general relativity, formalized as the
kinematic skeleton of the source's line element in a concrete framework.

Source: Wikipedia, *ADM formalism*,
https://en.wikipedia.org/wiki/ADM_formalism .  Exact source statements:

"The Arnowitt-Deser-Misner (ADM) formalism ... is a Hamiltonian formulation of
general relativity that plays an important role in canonical quantum gravity
and numerical relativity."  "The formalism supposes that spacetime is foliated
into a family of spacelike surfaces Sigma_t, labeled by their time coordinate
t, and with coordinates on each slice given by x^i. The dynamic variables of
this theory are taken to be the metric tensor of three-dimensional spatial
slices gamma_ij(t, x^k) and their conjugate momenta pi_ij(t, x^k)."  "In
addition to the twelve variables gamma_ij and pi_ij, there are four Lagrange
multipliers: the lapse function, N, and components of shift vector field, N^i.
These describe how each of the 'leaves' Sigma_t of the foliation of spacetime
are welded together."

The ADM split: "The ADM split denotes the separation of the spacetime metric
into three spatial components and one temporal component (foliation)."
Mathematically,

ds^2 = -N^2 dt^2 + g_ij (dx^i + N^i dt)(dx^j + N^j dt),

"where N is the lapse function encoding the proper time evolution, N^i is the
shift vector, encoding how spatial coordinates change between hypersurfaces.
g_ij is the emergent 3D spatial metric on each hypersurface."  "This
decomposition allows for a separation of the spacetime evolution equations into
constraints (which relate the initial data on a spatial hypersurface) and
evolution equations (which describe how the geometry of spacetime changes from
one hypersurface to another)."  In the derivation, "The metric of the
three-dimensional slices g_ij = (4)g_ij will be the generalized coordinates for
a Hamiltonian formulation", and "The lapse N = (- (4)g_00)^{-1/2} and the shift
vector N^i = (4)g_{0i} are the remaining elements of the four-metric tensor."

Scope, disclosed.  No manifold machinery and no dynamics: the mission
formalizes the kinematic core of the 3+1 split on the plain product space
`Spc4 = R x (Fin 3 -> R)` (a base event `(t, x)` and tangent vectors as pairs
of a time component and a spatial component).  The ADM data is a structure: a
positive lapse `N`, a shift vector field `ns`, and a spatial metric `gamma`
that is symmetric and positive definite on every slice (the slices are
Riemannian — the source's "spacelike surfaces"), with smoothness of all three
fields carried as `ContDiff R infinity` hypotheses on the product.  The
line element is the bilinear form `admForm` — exactly the source's `ds^2`
formula read as a bilinear form on tangent vectors.  The theorems are the
kinematic content of the split, pointwise in the base event `(t, x)`: the
slices are spacelike with induced metric `gamma` (the source's `g_ij = (4)g_ij`
plus the spacelike character of the foliation); the Eulerian observers'
4-velocity — the normalized normal vector `(1/N, -N^i/N)` — is a unit timelike
vector orthogonal to every purely spatial direction; the proper-time rate of
these observers is the lapse (`dtau = N dt`, "the lapse function encoding the
proper time evolution"); the ADM 4-metric is nondegenerate; and the goal: the
ADM 4-metric is congruent to the flat Minkowski form of signature `(-,+,+,+)`
— the ADM data defines a Lorentzian metric, the premise on which the
formalism's dynamics (constraints and evolution equations) rests.

What is NOT formalized: the Einstein-Hilbert Lagrangian and its 3+1 rewriting,
the conjugate momenta `pi_ij`, the Hamiltonian and momentum constraints `H`,
`P_i` (they involve the intrinsic Ricci scalar `(3)R` and covariant
derivatives), the evolution equations for `gamma_ij` and `pi_ij` (nonlinear
PDE), curvature entirely, the Wheeler-DeWitt equation and canonical quantization,
numerical-relativity schemes, and the ADM energy/mass at infinity.
-/

namespace ADMFormalism

open Matrix
open scoped ContDiff

/-- Spatial coordinates: plain real triples. -/
abbrev Spc3 := Fin 3 → ℝ

/-- Spacetime in 3+1 split: a time coordinate paired with spatial coordinates.
Tangent vectors are pairs `(time component, spatial component)`. -/
abbrev Spc4 := ℝ × Spc3

/-- ADM data: the dynamic and gauge variables of the source.  `N` is the lapse
function ("encoding the proper time evolution"), `ns` the shift vector field
("encoding how spatial coordinates change between hypersurfaces"), and `γ` the
spatial metric of the slices ("the metric tensor of three-dimensional spatial
slices"), symmetric and positive definite — the slices are Riemannian, i.e.
"spacelike surfaces".  Smoothness of all three fields is carried as `C^∞`
hypotheses on the product `(t, x)`. -/
structure ADMData where
  /-- The lapse function. -/
  N : ℝ → Spc3 → ℝ
  /-- The shift vector field. -/
  ns : ℝ → Spc3 → Fin 3 → ℝ
  /-- The spatial metric on the slices. -/
  γ : ℝ → Spc3 → Matrix (Fin 3) (Fin 3) ℝ
  /-- The lapse is positive. -/
  hN : ∀ t x, 0 < N t x
  /-- The slice metric is symmetric. -/
  hγsymm : ∀ t x i j, γ t x i j = γ t x j i
  /-- The slice metric is positive definite — the slices are spacelike. -/
  hγpd : ∀ t x, (γ t x).PosDef
  /-- Smoothness of the lapse. -/
  hNsmooth : ContDiff ℝ ∞ (fun p : ℝ × Spc3 => N p.1 p.2)
  /-- Smoothness of the shift. -/
  hnssmooth : ContDiff ℝ ∞ (fun p : ℝ × Spc3 => ns p.1 p.2)
  /-- Smoothness of the slice metric, entrywise. -/
  hγsmooth : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × Spc3 => γ p.1 p.2 i j)

/-- The spatial metric pairing `g_ij a^i b^j` on a slice. -/
def gammaPair (D : ADMData) (t : ℝ) (x : Spc3) (a b : Spc3) : ℝ :=
  ∑ i, ∑ j, D.γ t x i j * a i * b j

/-- The ADM line element of the source, read as a bilinear form on tangent
vectors at the base event `(t, x)`:

`ds² = -N² dt² + γ_ij (dx^i + N^i dt)(dx^j + N^j dt)`. -/
def admForm (D : ADMData) (t : ℝ) (x : Spc3) (u v : Spc4) : ℝ :=
  -(D.N t x) ^ 2 * (u.1 * v.1)
  + ∑ i, ∑ j, D.γ t x i j * (u.2 i + D.ns t x i * u.1) * (v.2 j + D.ns t x j * v.1)

/-- The 4-velocity of the Eulerian (normal) observers: the unit normal to the
slices, `(1/N, -N^i/N)`. -/
noncomputable def normalVec (D : ADMData) (t : ℝ) (x : Spc3) : Spc4 :=
  (1 / D.N t x, fun i => -(D.ns t x i) / D.N t x)

/-- The flat Minkowski form of signature `(-,+,+,+)` on the 3+1 product space,
the target of the goal congruence. -/
def minkForm (u v : Spc4) : ℝ := -(u.1 * v.1) + ∑ i, u.2 i * v.2 i

end ADMFormalism


