-- Prove2me | Definitions.Def_EquivalencePrinciple
-- name    : EquivalencePrinciple
-- status  : Definition
-- author  : @LG
-- created : 2026-11-27T00:56:02.334811+00:00
-- url     : https://prove2.me/theorems/ed6e000d-9f61-41f6-9975-f789596095ae
-- title:
--   Equivalence principle: free fall, metric spacetimes and local flatness
-- statement:
--   This definition file introduces, in the namespace `EquivalencePrinciple`, the notions used to formalize the equivalence principle (weak, Einstein) on plain coordinate spaces.
--
--   **1. Spaces.** `Vec3 = Fin 3 → ℝ` (space) and `Sp = Fin 4 → ℝ` (spacetime), both plain tuples in standard coordinates; `stdBasis k` is the standard basis vector of `Sp` (1 in position `k`, 0 elsewhere), and `minkowskiDiag` is the signature diagonal `(-1, 1, 1, 1)`.
--
--   **2. Newtonian free fall (`IsGravField`, `FallingBody`, `SameLaunch`, `eotvosRatio`).** A gravitational field is a continuously differentiable vector field `G : Vec3 → Vec3` — the acceleration field $-\nabla\Phi$ of a gravitational potential; the potential itself is not carried. A falling test body in `G` is a structure: passive gravitational mass `mg` and inertial mass `mi`, both positive; a twice continuously differentiable trajectory `x : ℝ → Vec3`; and Newton's second law with gravity as the only force,
--
--   $$\mathrm{deriv}\,(\mathrm{deriv}\ x)\ t \;=\; (m_g / m_i) \,\cdot\, G(x(t)) \quad \text{for every } t,$$
--
--   i.e. $m_i\, x'' = m_g\, G \circ x$. Two bodies are `SameLaunch A B t₀` when $A.x\, t₀ = B.x\, t₀$ and $\mathrm{deriv}\ A.x\ t₀ = \mathrm{deriv}\ B.x\ t₀$ (same initial position and velocity). The Eötvös ratio of two bodies is
--
--   $$\eta(A, B) \;=\; 2\,(r_A - r_B)\,/\,(r_A + r_B), \qquad r = m_g/m_i,$$
--
--   the normalized difference of mass ratios compared by the torsion-balance experiments; the weak equivalence principle says $\eta = 0$ for every pair.
--
--   **3. Metric spacetimes (`Spacetime`).** A structure with fields: `g : Sp → Fin 4 → Fin 4 → ℝ`, the metric components in standard coordinates; `hg : ContDiff ℝ 2 g`; `hsymm`, symmetry $g_{ij} = g_{ji}$; the Lorentz-signature witness `hB`: for every point $p$ there is an invertible matrix $B$ (IsUnit of the determinant) with
--
--   $$B^{T}\, (g_{ij}(p))_{i,j}\, B \;=\; \mathrm{diag}(-1, 1, 1, 1),$$
--
--   which encodes both the signature and nondegeneracy; and a carried pointwise inverse `ginv p` of the component matrix with `hinv : (ginv p) · (g(p)) = 1`. Carrying these witnesses as data rules out vacuous encodings (the platform's Hodge-conjecture convention).
--
--   **4. Christoffel symbols (`Christoffel`).** Of the second kind, in standard coordinates:
--
--   $$\Gamma^k_{ij}(p) \;=\; \tfrac12 \sum_{l} (g^{-1})^{kl}(p)\,\big(\partial_i g_{jl} + \partial_j g_{il} - \partial_l g_{ij}\big)(p),$$
--
--   where the partial derivatives are the framework differentials `fderiv` of the component functions applied to the standard basis vectors.
--
--   **5. Freely falling worldlines (`IsFreelyFalling`).** `γ : ℝ → Sp` is freely falling in `S` when it is twice continuously differentiable and satisfies the geodesic equation for every `t`:
--
--   $$\gamma''^k(t) \;=\; -\sum_{i,j} \Gamma^k_{ij}(\gamma(t))\ \gamma'^i(t)\ \gamma'^j(t).$$
--
--   No mass, charge, composition or other particle property enters the equation — the geometric form of the universality of free fall ("trajectories of freely falling bodies are geodesics of symmetric metric").
--
--   **6. Pulled-back metric (`pullbackMetric`).** For a change of coordinates `φ : Sp → Sp`, the components at `q` of the metric in the transformed coordinates:
--
--   $$(\varphi^* g)_{ij}(q) \;=\; \sum_{a,b}\ \partial_i \varphi^a(q)\ \partial_j \varphi^b(q)\ g_{ab}(\varphi\, q),$$
--
--   with the partial derivatives again read from the framework differentials of `φ`.
--
--   **Formalization note.** All statements live on plain coordinate spaces (`Fin 3 → ℝ`, `Fin 4 → ℝ`) with no manifold machinery; differentiability is Mathlib's `ContDiff`/`fderiv`/`deriv` on these finite-dimensional real vector spaces.
-- source:
--   Wikipedia, Equivalence principle, https://en.wikipedia.org/wiki/Equivalence_principle (source of the quoted statements, reproduced verbatim in the definition file)

import Mathlib

/-!
The equivalence principle — weak (Galilean), Einstein and strong — formalised in
a concrete Newtonian and metric framework.

Source: Wikipedia, *Equivalence principle*,
https://en.wikipedia.org/wiki/Equivalence_principle .  Exact source statements:

"The equivalence principle is the hypothesis that the observed equivalence of
gravitational and inertial mass is a consequence of nature. The weak form, known
for centuries, relates to masses of any composition in free fall taking the same
trajectories and landing at identical times. The extended form by Albert Einstein
requires special relativity to also hold in free fall and requires the weak
equivalence to be valid everywhere. This form was a critical input for the
development of the theory of general relativity. The strong form requires
Einstein's form to work for stellar objects."

Weak equivalence principle (a.k.a. universality of free fall): "All uncharged,
freely falling test particles follow the same trajectories, once an initial
position and velocity have been prescribed"; "... in a gravitational field the
acceleration of a test particle is independent of its properties, including its
rest mass."  In Newtonian mechanics the identity reading is: "inertial mass
times acceleration = gravitational mass times gravitational acceleration", with
passive gravitational mass proportional to inertial mass if and only if the weak
equivalence principle is obeyed; the dimensionless Eotvos ratio compares two
test bodies.

Einstein equivalence principle: the weak principle together with local Lorentz
invariance and local position invariance; "Theories of gravity that obey the
Einstein equivalence principle must be 'metric theories', meaning that
trajectories of freely falling bodies are geodesics of symmetric metric."
Einstein (1907): "...assume the complete physical equivalence of a gravitational
field and a corresponding acceleration of the reference system."

Scope, disclosed.  The local-Lorentz and local-position invariance legs of the
Einstein principle refer to outcomes of laboratory experiments, for which the
source itself notes "there is no universally accepted way to distinguish
gravitational from non-gravitational experiments"; they are not formalised
here.  The strong principle (self-gravitating test bodies) is likewise out of
scope.  What is formalised is the mathematically sharp content of the source:
(i) free fall in a Newtonian gravitational field, with the mass-ratio law
`m_inertial * x'' = m_gravitational * G(x)` and the Eotvos ratio; (ii) metric
spacetimes — smooth symmetric fields of nondegenerate bilinear forms of
Lorentz signature `(-,+,+,+)` on `R^4`, with carried coordinate-change and
inverse witnesses — Christoffel symbols, and freely falling worldlines as
solutions of the geodesic equation, in which no property of the particle
appears; (iii) the two universality-of-free-fall theorems (Newtonian and
geodesic) and the local-flatness statement that realises Einstein's "complete
physical equivalence of a gravitational field and a corresponding acceleration
of the reference system" to first order: at every point a twice continuously
differentiable change of coordinates makes the metric Minkowski at the point
and removes all of its first derivatives there (Riemann normal coordinates to
first order).

Everything is elementary and concrete: space is `Fin 3 -> R`, spacetime is
`Fin 4 -> R` in standard coordinates, no manifold machinery is used, and the
metric's coordinate-change and inverse witnesses are carried as data (as in the
platform's Hodge-conjecture framework, carrying witnesses rules out vacuous
encodings).
-/

namespace EquivalencePrinciple

open Matrix

/-- Space: triples of real coordinates. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Spacetime: quadruples of real coordinates. -/
abbrev Sp := Fin 4 → ℝ

/-- The standard basis vector of `Fin 4 → ℝ`. -/
def stdBasis (k : Fin 4) : Sp := fun j => if j = k then 1 else 0

/-- The Minkowski signature diagonal `(-1, 1, 1, 1)`. -/
def minkowskiDiag : Fin 4 → ℝ := fun i => if i = 0 then -1 else 1

/-- A Newtonian gravitational field: a continuously differentiable vector field
`G` on space — the acceleration field `-∇Φ` of a gravitational potential `Φ`;
the potential itself is not needed. -/
def IsGravField (G : Vec3 → Vec3) : Prop := ContDiff ℝ 1 G

/-- A falling test body in the field `G`: passive gravitational mass `mg` and
inertial mass `mi`, both positive, and a twice continuously differentiable
trajectory obeying Newton's second law with gravity as the only force,

`mi • x''(t) = mg • G (x t)`,  i.e.  `x''(t) = (mg / mi) • G (x t)`.

The source: "inertial mass × acceleration = gravitational mass × gravitational
acceleration".  The acceleration of the body depends on the masses only through
the ratio `mg / mi`; the weak equivalence principle asserts (and experiment
confirms) that this ratio is the same for all bodies. -/
structure FallingBody (G : Vec3 → Vec3) where
  /-- Passive gravitational mass. -/
  mg : ℝ
  /-- Inertial mass. -/
  mi : ℝ
  /-- Masses are positive. -/
  hmg : 0 < mg
  /-- Masses are positive. -/
  hmi : 0 < mi
  /-- The trajectory. -/
  x : ℝ → Vec3
  /-- The trajectory is twice continuously differentiable. -/
  hx : ContDiff ℝ 2 x
  /-- Newton's second law with gravity as the only force. -/
  law : ∀ t : ℝ, deriv (deriv x) t = (mg / mi) • G (x t)

/-- Two falling bodies launched from the same place with the same velocity at
time `t₀`: "once an initial position and velocity have been prescribed". -/
def SameLaunch {G : Vec3 → Vec3} (A B : FallingBody G) (t₀ : ℝ) : Prop :=
  A.x t₀ = B.x t₀ ∧ deriv A.x t₀ = deriv B.x t₀

/-- The Eötvös ratio of two falling bodies: the normalised difference of their
passive-gravitational-to-inertial mass ratios,

`η(A, B) = 2 (r_A - r_B) / (r_A + r_B)`,  `r = mg / mi`,

the quantity the Eötvös and later torsion-balance experiments drive toward
zero; the weak equivalence principle says `η = 0` for every pair of bodies. -/
noncomputable def eotvosRatio {G : Vec3 → Vec3} (A B : FallingBody G) : ℝ :=
  2 * (A.mg / A.mi - B.mg / B.mi) / (A.mg / A.mi + B.mg / B.mi)

/-- A metric spacetime: a twice continuously differentiable field of symmetric
nondegenerate bilinear forms of Lorentz signature `(-,+,+,+)` on `R^4`, given by
its component functions `g p i j` in the standard coordinates, together with
carried witnesses: at every point `p` an invertible matrix `B p` congruence-
transforming `g p` to the Minkowski diagonal (this encodes the signature and,
with it, nondegeneracy), and a pointwise inverse `ginv p` of the component
matrix.  Carrying the witnesses as data rules out vacuous encodings, as in the
platform's Hodge-conjecture framework. -/
structure Spacetime where
  /-- Metric components in the standard coordinates. -/
  g : Sp → Fin 4 → Fin 4 → ℝ
  /-- The metric is twice continuously differentiable. -/
  hg : ContDiff ℝ 2 g
  /-- The metric is symmetric. -/
  hsymm : ∀ p i j, g p i j = g p j i
  /-- Lorentz signature `(-,+,+,+)` at every point, by invertible congruence. -/
  hB : ∀ p, ∃ B : Matrix (Fin 4) (Fin 4) ℝ, IsUnit B.det ∧
    Bᵀ * (Matrix.of fun i j => g p i j) * B = Matrix.diagonal minkowskiDiag
  /-- A pointwise inverse of the component matrix. -/
  ginv : Sp → Matrix (Fin 4) (Fin 4) ℝ
  /-- The carried inverse is a left inverse. -/
  hinv : ∀ p, ginv p * (Matrix.of fun i j => g p i j) = 1

/-- Christoffel symbols of the second kind of the metric, in the standard
coordinates:

`Γ^k_{ij}(p) = ½ Σ_l (g⁻¹)^{kl}(p) (∂_i g_{jl} + ∂_j g_{il} - ∂_l g_{ij})(p)`. -/
noncomputable def Christoffel (S : Spacetime) (p : Sp) (k i j : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 4, (S.ginv p k l) *
    ((fderiv ℝ (fun q => S.g q j l) p (stdBasis i)) +
     (fderiv ℝ (fun q => S.g q i l) p (stdBasis j)) -
     (fderiv ℝ (fun q => S.g q i j) p (stdBasis l)))

/-- A freely falling test particle in the spacetime `S`: a twice continuously
differentiable worldline obeying the geodesic equation

`γ''^k = - Σ_{i,j} Γ^k_{ij}(γ) γ'^i γ'^j`,

the equation of motion of a metric theory ("trajectories of freely falling
bodies are geodesics of symmetric metric").  No mass, charge, composition or
other property of the particle enters the equation — this is the geometric
form of the universality of free fall. -/
def IsFreelyFalling (S : Spacetime) (γ : ℝ → Sp) : Prop :=
  ContDiff ℝ 2 γ ∧ ∀ t : ℝ, deriv (deriv γ) t = fun k =>
    (-∑ i : Fin 4, ∑ j : Fin 4,
      Christoffel S (γ t) k i j * (deriv γ t i) * (deriv γ t j))

/-- The components at `q` of the metric in the coordinates transformed by the
change of coordinates `φ` (the pullback of the metric field along `φ`):

`(φ* g)_{ij}(q) = Σ_{a,b} ∂_i φ^a (q) ∂_j φ^b (q) g_{ab}(φ q)`. -/
noncomputable def pullbackMetric (φ : Sp → Sp) (g : Sp → Fin 4 → Fin 4 → ℝ)
    (q : Sp) (i j : Fin 4) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, (fderiv ℝ φ q (stdBasis i) a) *
    (fderiv ℝ φ q (stdBasis j) b) * g (φ q) a b

end EquivalencePrinciple


