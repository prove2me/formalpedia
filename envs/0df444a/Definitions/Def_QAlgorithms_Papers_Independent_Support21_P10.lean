-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P10
-- name    : QAlgorithms_Papers_Independent_Support21_P10
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:51:29.374733+00:00
-- url     : https://prove2.me/theorems/d568c8c5-0568-4db4-98cf-f787405c22b8
-- title:
--   Definitions for Observable actions of algebraic groups
-- statement:
--   The objects the formalized statements of *Observable actions of algebraic groups* (arXiv:0902.0137) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Point`: Geometric k-points of an affine k-algebra, PDF pp.1--3.
--   - `tensorEvaluation`: Evaluation at a point of an affine product, PDF pp.1--3. On a pure tensor a tensor b this is x(a)y(b).
--   - `IsAffineAlgebraicGroup`: The coordinate-ring description of the standing smooth affine algebraic group convention, PDF p.1. Over an algebraically closed field, finite type plus formal smoothness is smoothness. Multiplication and inversion are regular, and their group identities are carried by the Group instance on geometric points. Reduced finite-type algebras over this field are determined by their k-points, so these are the usual classical algebraic-group data.
--   - `IsAffineVariety`: The standing affine-variety convention in coordinate form, PDF p.1. Affineness implies separation. Empty varieties (the zero algebra) are allowed; irreducibility is imposed separately when required.
--   - `IsRegularAction`: Regularity of an action on the coordinate algebra, PDF pp.1--3. The homomorphism rho acts by algebra automorphisms. Its evaluation is regular in (g,x), witnessed by a map into the actual tensor-product coordinate ring. The corresponding left action on X is (g,x) mapsto x composed with rho(g^-1), so the induced coordinate action is precisely the source's g.f(x)=f(g^-1.x). The homomorphism laws already impose the action identities.
--   - `pointAction`: The induced left action on geometric points, with the source's inverse pullback convention, PDF p.1.
--   - `invariantSubalgebra`: The invariant subalgebra k[X]^G, PDF p.2.
--   - `IsStableIdeal`: Stability of an arbitrary ideal, including nonradical ideals, PDF p.3, Definition 2.4.
--   - `IsObservable`: Observability, exactly the nonzero-stable-ideal definition on PDF p.3, Definition 2.4. The invariant element is itself required to be nonzero.
--   - `IsConstantOnOrbits`: Constancy on geometric orbits of a morphism X to Spec B, PDF p.4. The morphism is represented by its pullback f : B to A.
--   - `IsRegularCharacter`: A regular algebraic character G to G_m, PDF p.11, Definition 3.14. A unit in k[G] is exactly a regular map from G to G_m; the monoid homomorphism condition is the character identity.
--   - `HasSemiInvariant`: Membership of a regular character in E_G(X), PDF p.11, Definition 3.14: existence of a nonzero semiinvariant of this weight.
--   - `SemiInvariantCharactersFormGroup`: E_G(X) is a group, PDF p.11. On the integral coordinate algebras used in Corollary 3.16, products of nonzero semiinvariants are nonzero, and the trivial character is represented by 1. Thus the remaining group condition is closure under inverses, with no assumption of finite generation.
--   - `localizedPullback`: Extension of each coordinate automorphism to the principal open X_f, PDF p.5. This uses the same invariant denominator, including f=0.
--   - `localizedInvariantSubalgebra`: The fixed coordinate algebra on X_f, PDF p.5. Its elements are fixed under the canonical extensions of all the original coordinate automorphisms.
--   - `invariantLocalizationMap`: The canonical restriction map from (k[X]^G)_f into k[X]_f, PDF p.5. It is the localization of the actual inclusion of the invariant algebra.
--   - `coordinateZeroLocus`: Common zero locus of coordinate functions on geometric k-points, PDF p.1.
--   - `coordinateVanishingIdeal`: The actual ideal of all functions vanishing on a subset, PDF p.1. Its use never replaces a nonradical stable ideal in observability.
--   - `classicalClosure`: Zariski closure in the classical affine variety, PDF pp.1,7--9,13. This is V(I(S)), computed from the subset, not an independently supplied set.
--   - `IsClassicallyOpen`: The classical Zariski-open subsets, complements of common zero loci, PDF p.1. No arbitrary topology is an input.
--   - `IsClassicallyDense`: Density in the actual classical Zariski topology, PDF p.11.
--   - `principalOpen`: The principal open X_f, including the empty open X_0, PDF p.1.
--   - `geometricOrbit`: The geometric geometricOrbit of a point, computed from the action, PDF pp.1--2.
--   - `IsClosedOrbit`: Closedness of the whole geometric geometricOrbit, PDF pp.1--2,7,9.
--   - `geometricOrbitDimension`: Dimension of an geometricOrbit, PDF p.7, Definition 3.6. An algebraic geometricOrbit is locally closed, so its dimension is the Krull dimension of its affine closure. The ring here is the actual coordinate ring of that closure. WithBot preserves dimension -1 for the empty closed set and avoids truncated natural subtraction; no finite-value coercion is used.
--   - `maximalOrbitLocus`: X_max is computed by comparison with every geometricOrbit in X, PDF p.7, Definition 3.6. This is not a chosen open subset.
--   - `omegaLocus`: Omega(X), the locus of closed orbits of maximal dimension, PDF p.7, Definition 3.6.
--   - `ContainsNonemptyOpen`: Containment of a nonempty Zariski-open subset, PDF p.9, Theorem 3.10.
--   - `IsInvariantRational`: Invariance of a rational function in the canonical fraction field, PDF pp.1--2,9. A nonzero denominator is explicit. For each g, the last identity is exactly rho(g)(a/b)=a/b after cross multiplication in a domain; it is independent of the chosen representation and uses the source's induced coordinate action. No rational invariance is assumed of a or b.
--   - `IsInvariantRegularFraction`: A rational function belongs to the canonical copy of [k[X]^G] in k(X) exactly when it is a fraction of invariant regular functions, PDF pp.1--2,7--9.
--   - `InvariantFractionFieldsEqual`: Equality [k[X]^G]=k(X)^G inside k(X), PDF pp.1--2,9. Both sides are membership predicates in the SAME canonical fraction field: the right side is precisely quotients of invariant regular functions with nonzero denominator. No unspecified field isomorphism is used.
--   - `quotientPoint`: Pullback of the canonical affinized-quotient map on geometric points, PDF p.4, Definition 2.8.
--   - `HasOrbitClosureFibersOver`: The geometricOrbit-closure description of every fiber over W, PDF pp.7--8, Theorem 3.7. The bar denotes the computed Zariski closure, and the chosen point is in the original X_max. W lives in the actual invariant quotient.
--   - `HasGenericOrbitClosureFibers`: Condition (2) of Theorem 3.7, PDF pp.7--8. The open set is required nonempty; fibers are geometricOrbit closures, not asserted to be closed orbits.
--   - `FinitePurelyInseparableInvariantExtension`: The finite purely inseparable extension in Theorem 3.7, PDF pp.8--9, written entirely inside the canonical k(X). Finiteness means that finitely many invariant rational functions span over [k[X]^G], with actual invariant fractions as coefficients. Pure inseparability means each element has a p-power in [k[X]^G], with p=1 in characteristic zero. Thus no arbitrary field inclusion or unrelated algebra structure is supplied as input.
-- source:
--   Observable actions of algebraic groups, arXiv:0902.0137v2, https://arxiv.org/abs/0902.0137v2

import Mathlib

/-!
Coordinate-algebra statements from Renner--Rittatore, Observable actions of
algebraic groups, arXiv:0902.0137v2. Classical affine varieties are represented
contravariantly by reduced finite-type algebras. A k-point is an algebra map
to k, and a regular map is an algebra map in the reverse direction.

All definitions are local to this paper. The group and regularity predicates
below give actual coordinate-algebra models; no theorem conclusion is a field
of these predicates. Deferred geometric results are recorded in HARD.md.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P10

open scoped BigOperators TensorProduct

universe u v w z

/-- Geometric k-points of an affine k-algebra, PDF pp.1--3. -/
abbrev Point (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] :=
  A →ₐ[k] k

/-- Evaluation at a point of an affine product, PDF pp.1--3.
On a pure tensor a tensor b this is x(a)y(b). -/
def tensorEvaluation {k : Type u} {A : Type v} {B : Type w}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (x : Point k A) (y : Point k B) : (A ⊗[k] B) →ₐ[k] k :=
  Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)

/-- The coordinate-ring description of the standing smooth affine algebraic
 group convention, PDF p.1. Over an algebraically closed field, finite type
 plus formal smoothness is smoothness. Multiplication and inversion are
 regular, and their group identities are carried by the Group instance on
 geometric points. Reduced finite-type algebras over this field are determined
 by their k-points, so these are the usual classical algebraic-group data. -/
def IsAffineAlgebraicGroup (k : Type u) (H : Type v)
    [Field k] [IsAlgClosed k] [CommRing H] [Algebra k H]
    [Group (Point k H)] : Prop :=
  Algebra.FiniteType k H ∧ IsReduced H ∧ Algebra.FormallySmooth k H ∧
    (∃ m : H →ₐ[k] (H ⊗[k] H),
      ∀ g h : Point k H, ∀ a : H, (g * h) a = tensorEvaluation g h (m a)) ∧
    (∃ s : H →ₐ[k] H,
      ∀ g : Point k H, ∀ a : H, g⁻¹ a = g (s a))

/-- The standing affine-variety convention in coordinate form, PDF p.1.
Affineness implies separation. Empty varieties (the zero algebra) are allowed;
irreducibility is imposed separately when required. -/
def IsAffineVariety (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] : Prop :=
  Algebra.FiniteType k A ∧ IsReduced A

/-- Regularity of an action on the coordinate algebra, PDF pp.1--3.
The homomorphism rho acts by algebra automorphisms. Its evaluation is regular
in (g,x), witnessed by a map into the actual tensor-product coordinate ring.
The corresponding left action on X is (g,x) mapsto x composed with rho(g^-1),
so the induced coordinate action is precisely the source's g.f(x)=f(g^-1.x).
The homomorphism laws already impose the action identities. -/
def IsRegularAction {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A)) : Prop :=
  ∃ c : A →ₐ[k] (H ⊗[k] A),
    ∀ g : Point k H, ∀ x : Point k A, ∀ a : A,
      x (rho g a) = tensorEvaluation g x (c a)

/-- The induced left action on geometric points, with the source's inverse
pullback convention, PDF p.1. -/
def pointAction {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A))
    (g : Point k H) (x : Point k A) : Point k A :=
  x.comp (rho g⁻¹).toAlgHom

/-- The invariant subalgebra k[X]^G, PDF p.2. -/
def invariantSubalgebra {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A)) : Subalgebra k A where
  carrier := {a | ∀ g, rho g a = a}
  zero_mem' := by intro g; exact map_zero (rho g)
  one_mem' := by intro g; exact map_one (rho g)
  add_mem' := by
    intro a b ha hb g
    rw [map_add, ha g, hb g]
  mul_mem' := by
    intro a b ha hb g
    rw [map_mul, ha g, hb g]
  algebraMap_mem' := by intro r g; exact (rho g).commutes r

/-- Stability of an arbitrary ideal, including nonradical ideals, PDF p.3,
Definition 2.4. -/
def IsStableIdeal {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A)) (I : Ideal A) : Prop :=
  ∀ g : Point k H, ∀ a : A, a ∈ I → rho g a ∈ I

/-- Observability, exactly the nonzero-stable-ideal definition on PDF p.3,
Definition 2.4. The invariant element is itself required to be nonzero. -/
def IsObservable {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A)) : Prop :=
  ∀ I : Ideal A, I ≠ ⊥ → IsStableIdeal rho I →
    ∃ a : A, a ∈ I ∧ a ≠ 0 ∧ a ∈ invariantSubalgebra rho

/-- Constancy on geometric orbits of a morphism X to Spec B, PDF p.4.
The morphism is represented by its pullback f : B to A. -/
def IsConstantOnOrbits {k : Type u} {H : Type v} {A : Type w} {B : Type z}
    [Field k] [CommRing H] [CommRing A] [CommRing B]
    [Algebra k H] [Algebra k A] [Algebra k B] [Group (Point k H)]
    (rho : Point k H →* (A ≃ₐ[k] A)) (f : B →ₐ[k] A) : Prop :=
  ∀ g : Point k H, ∀ x : Point k A,
    (pointAction rho g x).comp f = x.comp f

/-- A regular algebraic character G to G_m, PDF p.11, Definition 3.14.
A unit in k[G] is exactly a regular map from G to G_m; the monoid
homomorphism condition is the character identity. -/
def IsRegularCharacter {k : Type u} {H : Type v}
    [Field k] [CommRing H] [Algebra k H] [Group (Point k H)]
    (chi : Point k H →* kˣ) : Prop :=
  ∃ a : Hˣ, ∀ g : Point k H, g (a : H) = (chi g : k)

/-- Membership of a regular character in E_G(X), PDF p.11,
Definition 3.14: existence of a nonzero semiinvariant of this weight. -/
def HasSemiInvariant {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A))
    (chi : Point k H →* kˣ) : Prop :=
  IsRegularCharacter chi ∧
    ∃ a : A, a ≠ 0 ∧ ∀ g : Point k H, rho g a = (chi g : k) • a

/-- E_G(X) is a group, PDF p.11. On the integral coordinate algebras used
in Corollary 3.16, products of nonzero semiinvariants are nonzero, and the
trivial character is represented by 1. Thus the remaining group condition
is closure under inverses, with no assumption of finite generation. -/
def SemiInvariantCharactersFormGroup {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A)) : Prop :=
  ∀ chi : Point k H →* kˣ, HasSemiInvariant rho chi → HasSemiInvariant rho chi⁻¹

/-- Extension of each coordinate automorphism to the principal open X_f,
PDF p.5. This uses the same invariant denominator, including f=0. -/
def localizedPullback {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A))
    (f : invariantSubalgebra rho) (g : Point k H) :
    Localization.Away (f : A) →ₐ[k] Localization.Away (f : A) := by
  let phi : A →ₐ[k] A := (rho g).toAlgHom
  letI : IsLocalization.Away (phi (f : A)) (Localization.Away (f : A)) := by
    change IsLocalization.Away (rho g (f : A)) (Localization.Away (f : A))
    rw [f.property g]
    infer_instance
  exact IsLocalization.Away.mapₐ
    (Localization.Away (f : A)) (Localization.Away (f : A)) phi (f : A)

/-- The fixed coordinate algebra on X_f, PDF p.5. Its elements are fixed
under the canonical extensions of all the original coordinate automorphisms. -/
def localizedInvariantSubalgebra {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A))
    (f : invariantSubalgebra rho) : Subalgebra k (Localization.Away (f : A)) where
  carrier := {a | ∀ g, localizedPullback rho f g a = a}
  zero_mem' := by intro g; exact map_zero (localizedPullback rho f g)
  one_mem' := by intro g; exact map_one (localizedPullback rho f g)
  add_mem' := by
    intro a b ha hb g
    rw [map_add, ha g, hb g]
  mul_mem' := by
    intro a b ha hb g
    rw [map_mul, ha g, hb g]
  algebraMap_mem' := by intro r g; exact (localizedPullback rho f g).commutes r

/-- The canonical restriction map from (k[X]^G)_f into k[X]_f, PDF p.5.
It is the localization of the actual inclusion of the invariant algebra. -/
def invariantLocalizationMap {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A))
    (f : invariantSubalgebra rho) :
    Localization.Away f →ₐ[k] Localization.Away (f : A) := by
  let phi : invariantSubalgebra rho →ₐ[k] A := (invariantSubalgebra rho).val
  letI : IsLocalization.Away (phi f) (Localization.Away (f : A)) := by
    change IsLocalization.Away (f : A) (Localization.Away (f : A))
    infer_instance
  exact IsLocalization.Away.mapₐ
    (Localization.Away f) (Localization.Away (f : A)) phi f

/-- Common zero locus of coordinate functions on geometric k-points,
PDF p.1. -/
def coordinateZeroLocus {k : Type u} {A : Type v}
    [Field k] [CommRing A] [Algebra k A] (T : Set A) : Set (Point k A) :=
  {x | ∀ a ∈ T, x a = 0}

/-- The actual ideal of all functions vanishing on a subset, PDF p.1.
Its use never replaces a nonradical stable ideal in observability. -/
def coordinateVanishingIdeal {k : Type u} {A : Type v}
    [Field k] [CommRing A] [Algebra k A] (S : Set (Point k A)) : Ideal A where
  carrier := {a | ∀ x ∈ S, x a = 0}
  zero_mem' := by intro x hx; exact map_zero x
  add_mem' := by
    intro a b ha hb x hx
    rw [map_add, ha x hx, hb x hx, add_zero]
  smul_mem' := by
    intro c a ha x hx
    change x (c * a) = 0
    rw [map_mul, ha x hx, mul_zero]

/-- Zariski closure in the classical affine variety, PDF pp.1,7--9,13.
This is V(I(S)), computed from the subset, not an independently supplied set. -/
def classicalClosure {k : Type u} {A : Type v}
    [Field k] [CommRing A] [Algebra k A] (S : Set (Point k A)) : Set (Point k A) :=
  coordinateZeroLocus (coordinateVanishingIdeal S : Set A)

/-- The classical Zariski-open subsets, complements of common zero loci,
PDF p.1. No arbitrary topology is an input. -/
def IsClassicallyOpen {k : Type u} {A : Type v}
    [Field k] [CommRing A] [Algebra k A] (U : Set (Point k A)) : Prop :=
  ∃ T : Set A, Uᶜ = coordinateZeroLocus T

/-- Density in the actual classical Zariski topology, PDF p.11. -/
def IsClassicallyDense {k : Type u} {A : Type v}
    [Field k] [CommRing A] [Algebra k A] (U : Set (Point k A)) : Prop :=
  classicalClosure U = Set.univ

/-- The principal open X_f, including the empty open X_0, PDF p.1. -/
def principalOpen {k : Type u} {A : Type v}
    [Field k] [CommRing A] [Algebra k A] (f : A) : Set (Point k A) :=
  {x | x f ≠ 0}

/-- The geometric geometricOrbit of a point, computed from the action, PDF pp.1--2. -/
def geometricOrbit {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A))
    (x : Point k A) : Set (Point k A) :=
  Set.range (fun g : Point k H => pointAction rho g x)

/-- Closedness of the whole geometric geometricOrbit, PDF pp.1--2,7,9. -/
def IsClosedOrbit {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A)) (x : Point k A) : Prop :=
  classicalClosure (geometricOrbit rho x) = geometricOrbit rho x

/-- Dimension of an geometricOrbit, PDF p.7, Definition 3.6.
An algebraic geometricOrbit is locally closed, so its dimension is the Krull dimension
of its affine closure. The ring here is the actual coordinate ring of that
closure. WithBot preserves dimension -1 for the empty closed set and avoids
truncated natural subtraction; no finite-value coercion is used. -/
def geometricOrbitDimension {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A))
    (x : Point k A) : WithBot ℕ∞ :=
  ringKrullDim (A ⧸ coordinateVanishingIdeal (geometricOrbit rho x))

/-- X_max is computed by comparison with every geometricOrbit in X, PDF p.7,
Definition 3.6. This is not a chosen open subset. -/
def maximalOrbitLocus {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A)) : Set (Point k A) :=
  {x | ∀ y : Point k A, geometricOrbitDimension rho y ≤ geometricOrbitDimension rho x}

/-- Omega(X), the locus of closed orbits of maximal dimension, PDF p.7,
Definition 3.6. -/
def omegaLocus {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A)) : Set (Point k A) :=
  {x | x ∈ maximalOrbitLocus rho ∧ IsClosedOrbit rho x}

/-- Containment of a nonempty Zariski-open subset, PDF p.9, Theorem 3.10. -/
def ContainsNonemptyOpen {k : Type u} {A : Type v}
    [Field k] [CommRing A] [Algebra k A] (S : Set (Point k A)) : Prop :=
  ∃ U : Set (Point k A), IsClassicallyOpen U ∧ U.Nonempty ∧ U ⊆ S

/-- Invariance of a rational function in the canonical fraction field,
PDF pp.1--2,9. A nonzero denominator is explicit. For each g, the last
identity is exactly rho(g)(a/b)=a/b after cross multiplication in a domain;
it is independent of the chosen representation and uses the source's
induced coordinate action. No rational invariance is assumed of a or b. -/
def IsInvariantRational {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [IsDomain A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (rho : Point k H →* (A ≃ₐ[k] A)) (q : FractionRing A) : Prop :=
  ∃ a b : A, b ≠ 0 ∧
    q = algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b ∧
    ∀ g : Point k H, rho g a * b = a * rho g b

/-- A rational function belongs to the canonical copy of [k[X]^G] in k(X)
exactly when it is a fraction of invariant regular functions, PDF pp.1--2,7--9. -/
def IsInvariantRegularFraction {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [IsDomain A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (rho : Point k H →* (A ≃ₐ[k] A)) (q : FractionRing A) : Prop :=
  ∃ a b : invariantSubalgebra rho, (b : A) ≠ 0 ∧
    q = algebraMap A (FractionRing A) (a : A) /
      algebraMap A (FractionRing A) (b : A)

/-- Equality [k[X]^G]=k(X)^G inside k(X), PDF pp.1--2,9.
Both sides are membership predicates in the SAME canonical fraction field:
the right side is precisely quotients of invariant regular functions with
nonzero denominator. No unspecified field isomorphism is used. -/
def InvariantFractionFieldsEqual {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [IsDomain A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (rho : Point k H →* (A ≃ₐ[k] A)) : Prop :=
  ∀ q : FractionRing A, IsInvariantRational rho q ↔ IsInvariantRegularFraction rho q

/-- Pullback of the canonical affinized-quotient map on geometric points,
PDF p.4, Definition 2.8. -/
def quotientPoint {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A))
    (x : Point k A) : Point k (invariantSubalgebra rho) :=
  x.comp (invariantSubalgebra rho).val

/-- The geometricOrbit-closure description of every fiber over W, PDF pp.7--8,
Theorem 3.7. The bar denotes the computed Zariski closure, and the chosen
point is in the original X_max. W lives in the actual invariant quotient. -/
def HasOrbitClosureFibersOver {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A))
    (W : Set (Point k (invariantSubalgebra rho))) : Prop :=
  ∀ z ∈ W, ∃ y : Point k A, y ∈ maximalOrbitLocus rho ∧
    {x : Point k A | quotientPoint rho x = z} = classicalClosure (geometricOrbit rho y)

/-- Condition (2) of Theorem 3.7, PDF pp.7--8. The open set is required
nonempty; fibers are geometricOrbit closures, not asserted to be closed orbits. -/
def HasGenericOrbitClosureFibers {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [Algebra k H] [Algebra k A]
    [Group (Point k H)] (rho : Point k H →* (A ≃ₐ[k] A)) : Prop :=
  ∃ W : Set (Point k (invariantSubalgebra rho)),
    IsClassicallyOpen W ∧ W.Nonempty ∧ HasOrbitClosureFibersOver rho W

/-- The finite purely inseparable extension in Theorem 3.7, PDF pp.8--9,
written entirely inside the canonical k(X). Finiteness means that finitely
many invariant rational functions span over [k[X]^G], with actual invariant
fractions as coefficients. Pure inseparability means each element has a
p-power in [k[X]^G], with p=1 in characteristic zero. Thus no arbitrary
field inclusion or unrelated algebra structure is supplied as input. -/
def FinitePurelyInseparableInvariantExtension {k : Type u} {H : Type v} {A : Type w}
    [Field k] [CommRing H] [CommRing A] [IsDomain A]
    [Algebra k H] [Algebra k A] [Group (Point k H)]
    (rho : Point k H →* (A ≃ₐ[k] A)) : Prop :=
  (∃ n : ℕ, ∃ v : Fin n → FractionRing A,
    (∀ i, IsInvariantRational rho (v i)) ∧
    ∀ q : FractionRing A, IsInvariantRational rho q →
      ∃ c : Fin n → FractionRing A,
        (∀ i, IsInvariantRegularFraction rho (c i)) ∧ q = ∑ i, c i * v i) ∧
  (∀ q : FractionRing A, IsInvariantRational rho q →
    ∃ n : ℕ, IsInvariantRegularFraction rho
      (q ^ ((if ringChar k = 0 then 1 else ringChar k) ^ n)))

section Sanity

variable {k : Type u} {H : Type v} {A : Type w} {B : Type z}
variable [Field k] [CommRing H] [CommRing A] [CommRing B]
variable [Algebra k H] [Algebra k A] [Algebra k B] [Group (Point k H)]

example (x : Point k A) (y : Point k B) (a : A) (b : B) :
    tensorEvaluation x y (a ⊗ₜ[k] b) = x a * y b := rfl

example (rho : Point k H →* (A ≃ₐ[k] A)) :
    (1 : A) ∈ invariantSubalgebra rho := by
  intro g
  exact map_one (rho g)

example (rho : Point k H →* (A ≃ₐ[k] A)) (x : Point k A) :
    pointAction rho 1 x = x := by
  simp only [pointAction, inv_one, map_one] <;> rfl

example (rho : Point k H →* (A ≃ₐ[k] A)) : IsStableIdeal rho (⊤ : Ideal A) := by
  intro g a ha
  trivial

example (rho : Point k H →* (A ≃ₐ[k] A)) [Nontrivial A] :
    HasSemiInvariant rho (1 : Point k H →* kˣ) := by
  refine ⟨⟨1, ?_⟩, 1, one_ne_zero, ?_⟩
  · intro g
    simp
  · intro g
    simp

example (rho : Point k H →* (A ≃ₐ[k] A))
    (f : invariantSubalgebra rho) :
    (1 : Localization.Away (f : A)) ∈ localizedInvariantSubalgebra rho f := by
  intro g
  exact map_one (localizedPullback rho f g)

example : coordinateZeroLocus (k := k) (∅ : Set A) = Set.univ := by
  ext x
  simp [coordinateZeroLocus]

example : principalOpen (k := k) (0 : A) = ∅ := by
  ext x
  simp [principalOpen]

example (rho : Point k H →* (A ≃ₐ[k] A)) [IsDomain A] :
    IsInvariantRational rho (0 : FractionRing A) := by
  refine ⟨0, 1, one_ne_zero, ?_, ?_⟩
  · simp
  · intro g
    simp

end Sanity

end QAlgorithms.Papers.Independent.Support21.P10


