-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P79
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P79
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:18:28.649485+00:00
-- url     : https://prove2.me/theorems/02b76cfd-645d-4fc0-a58a-5748d78b3414
-- title:
--   Definitions for Local structure of algebraic monoids
-- statement:
--   The objects the formalized statements of *Local structure of algebraic monoids* (arXiv:0709.1255) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `KScheme`: Schemes over the ground field; all arrows in this category are k-morphisms.
--   - `IsVariety`: The paper's convention for a variety, PDF p. 3; irreducibility is separate.
--   - `constantMap`: The constant morphism with value the k-rational point e.
--   - `rightMultiplication`: Right multiplication r_e(x)=xe, (1.1.2), PDF p. 4.
--   - `leftMultiplication`: Left multiplication ell_e(x)=ex, (1.1.1), PDF p. 4.
--   - `reducedOver`: Reduction of a k-scheme using its actual nilradical ideal sheaf.
--   - `reductionInclusion`: The canonical reduction inclusion.
--   - `stabilizerEquations`: Scheme-theoretic equations xe=e, ex=e, or (xe,ex)=(e,e). The three cases encode the left, right, and two-sided stabilizers, respectively.
--   - `stabilizerEquationsInclusion`: Canonical inclusion of the scheme-theoretic stabilizer into M.
--   - `stabilizer`: The reduced stabilizer varieties of (1.1.4), (1.1.6), (1.1.8), PDF pp. 4-5. Side 0 means M_e^ell, side 1 means M_e^r, and side 2 means M_e.
--   - `stabilizerInclusion`: The canonical closed inclusion of the reduced stabilizer in M.
--   - `unitPairs`: The scheme of inverse pairs (x,y), defined by xy=yx=1 on all test schemes. Projection to x represents the unit functor, rather than an arbitrary abstract group.
--   - `unitsInclusion`: The canonical map from inverse pairs to their invertible first coordinate.
--   - `groupStabilizer`: The group stabilizer G intersected with M_e^ell, M_e^r or M_e, computed inside the inverse-pair scheme by the same stabilizer equations.
--   - `groupStabilizerInclusion`: Canonical map from a group stabilizer to M.
--   - `IsIdempotentPoint`: On test schemes, a point of M is idempotent for the actual regular product.
--   - `affineSpace`: A^n over k, including A^0=Spec k up to the standard polynomial isomorphism.
--   - `IsSmoothPoint`: Smoothness at a k-rational point, expressed on a Zariski open neighbourhood.
--   - `projectiveSpace`: Projective n-space as Proj of the ordinary total-degree graded polynomial ring.
--   - `degreeZeroConstants`: Constants land in the actual degree-zero ring of homogeneous polynomials.
--   - `projectiveSpaceBase`: The structure morphism P^n_k to Spec k.
--   - `IsQuasiProjective`: Quasi-projectivity means a locally closed scheme immersion into some P^n_k, compatible with the fixed k-structure; it is not assumed in IsVariety.
--   - `MonoidSchemePoint`: Closed points of a variety over the algebraically closed ground field are its k-rational sections; their multiplication is induced by the regular product.
--   - `stabilizerPoints`: The closed-point view of the reduced stabilizers already defined above.
--   - `groupStabilizerPoints`: Closed-point group stabilizers are computed by invertibility in M.
--   - `groupCentralizerPoints`: The left (side 0), right (side 1), or full (side 2) centralizer in the actual unit group, in the equations (1.3.1), (1.3.7), (1.2.1).
--   - `rightIdealPoints`: The right ideal Me, not the subscript stabilizer M_e.
--   - `leftIdealPoints`: The left ideal eM.
--   - `localOpenPoints`: The point locus of M_0^r or M_0^ell, from (2.1.1) and (2.1.4), or their intersection M_0. Every orbit/product is computed from M and e.
--   - `IsMinimalIdempotent`: Minimality in PDF p. 14: e is the only idempotent in eMe. Idempotence of e is supplied separately, as in the source.
--   - `kernelPoints`: The kernel of a monoid is its least nonempty two-sided ideal. Here it is computed as membership in every nonempty two-sided ideal, not as a free parameter. For an irreducible algebraic monoid this is the closed two-sided unit-group orbit.
-- source:
--   Local structure of algebraic monoids, arXiv:0709.1255v2, https://arxiv.org/abs/0709.1255v2

import Mathlib

/-!
Local definitions and statement drafts for Michel Brion, *Local structure of algebraic
monoids*, arXiv:0709.1255v2. Varieties have precisely the convention on PDF p. 3:
separated reduced schemes of finite type over an algebraically closed field of
characteristic zero. No quasi-projectivity, normality or affineness is built into
that convention. Deferred nodes are listed in the accompanying HARD.md.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
open scoped CategoryTheory.MonObj Pointwise

universe u

namespace QAlgorithms.Papers.Independent.Intakethird100.P79

variable (k : Type u) [Field k]

/-- Schemes over the ground field; all arrows in this category are k-morphisms. -/
abbrev KScheme := Over (Spec (CommRingCat.of k))

/-- The paper's convention for a variety, PDF p. 3; irreducibility is separate. -/
class IsVariety (X : KScheme k) : Prop where
  locally_finite_type : LocallyOfFiniteType X.hom
  quasi_compact : QuasiCompact X.hom
  separated : IsSeparated X.hom
  reduced : IsReduced X.left

attribute [instance] IsVariety.locally_finite_type IsVariety.quasi_compact
  IsVariety.separated IsVariety.reduced

variable {k}

/-- The constant morphism with value the k-rational point e. -/
def constantMap {X Y : KScheme k} (e : 𝟙_ (KScheme k) ⟶ Y) : X ⟶ Y :=
  toUnit X ≫ e

/-- Right multiplication r_e(x)=xe, (1.1.2), PDF p. 4. -/
def rightMultiplication (M : KScheme k) [MonObj M]
    (e : 𝟙_ (KScheme k) ⟶ M) : M ⟶ M :=
  lift (𝟙 M) (constantMap e) ≫ μ[M]

/-- Left multiplication ell_e(x)=ex, (1.1.1), PDF p. 4. -/
def leftMultiplication (M : KScheme k) [MonObj M]
    (e : 𝟙_ (KScheme k) ⟶ M) : M ⟶ M :=
  lift (constantMap e) (𝟙 M) ≫ μ[M]

/-- Reduction of a k-scheme using its actual nilradical ideal sheaf. -/
def reducedOver (X : KScheme k) : KScheme k :=
  Over.mk (X.left.nilradical.subschemeι ≫ X.hom)

/-- The canonical reduction inclusion. -/
def reductionInclusion (X : KScheme k) : reducedOver X ⟶ X :=
  Over.homMk X.left.nilradical.subschemeι

/-- Scheme-theoretic equations xe=e, ex=e, or (xe,ex)=(e,e).
The three cases encode the left, right, and two-sided stabilizers, respectively. -/
def stabilizerEquations (M : KScheme k) [MonObj M]
    (e : 𝟙_ (KScheme k) ⟶ M) (side : Fin 3) : KScheme k :=
  if side = 0 then equalizer (rightMultiplication M e) (constantMap e)
  else if side = 1 then equalizer (leftMultiplication M e) (constantMap e)
  else equalizer
    (lift (rightMultiplication M e) (leftMultiplication M e))
    (constantMap (lift e e))

/-- Canonical inclusion of the scheme-theoretic stabilizer into M. -/
def stabilizerEquationsInclusion (M : KScheme k) [MonObj M]
    (e : 𝟙_ (KScheme k) ⟶ M) (side : Fin 3) : stabilizerEquations M e side ⟶ M := by
  classical
  unfold stabilizerEquations
  split
  · exact equalizer.ι _ _
  · split
    · exact equalizer.ι _ _
    · exact equalizer.ι _ _

/-- The reduced stabilizer varieties of (1.1.4), (1.1.6), (1.1.8), PDF pp. 4-5.
Side 0 means M_e^ell, side 1 means M_e^r, and side 2 means M_e. -/
def stabilizer (M : KScheme k) [MonObj M]
    (e : 𝟙_ (KScheme k) ⟶ M) (side : Fin 3) : KScheme k :=
  reducedOver (stabilizerEquations M e side)

/-- The canonical closed inclusion of the reduced stabilizer in M. -/
def stabilizerInclusion (M : KScheme k) [MonObj M]
    (e : 𝟙_ (KScheme k) ⟶ M) (side : Fin 3) : stabilizer M e side ⟶ M :=
  reductionInclusion _ ≫ stabilizerEquationsInclusion M e side

/-- The scheme of inverse pairs (x,y), defined by xy=yx=1 on all test schemes.
Projection to x represents the unit functor, rather than an arbitrary abstract group. -/
def unitPairs (M : KScheme k) [MonObj M] : KScheme k :=
  equalizer
    (lift μ[M] (lift (snd M M) (fst M M) ≫ μ[M]))
    (constantMap (lift η[M] η[M]))

/-- The canonical map from inverse pairs to their invertible first coordinate. -/
def unitsInclusion (M : KScheme k) [MonObj M] : unitPairs M ⟶ M :=
  equalizer.ι _ _ ≫ fst M M

/-- The group stabilizer G intersected with M_e^ell, M_e^r or M_e,
computed inside the inverse-pair scheme by the same stabilizer equations. -/
def groupStabilizer (M : KScheme k) [MonObj M]
    (e : 𝟙_ (KScheme k) ⟶ M) (side : Fin 3) : KScheme k :=
  if side = 0 then equalizer
    (unitsInclusion M ≫ rightMultiplication M e) (constantMap e)
  else if side = 1 then equalizer
    (unitsInclusion M ≫ leftMultiplication M e) (constantMap e)
  else equalizer
    (unitsInclusion M ≫ lift (rightMultiplication M e) (leftMultiplication M e))
    (constantMap (lift e e))

/-- Canonical map from a group stabilizer to M. -/
def groupStabilizerInclusion (M : KScheme k) [MonObj M]
    (e : 𝟙_ (KScheme k) ⟶ M) (side : Fin 3) : groupStabilizer M e side ⟶ M := by
  classical
  unfold groupStabilizer
  split
  · exact equalizer.ι _ _ ≫ unitsInclusion M
  · split
    · exact equalizer.ι _ _ ≫ unitsInclusion M
    · exact equalizer.ι _ _ ≫ unitsInclusion M

/-- On test schemes, a point of M is idempotent for the actual regular product. -/
def IsIdempotentPoint (M : KScheme k) [MonObj M]
    (e : 𝟙_ (KScheme k) ⟶ M) : Prop :=
  lift e e ≫ μ[M] = e

/-- Sanity check: the identity section is idempotent. -/
example (M : KScheme k) [MonObj M] : IsIdempotentPoint M η[M] := by
  change η[M] * η[M] = η[M]
  have h : (η[M] : 𝟙_ (KScheme k) ⟶ M) = 1 := by
    change η[M] = toUnit (𝟙_ (KScheme k)) ≫ η[M]
    rw [show toUnit (𝟙_ (KScheme k)) = 𝟙 _ from toUnit_unique _ _,
      Category.id_comp]
  rw [h, _root_.one_mul]

/-- Sanity check: left stabilizers impose xe=e, with no reversed convention. -/
example (M : KScheme k) [MonObj M] (e : 𝟙_ (KScheme k) ⟶ M) :
    stabilizerEquations M e 0 =
      equalizer (rightMultiplication M e) (constantMap e) := by
  simp [stabilizerEquations]

/-- Sanity check: right stabilizers impose ex=e. -/
example (M : KScheme k) [MonObj M] (e : 𝟙_ (KScheme k) ⟶ M) :
    stabilizerEquations M e 1 =
      equalizer (leftMultiplication M e) (constantMap e) := by
  simp [stabilizerEquations]

/-- A^n over k, including A^0=Spec k up to the standard polynomial isomorphism. -/
def affineSpace (n : ℕ) : KScheme k :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)))

/-- Smoothness at a k-rational point, expressed on a Zariski open neighbourhood. -/
def IsSmoothPoint (X : KScheme k) (e : 𝟙_ (KScheme k) ⟶ X) : Prop :=
  ∃ U : X.left.Opens,
    e.left (IsLocalRing.closedPoint k) ∈ U ∧ Smooth (U.ι ≫ X.hom)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective n-space as Proj of the ordinary total-degree graded polynomial ring. -/
def projectiveSpace (n : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)

/-- Constants land in the actual degree-zero ring of homogeneous polynomials. -/
def degreeZeroConstants (n : ℕ) :
    k →+* (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0) where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C _ a⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)

/-- The structure morphism P^n_k to Spec k. -/
def projectiveSpaceBase (n : ℕ) : projectiveSpace (k := k) n ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) ≫
    Spec.map (CommRingCat.ofHom (degreeZeroConstants (k := k) n))

/-- Quasi-projectivity means a locally closed scheme immersion into some P^n_k,
compatible with the fixed k-structure; it is not assumed in IsVariety. -/
def IsQuasiProjective (X : KScheme k) : Prop :=
  ∃ n : ℕ, ∃ i : X.left ⟶ projectiveSpace (k := k) n,
    IsImmersion i ∧ i ≫ projectiveSpaceBase n = X.hom

/-- Sanity check: quasi-projectivity retains the prescribed ground-field morphism. -/
example (X : KScheme k) (h : IsQuasiProjective X) :
    ∃ n : ℕ, ∃ i : X.left ⟶ projectiveSpace (k := k) n,
      IsImmersion i ∧ i ≫ projectiveSpaceBase n = X.hom := h

/-- Closed points of a variety over the algebraically closed ground field are
its k-rational sections; their multiplication is induced by the regular product. -/
abbrev MonoidSchemePoint (M : KScheme k) := 𝟙_ (KScheme k) ⟶ M

/-- The closed-point view of the reduced stabilizers already defined above. -/
def stabilizerPoints (M : KScheme k) [MonObj M] (e : MonoidSchemePoint M)
    (side : Fin 3) : Set (MonoidSchemePoint M) :=
  if side = 0 then {x | x * e = e}
  else if side = 1 then {x | e * x = e}
  else {x | x * e = e ∧ e * x = e}

/-- Closed-point group stabilizers are computed by invertibility in M. -/
def groupStabilizerPoints (M : KScheme k) [MonObj M] (e : MonoidSchemePoint M)
    (side : Fin 3) : Set (MonoidSchemePoint M) :=
  {x | IsUnit x} ∩ stabilizerPoints M e side

/-- The left (side 0), right (side 1), or full (side 2) centralizer in the
actual unit group, in the equations (1.3.1), (1.3.7), (1.2.1). -/
def groupCentralizerPoints (M : KScheme k) [MonObj M] (e : MonoidSchemePoint M)
    (side : Fin 3) : Set (MonoidSchemePoint M) :=
  {x | IsUnit x} ∩
    (if side = 0 then {x | x * e = e * x * e}
     else if side = 1 then {x | e * x = e * x * e}
     else {x | x * e = e * x})

/-- The right ideal Me, not the subscript stabilizer M_e. -/
def rightIdealPoints (M : KScheme k) [MonObj M] (e : MonoidSchemePoint M) : Set (MonoidSchemePoint M) :=
  Set.range (fun x : MonoidSchemePoint M => x * e)

/-- The left ideal eM. -/
def leftIdealPoints (M : KScheme k) [MonObj M] (e : MonoidSchemePoint M) : Set (MonoidSchemePoint M) :=
  Set.range (fun x : MonoidSchemePoint M => e * x)

/-- The point locus of M_0^r or M_0^ell, from (2.1.1) and (2.1.4),
or their intersection M_0. Every orbit/product is computed from M and e. -/
def localOpenPoints (M : KScheme k) [MonObj M] (e : MonoidSchemePoint M)
    (side : Fin 3) : Set (MonoidSchemePoint M) :=
  if side = 0 then {x | x * e ∈ groupCentralizerPoints M e 1 * {e}}
  else if side = 1 then {x | e * x ∈ {e} * groupCentralizerPoints M e 0}
  else {x | x * e ∈ groupCentralizerPoints M e 1 * {e} ∧
            e * x ∈ {e} * groupCentralizerPoints M e 0}

/-- Minimality in PDF p. 14: e is the only idempotent in eMe.
Idempotence of e is supplied separately, as in the source. -/
def IsMinimalIdempotent (M : KScheme k) [MonObj M] (e : MonoidSchemePoint M) : Prop :=
  ∀ x : MonoidSchemePoint M, e * x * e = x → x * x = x → x = e

/-- The kernel of a monoid is its least nonempty two-sided ideal. Here it is
computed as membership in every nonempty two-sided ideal, not as a free parameter.
For an irreducible algebraic monoid this is the closed two-sided unit-group orbit. -/
def kernelPoints (M : KScheme k) [MonObj M] : Set (MonoidSchemePoint M) :=
  {x | ∀ I : Set (MonoidSchemePoint M), I.Nonempty →
    (∀ a ∈ I, ∀ b c : MonoidSchemePoint M, b * a * c ∈ I) → x ∈ I}

/-- Sanity check at e=1: the right ideal M1 is the whole point set. -/
example (M : KScheme k) [MonObj M] :
    rightIdealPoints M (1 : MonoidSchemePoint M) = Set.univ := by
  ext x
  simp [rightIdealPoints]

/-- Sanity check at e=1: the two-sided stabilizer has just its identity point. -/
example (M : KScheme k) [MonObj M] :
    stabilizerPoints M (1 : MonoidSchemePoint M) 2 = {1} := by
  ext x
  simp [stabilizerPoints]

end QAlgorithms.Papers.Independent.Intakethird100.P79


