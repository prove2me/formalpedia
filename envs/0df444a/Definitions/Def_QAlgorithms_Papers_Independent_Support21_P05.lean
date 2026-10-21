-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P05
-- name    : QAlgorithms_Papers_Independent_Support21_P05
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:31:05.564988+00:00
-- url     : https://prove2.me/theorems/8de463e5-335f-4e6b-8fcc-39dddeba774d
-- title:
--   Definitions for Exceptional Lie Algebras, SU(3) and Jordan Pairs Part 2: Zorn-type Representations
-- statement:
--   The objects the formalized statements of *Exceptional Lie Algebras, SU(3) and Jordan Pairs Part 2: Zorn-type Representations* (arXiv:1403.5120) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Vec3`
--   - `Mat3`
--   - `shift3`: Cyclic successor, with the paper's indices 1,2,3 encoded by 0,1,2. PDF p. 9.
--   - `outer3`: Column times row, using the ordinary contraction convention. PDF p. 10.
--   - `matrixComm`: Matrix commutator, used only for associative entry algebras.
--   - `Sl3`: Traceless complex 3 by 3 matrices (the complex a2). PDF p. 11.
--   - `G2Raw`
--   - `G2Coordinates`
--   - `g2Value`: Forget the trace proof, retaining exactly the three slots in (4.4).
--   - `circle3`: The circle product (4.3), not ordinary block matrix multiplication. PDF p. 10.
--   - `g2Bracket`: The closed raw commutator (4.5). PDF p. 11.
--   - `Octonions`: Zorn octonions: the two diagonal scalars, then the positive and negative vectors. PDF p. 9.
--   - `octonionMul`: The actual octonion product (3.3), whose diagonal contraction has a MINUS sign. PDF p. 9.
--   - `octonionTrace`: Octonion trace, not any Hermitian scalar-field trace. PDF pp. 9,13.
--   - `TracelessOctonions`
--   - `octonionAction`: The action (4.10); every row-column contraction here is the ordinary positive dot. PDF p. 12.
--   - `octonionInner`: Normalized inner derivation D(c,d)z = [[c,d],z]/3 - (c,d,z). PDF p. 9.
--   - `innerCoordinates`: Explicit coefficients (4.9). PDF p. 12.
--   - `vectorUnit`: Standard vector and matrix units, with Fin 3 indexing. PDF p. 11.
--   - `epsilonPlus`: Nilpotent epsilon-plus coordinates in (3.2).
--   - `epsilonMinus`: Nilpotent epsilon-minus coordinates in (3.2).
--   - `SplitComposition`: The complexified two-dimensional composition algebra in its idempotent basis. Its scalar embedding is r |-> (r,r), its u1 is (-i,i), and rho+ and rho- are (1,0),(0,1). Conjugation swaps the factors and fixes the base complex field. PDF pp. 17–20.
--   - `splitConjugation`: Composition conjugation, NOT base-complex conjugation.
--   - `splitScalarPart`: The scalar part in the split algebra.
--   - `QuaternionComposition`: Complexified quaternions as M2(C), with symplectic conjugation, not conjugate transpose.
--   - `quaternionConjugation`: Quaternion composition conjugation q |-> tr(q)I-q; it fixes every base scalar. PDF pp. 20–21.
--   - `quaternionScalarPart`: Scalar part of a complexified quaternion, half its 2 by 2 matrix trace.
--   - `daggerMap`: Composition-conjugate transpose, complex-linear. PDF §§2,6–8.
--   - `hermitianSpace`: H3(A) as an actual subspace of matrices with composition-conjugate symmetry.
--   - `scalarTrace`: Scalar trace, taking scalar parts of diagonal composition entries. PDF pp. 7–8,21.
--   - `jordanProduct`: Jordan multiplication (xy+yx)/2, using associative matrix products here.
--   - `jordanScalarTracePair`: t(x,y)=t(x dot y); for quaternion entries it must not be replaced by an A-valued trace. This composition-algebra scalar pairing differs from the accepted Bool-matrix and trace-class pairings named tracePair. PDF pp. 7–8,13,21.
--   - `sharpProduct`: The unhalved polarization x#y from (2.6), expanded as (5.4). PDF pp. 8,13.
--   - `jordanCross`: Vector cross product with sharp in place of scalar multiplication, (5.4).
--   - `columnAction`: External a2 action on a column of Jordan matrices.
--   - `rowAction`: External contragredient row contraction; its minus sign is in the bracket.
--   - `diamondExternal`: The external traceless component of the diamond product (5.4).
--   - `diamondCentral`: The central component of the diamond product (5.4), before taking a commutator.
--   - `AssociativeRaw`
--   - `associativeBracket`: Raw (5.3)/(6.3) bracket, including both diamond components and both cross terms. The bottom-right block is determined by minus the dagger of the central slot.
--   - `AssociativeCoordinates`: Constrained coordinate space; T is the precise central trace constraint and J=H3(A). Both opposite spaces are complex-linear copies, with the distinct actions above.
--   - `associativeValue`: Retain all entries while forgetting only their subspace membership proofs.
--   - `rawJacobi`: The raw cyclic Jacobi expression. It does not assume closure or a LieRing instance.
--   - `F4Coordinates`: F4 coordinates: two complex sl3 factors and opposite triples of symmetric complex matrices.
--   - `E6Central`: E6 central matrices have zero full split-composition trace, i.e. two complex trace constraints.
--   - `E6Coordinates`
--   - `E7Central`: E7 removes only the scalar quaternionic trace: 36-1=35 central parameters, not 36-4.
--   - `E7Coordinates`
--   - `splitJoin`: Join the two idempotent coefficient matrices, not a base-field conjugation. PDF p. 19.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs Part 2: Zorn-type Representations, arXiv:1403.5120v2, https://arxiv.org/abs/1403.5120v2

import Mathlib
import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

/-!
Concrete coordinates for Marrani–Truini, arXiv:1403.5120v2.
All scalars are complex. Composition conjugation fixes these scalars.
No Lie instance is installed on a raw Zorn space: bracket identities below
are assertions about the explicit operations, not consequences of instances.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P05

-- Reuse the accepted complex matrix unit; its dimension is inferred as 3.
open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

abbrev Vec3 := Fin 3 → ℂ

abbrev Mat3 (A : Type*) := Matrix (Fin 3) (Fin 3) A

/-- Cyclic successor, with the paper's indices 1,2,3 encoded by 0,1,2. PDF p. 9. -/
def shift3 (i : Fin 3) : Fin 3 := ⟨(i.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

/-- Column times row, using the ordinary contraction convention. PDF p. 10. -/
def outer3 (v w : Vec3) : Mat3 ℂ := fun i j => v i * w j

/-- Matrix commutator, used only for associative entry algebras. -/
def matrixComm {A : Type*} [Ring A] (x y : Mat3 A) : Mat3 A := x * y - y * x

/-- Traceless complex 3 by 3 matrices (the complex a2). PDF p. 11. -/
abbrev Sl3 := LinearMap.ker (Matrix.traceLinearMap (Fin 3) ℂ ℂ)

abbrev G2Raw := Mat3 ℂ × Vec3 × Vec3

abbrev G2Coordinates := Sl3 × Vec3 × Vec3

/-- Forget the trace proof, retaining exactly the three slots in (4.4). -/
def g2Value (x : G2Coordinates) : G2Raw := (x.1.val, x.2.1, x.2.2)

/-- The circle product (4.3), not ordinary block matrix multiplication. PDF p. 10. -/
def circle3 (v w : Vec3) : Mat3 ℂ := dotProduct v w • (1 : Mat3 ℂ) - (3 : ℂ) • outer3 v w

/-- The closed raw commutator (4.5). PDF p. 11. -/
def g2Bracket (x y : G2Raw) : G2Raw :=
  (matrixComm x.1 y.1 + circle3 x.2.1 y.2.2 - circle3 y.2.1 x.2.2,
   (fun i => (∑ j, x.1 i j * y.2.1 j) - (∑ j, y.1 i j * x.2.1 j) +
     2 * crossProduct x.2.2 y.2.2 i),
   (fun i => (∑ j, x.2.2 j * y.1 j i) - (∑ j, y.2.2 j * x.1 j i) +
     2 * crossProduct x.2.1 y.2.1 i))

/-- Zorn octonions: the two diagonal scalars, then the positive and negative vectors. PDF p. 9. -/
abbrev Octonions := ℂ × ℂ × Vec3 × Vec3

/-- The actual octonion product (3.3), whose diagonal contraction has a MINUS sign. PDF p. 9. -/
def octonionMul (x y : Octonions) : Octonions :=
  (x.1 * y.1 - dotProduct x.2.2.1 y.2.2.2,
   x.2.1 * y.2.1 - dotProduct x.2.2.2 y.2.2.1,
   (fun i => x.1 * y.2.2.1 i + y.2.1 * x.2.2.1 i + crossProduct x.2.2.2 y.2.2.2 i),
   (fun i => x.2.1 * y.2.2.2 i + y.1 * x.2.2.2 i + crossProduct x.2.2.1 y.2.2.1 i))

/-- Octonion trace, not any Hermitian scalar-field trace. PDF pp. 9,13. -/
def octonionTrace : Octonions →ₗ[ℂ] ℂ where
  toFun x := x.1 + x.2.1
  map_add' x y := by change (x.1 + y.1) + (x.2.1 + y.2.1) = _; ring
  map_smul' r x := by change r * x.1 + r * x.2.1 = r * (x.1 + x.2.1); ring

abbrev TracelessOctonions := LinearMap.ker octonionTrace

/-- The action (4.10); every row-column contraction here is the ordinary positive dot. PDF p. 12. -/
def octonionAction (a : G2Raw) (v : Octonions) : Octonions :=
  (-dotProduct v.2.2.2 a.2.1 + dotProduct a.2.2 v.2.2.1,
   dotProduct v.2.2.2 a.2.1 - dotProduct a.2.2 v.2.2.1,
   (fun i => (∑ j, a.1 i j * v.2.2.1 j) + (v.2.1 - v.1) * a.2.1 i -
     crossProduct a.2.2 v.2.2.2 i),
   (fun i => -(∑ j, v.2.2.2 j * a.1 j i) - (v.2.1 - v.1) * a.2.2 i -
     crossProduct a.2.1 v.2.2.1 i))

/-- Normalized inner derivation D(c,d)z = [[c,d],z]/3 - (c,d,z). PDF p. 9. -/
def octonionInner (c d z : Octonions) : Octonions :=
  (1 / 3 : ℂ) • (octonionMul (octonionMul c d - octonionMul d c) z -
    octonionMul z (octonionMul c d - octonionMul d c)) -
  (octonionMul (octonionMul c d) z - octonionMul c (octonionMul d z))

/-- Explicit coefficients (4.9). PDF p. 12. -/
def innerCoordinates (c d : Octonions) : G2Raw :=
  (outer3 d.2.2.1 c.2.2.2 - outer3 c.2.2.1 d.2.2.2 -
     ((dotProduct c.2.2.2 d.2.2.1 - dotProduct c.2.2.1 d.2.2.2) / 3) • (1 : Mat3 ℂ),
   (fun i => ((c.1 - c.2.1) * d.2.2.1 i - (d.1 - d.2.1) * c.2.2.1 i -
     crossProduct c.2.2.2 d.2.2.2 i) / 3),
   (fun i => ((c.2.1 - c.1) * d.2.2.2 i - (d.2.1 - d.1) * c.2.2.2 i -
     crossProduct c.2.2.1 d.2.2.1 i) / 3))

/-- Standard vector and matrix units, with Fin 3 indexing. PDF p. 11. -/
def vectorUnit (i : Fin 3) : Vec3 := fun j => if i = j then 1 else 0

/-- Nilpotent epsilon-plus coordinates in (3.2). -/
def epsilonPlus (i : Fin 3) : Octonions := (0, 0, vectorUnit i, 0)

/-- Nilpotent epsilon-minus coordinates in (3.2). -/
def epsilonMinus (i : Fin 3) : Octonions := (0, 0, 0, vectorUnit i)

example : shift3 2 = 0 := rfl

example (v : Vec3) : dotProduct 0 v = 0 := by simp [dotProduct]

example : crossProduct (vectorUnit 0) (vectorUnit 1) 2 = 1 := by
  rw [cross_apply]
  change vectorUnit 0 0 * vectorUnit 1 1 - vectorUnit 0 1 * vectorUnit 1 0 = (1 : ℂ)
  norm_num [vectorUnit]

example : octonionTrace (1, 1, 0, 0) = 2 := by norm_num [octonionTrace]

/-- The complexified two-dimensional composition algebra in its idempotent basis.
Its scalar embedding is r |-> (r,r), its u1 is (-i,i), and rho+ and rho- are (1,0),(0,1).
Conjugation swaps the factors and fixes the base complex field. PDF pp. 17–20. -/
abbrev SplitComposition := ℂ × ℂ

/-- Composition conjugation, NOT base-complex conjugation. -/
def splitConjugation : SplitComposition →ₗ[ℂ] SplitComposition where
  toFun x := (x.2, x.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The scalar part in the split algebra. -/
def splitScalarPart : SplitComposition →ₗ[ℂ] ℂ where
  toFun x := (x.1 + x.2) / 2
  map_add' x y := by dsimp; ring
  map_smul' r x := by change (r * x.1 + r * x.2) / 2 = r * ((x.1 + x.2) / 2); ring

/-- Complexified quaternions as M2(C), with symplectic conjugation, not conjugate transpose. -/
abbrev QuaternionComposition := Matrix (Fin 2) (Fin 2) ℂ

/-- Quaternion composition conjugation q |-> tr(q)I-q; it fixes every base scalar. PDF pp. 20–21. -/
def quaternionConjugation : QuaternionComposition →ₗ[ℂ] QuaternionComposition where
  toFun q := Matrix.trace q • (1 : QuaternionComposition) - q
  map_add' q r := by simp only [Matrix.trace_add, add_smul]; abel
  map_smul' r q := by simp [Matrix.trace_smul, smul_sub, smul_smul, mul_comm]

/-- Scalar part of a complexified quaternion, half its 2 by 2 matrix trace. -/
def quaternionScalarPart : QuaternionComposition →ₗ[ℂ] ℂ :=
  (1 / 2 : ℂ) • Matrix.traceLinearMap (Fin 2) ℂ ℂ

section AssociativeCoordinates

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Composition-conjugate transpose, complex-linear. PDF §§2,6–8. -/
def daggerMap (c : A →ₗ[ℂ] A) : Mat3 A →ₗ[ℂ] Mat3 A where
  toFun x i j := c (x j i)
  map_add' x y := by ext i j; exact c.map_add _ _
  map_smul' r x := by ext i j; exact c.map_smul r _

/-- H3(A) as an actual subspace of matrices with composition-conjugate symmetry. -/
def hermitianSpace (c : A →ₗ[ℂ] A) : Submodule ℂ (Mat3 A) :=
  LinearMap.ker (daggerMap c - LinearMap.id)

/-- Scalar trace, taking scalar parts of diagonal composition entries. PDF pp. 7–8,21. -/
def scalarTrace (p : A →ₗ[ℂ] ℂ) : Mat3 A →ₗ[ℂ] ℂ :=
  p.comp (Matrix.traceLinearMap (Fin 3) ℂ A)

/-- Jordan multiplication (xy+yx)/2, using associative matrix products here. -/
def jordanProduct (x y : Mat3 A) : Mat3 A := (1 / 2 : ℂ) • (x * y + y * x)

/-- t(x,y)=t(x dot y); for quaternion entries it must not be replaced by an A-valued trace.
This composition-algebra scalar pairing differs from the accepted Bool-matrix
and trace-class pairings named tracePair. PDF pp. 7–8,13,21. -/
def jordanScalarTracePair (p : A →ₗ[ℂ] ℂ) (x y : Mat3 A) : ℂ := scalarTrace p (jordanProduct x y)

/-- The unhalved polarization x#y from (2.6), expanded as (5.4). PDF pp. 8,13. -/
def sharpProduct (p : A →ₗ[ℂ] ℂ) (x y : Mat3 A) : Mat3 A :=
  x * y + y * x - scalarTrace p x • y - scalarTrace p y • x +
    (scalarTrace p x * scalarTrace p y - jordanScalarTracePair p x y) • (1 : Mat3 A)

/-- Vector cross product with sharp in place of scalar multiplication, (5.4). -/
def jordanCross (p : A →ₗ[ℂ] ℂ) (x y : Fin 3 → Mat3 A) : Fin 3 → Mat3 A :=
  fun i => sharpProduct p (x (shift3 i)) (y (shift3 (shift3 i))) -
    sharpProduct p (x (shift3 (shift3 i))) (y (shift3 i))

/-- External a2 action on a column of Jordan matrices. -/
def columnAction (a : Mat3 ℂ) (x : Fin 3 → Mat3 A) : Fin 3 → Mat3 A :=
  fun i => ∑ j, a i j • x j

/-- External contragredient row contraction; its minus sign is in the bracket. -/
def rowAction (x : Fin 3 → Mat3 A) (a : Mat3 ℂ) : Fin 3 → Mat3 A :=
  fun i => ∑ j, a j i • x j

/-- The external traceless component of the diamond product (5.4). -/
def diamondExternal (p : A →ₗ[ℂ] ℂ) (x y : Fin 3 → Mat3 A) : Mat3 ℂ :=
  ((∑ k, jordanScalarTracePair p (x k) (y k)) / 3) • (1 : Mat3 ℂ) -
    Matrix.of (fun i j => jordanScalarTracePair p (x i) (y j))

/-- The central component of the diamond product (5.4), before taking a commutator. -/
def diamondCentral (p : A →ₗ[ℂ] ℂ) (x y : Fin 3 → Mat3 A) : Mat3 A :=
  ((∑ k, jordanScalarTracePair p (x k) (y k)) / 3) • (1 : Mat3 A) - ∑ k, x k * y k

abbrev AssociativeRaw (A : Type*) := Mat3 ℂ × Mat3 A × (Fin 3 → Mat3 A) × (Fin 3 → Mat3 A)

/-- Raw (5.3)/(6.3) bracket, including both diamond components and both cross terms.
The bottom-right block is determined by minus the dagger of the central slot. -/
def associativeBracket (c : A →ₗ[ℂ] A) (p : A →ₗ[ℂ] ℂ)
    (x y : AssociativeRaw A) : AssociativeRaw A :=
  (matrixComm x.1 y.1 + diamondExternal p x.2.2.1 y.2.2.2 -
     diamondExternal p y.2.2.1 x.2.2.2,
   matrixComm x.2.1 y.2.1 + diamondCentral p x.2.2.1 y.2.2.2 -
     diamondCentral p y.2.2.1 x.2.2.2,
   (fun i => columnAction x.1 y.2.2.1 i - columnAction y.1 x.2.2.1 i +
     x.2.1 * y.2.2.1 i + y.2.2.1 i * daggerMap c x.2.1 -
     y.2.1 * x.2.2.1 i - x.2.2.1 i * daggerMap c y.2.1 +
     jordanCross p x.2.2.2 y.2.2.2 i),
   (fun i => rowAction x.2.2.2 y.1 i - rowAction y.2.2.2 x.1 i -
     daggerMap c x.2.1 * y.2.2.2 i - y.2.2.2 i * x.2.1 +
     daggerMap c y.2.1 * x.2.2.2 i + x.2.2.2 i * y.2.1 +
     jordanCross p x.2.2.1 y.2.2.1 i))

/-- Constrained coordinate space; T is the precise central trace constraint and J=H3(A).
Both opposite spaces are complex-linear copies, with the distinct actions above. -/
abbrev AssociativeCoordinates (T J : Submodule ℂ (Mat3 A)) :=
  Sl3 × T × (Fin 3 → J) × (Fin 3 → J)

/-- Retain all entries while forgetting only their subspace membership proofs. -/
def associativeValue {T J : Submodule ℂ (Mat3 A)}
    (x : AssociativeCoordinates T J) : AssociativeRaw A :=
  (x.1.val, x.2.1.val, (fun i => (x.2.2.1 i).val), (fun i => (x.2.2.2 i).val))

/-- The raw cyclic Jacobi expression. It does not assume closure or a LieRing instance. -/
def rawJacobi (c : A →ₗ[ℂ] A) (p : A →ₗ[ℂ] ℂ) (x y z : AssociativeRaw A) : AssociativeRaw A :=
  associativeBracket c p (associativeBracket c p x y) z +
    associativeBracket c p (associativeBracket c p y z) x +
    associativeBracket c p (associativeBracket c p z x) y

example (c : A →ₗ[ℂ] A) : daggerMap c (0 : Mat3 A) = 0 := by
  ext i j
  exact c.map_zero

example (p : A →ₗ[ℂ] ℂ) : scalarTrace p (0 : Mat3 A) = 0 := (scalarTrace p).map_zero

example (p : A →ₗ[ℂ] ℂ) (x : Mat3 A) : sharpProduct p x 0 = 0 := by
  simp [sharpProduct, jordanScalarTracePair, jordanProduct]

end AssociativeCoordinates

/-- F4 coordinates: two complex sl3 factors and opposite triples of symmetric complex matrices. -/
abbrev F4Coordinates := AssociativeCoordinates Sl3 (hermitianSpace (LinearMap.id : ℂ →ₗ[ℂ] ℂ))

/-- E6 central matrices have zero full split-composition trace, i.e. two complex trace constraints. -/
abbrev E6Central := LinearMap.ker (Matrix.traceLinearMap (Fin 3) ℂ SplitComposition)

abbrev E6Coordinates := AssociativeCoordinates E6Central (hermitianSpace splitConjugation)

/-- E7 removes only the scalar quaternionic trace: 36-1=35 central parameters, not 36-4. -/
abbrev E7Central := LinearMap.ker (scalarTrace quaternionScalarPart)

abbrev E7Coordinates := AssociativeCoordinates E7Central (hermitianSpace quaternionConjugation)

example (x : SplitComposition) : splitConjugation (splitConjugation x) = x := rfl

example : quaternionScalarPart (1 : QuaternionComposition) = 1 := by
  norm_num [quaternionScalarPart, Matrix.trace, Fin.sum_univ_two]

example (r : ℂ) : splitScalarPart (r, r) = r := by
  dsimp [splitScalarPart]
  ring

example (q : QuaternionComposition) : quaternionConjugation q 0 0 = q 1 1 := by
  simp [quaternionConjugation, Matrix.trace, Fin.sum_univ_two]
  <;> ring

/-- Join the two idempotent coefficient matrices, not a base-field conjugation. PDF p. 19. -/
def splitJoin (x y : Mat3 ℂ) : Mat3 SplitComposition := fun i j => (x i j, y i j)

end QAlgorithms.Papers.Independent.Support21.P05


