-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P22
-- name    : QAlgorithms_Papers_Independent_Renew46_P22
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:29:12.989313+00:00
-- url     : https://prove2.me/theorems/7f327fdb-b879-4445-a68d-346d5d639889
-- title:
--   Definitions for Constructing algebraic groups from their Lie algebras
-- statement:
--   The objects the formalized statements of *Constructing algebraic groups from their Lie algebras* (arXiv:math/0612557) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GeometricGL`: Geometric invertible matrices as units, PDF p.2.
--   - `Coord`: Row/column matrix-entry indices, PDF p.2.
--   - `Poly`: The source coordinate polynomial ring R(n,F), PDF p.2.
--   - `zeros`: The geometric zero locus of base-field equations, relative to GeometricGL. PDF p.2.
--   - `vanishingIdeal`: The full ideal of base-field polynomials vanishing on geometric points. PDF p.2.
--   - `zariskiClosure`: Relative Zariski closure, using all K-polynomials vanishing on S. PDF p.3.
--   - `IsZariskiClosed`: Closedness in GeometricGL, rather than in the entire affine matrix space. PDF pp.2–3.
--   - `IsAlgebraicGroup`: A geometric algebraic matrix subgroup. PDF p.2.
--   - `DefinedOver`: The source's ideal-generation definition of being defined over F. PDF p.2.
--   - `IsZariskiConnected`: Connectedness by the absence of a separation by relatively closed sets. PDF p.1.
--   - `identityEquations`: Identity equations used in Algorithm 3, Step 1. PDF p.3.
--   - `tangentSet`: Tangent vectors over F, computed from the full geometric vanishing ideal. PDF p.2.
--   - `groupHull`: Intrinsic hull: intersect all algebraic groups whose tangent contains L. The ambient group is included explicitly as an upper bound, so the infimum is never taken over an empty class. No selected answer or output specification is a field. PDF pp.2,5.
--   - `IsAlgebraicLie`: Algebraicity in the embedded, connected, F-defined geometric sense. PDF pp.1–2.
--   - `genericNilpotent`: The polynomial linear combination of the input nilpotent basis. PDF p.4.
--   - `polynomialExponential`: Finite matrix exponential; Engel triangularization gives nilpotence exponent at most n. For n=0 the empty sum equals the unique empty identity matrix. PDF p.4.
--   - `exponentialGraphIdeal`: The graph ideal I=(xij-Mij), constructed from the given basis. PDF p.4.
--   - `nilpotentEliminationIdeal`: Contraction of I to the matrix-coordinate polynomial ring, not an assumed answer. PDF p.4.
--   - `rotationEquations`: Exactly the three returned equations in Example 8. PDF p.7.
--   - `relationKernel`: Kernel of the root-sum map over an arbitrary coefficient ring. R=Z gives Lambda; R=Q gives Lambda_Q. PDF p.5.
--   - `IntegerRowsBasis`: Integral rows form a basis of the full relation lattice, not merely a sublattice. PDF p.5.
--   - `RationalRowsBasis`: Rational images of all rows form a basis of the entire rational kernel. PDF p.5.
--   - `rectangularDiagonal`: Rectangular diagonal matrix; extra columns are zero. PDF pp.5–6.
--   - `SmithData`: The source's unimodular transformations and positive Smith factors. PDF pp.5–6.
--   - `saturationMatrix`: The actual matrix P^{-1} S' Q^{-1}, with every nonzero diagonal factor replaced by 1. PDF p.6.
--   - `centralizerWithin`: Centralizer of D within S. Its underlying sum later is a submodule sum. PDF p.8.
--   - `matrixNilpotentIdeal`: The largest matrix-nilpotent ideal, distinct from the abstract Lie nilradical. PDF p.8.
--   - `ambientSubmodule`: Ambient matrix image of an F-subspace of g. PDF pp.8–9.
--   - `ToralComplement`: A toral complement inside the source's solvable radical, with an actual direct vector sum. PDF p.8.
--   - `SolvableContext`: The starting structure explicitly supplied before Lemma 9, not its conclusions. PDF p.8.
--   - `IsCartanInRadical`: Cartan in the indicated solvable radical, using Mathlib's nilpotent/self-normalizing definition. PDF p.8.
--   - `nilpotentPart`: The canonical nilpotent matrix part selected from Mathlib's proved Jordan existence theorem. This mathematical definition is noncomputable and is never advertised as an algorithm. PDF p.9.
--   - `semisimplePart`: The corresponding semisimple matrix part of the same Jordan decomposition. PDF p.9.
--   - `bracketIterate`: [h,[h,...,[h,s]...]], with exactly k factors h. PDF p.9.
--   - `fittingOne`: The positive Fitting component: intersection over every positive bracket depth. PDF p.9.
--   - `NormalUnipotentWithin`: Connected normal unipotent algebraic subgroups, inside a specified geometric group. Normality repairs the omitted word in the opening of section 5. PDF p.8.
--   - `IsUnipotentRadical`: The unipotent radical as the largest connected normal unipotent algebraic subgroup. PDF p.8.
--   - `IsReductive`: Reductivity in characteristic zero, expressed by trivial connected normal unipotent subgroups. PDF p.8.
--   - `IsMaximalReductiveWithin`: A maximal reductive subgroup of the specified connected group. PDF p.8.
--   - `IsSemidirectProduct`: Internal semidirect product, including normality, trivial intersection, and product exhaustion. PDF p.8.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, https://arxiv.org/abs/math/0612557v1

import Mathlib

/-!
Statements from de Graaf, Constructing algebraic groups from their Lie algebras,
arXiv:math/0612557v1. Paper-specific objects are local; standard matrix and set operations come from Mathlib.
Geometric points live in GeometricGL(n,K), for the specified algebraic closure K/F.
The computational headlines deferred in HARD.md are deliberately absent.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P22

open scoped BigOperators Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Geometric invertible matrices as units, PDF p.2. -/
abbrev GeometricGL (n : ℕ) (K : Type*) [Field K] := (Matrix (Fin n) (Fin n) K)ˣ

/-- Row/column matrix-entry indices, PDF p.2. -/
abbrev Coord (n : ℕ) := Fin n × Fin n

/-- The source coordinate polynomial ring R(n,F), PDF p.2. -/
abbrev Poly (n : ℕ) (R : Type*) [CommSemiring R] := MvPolynomial (Coord n) R

/-- The geometric zero locus of base-field equations, relative to GeometricGL. PDF p.2. -/
def zeros {n : ℕ} {F K : Type*} [Field F] [Field K] [Algebra F K]
    (S : Set (Poly n F)) : Set (GeometricGL n K) :=
  {a | ∀ p ∈ S, MvPolynomial.eval₂ (algebraMap F K) (Function.uncurry (a : Matrix (Fin n) (Fin n) K)) p = 0}

/-- The full ideal of base-field polynomials vanishing on geometric points. PDF p.2. -/
def vanishingIdeal {n : ℕ} (F : Type*) {K : Type*}
    [Field F] [Field K] [Algebra F K] (S : Set (GeometricGL n K)) : Ideal (Poly n F) :=
  MvPolynomial.vanishingIdeal F ((fun a : GeometricGL n K => Function.uncurry (a : Matrix (Fin n) (Fin n) K)) '' S)

/-- Relative Zariski closure, using all K-polynomials vanishing on S. PDF p.3. -/
def zariskiClosure {n : ℕ} {K : Type*} [Field K] (S : Set (GeometricGL n K)) : Set (GeometricGL n K) :=
  zeros (↑(vanishingIdeal (n := n) K S) : Set (Poly n K))

/-- Closedness in GeometricGL, rather than in the entire affine matrix space. PDF pp.2–3. -/
def IsZariskiClosed {n : ℕ} {K : Type*} [Field K] (S : Set (GeometricGL n K)) : Prop :=
  ∃ P : Set (Poly n K), S = zeros P

/-- A geometric algebraic matrix subgroup. PDF p.2. -/
def IsAlgebraicGroup {n : ℕ} {K : Type*} [Field K] (H : Subgroup (GeometricGL n K)) : Prop :=
  IsZariskiClosed (H : Set (GeometricGL n K))

/-- The source's ideal-generation definition of being defined over F. PDF p.2. -/
def DefinedOver {n : ℕ} (F : Type*) {K : Type*}
    [Field F] [Field K] [Algebra F K] (H : Subgroup (GeometricGL n K)) : Prop :=
  vanishingIdeal K (H : Set (GeometricGL n K)) =
    Ideal.span ((MvPolynomial.map (algebraMap F K)) ''
      (vanishingIdeal F (H : Set (GeometricGL n K)) : Set (Poly n F)))

/-- Connectedness by the absence of a separation by relatively closed sets. PDF p.1. -/
def IsZariskiConnected {n : ℕ} {K : Type*} [Field K] (S : Set (GeometricGL n K)) : Prop :=
  S.Nonempty ∧ ∀ U V : Set (GeometricGL n K), IsZariskiClosed U → IsZariskiClosed V →
    S ⊆ U ∪ V → S ∩ U ∩ V = ∅ → S ⊆ U ∨ S ⊆ V

/-- Identity equations used in Algorithm 3, Step 1. PDF p.3. -/
def identityEquations (n : ℕ) (F : Type*) [Field F] : Set (Poly n F) :=
  Set.range (fun ij : Coord n => MvPolynomial.X ij - MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) F) ij.1 ij.2))

/-- Tangent vectors over F, computed from the full geometric vanishing ideal. PDF p.2. -/
def tangentSet {n : ℕ} (F : Type*) {K : Type*}
    [Field F] [Field K] [Algebra F K] (H : Subgroup (GeometricGL n K)) : Set (Matrix (Fin n) (Fin n) F) :=
  {X | ∀ p ∈ vanishingIdeal K (H : Set (GeometricGL n K)),
    ∑ ij : Coord n, algebraMap F K (X ij.1 ij.2) *
      MvPolynomial.eval (Function.uncurry (1 : Matrix (Fin n) (Fin n) K)) (MvPolynomial.pderiv ij p) = 0}

/-- Intrinsic hull: intersect all algebraic groups whose tangent contains L.
The ambient group is included explicitly as an upper bound, so the infimum is
never taken over an empty class. No selected answer or output specification is a field. PDF pp.2,5. -/
def groupHull {n : ℕ} (F : Type*) (K : Type*) [Field F] [Field K] [Algebra F K]
    (L : Submodule F (Matrix (Fin n) (Fin n) F)) : Subgroup (GeometricGL n K) :=
  sInf (insert ⊤ {H : Subgroup (GeometricGL n K) | IsAlgebraicGroup H ∧
    (L : Set (Matrix (Fin n) (Fin n) F)) ⊆ tangentSet F H})

/-- Algebraicity in the embedded, connected, F-defined geometric sense. PDF pp.1–2. -/
def IsAlgebraicLie {n : ℕ} (F K : Type*) [Field F] [Field K] [Algebra F K]
    (g : LieSubalgebra F (Matrix (Fin n) (Fin n) F)) : Prop :=
  ∃ G : Subgroup (GeometricGL n K), IsAlgebraicGroup G ∧ DefinedOver F G ∧
    IsZariskiConnected (G : Set (GeometricGL n K)) ∧ tangentSet F G = (g : Set (Matrix (Fin n) (Fin n) F))

example {n : ℕ} {F K : Type*} [Field F] [Field K] [Algebra F K] :
    zeros (∅ : Set (Poly n F)) = (Set.univ : Set (GeometricGL n K)) := by
  ext a
  simp [zeros]

example {n : ℕ} {F K : Type*} [Field F] [Field K] [Algebra F K] :
    (1 : GeometricGL n K) ∈ zeros (identityEquations n F) := by
  intro p hp
  obtain ⟨ij, rfl⟩ := hp
  by_cases hij : ij.1 = ij.2 <;> simp [Function.uncurry, Matrix.one_apply, hij]

example {n : ℕ} {F K : Type*} [Field F] [Field K] [Algebra F K] :
    zeros (identityEquations n F) = ({1} : Set (GeometricGL n K)) := by
  ext a
  constructor
  · intro ha
    have hm : (a : Matrix (Fin n) (Fin n) K) = 1 := by
      ext i j
      have hp := ha (MvPolynomial.X (i, j) - MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) F) i j))
        ⟨(i, j), rfl⟩
      have hpzero : (a : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j = 0 := by
        by_cases hij : i = j <;> simpa [Function.uncurry, Matrix.one_apply, hij] using hp
      exact sub_eq_zero.mp hpzero
    exact Set.mem_singleton_iff.mpr (Units.ext hm)
  · intro ha
    have haone : a = 1 := Set.mem_singleton_iff.mp ha
    subst a
    intro p hp
    obtain ⟨ij, rfl⟩ := hp
    by_cases hij : ij.1 = ij.2 <;> simp [Function.uncurry, Matrix.one_apply, hij]

example {n : ℕ} {K : Type*} [Field K] :
    IsAlgebraicGroup (⊤ : Subgroup (GeometricGL n K)) := by
  refine ⟨∅, ?_⟩
  ext a
  simp [zeros]

example {n : ℕ} {F K : Type*} [Field F] [Field K] [Algebra F K]
    (L : Submodule F (Matrix (Fin n) (Fin n) F)) :
    (insert ⊤ {H : Subgroup (GeometricGL n K) | IsAlgebraicGroup H ∧
      (L : Set (Matrix (Fin n) (Fin n) F)) ⊆ tangentSet F H}).Nonempty := by
  exact ⟨⊤, Set.mem_insert _ _⟩

section Geometric

variable {F K : Type*} [Field F] [hchar : CharZero F] [Field K] [Algebra F K] [hclosure : IsAlgClosure F K]
variable {n : ℕ}

section

include hchar hclosure

end

/-- The polynomial linear combination of the input nilpotent basis. PDF p.4. -/
def genericNilpotent {r : ℕ} (B : Fin r → Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin r ⊕ Coord n) F) :=
  fun i j => ∑ k : Fin r, MvPolynomial.X (Sum.inl k) * MvPolynomial.C (B k i j)

/-- Finite matrix exponential; Engel triangularization gives nilpotence exponent at most n.
For n=0 the empty sum equals the unique empty identity matrix. PDF p.4. -/
def polynomialExponential {r : ℕ} (B : Fin r → Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin r ⊕ Coord n) F) :=
  ∑ k ∈ Finset.range n, (MvPolynomial.C (((Nat.factorial k : ℕ) : F)⁻¹) :
    MvPolynomial (Fin r ⊕ Coord n) F) •
    (genericNilpotent B) ^ k

/-- The graph ideal I=(xij-Mij), constructed from the given basis. PDF p.4. -/
def exponentialGraphIdeal {r : ℕ} (B : Fin r → Matrix (Fin n) (Fin n) F) :
    Ideal (MvPolynomial (Fin r ⊕ Coord n) F) :=
  Ideal.span (Set.range (fun ij : Coord n =>
    MvPolynomial.X (Sum.inr ij) - polynomialExponential B ij.1 ij.2))

/-- Contraction of I to the matrix-coordinate polynomial ring, not an assumed answer. PDF p.4. -/
def nilpotentEliminationIdeal {r : ℕ} (B : Fin r → Matrix (Fin n) (Fin n) F) : Ideal (Poly n F) :=
  Ideal.comap (MvPolynomial.rename (Sum.inr : Coord n → Fin r ⊕ Coord n)).toRingHom
    (exponentialGraphIdeal B)

section

include hchar hclosure

end

/-- Exactly the three returned equations in Example 8. PDF p.7. -/
def rotationEquations : Set (Poly 2 F) :=
  {MvPolynomial.X (0, 0) ^ 2 + MvPolynomial.X (0, 1) ^ 2 - 1,
   MvPolynomial.X (1, 0) + MvPolynomial.X (0, 1),
   MvPolynomial.X (0, 0) - MvPolynomial.X (1, 1)}

section

include hchar hclosure

end

end Geometric

section Relations

variable {K : Type*} [Field K] [CharZero K] {m n : ℕ}

/-- Kernel of the root-sum map over an arbitrary coefficient ring.
R=Z gives Lambda; R=Q gives Lambda_Q. PDF p.5. -/
def relationKernel (R : Type*) [CommRing R] [Algebra R K] (alpha : Fin n → K) :
    Submodule R (Fin n → R) :=
  LinearMap.ker
    ({
      toFun := fun e => ∑ i : Fin n, algebraMap R K (e i) * alpha i
      map_add' := by
        intro x y
        simp [map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a e
        simp [map_mul, mul_assoc, Finset.mul_sum, Algebra.smul_def] } :
      (Fin n → R) →ₗ[R] K)

/-- Integral rows form a basis of the full relation lattice, not merely a sublattice. PDF p.5. -/
def IntegerRowsBasis (alpha : Fin n → K) (B : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  LinearIndependent ℤ B ∧ Submodule.span ℤ (Set.range B) = relationKernel ℤ alpha

/-- Rational images of all rows form a basis of the entire rational kernel. PDF p.5. -/
def RationalRowsBasis (alpha : Fin n → K) (B : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  LinearIndependent ℚ (fun i j => (B i j : ℚ)) ∧
    Submodule.span ℚ (Set.range (fun i j => (B i j : ℚ))) = relationKernel ℚ alpha

/-- Rectangular diagonal matrix; extra columns are zero. PDF pp.5–6. -/
def rectangularDiagonal (m n : ℕ) (d : Fin m → ℤ) : Matrix (Fin m) (Fin n) ℤ :=
  fun i j => if i.val = j.val then d i else 0

/-- The source's unimodular transformations and positive Smith factors. PDF pp.5–6. -/
structure SmithData (B : Matrix (Fin m) (Fin n) ℤ) where
  rows_le_cols : m ≤ n
  P : (Matrix (Fin m) (Fin m) ℤ)ˣ
  Q : (Matrix (Fin n) (Fin n) ℤ)ˣ
  factors : Fin m → ℤ
  positive : ∀ i, 0 < factors i
  divides : ∀ i j, i.val ≤ j.val → factors i ∣ factors j
  equation : (P : Matrix (Fin m) (Fin m) ℤ) * B *
    (Q : Matrix (Fin n) (Fin n) ℤ) = rectangularDiagonal m n factors

/-- The actual matrix P^{-1} S' Q^{-1}, with every nonzero diagonal factor replaced by 1. PDF p.6. -/
def saturationMatrix {B : Matrix (Fin m) (Fin n) ℤ} (D : SmithData B) :
    Matrix (Fin m) (Fin n) ℤ :=
  (D.P⁻¹ : Matrix (Fin m) (Fin m) ℤ) * rectangularDiagonal m n (fun _ => 1) *
    (D.Q⁻¹ : Matrix (Fin n) (Fin n) ℤ)

example : rectangularDiagonal 1 2 (fun _ => 1) (0 : Fin 1) (0 : Fin 2) = 1 := by
  rfl

example : rectangularDiagonal 1 2 (fun _ => 1) (0 : Fin 1) (1 : Fin 2) = 0 := by
  rfl

variable {F : Type*} [Field F] [hcharF : CharZero F] [Algebra F K] [hclosureF : IsAlgClosure F K]

section

include hcharF hclosureF

end

section

include hcharF hclosureF

end

end Relations

section LieStructure

variable {F K : Type*} [Field F] [hchar : CharZero F] [Field K] [Algebra F K] [hclosure : IsAlgClosure F K]
variable {n : ℕ}

/-- Centralizer of D within S. Its underlying sum later is a submodule sum. PDF p.8. -/
def centralizerWithin {L : Type*} [LieRing L] [LieAlgebra F L]
    (S D : LieSubalgebra F L) : LieSubalgebra F L where
  carrier := {x | x ∈ S ∧ ∀ y ∈ D, ⁅y, x⁆ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine ⟨S.add_mem hx.1 hy.1, ?_⟩
    intro z hz
    simp [lie_add, hx.2 z hz, hy.2 z hz]
  smul_mem' := by
    intro a x hx
    refine ⟨S.smul_mem a hx.1, ?_⟩
    intro z hz
    simp [lie_smul, hx.2 z hz]
  lie_mem' := by
    intro x y hx hy
    refine ⟨S.lie_mem hx.1 hy.1, ?_⟩
    intro z hz
    rw [leibniz_lie, hx.2 z hz, hy.2 z hz, zero_lie, lie_zero, add_zero]

/-- The largest matrix-nilpotent ideal, distinct from the abstract Lie nilradical. PDF p.8. -/
def matrixNilpotentIdeal (g : LieSubalgebra F (Matrix (Fin n) (Fin n) F)) : LieIdeal F g :=
  sSup {I : LieIdeal F g | ∀ x : I, IsNilpotent ((x : g) : Matrix (Fin n) (Fin n) F)}

/-- Ambient matrix image of an F-subspace of g. PDF pp.8–9. -/
def ambientSubmodule (g : LieSubalgebra F (Matrix (Fin n) (Fin n) F)) (S : Submodule F g) :
    Submodule F (Matrix (Fin n) (Fin n) F) := S.map g.toSubmodule.subtype

/-- A toral complement inside the source's solvable radical, with an actual direct vector sum. PDF p.8. -/
structure ToralComplement (g : LieSubalgebra F (Matrix (Fin n) (Fin n) F)) (d : LieSubalgebra F g) : Prop where
  inside : d ≤ (LieAlgebra.radical F g).toLieSubalgebra
  abelian : ∀ x y : d, ⁅(x : g), (y : g)⁆ = 0
  semisimple : ∀ x : d, Module.End.IsSemisimple (Matrix.mulVecLin ((x : g) : Matrix (Fin n) (Fin n) F))
  sum_eq : d.toSubmodule ⊔ (matrixNilpotentIdeal g).toSubmodule =
    (LieAlgebra.radical F g).toSubmodule
  disjoint : Disjoint d.toSubmodule (matrixNilpotentIdeal g).toSubmodule

/-- The starting structure explicitly supplied before Lemma 9, not its conclusions. PDF p.8. -/
structure SolvableContext (g : LieSubalgebra F (Matrix (Fin n) (Fin n) F)) (d : LieSubalgebra F g) : Prop where
  algebraic : IsAlgebraicLie F K g
  toral : ToralComplement g d
  nilpotent_characterization : ∀ x : g, x ∈ matrixNilpotentIdeal g ↔
    x ∈ LieAlgebra.radical F g ∧ IsNilpotent (x : Matrix (Fin n) (Fin n) F)

/-- Cartan in the indicated solvable radical, using Mathlib's nilpotent/self-normalizing definition. PDF p.8. -/
def IsCartanInRadical (g : LieSubalgebra F (Matrix (Fin n) (Fin n) F)) (h : LieSubalgebra F g) : Prop :=
  h ≤ (LieAlgebra.radical F g).toLieSubalgebra ∧
    (h.comap (LieAlgebra.radical F g).toLieSubalgebra.incl).IsCartanSubalgebra

section

include hchar hclosure

end

section

include hchar hclosure

end

/-- The canonical nilpotent matrix part selected from Mathlib's proved Jordan existence theorem.
This mathematical definition is noncomputable and is never advertised as an algorithm. PDF p.9. -/
def nilpotentPart (X : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  LinearMap.toMatrix' (Classical.choose (Module.End.exists_isNilpotent_isSemisimple (f := Matrix.mulVecLin X)))

/-- The corresponding semisimple matrix part of the same Jordan decomposition. PDF p.9. -/
def semisimplePart (X : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  LinearMap.toMatrix' (Classical.choose
    (Classical.choose_spec (Module.End.exists_isNilpotent_isSemisimple (f := Matrix.mulVecLin X))).2)

/-- [h,[h,...,[h,s]...]], with exactly k factors h. PDF p.9. -/
def bracketIterate {L : Type*} [LieRing L] [LieAlgebra F L]
    (h s : Submodule F L) : ℕ → Submodule F L
  | 0 => s
  | k + 1 => Submodule.span F {z | ∃ a ∈ h, ∃ b ∈ bracketIterate h s k, z = ⁅a, b⁆}

/-- The positive Fitting component: intersection over every positive bracket depth. PDF p.9. -/
def fittingOne {L : Type*} [LieRing L] [LieAlgebra F L]
    (h s : Submodule F L) : Submodule F L :=
  ⨅ k : ℕ, bracketIterate h s (k + 1)

section

include hchar hclosure

end

/-- Connected normal unipotent algebraic subgroups, inside a specified geometric group.
Normality repairs the omitted word in the opening of section 5. PDF p.8. -/
def NormalUnipotentWithin (G U : Subgroup (GeometricGL n K)) : Prop :=
  U ≤ G ∧ IsAlgebraicGroup U ∧ IsZariskiConnected (U : Set (GeometricGL n K)) ∧
    (∀ a ∈ G, ∀ u ∈ U, a * u * a⁻¹ ∈ U) ∧
    (∀ u ∈ U, IsNilpotent ((u : Matrix (Fin n) (Fin n) K) - 1))

/-- The unipotent radical as the largest connected normal unipotent algebraic subgroup. PDF p.8. -/
def IsUnipotentRadical (G U : Subgroup (GeometricGL n K)) : Prop :=
  NormalUnipotentWithin G U ∧ ∀ V, NormalUnipotentWithin G V → V ≤ U

/-- Reductivity in characteristic zero, expressed by trivial connected normal unipotent subgroups. PDF p.8. -/
def IsReductive (H : Subgroup (GeometricGL n K)) : Prop :=
  IsAlgebraicGroup H ∧ IsZariskiConnected (H : Set (GeometricGL n K)) ∧
    ∀ U, NormalUnipotentWithin H U → U = ⊥

/-- A maximal reductive subgroup of the specified connected group. PDF p.8. -/
def IsMaximalReductiveWithin (G H : Subgroup (GeometricGL n K)) : Prop :=
  H ≤ G ∧ IsReductive H ∧ ∀ J, J ≤ G → IsReductive J → H ≤ J → J = H

/-- Internal semidirect product, including normality, trivial intersection, and product exhaustion. PDF p.8. -/
def IsSemidirectProduct (G H U : Subgroup (GeometricGL n K)) : Prop :=
  H ≤ G ∧ U ≤ G ∧ (∀ a ∈ G, ∀ u ∈ U, a * u * a⁻¹ ∈ U) ∧
    Disjoint H U ∧ ∀ a ∈ G, ∃ h ∈ H, ∃ u ∈ U, a = h * u

section

include hchar hclosure

end

end LieStructure

end QAlgorithms.Papers.Independent.Renew46.P22


