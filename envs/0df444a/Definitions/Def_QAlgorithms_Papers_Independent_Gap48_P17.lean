-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17
-- name    : QAlgorithms_Papers_Independent_Gap48_P17
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T21:57:49.047082+00:00
-- url     : https://prove2.me/theorems/e8f66b27-22cd-4399-a1b8-18d374f22717
-- title:
--   Definitions for Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$
-- statement:
--   The objects the formalized statements of *Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$* (arXiv:math/9511215) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `signatureMatrix`: The paper's metric matrix, positive directions first (PDF p. 6).
--   - `cliffordQ`: Clifford algebras in this paper use the negative of the metric (PDF pp. 21, 26).
--   - `RealCl`
--   - `RealEvenCl`: A real Clifford algebra's actual even subalgebra, not a tabulated model.
--   - `ComplexCl`
--   - `ComplexEvenCl`
--   - `SpinStable`: Invariant subspace for an explicitly specified set of operators.
--   - `IrreducibleOperators`: Irreducibility includes nontriviality of the represented space.
--   - `SpinRepresentation`: The full spinor is an irreducible Clifford module (PDF p. 7). No irreducibility of its even restriction is assumed.
--   - `cliffordVectorAction`: Vector Clifford multiplication, obtained from the algebra representation.
--   - `spinGenerator`: Infinitesimal spin action of u wedge v, with compatible vector action.
--   - `vectorGenerator`: Standard infinitesimal rotation on the vector module.
--   - `evenOperators`: Actual even Clifford operators in the given representation.
--   - `schurAlgebra`: The Schur algebra is the centralizer of the actual even Clifford action (PDF p. 15).
--   - `invariantForms`: Invariant bilinear forms; the generators span so(g) for the metrics used below.
--   - `equivariantForms`: J: vector-valued families of bilinear forms, equivariant for so(g) (PDF p. 11). The metric identifies V with its linear dual.
--   - `equivariantMultiplications`: M: equivariant multiplications, written in curried form (PDF p. 11).
--   - `formCompose`: Precomposition of the first argument: b_A(s,t)=b(As,t).
--   - `cliffordForm`: The concrete Clifford contraction beta -> j_rho(beta) (PDF pp. 3, 14).
--   - `IsSign`: A two-valued sign is relational, so the zero form has no chosen unique sign.
--   - `FormIsotropy`: Orthogonality/isotropy relative to an explicit grading involution.
--   - `FormSigns`: A form's Clifford type and exchange symmetry (Definition 2.1, PDF p. 18).
--   - `EndSigns`: Endomorphism Clifford type and beta-symmetry (Definition 2.2, PDF p. 18).
--   - `EndIsotropy`: Endomorphism isotropy: preservation or interchange of the chosen halves.
--   - `IrreducibleSubspace`: A subspace is irreducible under the indicated operators, including nonzero.
--   - `SpinSplitting`: Actual semispinor splitting by a compatible Clifford grading, PDF pp. 7, 19. The two eigenspaces are required to be irreducible even modules; they may be equivalent.
--   - `FormAdmissible`: Admissibility with every defined isotropy sign, for the source's chosen splitting. CompleteSplitting separately requires irreducibility when no splitting is supplied.
--   - `EndAdmissible`: Beta-admissibility is a property, without any canonically chosen numerical signs.
--   - `CompleteSplitting`: A missing split is permitted only in the irreducible-even case.
--   - `bracketForms`: The actual symmetry subspace J^sigma, including zero (PDF p. 38).
--   - `refinedBracketForms`: Refined symmetry/isotropy subspace, used only for an actual split (PDF p. 38).
--   - `extensionDimension`: L is dimension of the actual equivariant bracket space, not a count of isomorphism classes.
--   - `refinedExtensionDimension`
--   - `RealAlgebraType`: The possible real matrix-algebra types, omitting matrix size (Definition 1.6, PDF p. 15).
--   - `HasRealAlgebraType`: Actual algebra isomorphism to positive-size matrices of the stated type.
--   - `realTypeTable`: Real Clifford graded-type table, ordered (even algebra, full algebra), PDF p. 15.
--   - `HasRealGradedType`: A graded type is asserted about both actual Clifford algebras.
--   - `HasSchurTable`: Exact real Schur-algebra isomorphisms, PDF p. 16.
--   - `realFormDimensionTable`: Dimensions of invariant real bilinear forms, PDF p. 17.
--   - `volumeElement`: Ordered Clifford volume with respect to an ordered basis, PDF pp. 25, 26, 31.
--   - `PseudoOrthonormal`: The basis has p positive and q negative unit vectors, in that order.
--   - `Counts4`
--   - `totalCounts`: Total plus/minus dimensions from the four refined entries (++,+-,-+,--).
--   - `realRefinedTable`: Table 9's refined entries. Only parity-compatible split signatures are used.
--   - `SplitSignature`: Residues for which the real full spinor has two semispinor summands.
--   - `realTotalTable`: Table 1 / unrefined Table 9. Invalid parity entries are unused.
--   - `complexRefinedTable`: Complex refined table (PDF p. 39), used only in positive even dimension.
--   - `complexTotalTable`: Complex total table; its values at negative integers are periodic residue data.
--   - `actualTotalDimensions`
--   - `actualRefinedDimensions`
--   - `EquivalentSubspaces`: Equivalent subrepresentations; preservation is checked without choosing new actions.
--   - `TwoIrreducibleSummands`: Two irreducible summands, with their equivalence or inequivalence retained.
--   - `RealDimensionClassification`: All real dimension identifications concern genuine Hom spaces, never the table as a definition.
--   - `RealTableSymmetries`: Periodicity and mirror supersymmetry on the realizable parity lattice.
--   - `gammaStep`: Reflections used in the introduction, acting on integer residue coordinates.
--   - `gammaTildeStep`
--   - `gammaOrbit`: Reflection group orbits, given by the equivalence closure of the generating reflections.
--   - `gammaTildeOrbit`
--   - `reflectionDomain`: Closed reflection domain F (PDF p. 4).
--   - `enlargedDomain`: The seven representatives for the enlarged group (PDF p. 5).
--   - `signatureDomain`: Nonnegative (p,q) representatives, not the same coordinate pairs as enlargedDomain.
--   - `orthogonalSpace`: Real metric-skew matrices, the concrete so(p,q).
--   - `poincareSpace`: Underlying vector space of so(p,q) semidirect V, PDF p. 6.
--   - `poincareBracket`: Explicit semidirect bracket on ambient affine coefficients.
--   - `AffineIsometryCoefficients`: Affine isometry coefficients, without restricting to an orientation component.
--   - `metricIsometryGroup`: The actual group of interval-preserving bijections of pseudo-Euclidean space. The theorem below identifies it with all affine metric isometries.
--   - `IsometryVelocity`: The tangent space at the identity of the affine metric isometry group. A smooth curve is required locally to lie in the actual group; no tangent membership equation is assumed as a substitute for a curve.
--   - `PinInvariant`: Invariance under all unit-vector Clifford actions equals invariance under their products, i.e. Pin invariance (PDF p. 24).
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, https://arxiv.org/abs/math/9511215v1

import Mathlib

/-!
Statements from Alekseevsky--Cortes, arXiv:math/9511215v1.
All new definitions are confined to this paper. The Clifford quadratic form is
minus the metric. Invariance is tested on the spanning infinitesimal rotations,
with spin action one quarter of the Clifford commutator. Bilinear forms are
linear over the indicated field, including in the complex case.
-/

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The paper's metric matrix, positive directions first (PDF p. 6). -/
def signatureMatrix (p q : ℕ) : Matrix (Fin (p + q)) (Fin (p + q)) ℝ :=
  Matrix.diagonal (fun i => if i.val < p then 1 else -1)

/-- Clifford algebras in this paper use the negative of the metric (PDF pp. 21, 26). -/
def cliffordQ {K : Type*} [Field K] {d : ℕ}
    (g : Matrix (Fin d) (Fin d) K) : QuadraticForm K ((Fin d → K)) :=
  (-g).toQuadraticForm'

abbrev RealCl (p q : ℕ) := CliffordAlgebra (cliffordQ (signatureMatrix p q))

/-- A real Clifford algebra's actual even subalgebra, not a tabulated model. -/
noncomputable abbrev RealEvenCl (p q : ℕ) := CliffordAlgebra.even (cliffordQ (signatureMatrix p q))

abbrev ComplexCl (d : ℕ) :=
  CliffordAlgebra (cliffordQ (1 : Matrix (Fin d) (Fin d) ℂ))

noncomputable abbrev ComplexEvenCl (d : ℕ) :=
  CliffordAlgebra.even (cliffordQ (1 : Matrix (Fin d) (Fin d) ℂ))

/-- Invariant subspace for an explicitly specified set of operators. -/
def SpinStable {K S : Type*} [Field K] [AddCommGroup S] [Module K S]
    (operators : Set (Module.End K S)) (P : Submodule K S) : Prop :=
  ∀ A ∈ operators, ∀ x ∈ P, A x ∈ P

/-- Irreducibility includes nontriviality of the represented space. -/
def IrreducibleOperators {K S : Type*} [Field K] [AddCommGroup S] [Module K S]
    (operators : Set (Module.End K S)) : Prop :=
  Nontrivial S ∧ ∀ P : Submodule K S, SpinStable operators P → P = ⊥ ∨ P = ⊤

/-- The full spinor is an irreducible Clifford module (PDF p. 7).
No irreducibility of its even restriction is assumed. -/
structure SpinRepresentation {K : Type*} [Field K] {d : ℕ}
    (g : Matrix (Fin d) (Fin d) K) (S : Type*) [AddCommGroup S] [Module K S] where
  action : CliffordAlgebra (cliffordQ g) →ₐ[K] Module.End K S
  irreducible : IrreducibleOperators (Set.range action)

section SpinDefinitions

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

/-- Vector Clifford multiplication, obtained from the algebra representation. -/
def cliffordVectorAction (rho : SpinRepresentation g S) : (Fin d → K) →ₗ[K] Module.End K S :=
  rho.action.toLinearMap.comp (CliffordAlgebra.ι (cliffordQ g))

/-- Infinitesimal spin action of u wedge v, with compatible vector action. -/
def spinGenerator (rho : SpinRepresentation g S) (u v : (Fin d → K)) : Module.End K S :=
  (1 / 4 : K) • (cliffordVectorAction rho u * cliffordVectorAction rho v -
    cliffordVectorAction rho v * cliffordVectorAction rho u)

/-- Standard infinitesimal rotation on the vector module. -/
def vectorGenerator (g : Matrix (Fin d) (Fin d) K) (u v x : (Fin d → K)) : (Fin d → K) :=
  (g.toBilin' u x) • v - (g.toBilin' v x) • u

/-- Actual even Clifford operators in the given representation. -/
def evenOperators (rho : SpinRepresentation g S) : Set (Module.End K S) :=
  {A | ∃ a : CliffordAlgebra.even (cliffordQ g), rho.action a.val = A}

/-- The Schur algebra is the centralizer of the actual even Clifford action (PDF p. 15). -/
def schurAlgebra (rho : SpinRepresentation g S) : Subalgebra K (Module.End K S) :=
  Subalgebra.centralizer K (evenOperators rho)

/-- Invariant bilinear forms; the generators span so(g) for the metrics used below. -/
def invariantForms (rho : SpinRepresentation g S) : Submodule K (LinearMap.BilinForm K S) where
  carrier := {b | ∀ u v s t, b (spinGenerator rho u v s) t +
    b s (spinGenerator rho u v t) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro b c hb hc u v s t
    change (b (spinGenerator rho u v s) t + c (spinGenerator rho u v s) t) +
      (b s (spinGenerator rho u v t) + c s (spinGenerator rho u v t)) = 0
    linear_combination hb u v s t + hc u v s t
  smul_mem' := by
    intro a b hb u v s t
    change a * b (spinGenerator rho u v s) t + a * b s (spinGenerator rho u v t) = 0
    rw [← mul_add, hb u v s t, mul_zero]

/-- J: vector-valued families of bilinear forms, equivariant for so(g) (PDF p. 11).
The metric identifies V with its linear dual. -/
def equivariantForms (rho : SpinRepresentation g S) :
    Submodule K ((Fin d → K) →ₗ[K] LinearMap.BilinForm K S) where
  carrier := {j | ∀ u v x s t,
    j (vectorGenerator g u v x) s t + j x (spinGenerator rho u v s) t +
      j x s (spinGenerator rho u v t) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro j k hj hk u v x s t
    change (j (vectorGenerator g u v x) s t + k (vectorGenerator g u v x) s t) +
      (j x (spinGenerator rho u v s) t + k x (spinGenerator rho u v s) t) +
      (j x s (spinGenerator rho u v t) + k x s (spinGenerator rho u v t)) = 0
    linear_combination hj u v x s t + hk u v x s t
  smul_mem' := by
    intro a j hj u v x s t
    change a * j (vectorGenerator g u v x) s t +
      a * j x (spinGenerator rho u v s) t + a * j x s (spinGenerator rho u v t) = 0
    linear_combination a * hj u v x s t

/-- M: equivariant multiplications, written in curried form (PDF p. 11). -/
def equivariantMultiplications (rho : SpinRepresentation g S) :
    Submodule K ((Fin d → K) →ₗ[K] Module.End K S) where
  carrier := {mu | ∀ u v x s,
    mu (vectorGenerator g u v x) s =
      spinGenerator rho u v (mu x s) - mu x (spinGenerator rho u v s)}
  zero_mem' := by simp
  add_mem' := by
    intro mu nu hmu hnu u v x s
    simp only [LinearMap.add_apply, map_add]
    rw [hmu u v x s, hnu u v x s]
    abel
  smul_mem' := by
    intro a mu hmu u v x s
    simp only [LinearMap.smul_apply, map_smul]
    rw [hmu u v x s, smul_sub]

/-- Precomposition of the first argument: b_A(s,t)=b(As,t). -/
def formCompose (b : LinearMap.BilinForm K S) (A : Module.End K S) :
    LinearMap.BilinForm K S := LinearMap.comp b A

/-- The concrete Clifford contraction beta -> j_rho(beta) (PDF pp. 3, 14). -/
def cliffordForm (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) :
    (Fin d → K) →ₗ[K] LinearMap.BilinForm K S where
  toFun v := formCompose b (cliffordVectorAction rho v)
  map_add' v w := by
    ext s t
    simp [formCompose, map_add]
  map_smul' a v := by
    ext s t
    simp [formCompose]

/-- A two-valued sign is relational, so the zero form has no chosen unique sign. -/
def IsSign (a : K) : Prop := a = 1 ∨ a = -1

/-- Orthogonality/isotropy relative to an explicit grading involution. -/
def FormIsotropy (E : Module.End K S) (b : LinearMap.BilinForm K S) (i : K) : Prop :=
  IsSign i ∧ ∀ s t, b (E s) t = i * b s (E t)

/-- A form's Clifford type and exchange symmetry (Definition 2.1, PDF p. 18). -/
def FormSigns (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S)
    (tau sigma : K) : Prop :=
  IsSign tau ∧ IsSign sigma ∧
    (∀ v s t, b (cliffordVectorAction rho v s) t = tau * b s (cliffordVectorAction rho v t)) ∧
    (∀ s t, b t s = sigma * b s t)

/-- Endomorphism Clifford type and beta-symmetry (Definition 2.2, PDF p. 18). -/
def EndSigns (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S)
    (A : Module.End K S) (tau sigma : K) : Prop :=
  IsSign tau ∧ IsSign sigma ∧
    (∀ v, cliffordVectorAction rho v * A = tau • (A * cliffordVectorAction rho v)) ∧
    (∀ s t, b (A s) t = sigma * b s (A t))

/-- Endomorphism isotropy: preservation or interchange of the chosen halves. -/
def EndIsotropy (E A : Module.End K S) (i : K) : Prop :=
  IsSign i ∧ E * A = i • (A * E)

/-- A subspace is irreducible under the indicated operators, including nonzero. -/
def IrreducibleSubspace (operators : Set (Module.End K S)) (P : Submodule K S) : Prop :=
  P ≠ ⊥ ∧ SpinStable operators P ∧
    ∀ Q : Submodule K S, Q ≤ P → SpinStable operators Q → Q = ⊥ ∨ Q = P

/-- Actual semispinor splitting by a compatible Clifford grading, PDF pp. 7, 19.
The two eigenspaces are required to be irreducible even modules; they may be equivalent. -/
structure SpinSplitting (rho : SpinRepresentation g S) where
  grading : Module.End K S
  square : grading * grading = 1
  odd : ∀ v, grading * cliffordVectorAction rho v = -(cliffordVectorAction rho v * grading)
  positive_irreducible : IrreducibleSubspace (evenOperators rho)
    (LinearMap.ker (grading - 1))
  negative_irreducible : IrreducibleSubspace (evenOperators rho)
    (LinearMap.ker (grading + 1))

/-- Admissibility with every defined isotropy sign, for the source's chosen splitting.
CompleteSplitting separately requires irreducibility when no splitting is supplied. -/
def FormAdmissible (rho : SpinRepresentation g S) (splitting : Option (SpinSplitting rho))
    (b : LinearMap.BilinForm K S) : Prop :=
  ∃ tau sigma : K, FormSigns rho b tau sigma ∧
    match splitting with
    | none => True
    | some h => ∃ i, FormIsotropy h.grading b i

/-- Beta-admissibility is a property, without any canonically chosen numerical signs. -/
def EndAdmissible (rho : SpinRepresentation g S) (splitting : Option (SpinSplitting rho))
    (b : LinearMap.BilinForm K S) (A : Module.End K S) : Prop :=
  ∃ tau sigma : K, EndSigns rho b A tau sigma ∧
    match splitting with
    | none => True
    | some h => ∃ i, EndIsotropy h.grading A i

/-- A missing split is permitted only in the irreducible-even case. -/
def CompleteSplitting (rho : SpinRepresentation g S)
    (splitting : Option (SpinSplitting rho)) : Prop :=
  match splitting with
  | none => IrreducibleOperators (evenOperators rho)
  | some _ => True

/-- The actual symmetry subspace J^sigma, including zero (PDF p. 38). -/
def bracketForms (rho : SpinRepresentation g S) (sigma : K) :
    Submodule K ((Fin d → K) →ₗ[K] LinearMap.BilinForm K S) where
  carrier := {j | j ∈ equivariantForms rho ∧ ∀ x s t, j x t s = sigma * j x s t}
  zero_mem' := by simp [equivariantForms]
  add_mem' := by
    intro j k hj hk
    refine ⟨(equivariantForms rho).add_mem hj.1 hk.1, ?_⟩
    intro x s t
    change j x t s + k x t s = sigma * (j x s t + k x s t)
    rw [hj.2, hk.2, mul_add]
  smul_mem' := by
    intro a j hj
    refine ⟨(equivariantForms rho).smul_mem a hj.1, ?_⟩
    intro x s t
    change a * j x t s = sigma * (a * j x s t)
    rw [hj.2]
    ring

/-- Refined symmetry/isotropy subspace, used only for an actual split (PDF p. 38). -/
def refinedBracketForms (rho : SpinRepresentation g S) (h : SpinSplitting rho)
    (sigma iota : K) : Submodule K ((Fin d → K) →ₗ[K] LinearMap.BilinForm K S) where
  carrier := {j | j ∈ bracketForms rho sigma ∧
    ∀ x s t, j x (h.grading s) t = iota * j x s (h.grading t)}
  zero_mem' := by simp [bracketForms, equivariantForms]
  add_mem' := by
    intro j k hj hk
    refine ⟨(bracketForms rho sigma).add_mem hj.1 hk.1, ?_⟩
    intro x s t
    change j x (h.grading s) t + k x (h.grading s) t =
      iota * (j x s (h.grading t) + k x s (h.grading t))
    rw [hj.2, hk.2, mul_add]
  smul_mem' := by
    intro a j hj
    refine ⟨(bracketForms rho sigma).smul_mem a hj.1, ?_⟩
    intro x s t
    change a * j x (h.grading s) t = iota * (a * j x s (h.grading t))
    rw [hj.2]
    ring

/-- L is dimension of the actual equivariant bracket space, not a count of isomorphism classes. -/
noncomputable def extensionDimension (rho : SpinRepresentation g S) (sigma : K) : ℕ :=
  Module.finrank K (bracketForms rho sigma)

noncomputable def refinedExtensionDimension (rho : SpinRepresentation g S)
    (h : SpinSplitting rho) (sigma iota : K) : ℕ :=
  Module.finrank K (refinedBracketForms rho h sigma iota)

example (rho : SpinRepresentation g S) :
    (0 : LinearMap.BilinForm K S) ∈ invariantForms rho :=
  (invariantForms rho).zero_mem

example (rho : SpinRepresentation g S) :
    (0 : (Fin d → K) →ₗ[K] LinearMap.BilinForm K S) ∈ bracketForms rho 1 :=
  (bracketForms rho 1).zero_mem

example (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S)
    (v : (Fin d → K)) (s t : S) :
    cliffordForm rho b v s t = b (cliffordVectorAction rho v s) t := rfl

end SpinDefinitions

/-- The possible real matrix-algebra types, omitting matrix size (Definition 1.6, PDF p. 15). -/
inductive RealAlgebraType
  | realSimple | complexSimple | quaternionSimple
  | realSplit | complexSplit | quaternionSplit
  deriving DecidableEq

/-- Actual algebra isomorphism to positive-size matrices of the stated type. -/
def HasRealAlgebraType (A : Type*) [Ring A] [Algebra ℝ A] (t : RealAlgebraType) : Prop :=
  match t with
  | .realSimple => ∃ k : ℕ, 0 < k ∧ Nonempty (A ≃ₐ[ℝ] Matrix (Fin k) (Fin k) ℝ)
  | .complexSimple => ∃ k : ℕ, 0 < k ∧ Nonempty (A ≃ₐ[ℝ] Matrix (Fin k) (Fin k) ℂ)
  | .quaternionSimple => ∃ k : ℕ, 0 < k ∧
      Nonempty (A ≃ₐ[ℝ] Matrix (Fin k) (Fin k) (Quaternion ℝ))
  | .realSplit => ∃ k : ℕ, 0 < k ∧
      Nonempty (A ≃ₐ[ℝ] (Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ))
  | .complexSplit => ∃ k : ℕ, 0 < k ∧
      Nonempty (A ≃ₐ[ℝ] (Matrix (Fin k) (Fin k) ℂ × Matrix (Fin k) (Fin k) ℂ))
  | .quaternionSplit => ∃ k : ℕ, 0 < k ∧
      Nonempty (A ≃ₐ[ℝ] (Matrix (Fin k) (Fin k) (Quaternion ℝ) ×
        Matrix (Fin k) (Fin k) (Quaternion ℝ)))

/-- Real Clifford graded-type table, ordered (even algebra, full algebra), PDF p. 15. -/
def realTypeTable (s : ℤ) : RealAlgebraType × RealAlgebraType :=
  match s % 8 with
  | 1 => (.realSimple, .complexSimple)
  | 2 => (.complexSimple, .quaternionSimple)
  | 3 => (.quaternionSimple, .quaternionSplit)
  | 4 => (.quaternionSplit, .quaternionSimple)
  | 5 => (.quaternionSimple, .complexSimple)
  | 6 => (.complexSimple, .realSimple)
  | 7 => (.realSimple, .realSplit)
  | _ => (.realSplit, .realSimple)

/-- A graded type is asserted about both actual Clifford algebras. -/
def HasRealGradedType (p q : ℕ) (t : RealAlgebraType × RealAlgebraType) : Prop :=
  HasRealAlgebraType (RealEvenCl p q) t.1 ∧ HasRealAlgebraType (RealCl p q) t.2

/-- Exact real Schur-algebra isomorphisms, PDF p. 16. -/
def HasSchurTable (A : Type*) [Ring A] [Algebra ℝ A] (s : ℤ) : Prop :=
  match s % 8 with
  | 1 => Nonempty (A ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
  | 2 => Nonempty (A ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ)
  | 3 => Nonempty (A ≃ₐ[ℝ] Quaternion ℝ)
  | 4 => Nonempty (A ≃ₐ[ℝ] (Quaternion ℝ × Quaternion ℝ))
  | 5 => Nonempty (A ≃ₐ[ℝ] Quaternion ℝ)
  | 6 => Nonempty (A ≃ₐ[ℝ] ℂ)
  | 7 => Nonempty (A ≃ₐ[ℝ] ℝ)
  | _ => Nonempty (A ≃ₐ[ℝ] (ℝ × ℝ))

/-- Dimensions of invariant real bilinear forms, PDF p. 17. -/
def realFormDimensionTable (s : ℤ) : ℕ :=
  match s % 8 with
  | 1 => 4 | 2 => 8 | 3 => 4 | 4 => 8 | 5 => 4 | 6 => 2 | 7 => 1 | _ => 2

/-- Ordered Clifford volume with respect to an ordered basis, PDF pp. 25, 26, 31. -/
noncomputable def volumeElement (p q : ℕ) (e : Module.Basis (Fin (p + q)) ℝ ((Fin (p + q) → ℝ))) : RealCl p q :=
  (List.ofFn fun i => CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) (e i)).prod

/-- The basis has p positive and q negative unit vectors, in that order. -/
def PseudoOrthonormal (p q : ℕ) (e : Module.Basis (Fin (p + q)) ℝ ((Fin (p + q) → ℝ))) : Prop :=
  ∀ i j, (signatureMatrix p q).toBilin' (e i) (e j) = signatureMatrix p q i j

example : realTypeTable 1 = (.realSimple, .complexSimple) := rfl

example : realFormDimensionTable (-1) = 1 := rfl

example (p q : ℕ) (v : (Fin (p + q) → ℝ)) :
    CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) v *
      CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) v =
      algebraMap ℝ (RealCl p q) (cliffordQ (signatureMatrix p q) v) :=
  CliffordAlgebra.ι_sq_scalar _ v

abbrev Counts4 := ℕ × ℕ × ℕ × ℕ

/-- Total plus/minus dimensions from the four refined entries (++,+-,-+,--). -/
def totalCounts (c : Counts4) : ℕ × ℕ := (c.1 + c.2.1, c.2.2.1 + c.2.2.2)

/-- Table 9's refined entries. Only parity-compatible split signatures are used. -/
def realRefinedTable (n s : ℤ) : Counts4 :=
  match s % 8, n % 8 with
  | 0, 0 => (0, 1, 0, 1) | 0, 2 => (2, 0, 0, 0)
  | 0, 4 => (0, 1, 0, 1) | 0, 6 => (0, 0, 2, 0)
  | 1, 1 => (2, 1, 0, 1) | 1, 3 => (2, 1, 0, 1)
  | 1, 5 => (0, 1, 2, 1) | 1, 7 => (0, 1, 2, 1)
  | 2, 0 => (2, 2, 2, 2) | 2, 2 => (4, 2, 0, 2)
  | 2, 4 => (2, 2, 2, 2) | 2, 6 => (0, 2, 4, 2)
  | 4, 0 => (0, 4, 0, 4) | 4, 2 => (6, 0, 2, 0)
  | 4, 4 => (0, 4, 0, 4) | 4, 6 => (2, 0, 6, 0)
  | _, _ => (0, 0, 0, 0)

/-- Residues for which the real full spinor has two semispinor summands. -/
def SplitSignature (s : ℤ) : Prop := s % 8 = 0 ∨ s % 8 = 1 ∨ s % 8 = 2 ∨ s % 8 = 4

/-- Table 1 / unrefined Table 9. Invalid parity entries are unused. -/
def realTotalTable (n s : ℤ) : ℕ × ℕ :=
  if s % 8 = 0 ∨ s % 8 = 1 ∨ s % 8 = 2 ∨ s % 8 = 4 then
    totalCounts (realRefinedTable n s) else
  match s % 8, n % 8 with
  | 3, 1 => (3, 1) | 3, 3 => (3, 1) | 3, 5 => (1, 3) | 3, 7 => (1, 3)
  | 5, 1 => (3, 1) | 5, 3 => (3, 1) | 5, 5 => (1, 3) | 5, 7 => (1, 3)
  | 6, 0 => (1, 1) | 6, 2 => (2, 0) | 6, 4 => (1, 1) | 6, 6 => (0, 2)
  | 7, 1 => (1, 0) | 7, 3 => (1, 0) | 7, 5 => (0, 1) | 7, 7 => (0, 1)
  | _, _ => (0, 0)

/-- Complex refined table (PDF p. 39), used only in positive even dimension. -/
def complexRefinedTable (d : ℤ) : Counts4 :=
  match d % 8 with
  | 0 => (0, 1, 0, 1) | 2 => (2, 0, 0, 0)
  | 4 => (0, 1, 0, 1) | 6 => (0, 0, 2, 0) | _ => (0, 0, 0, 0)

/-- Complex total table; its values at negative integers are periodic residue data. -/
def complexTotalTable (d : ℤ) : ℕ × ℕ :=
  if d % 2 = 0 then totalCounts (complexRefinedTable d) else
  if d % 8 = 1 ∨ d % 8 = 3 then (1, 0) else (0, 1)

section ActualDimensions

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

noncomputable def actualTotalDimensions (rho : SpinRepresentation g S) : ℕ × ℕ :=
  (extensionDimension rho 1, extensionDimension rho (-1))

noncomputable def actualRefinedDimensions (rho : SpinRepresentation g S)
    (h : SpinSplitting rho) : Counts4 :=
  (refinedExtensionDimension rho h 1 1, refinedExtensionDimension rho h 1 (-1),
    refinedExtensionDimension rho h (-1) 1, refinedExtensionDimension rho h (-1) (-1))

/-- Equivalent subrepresentations; preservation is checked without choosing new actions. -/
def EquivalentSubspaces (operators : Set (Module.End K S)) (P Q : Submodule K S) : Prop :=
  ∃ e : P ≃ₗ[K] Q, ∀ A ∈ operators, ∀ x y : P,
    (y : S) = A x → (e y : S) = A (e x)

/-- Two irreducible summands, with their equivalence or inequivalence retained. -/
def TwoIrreducibleSummands (rho : SpinRepresentation g S) (equivalent : Bool) : Prop :=
  ∃ P Q : Submodule K S, IsCompl P Q ∧
    IrreducibleSubspace (evenOperators rho) P ∧
    IrreducibleSubspace (evenOperators rho) Q ∧
    (if equivalent then EquivalentSubspaces (evenOperators rho) P Q else
      ¬ EquivalentSubspaces (evenOperators rho) P Q)

end ActualDimensions

/-- All real dimension identifications concern genuine Hom spaces, never the table as a definition. -/
def RealDimensionClassification : Prop :=
  ∀ (p q : ℕ), 0 < p + q →
    ∀ (S : Type) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
      (rho : SpinRepresentation (signatureMatrix p q) S),
      actualTotalDimensions rho = realTotalTable (p + q) ((p : ℤ) - q) ∧
      (Nonempty (SpinSplitting rho) ↔ SplitSignature ((p : ℤ) - q)) ∧
      ∀ h : SpinSplitting rho,
        actualRefinedDimensions rho h = realRefinedTable (p + q) ((p : ℤ) - q)

/-- Periodicity and mirror supersymmetry on the realizable parity lattice. -/
def RealTableSymmetries : Prop :=
  ∀ n s : ℤ, Even (n + s) →
    realTotalTable (n + 8) s = realTotalTable n s ∧
    realTotalTable n (s + 8) = realTotalTable n s ∧
    realTotalTable (-n) s = ((realTotalTable n s).2, (realTotalTable n s).1) ∧
    (SplitSignature s →
      realRefinedTable (n + 8) s = realRefinedTable n s ∧
      realRefinedTable n (s + 8) = realRefinedTable n s ∧
      realRefinedTable (-n) s =
        ((realRefinedTable n s).2.2.1, (realRefinedTable n s).2.2.2,
          (realRefinedTable n s).1, (realRefinedTable n s).2.1))

/-- Reflections used in the introduction, acting on integer residue coordinates. -/
def gammaStep (a b : ℤ × ℤ) : Prop :=
  b = (-4 - a.1, a.2) ∨ b = (4 - a.1, a.2) ∨
  b = (a.1, -2 - a.2) ∨ b = (a.1, 6 - a.2)

def gammaTildeStep (a b : ℤ × ℤ) : Prop := gammaStep a b ∨ b = (-a.1, a.2)

/-- Reflection group orbits, given by the equivalence closure of the generating reflections. -/
def gammaOrbit : (ℤ × ℤ) → (ℤ × ℤ) → Prop := Relation.EqvGen gammaStep

def gammaTildeOrbit : (ℤ × ℤ) → (ℤ × ℤ) → Prop := Relation.EqvGen gammaTildeStep

/-- Closed reflection domain F (PDF p. 4). -/
def reflectionDomain : Finset (ℤ × ℤ) :=
  {(-2, 0), (-2, 2), (-1, -1), (-1, 1), (-1, 3), (0, 0), (0, 2),
    (1, -1), (1, 1), (1, 3), (2, 0), (2, 2)}

/-- The seven representatives for the enlarged group (PDF p. 5). -/
def enlargedDomain : Finset (ℤ × ℤ) :=
  {(0, 0), (0, 2), (1, -1), (1, 1), (1, 3), (2, 0), (2, 2)}

/-- Nonnegative (p,q) representatives, not the same coordinate pairs as enlargedDomain. -/
def signatureDomain : Finset (ℤ × ℤ) :=
  {(2, 0), (1, 1), (3, 0), (2, 1), (1, 2), (3, 1), (2, 2)}

example : (0, 0) ∈ reflectionDomain := by simp [reflectionDomain]

example : totalCounts (2, 1, 0, 1) = (3, 1) := rfl

/-- Real metric-skew matrices, the concrete so(p,q). -/
def orthogonalSpace (p q : ℕ) : LieSubalgebra ℝ
    (Matrix (Fin (p + q)) (Fin (p + q)) ℝ) :=
  skewAdjointMatricesLieSubalgebra (signatureMatrix p q)

/-- Underlying vector space of so(p,q) semidirect V, PDF p. 6. -/
def poincareSpace (p q : ℕ) : Submodule ℝ
    (Matrix (Fin (p + q)) (Fin (p + q)) ℝ × (Fin (p + q) → ℝ)) :=
  (orthogonalSpace p q).toSubmodule.prod ⊤

/-- Explicit semidirect bracket on ambient affine coefficients. -/
def poincareBracket {d : ℕ}
    (x y : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ)) :
    Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) :=
  (x.1 * y.1 - y.1 * x.1, x.1.mulVec y.2 - y.1.mulVec x.2)

/-- Affine isometry coefficients, without restricting to an orientation component. -/
def AffineIsometryCoefficients (p q : ℕ)
    (A : Matrix (Fin (p + q)) (Fin (p + q)) ℝ) : Prop :=
  A.det ≠ 0 ∧ A.transpose * signatureMatrix p q * A = signatureMatrix p q

/-- The actual group of interval-preserving bijections of pseudo-Euclidean space.
The theorem below identifies it with all affine metric isometries. -/
def metricIsometryGroup (p q : ℕ) : Subgroup (Equiv.Perm ((Fin (p + q) → ℝ))) where
  carrier := {f | ∀ x y, (signatureMatrix p q).toBilin' (f x - f y) (f x - f y) =
    (signatureMatrix p q).toBilin' (x - y) (x - y)}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro f h hf hh x y
    exact (hf (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro f hf x y
    have h := hf (f.symm x) (f.symm y)
    simpa using h.symm

example (p q : ℕ) : (1 : Equiv.Perm ((Fin (p + q) → ℝ))) ∈ metricIsometryGroup p q :=
  (metricIsometryGroup p q).one_mem

/-- The tangent space at the identity of the affine metric isometry group.
A smooth curve is required locally to lie in the actual group; no tangent
membership equation is assumed as a substitute for a curve. -/
def IsometryVelocity (p q : ℕ)
    (z : Matrix (Fin (p + q)) (Fin (p + q)) ℝ × (Fin (p + q) → ℝ)) : Prop :=
  ∃ (A : ℝ → Matrix (Fin (p + q)) (Fin (p + q)) ℝ)
    (b : ℝ → (Fin (p + q) → ℝ)),
    A 0 = 1 ∧ b 0 = 0 ∧ ContDiff ℝ ⊤ A ∧ ContDiff ℝ ⊤ b ∧
    (∀ᶠ t in nhds (0 : ℝ), AffineIsometryCoefficients p q (A t)) ∧
    HasDerivAt A z.1 0 ∧ HasDerivAt b z.2 0

example {d : ℕ} (v w : (Fin d → ℝ)) :
    poincareBracket (0, v) (0, w) = (0, 0) := by simp [poincareBracket]

example {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (w : (Fin d → ℝ)) :
    poincareBracket (A, 0) (0, w) = (0, A.mulVec w) := by simp [poincareBracket]

/-- Invariance under all unit-vector Clifford actions equals invariance under their
products, i.e. Pin invariance (PDF p. 24). -/
def PinInvariant {p q : ℕ} {S : Type*} [AddCommGroup S] [Module ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S)
    (b : LinearMap.BilinForm ℝ S) : Prop :=
  ∀ v : (Fin (p + q) → ℝ),
    ((signatureMatrix p q).toBilin' v v = 1 ∨
      (signatureMatrix p q).toBilin' v v = -1) →
    ∀ s t, b (cliffordVectorAction rho v s) (cliffordVectorAction rho v t) = b s t

/-- Sanity: the metric uses the printed positive/negative sign order. -/
example (p q : ℕ) (i : Fin (p + q)) :
    signatureMatrix p q i i = if i.val < p then 1 else -1 := by
  simp [signatureMatrix]

section AdditionalSanity

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

example (P : Submodule K S) : SpinStable (∅ : Set (Module.End K S)) P := by
  simp [SpinStable]

example (rho : SpinRepresentation g S) : (1 : Module.End K S) ∈ evenOperators rho := by
  exact ⟨1, by simp⟩

example (rho : SpinRepresentation g S) : (1 : Module.End K S) ∈ schurAlgebra rho :=
  (schurAlgebra rho).one_mem

example (rho : SpinRepresentation g S) : FormSigns rho 0 1 1 := by
  simp [FormSigns, IsSign]

example (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) :
    EndSigns rho b 0 1 1 := by
  simp [EndSigns, IsSign]

example (E : Module.End K S) : FormIsotropy E 0 1 := by
  simp [FormIsotropy, IsSign]

example (E : Module.End K S) : EndIsotropy E 0 1 := by
  simp [EndIsotropy, IsSign]

example (rho : SpinRepresentation g S) : FormAdmissible rho none 0 := by
  exact ⟨1, 1, by simp [FormSigns, IsSign], trivial⟩

example (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) :
    EndAdmissible rho none b 0 := by
  exact ⟨1, 1, by simp [EndSigns, IsSign], trivial⟩

example (rho : SpinRepresentation g S) (h : SpinSplitting rho) :
    (0 : (Fin d → K) →ₗ[K] LinearMap.BilinForm K S) ∈ refinedBracketForms rho h 1 1 :=
  (refinedBracketForms rho h 1 1).zero_mem

example (b : LinearMap.BilinForm K S) : formCompose b (1 : Module.End K S) = b := by
  ext s t
  rfl

example (operators : Set (Module.End K S)) (P : Submodule K S) :
    EquivalentSubspaces operators P P := by
  refine ⟨LinearEquiv.refl K P, ?_⟩
  intro A hA x y hxy
  exact hxy

end AdditionalSanity

example : complexRefinedTable (-2) = (0, 0, 2, 0) := rfl

example (a : ℤ × ℤ) : gammaStep a (-4 - a.1, a.2) := Or.inl rfl

example {p q : ℕ} {S : Type*} [AddCommGroup S] [Module ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S) : PinInvariant rho 0 := by
  simp [PinInvariant]

end QAlgorithms.Papers.Independent.Gap48.P17


