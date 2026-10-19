-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
-- name    : QAlgorithms_Papers_Independent_Independent1_P02_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:15:00.35012+00:00
-- url     : https://prove2.me/theorems/f2f79ab6-b7ac-4e41-b3b8-f3a82643f8af
-- title:
--   General Entanglement Breaking Channels: supporting definitions
-- statement:
--   Reviewed paper-local supporting definitions and conventions. The attached text aggregates the existing blind readbacks of every definition; it makes no theorem proof claim.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2. PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465. Exact locators remain in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02

abbrev Algebra (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

abbrev Endomorphism (d : ℕ) := Algebra d →ₗ[ℂ] Algebra d

abbrev StateVector (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Trace preservation on all operators (p.2). -/
def PreservesTrace {d : ℕ} (Phi : Endomorphism d) : Prop :=
  ∀ X, (Phi X).trace = X.trace

/-- Positivity alone, without CP or TP (pp.4,6). -/
def PreservesPositive {d : ℕ} (Phi : Endomorphism d) : Prop :=
  ∀ X, X.PosSemidef → (Phi X).PosSemidef

/-- CPT maps (p.2), using the accepted channel predicate. -/
def cptSet (d : ℕ) : Set (Endomorphism d) := {Phi | IsChannel Phi}

/-- EBT maps (p.2), homogeneous EB with trace preservation. -/
def ebtSet (d : ℕ) : Set (Endomorphism d) :=
  {Phi | Entanglement.IsEntanglementBreakingPositive Phi ∧ PreservesTrace Phi}

/-- Eq.(1), pp.2,4,5. The Boolean selects the POVM specialization.
The general case allows an empty list, representing the zero map. -/
def HasHolevoRepresentation {d : ℕ} (Phi : Endomorphism d) (normalized : Bool) : Prop :=
  ∃ m : ℕ, ∃ R F : Fin m → Algebra d,
    (∀ k, IsDensityMatrix (R k)) ∧ (∀ k, (F k).PosSemidef) ∧
    (normalized = true → IsPOVM F) ∧ Phi = Entanglement.holevoMap R F

/-- Theorem 4(D), pp.4–5. Rank is exactly one; zero terms may be omitted. -/
def HasRankOneRepresentation {d : ℕ} (Phi : Endomorphism d) (normalized : Bool) : Prop :=
  ∃ m : ℕ, ∃ A : Fin m → Algebra d, (∀ k, (A k).rank = 1) ∧
    (normalized = true → IsKrausFamily A) ∧ ∀ X, Phi X = krausApply A X

/-- Normalized Choi operator, Theorem 4(C), p.4. -/
def choiOperator {d : ℕ} (hd : 0 < d) (Phi : Endomorphism d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  idTensorSuperop Phi (pureDensity (finiteMaxEntangled (Fin d)))

/-- Transposition is complex-linear (Lemma 7, p.9). -/
def transposeEndomorphism (d : ℕ) : Endomorphism d where
  toFun := Matrix.transpose
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Full complex-linear operator sum, Eq.(7), p.6. -/
def krausEndomorphism {d m : ℕ} (A : Fin m → Algebra d) : Endomorphism d where
  toFun := krausApply A
  map_add' X Y := by simp [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' a X := by simp [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- Unitary conjugation as a linear map (p.2). -/
def conjugationEndomorphism {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) : Endomorphism d :=
  krausEndomorphism (fun _ : Fin 1 => (U : Algebra d))

/-- The point channel on all operators, X ↦ Tr(X)R (p.3). -/
def pointEndomorphism {d : ℕ} (R : Algebra d) : Endomorphism d :=
  Entanglement.holevoMap (fun _ : Fin 1 => R) (fun _ => 1)

/-- Purity includes unit normalization (p.2). -/
def IsPureDensity {d : ℕ} (R : Algebra d) : Prop :=
  ∃ psi : StateVector d, IsState psi ∧ R = pureDensity psi

/-- CQ: orthonormal input basis, arbitrary density outputs (p.3). -/
def IsCQ {d : ℕ} (Phi : Endomorphism d) : Prop :=
  ∃ e : OrthonormalBasis (Fin d) ℂ (StateVector d), ∃ R : Fin d → Algebra d,
    (∀ k, IsDensityMatrix (R k)) ∧
    Phi = Entanglement.holevoMap R (fun k => pureDensity (e k))

/-- QC: orthonormal output basis and a POVM, allowing zero effects (p.3). -/
def IsQC {d : ℕ} (Phi : Endomorphism d) : Prop :=
  ∃ e : OrthonormalBasis (Fin d) ℂ (StateVector d), ∃ F : Fin d → Algebra d,
    IsPOVM F ∧ Phi = Entanglement.holevoMap (fun k => pureDensity (e k)) F

/-- Eq.(8), p.7: compute the map from the supplied vectors. -/
def pureCQEndomorphism {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d))
    (psi : Fin d → StateVector d) : Endomorphism d :=
  Entanglement.holevoMap (fun k => pureDensity (psi k)) (fun k => pureDensity (e k))

/-- Source-defined "extreme CQ", without assuming convex extremality (pp.3,7). -/
def IsPureCQ {d : ℕ} (Phi : Endomorphism d) : Prop :=
  ∃ e : OrthonormalBasis (Fin d) ℂ (StateVector d), ∃ psi : Fin d → StateVector d,
    (∀ k, IsState (psi k)) ∧ Phi = pureCQEndomorphism e psi

/-- Outer product, conjugating the bra. -/
def outerOperator {d : ℕ} (v w : StateVector d) : Algebra d :=
  Matrix.of fun i j => v i * star (w j)

/-- Eq.(3), p.3: sqrt(R_k)|e_m⟩⟨f_n|sqrt(F_k). -/
def holevoKrausOperators {d m : ℕ} (R F : Fin m → Algebra d)
    (e f : OrthonormalBasis (Fin d) ℂ (StateVector d)) :
    Fin m × (Fin d × Fin d) → Algebra d :=
  fun z => cfc Real.sqrt (R z.1) * outerOperator (e z.2.1) (f z.2.2) * cfc Real.sqrt (F z.1)

/-- CQ reduction, p.4: f is the input basis, e arbitrary. -/
def cqKrausOperators {d : ℕ} (R : Fin d → Algebra d)
    (e f : OrthonormalBasis (Fin d) ℂ (StateVector d)) : Fin d × Fin d → Algebra d :=
  fun z => cfc Real.sqrt (R z.1) * outerOperator (e z.2) (f z.1)

/-- QC reduction, p.4: e is the output basis, f arbitrary. -/
def qcKrausOperators {d : ℕ} (F : Fin d → Algebra d)
    (e f : OrthonormalBasis (Fin d) ℂ (StateVector d)) : Fin d × Fin d → Algebra d :=
  fun z => outerOperator (e z.1) (f z.2) * cfc Real.sqrt (F z.1)

/-- Proposed correction, pp.8–9: E_3 uses g_- instead of the printed g_+.
The correction is pending independent source moderation. -/
def trineEffects (g : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) : Fin 4 → Algebra 4 :=
  ![(2/3 : ℂ) • pureDensity (g 0),
    (2/3 : ℂ) • pureDensity ((1/2 : ℂ) • g 0 + (Real.sqrt 3/2 : ℂ) • g 1),
    (2/3 : ℂ) • pureDensity ((1/2 : ℂ) • g 0 - (Real.sqrt 3/2 : ℂ) • g 1),
    pureDensity (g 2) + pureDensity (g 3)]

/-- Computed four-dimensional example, pp.8–9, with the recorded correction. -/
def trineEndomorphism (g e : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) : Endomorphism 4 :=
  Entanglement.holevoMap (fun k => pureDensity (e k)) (trineEffects g)

/-- Tetrahedral vectors of Eq.(19), p.11, in the specified basis. -/
def tetrahedralVectors (e : OrthonormalBasis (Fin 3) ℂ (StateVector 3)) : Fin 4 → StateVector 3 :=
  fun i => ((Real.sqrt 3)⁻¹ : ℂ) •
    (![e 0 + e 1 + e 2, e 0 - e 1 - e 2,
      -e 0 + e 1 - e 2, -e 0 - e 1 + e 2] i)

/-- Eq.(19), p.11, including its 3/4 factor. -/
def tetrahedralEndomorphism (e : OrthonormalBasis (Fin 3) ℂ (StateVector 3)) : Endomorphism 3 :=
  Entanglement.holevoMap (fun i => pureDensity (tetrahedralVectors e i))
    (fun i => (3/4 : ℂ) • pureDensity (tetrahedralVectors e i))

/-- Section 4's real Hilbert–Schmidt basis, p.12. Span is exactly the Hermitian
space; no reconstruction identity or coordinate bound is assumed. -/
structure HermitianFrame (d : ℕ) where
  positive : 0 < d
  matrix : Fin (d^2) → Algebra d
  hermitian : ∀ j, (matrix j).IsHermitian
  orthonormal : ∀ j k, ((matrix j * matrix k).trace).re = if j = k then 1 else 0
  spans : ∀ X : Algebra d, X.IsHermitian → X ∈ Submodule.span ℝ (Set.range matrix)
  identity : matrix ⟨0,by positivity⟩ = ((Real.sqrt d)⁻¹ : ℂ) • 1
  traceless : ∀ j, j.val ≠ 0 → (matrix j).trace = 0

/-- Eq.(23), p.12: coefficients computed by trace. -/
def hermitianCoordinates {d : ℕ} (G : HermitianFrame d) (X : Algebra d) : Fin (d^2) → ℝ :=
  fun j => (X * G.matrix j).trace.re

/-- Full real coordinate matrix, pp.12–13. -/
def coordinateMatrix {d : ℕ} (G : HermitianFrame d) (Phi : Endomorphism d) :
    Matrix (Fin (d^2)) (Fin (d^2)) ℝ :=
  Matrix.of fun j k => (G.matrix j * Phi (G.matrix k)).trace.re

/-- W,U each have d² rows and m columns (p.13). -/
def coordinateFactors {d m : ℕ} (G : HermitianFrame d) (R F : Fin m → Algebra d) :
    Matrix (Fin (d^2)) (Fin m) ℝ × Matrix (Fin (d^2)) (Fin m) ℝ :=
  (Matrix.of fun j k => hermitianCoordinates G (R k) j,
    Matrix.of fun j k => hermitianCoordinates G (F k) j)

/-! Sanity checks of local definitions, not proofs of source theorems. -/

example (d : ℕ) : PreservesTrace (LinearMap.id : Endomorphism d) := fun _ => rfl

example (d : ℕ) : PreservesPositive (0 : Endomorphism d) := fun _ _ => Matrix.PosSemidef.zero

example (d : ℕ) : HasHolevoRepresentation (0 : Endomorphism d) false := by
  refine ⟨0, Fin.elim0, Fin.elim0, (fun k => Fin.elim0 k), (fun k => Fin.elim0 k), ?_, ?_⟩
  · intro h; cases h
  · ext X i j; simp [Entanglement.holevoMap]

example (d : ℕ) : HasRankOneRepresentation (0 : Endomorphism d) false := by
  refine ⟨0, Fin.elim0, (fun k => Fin.elim0 k), ?_, ?_⟩
  · intro h; cases h
  · intro X; simp [krausApply]

example {d : ℕ} (hd : 0 < d) : choiOperator hd (0 : Endomorphism d) = 0 := rfl

example (X : Algebra 1) : transposeEndomorphism 1 (transposeEndomorphism 1 X) = X := rfl

example {d : ℕ} (X : Algebra d) : conjugationEndomorphism (1 : Matrix.unitaryGroup (Fin d) ℂ) X = X := by
  simp [conjugationEndomorphism, krausEndomorphism, krausApply]

example {d : ℕ} (R X : Algebra d) : pointEndomorphism R X = X.trace • R := by
  simp [pointEndomorphism, Entanglement.holevoMap]

example (v : StateVector 1) : outerOperator v v = pureDensity v := rfl

example {d m : ℕ} (F : Fin m → Algebra d)
    (e f : OrthonormalBasis (Fin d) ℂ (StateVector d)) :
    holevoKrausOperators (fun _ => 0) F e f = 0 := by
  funext z; simp [holevoKrausOperators, cfc_zero]

example {d : ℕ} (e f : OrthonormalBasis (Fin d) ℂ (StateVector d)) :
    cqKrausOperators (fun _ => 0) e f = 0 ∧ qcKrausOperators (fun _ => 0) e f = 0 := by
  constructor <;> funext z <;> simp [cqKrausOperators, qcKrausOperators, cfc_zero]

example (g : OrthonormalBasis (Fin 4) ℂ (StateVector 4)) :
    trineEffects g 3 = pureDensity (g 2) + pureDensity (g 3) := rfl

example (e : OrthonormalBasis (Fin 3) ℂ (StateVector 3)) :
    tetrahedralVectors e 1 = ((Real.sqrt 3)⁻¹ : ℂ) • (e 0 - e 1 - e 2) := rfl

example {d : ℕ} (G : HermitianFrame d) : hermitianCoordinates G 0 = 0 := by
  funext j; simp [hermitianCoordinates]

example {d : ℕ} (G : HermitianFrame d) : coordinateMatrix G 0 = 0 := by
  ext j k; simp [coordinateMatrix]

example {d : ℕ} (G : HermitianFrame d) :
    coordinateFactors G (fun _ : Fin 0 => 0) (fun _ => 0) = (0,0) := by
  apply Prod.ext <;> ext j k <;> exact Fin.elim0 k






















end QAlgorithms.Papers.Independent.Independent1.P02


